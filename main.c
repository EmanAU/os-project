/*
 * ============================================================================
 * RBAC (Role-Based Access Control) System
 * Operating Systems Lab Project
 *
 * Demonstrates: Processes (fork), POSIX Threads, Mutexes, Semaphores,
 *               IPC (pipes + shared memory), File I/O, Deadlock Prevention,
 *               and Process Scheduling Simulation.
 *
 * Author  : OS Lab Student
 * Compile : gcc -o rbac_os_lab rbac_os_lab.c -lpthread -lrt
 * Run     : ./rbac_os_lab
 * ============================================================================
 */

/* ── Standard headers ─────────────────────────────────────────────────── */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <time.h>
#include <signal.h>

/* Processes & IPC */
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <sys/mman.h>
#include <sys/stat.h>

/* Threads & synchronisation */
#include <pthread.h>
#include <semaphore.h>

/* ── Compile-time constants ───────────────────────────────────────────── */
#define MAX_USERS          10
#define MAX_RESOURCES      8
#define MAX_LOG_ENTRIES    256
#define MAX_PENDING_REQS   16
#define USERNAME_LEN       32
#define PASSWORD_LEN       32
#define RESOURCE_NAME_LEN  32
#define LOG_FILE           "rbac_activity.log"
#define USERS_FILE         "rbac_users.dat"
#define SHM_NAME           "/rbac_shared_mem"
#define SHM_SIZE           4096
#define PIPE_BUF_SIZE      256
#define LOCK_TIMEOUT_SEC   3          /* deadlock-prevention timeout */
#define NUM_LOG_THREADS    2
#define NUM_WORKER_THREADS 3

/* ── Role definitions ─────────────────────────────────────────────────── */
typedef enum {
    ROLE_GUEST    = 0,
    ROLE_EMPLOYEE = 1,
    ROLE_MANAGER  = 2,
    ROLE_ADMIN    = 3
} Role;

static const char *role_names[] = { "Guest", "Employee", "Manager", "Admin" };

/* ── Permission bitmask ───────────────────────────────────────────────── */
#define PERM_READ    (1 << 0)   /* 0x01 */
#define PERM_WRITE   (1 << 1)   /* 0x02 */
#define PERM_EXECUTE (1 << 2)   /* 0x04 */
#define PERM_DELETE  (1 << 3)   /* 0x08 */
#define PERM_MANAGE  (1 << 4)   /* 0x10 */

/* Permissions per role (index == Role enum) */
static const int role_permissions[] = {
    /* Guest    */ PERM_READ,
    /* Employee */ PERM_READ | PERM_WRITE | PERM_EXECUTE,
    /* Manager  */ PERM_READ | PERM_WRITE | PERM_EXECUTE | PERM_DELETE,
    /* Admin    */ PERM_READ | PERM_WRITE | PERM_EXECUTE | PERM_DELETE | PERM_MANAGE
};

/* ── User record ──────────────────────────────────────────────────────── */
typedef struct {
    char username[USERNAME_LEN];
    char password[PASSWORD_LEN];   /* plain-text for lab simplicity */
    Role role;
    int  active;
    int  priority;                 /* for scheduling simulation (1–10) */
} User;

/* ── Resource record ─────────────────────────────────────────────────── */
typedef enum {
    RSRC_FILE   = 0,
    RSRC_LOG    = 1,
    RSRC_SHMEM  = 2,
    RSRC_PROTECTED = 3
} ResourceType;

typedef struct {
    int          id;
    char         name[RESOURCE_NAME_LEN];
    ResourceType type;
    int          min_role;         /* minimum role required */
    int          required_perm;    /* required permission bitmask */
    int          locked;           /* currently held (for deadlock demo) */
    pthread_mutex_t mutex;
} Resource;

/* ── Shared-memory segment (IPC) ─────────────────────────────────────── */
typedef struct {
    int   active_users;
    int   total_operations;
    char  last_action[128];
    pid_t last_pid;
} SharedMemData;

/* ── Message-queue message (IPC) ─────────────────────────────────────── */
typedef struct {
    long mtype;
    char mtext[PIPE_BUF_SIZE];
} MsgBuf;

/* ── Log entry ────────────────────────────────────────────────────────── */
typedef struct {
    char      timestamp[32];
    char      username[USERNAME_LEN];
    char      action[128];
    int       success;
} LogEntry;

/* ── Pending request (scheduling queue) ─────────────────────────────── */
typedef struct {
    int  user_idx;
    int  priority;
    char request[128];
} PendingRequest;

/* ── Global state ────────────────────────────────────────────────────── */
static User       g_users[MAX_USERS];
static int        g_user_count   = 0;
static Resource   g_resources[MAX_RESOURCES];
static int        g_resource_count = 0;
static int        g_logged_in_user = -1;   /* index into g_users */

/* Shared-memory */
static SharedMemData *g_shm = NULL;
static int            g_shm_fd  = -1;

/* IPC – anonymous pipe (parent ↔ child) */
static int g_pipe_fd[2] = {-1, -1};

/* Message queue */
static int g_msgq_id = -1;

/* Log queue & thread infrastructure */
static LogEntry      g_log_queue[MAX_LOG_ENTRIES];
static int           g_log_head = 0, g_log_tail = 0, g_log_size = 0;
static pthread_mutex_t g_log_mutex   = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  g_log_cond    = PTHREAD_COND_INITIALIZER;
static pthread_t       g_log_threads[NUM_LOG_THREADS];
static int             g_log_running = 1;

/* Scheduling queue */
static PendingRequest  g_req_queue[MAX_PENDING_REQS];
static int             g_req_count = 0;
static pthread_mutex_t g_req_mutex  = PTHREAD_MUTEX_INITIALIZER;
static sem_t           g_req_sem;
static pthread_t       g_worker_threads[NUM_WORKER_THREADS];
static int             g_workers_running = 1;

/* Resource-hierarchy mutex order (deadlock prevention) */
static pthread_mutex_t g_resource_hierarchy_mutex = PTHREAD_MUTEX_INITIALIZER;

/* Global log-file mutex */
static pthread_mutex_t g_logfile_mutex = PTHREAD_MUTEX_INITIALIZER;

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 1 – Utility helpers
 * ═══════════════════════════════════════════════════════════════════════ */

static void get_timestamp(char *buf, size_t sz)
{
    time_t t = time(NULL);
    struct tm *tm_info = localtime(&t);
    strftime(buf, sz, "%Y-%m-%d %H:%M:%S", tm_info);
}

static void clear_screen(void) { printf("\033[2J\033[H"); }

static void print_separator(char c, int n)
{
    for (int i = 0; i < n; i++) putchar(c);
    putchar('\n');
}

static void print_header(const char *title)
{
    print_separator('=', 60);
    printf("  %s\n", title);
    print_separator('=', 60);
}

/* Safe string input (no trailing newline, length-limited) */
static void safe_input(char *buf, int maxlen)
{
    if (!fgets(buf, maxlen, stdin)) { buf[0] = '\0'; return; }
    buf[strcspn(buf, "\n")] = '\0';
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 2 – Logging subsystem  (uses pthread + mutex + cond variable)
 * ═══════════════════════════════════════════════════════════════════════ */

/*
 * OS CONCEPT – THREADS & SYNCHRONISATION
 * log_worker() runs in a dedicated POSIX thread.  It sleeps on a condition
 * variable (g_log_cond) until a log entry is placed in the queue, then
 * wakes up, claims the mutex, dequeues the entry, writes it to disk, and
 * releases the mutex.  This prevents the main thread from blocking on I/O
 * and demonstrates producer-consumer synchronisation.
 */
static void *log_worker(void *arg)
{
    int tid = *(int *)arg;
    free(arg);
    char ts[32];

    while (1) {
        pthread_mutex_lock(&g_log_mutex);

        /* Wait for work (or shutdown signal) */
        while (g_log_size == 0 && g_log_running)
            pthread_cond_wait(&g_log_cond, &g_log_mutex);

        if (!g_log_running && g_log_size == 0) {
            pthread_mutex_unlock(&g_log_mutex);
            break;
        }

        /* Dequeue one entry */
        LogEntry entry = g_log_queue[g_log_head];
        g_log_head     = (g_log_head + 1) % MAX_LOG_ENTRIES;
        g_log_size--;
        pthread_mutex_unlock(&g_log_mutex);

        /* Write to file – protect with a separate file mutex */
        pthread_mutex_lock(&g_logfile_mutex);
        FILE *f = fopen(LOG_FILE, "a");
        if (f) {
            fprintf(f, "[%s] User=%-12s Action=%-40s Status=%s (log-thread-%d)\n",
                    entry.timestamp, entry.username, entry.action,
                    entry.success ? "OK" : "DENIED", tid);
            fclose(f);
        }
        pthread_mutex_unlock(&g_logfile_mutex);

        /* Also update shared-memory "last action" */
        if (g_shm) {
            pthread_mutex_lock(&g_resource_hierarchy_mutex);
            snprintf(g_shm->last_action, 128, "[%s] %s – %s",
                     entry.timestamp, entry.username, entry.action);
            g_shm->total_operations++;
            pthread_mutex_unlock(&g_resource_hierarchy_mutex);
        }
    }
    (void)ts;
    return NULL;
}

/* Enqueue a log entry (non-blocking for caller) */
static void log_action(const char *username, const char *action, int success)
{
    pthread_mutex_lock(&g_log_mutex);
    if (g_log_size < MAX_LOG_ENTRIES) {
        LogEntry *e = &g_log_queue[g_log_tail];
        get_timestamp(e->timestamp, sizeof(e->timestamp));
        strncpy(e->username, username ? username : "system", USERNAME_LEN - 1);
        strncpy(e->action,   action   ? action   : "",       127);
        e->success  = success;
        g_log_tail  = (g_log_tail + 1) % MAX_LOG_ENTRIES;
        g_log_size++;
        pthread_cond_signal(&g_log_cond);   /* wake one log worker */
    }
    pthread_mutex_unlock(&g_log_mutex);
}

static void start_log_threads(void)
{
    for (int i = 0; i < NUM_LOG_THREADS; i++) {
        int *id = malloc(sizeof(int));
        *id = i + 1;
        pthread_create(&g_log_threads[i], NULL, log_worker, id);
    }
}

static void stop_log_threads(void)
{
    pthread_mutex_lock(&g_log_mutex);
    g_log_running = 0;
    pthread_cond_broadcast(&g_log_cond);
    pthread_mutex_unlock(&g_log_mutex);
    for (int i = 0; i < NUM_LOG_THREADS; i++)
        pthread_join(g_log_threads[i], NULL);
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 3 – User management & Authentication
 * ═══════════════════════════════════════════════════════════════════════ */

static void save_users(void)
{
    FILE *f = fopen(USERS_FILE, "wb");
    if (!f) { perror("save_users"); return; }
    fwrite(&g_user_count, sizeof(int), 1, f);
    fwrite(g_users, sizeof(User), g_user_count, f);
    fclose(f);
}

static void load_users(void)
{
    FILE *f = fopen(USERS_FILE, "rb");
    if (!f) return;   /* no file yet – OK */
    fread(&g_user_count, sizeof(int), 1, f);
    if (g_user_count > MAX_USERS) g_user_count = MAX_USERS;
    fread(g_users, sizeof(User), g_user_count, f);
    fclose(f);
}

static void seed_default_users(void)
{
    /* Only seed once */
    if (g_user_count > 0) return;

    struct { const char *u, *p; Role r; int pri; } defaults[] = {
        { "admin",    "admin123",    ROLE_ADMIN,    10 },
        { "manager1", "mgr123",      ROLE_MANAGER,   7 },
        { "emp1",     "emp123",      ROLE_EMPLOYEE,  5 },
        { "guest1",   "guest123",    ROLE_GUEST,     1 },
    };
    for (int i = 0; i < 4; i++) {
        strncpy(g_users[g_user_count].username, defaults[i].u, USERNAME_LEN - 1);
        strncpy(g_users[g_user_count].password, defaults[i].p, PASSWORD_LEN - 1);
        g_users[g_user_count].role     = defaults[i].r;
        g_users[g_user_count].active   = 1;
        g_users[g_user_count].priority = defaults[i].pri;
        g_user_count++;
    }
    save_users();
}

/* Returns user index on success, -1 on failure */
static int authenticate(const char *username, const char *password)
{
    for (int i = 0; i < g_user_count; i++) {
        if (g_users[i].active &&
            strcmp(g_users[i].username, username) == 0 &&
            strcmp(g_users[i].password, password) == 0)
            return i;
    }
    return -1;
}

static int check_permission(int user_idx, int required_perm)
{
    if (user_idx < 0) return 0;
    return (role_permissions[g_users[user_idx].role] & required_perm) == required_perm;
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 4 – Resource initialisation
 * ═══════════════════════════════════════════════════════════════════════ */

static void init_resources(void)
{
    struct { const char *name; ResourceType type; Role min_role; int perm; } defs[] = {
        { "public_file",      RSRC_FILE,      ROLE_GUEST,    PERM_READ                  },
        { "employee_report",  RSRC_FILE,      ROLE_EMPLOYEE, PERM_READ | PERM_WRITE     },
        { "manager_report",   RSRC_FILE,      ROLE_MANAGER,  PERM_READ | PERM_WRITE     },
        { "system_log",       RSRC_LOG,       ROLE_MANAGER,  PERM_READ                  },
        { "audit_log",        RSRC_LOG,       ROLE_ADMIN,    PERM_READ | PERM_WRITE     },
        { "shared_memory_A",  RSRC_SHMEM,     ROLE_EMPLOYEE, PERM_READ | PERM_WRITE     },
        { "protected_config", RSRC_PROTECTED, ROLE_ADMIN,    PERM_READ | PERM_WRITE | PERM_MANAGE },
        { "exec_scripts",     RSRC_FILE,      ROLE_MANAGER,  PERM_EXECUTE               },
    };
    g_resource_count = 8;
    for (int i = 0; i < g_resource_count; i++) {
        g_resources[i].id            = i;
        strncpy(g_resources[i].name, defs[i].name, RESOURCE_NAME_LEN - 1);
        g_resources[i].type          = defs[i].type;
        g_resources[i].min_role      = defs[i].min_role;
        g_resources[i].required_perm = defs[i].perm;
        g_resources[i].locked        = 0;
        pthread_mutex_init(&g_resources[i].mutex, NULL);
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 5 – Shared memory (IPC)
 * ═══════════════════════════════════════════════════════════════════════ */

/*
 * OS CONCEPT – IPC (SHARED MEMORY)
 * POSIX shared memory lets multiple processes read/write the same physical
 * pages.  Here the parent process creates the segment and a forked child
 * process can also access it.  Access is protected by a mutex to prevent
 * races across threads.
 */
static void init_shared_memory(void)
{
    g_shm_fd = shm_open(SHM_NAME, O_CREAT | O_RDWR, 0666);
    if (g_shm_fd < 0) { perror("shm_open"); return; }
    if (ftruncate(g_shm_fd, SHM_SIZE) < 0) { perror("ftruncate"); return; }
    g_shm = mmap(NULL, SHM_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, g_shm_fd, 0);
    if (g_shm == MAP_FAILED) { perror("mmap"); g_shm = NULL; return; }
    g_shm->active_users      = 0;
    g_shm->total_operations  = 0;
    snprintf(g_shm->last_action, 128, "System initialised");
    g_shm->last_pid = getpid();
}

static void cleanup_shared_memory(void)
{
    if (g_shm) { munmap(g_shm, SHM_SIZE); g_shm = NULL; }
    if (g_shm_fd >= 0) { close(g_shm_fd); g_shm_fd = -1; }
    shm_unlink(SHM_NAME);
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 6 – Scheduling simulation  (priority queue + worker threads)
 * ═══════════════════════════════════════════════════════════════════════ */

/*
 * OS CONCEPT – PROCESS SCHEDULING SIMULATION
 * Requests are inserted into a priority queue (higher priority first).
 * Worker threads pick requests from the queue using a semaphore for
 * signalling and a mutex for exclusive queue access – a classic
 * bounded-buffer / producer-consumer pattern.
 */
static void enqueue_request(int user_idx, const char *request_str)
{
    pthread_mutex_lock(&g_req_mutex);
    if (g_req_count < MAX_PENDING_REQS) {
        PendingRequest req;
        req.user_idx = user_idx;
        req.priority = (user_idx >= 0) ? g_users[user_idx].priority : 0;
        strncpy(req.request, request_str, 127);

        /* Insertion sort by priority (descending) */
        int pos = g_req_count;
        while (pos > 0 && g_req_queue[pos - 1].priority < req.priority) {
            g_req_queue[pos] = g_req_queue[pos - 1];
            pos--;
        }
        g_req_queue[pos] = req;
        g_req_count++;
        sem_post(&g_req_sem);
    }
    pthread_mutex_unlock(&g_req_mutex);
}

static void *worker_thread(void *arg)
{
    int wid = *(int *)arg;
    free(arg);

    while (g_workers_running) {
        /* Block until work is available */
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        ts.tv_sec += 1;
        if (sem_timedwait(&g_req_sem, &ts) == -1) continue;

        pthread_mutex_lock(&g_req_mutex);
        if (g_req_count == 0) { pthread_mutex_unlock(&g_req_mutex); continue; }

        PendingRequest req = g_req_queue[0];
        memmove(g_req_queue, g_req_queue + 1, sizeof(PendingRequest) * (g_req_count - 1));
        g_req_count--;
        pthread_mutex_unlock(&g_req_mutex);

        /* Simulate processing time proportional to priority */
        printf("  [Worker-%d] Processing request (priority=%d): %s\n",
               wid, req.priority, req.request);
        usleep(50000 * (11 - req.priority));   /* higher priority = faster */

        const char *uname = (req.user_idx >= 0) ? g_users[req.user_idx].username : "system";
        log_action(uname, req.request, 1);
    }
    return NULL;
}

static void start_worker_threads(void)
{
    sem_init(&g_req_sem, 0, 0);
    for (int i = 0; i < NUM_WORKER_THREADS; i++) {
        int *id = malloc(sizeof(int));
        *id = i + 1;
        pthread_create(&g_worker_threads[i], NULL, worker_thread, id);
    }
}

static void stop_worker_threads(void)
{
    g_workers_running = 0;
    for (int i = 0; i < NUM_WORKER_THREADS; i++) sem_post(&g_req_sem);
    for (int i = 0; i < NUM_WORKER_THREADS; i++) pthread_join(g_worker_threads[i], NULL);
    sem_destroy(&g_req_sem);
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 7 – Deadlock prevention demo
 * ═══════════════════════════════════════════════════════════════════════ */

/*
 * OS CONCEPT – DEADLOCK PREVENTION
 * Strategy 1: Resource-ordering (mutex hierarchy).
 *   Threads always acquire resource mutexes in ascending ID order, so a
 *   circular-wait (condition 4 of Coffman) can never occur.
 *
 * Strategy 2: Timeout-based locking (try-lock with deadline).
 *   If a thread cannot acquire a mutex within LOCK_TIMEOUT_SEC seconds it
 *   backs off and retries – breaking the "hold-and-wait" condition.
 */
static int try_lock_resource(Resource *r, int timeout_sec)
{
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_sec += timeout_sec;

    int rc = pthread_mutex_timedlock(&r->mutex, &ts);
    if (rc == ETIMEDOUT) {
        printf("  [DEADLOCK-PREV] Timeout acquiring '%s' – backing off.\n", r->name);
        return 0;
    }
    return (rc == 0) ? 1 : 0;
}

static void deadlock_demo(void)
{
    print_header("DEADLOCK PREVENTION DEMONSTRATION");
    printf("\nStrategy: Resource Ordering + Timeout-Based Locking\n\n");

    /* We will lock resource 0 then resource 1, always in ID order */
    Resource *r0 = &g_resources[0];
    Resource *r1 = &g_resources[1];

    printf("Thread main: attempting to lock '%s' (id=%d) first ...\n", r0->name, r0->id);
    if (try_lock_resource(r0, LOCK_TIMEOUT_SEC)) {
        printf("  Acquired '%s'\n", r0->name);
        usleep(100000);

        printf("Thread main: attempting to lock '%s' (id=%d) next ...\n", r1->name, r1->id);
        if (try_lock_resource(r1, LOCK_TIMEOUT_SEC)) {
            printf("  Acquired '%s'\n", r1->name);
            printf("  Performing cross-resource operation ...\n");
            usleep(200000);
            pthread_mutex_unlock(&r1->mutex);
            printf("  Released '%s'\n", r1->name);
        }
        pthread_mutex_unlock(&r0->mutex);
        printf("  Released '%s'\n", r0->name);
    }

    printf("\nDeadlock Prevention Summary:\n");
    printf("  * Resources are always acquired in ascending ID order\n");
    printf("    => circular-wait is impossible (Coffman condition 4 broken)\n");
    printf("  * pthread_mutex_timedlock() backs off after %d s\n", LOCK_TIMEOUT_SEC);
    printf("    => hold-and-wait is broken under contention\n");
    log_action("system", "deadlock_demo_completed", 1);
    printf("\nPress Enter to continue...\n");
    getchar();
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 8 – IPC pipe demo  (fork + pipe)
 * ═══════════════════════════════════════════════════════════════════════ */

/*
 * OS CONCEPT – PROCESSES & IPC (PIPES)
 * fork() creates an exact copy of the current process.  We then use an
 * anonymous pipe so the child can send a status message back to the parent.
 * The parent waits with waitpid() and displays the child's report.
 */
static void fork_ipc_demo(void)
{
    print_header("PROCESS FORK + IPC PIPE DEMONSTRATION");

    if (pipe(g_pipe_fd) == -1) { perror("pipe"); return; }

    pid_t pid = fork();
    if (pid < 0) { perror("fork"); return; }

    if (pid == 0) {
        /* ── CHILD PROCESS ── */
        close(g_pipe_fd[0]);   /* close read end */

        char msg[PIPE_BUF_SIZE];
        snprintf(msg, PIPE_BUF_SIZE,
                 "CHILD(pid=%d): accessed shared resource as forked service process. "
                 "Active users in SHM: %d",
                 getpid(),
                 g_shm ? g_shm->active_users : -1);

        write(g_pipe_fd[1], msg, strlen(msg) + 1);
        close(g_pipe_fd[1]);

        /* Update shared memory */
        if (g_shm) {
            g_shm->last_pid = getpid();
            snprintf(g_shm->last_action, 128, "Child process %d completed", getpid());
        }
        _exit(0);
    } else {
        /* ── PARENT PROCESS ── */
        close(g_pipe_fd[1]);   /* close write end */

        char buf[PIPE_BUF_SIZE] = {0};
        ssize_t n = read(g_pipe_fd[0], buf, PIPE_BUF_SIZE - 1);
        close(g_pipe_fd[0]);

        if (n > 0) {
            printf("\nPARENT(pid=%d) received from child via pipe:\n", getpid());
            printf("  \"%s\"\n", buf);
        }

        int status;
        waitpid(pid, &status, 0);
        printf("\nChild process exited with status %d\n",
               WIFEXITED(status) ? WEXITSTATUS(status) : -1);

        if (g_shm)
            printf("Shared memory last_action: \"%s\"\n", g_shm->last_action);

        log_action("system", "fork_ipc_demo_completed", 1);
    }

    printf("\nPress Enter to continue...\n");
    getchar();
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 9 – Resource access
 * ═══════════════════════════════════════════════════════════════════════ */

static void access_resource(int user_idx, int resource_id)
{
    if (user_idx < 0) { printf("Not logged in.\n"); return; }
    if (resource_id < 0 || resource_id >= g_resource_count) {
        printf("Invalid resource ID.\n"); return;
    }

    Resource *r = &g_resources[resource_id];
    User     *u = &g_users[user_idx];
    char action_buf[128];

    printf("\nAttempting to access resource: %s\n", r->name);

    /* Role-level check */
    if ((int)u->role < r->min_role) {
        snprintf(action_buf, 128, "ACCESS_DENIED role<%s> resource<%s>",
                 role_names[u->role], r->name);
        printf("  ACCESS DENIED: insufficient role (%s required %s).\n",
               role_names[u->role], role_names[r->min_role]);
        log_action(u->username, action_buf, 0);
        return;
    }

    /* Permission check */
    if (!check_permission(user_idx, r->required_perm)) {
        snprintf(action_buf, 128, "ACCESS_DENIED perm<%d> resource<%s>",
                 r->required_perm, r->name);
        printf("  ACCESS DENIED: missing required permission bits.\n");
        log_action(u->username, action_buf, 0);
        return;
    }

    /*
     * OS CONCEPT – MUTEX (CRITICAL SECTION)
     * Before touching the resource we acquire its per-resource mutex.
     * We use the timeout variant so a stuck lock never freezes the UI.
     */
    if (!try_lock_resource(r, LOCK_TIMEOUT_SEC)) {
        printf("  Resource '%s' is busy (timeout). Try again later.\n", r->name);
        return;
    }

    /* Simulate work */
    printf("  Access GRANTED. Performing operation on '%s'...\n", r->name);
    usleep(200000);

    snprintf(action_buf, 128, "ACCESS_OK resource<%s> type<%s>",
             r->name,
             r->type == RSRC_FILE ? "FILE" :
             r->type == RSRC_LOG  ? "LOG"  :
             r->type == RSRC_SHMEM ? "SHMEM" : "PROTECTED");

    log_action(u->username, action_buf, 1);

    /* Enqueue a background follow-up task */
    char sched_req[128];
    snprintf(sched_req, 128, "post-access-callback:%s", r->name);
    enqueue_request(user_idx, sched_req);

    pthread_mutex_unlock(&r->mutex);
    printf("  Operation complete. Resource released.\n");
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 10 – Admin management functions
 * ═══════════════════════════════════════════════════════════════════════ */

static void add_user_admin(int admin_idx)
{
    if (g_users[admin_idx].role != ROLE_ADMIN) {
        printf("Permission denied.\n"); return;
    }
    if (g_user_count >= MAX_USERS) {
        printf("User table full.\n"); return;
    }

    User *nu = &g_users[g_user_count];
    printf("New username  : "); safe_input(nu->username, USERNAME_LEN);
    printf("New password  : "); safe_input(nu->password, PASSWORD_LEN);
    printf("Role (0=Guest,1=Employee,2=Manager,3=Admin): ");
    char rbuf[4]; safe_input(rbuf, sizeof(rbuf));
    int r = atoi(rbuf);
    if (r < 0 || r > 3) r = 0;
    nu->role     = (Role)r;
    nu->active   = 1;
    nu->priority = (r + 1) * 2;

    g_user_count++;
    save_users();

    char act[128];
    snprintf(act, 128, "ADD_USER<%s> role<%s>", nu->username, role_names[nu->role]);
    log_action(g_users[admin_idx].username, act, 1);
    printf("User '%s' added as %s.\n", nu->username, role_names[nu->role]);
}

static void list_users(int user_idx)
{
    if (g_users[user_idx].role < ROLE_MANAGER) {
        printf("Insufficient permissions.\n"); return;
    }
    print_separator('-', 60);
    printf("%-4s %-16s %-10s %-6s %-5s\n", "ID", "Username", "Role", "Active", "Priority");
    print_separator('-', 60);
    for (int i = 0; i < g_user_count; i++) {
        printf("%-4d %-16s %-10s %-6s %-5d\n",
               i,
               g_users[i].username,
               role_names[g_users[i].role],
               g_users[i].active ? "Yes" : "No",
               g_users[i].priority);
    }
    print_separator('-', 60);
    log_action(g_users[user_idx].username, "LIST_USERS", 1);
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 11 – System status (shared memory read)
 * ═══════════════════════════════════════════════════════════════════════ */

static void show_system_status(void)
{
    print_header("SYSTEM STATUS (via Shared Memory)");
    if (!g_shm) { printf("Shared memory unavailable.\n"); return; }

    pthread_mutex_lock(&g_resource_hierarchy_mutex);
    printf("  Active users        : %d\n", g_shm->active_users);
    printf("  Total operations    : %d\n", g_shm->total_operations);
    printf("  Last action         : %s\n", g_shm->last_action);
    printf("  Last PID            : %d\n", (int)g_shm->last_pid);
    pthread_mutex_unlock(&g_resource_hierarchy_mutex);

    printf("\n  Pending scheduled requests : %d\n", g_req_count);

    /* Resource lock states */
    printf("\n  Resource Lock Table:\n");
    printf("  %-24s %-10s %-6s\n", "Resource", "Type", "Locked");
    print_separator('-', 45);
    for (int i = 0; i < g_resource_count; i++) {
        printf("  %-24s %-10s %-6s\n",
               g_resources[i].name,
               g_resources[i].type == RSRC_FILE  ? "FILE"  :
               g_resources[i].type == RSRC_LOG   ? "LOG"   :
               g_resources[i].type == RSRC_SHMEM ? "SHMEM" : "PROT",
               g_resources[i].locked ? "YES" : "no");
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 12 – Semaphore demo
 * ═══════════════════════════════════════════════════════════════════════ */

/*
 * OS CONCEPT – SEMAPHORES
 * A counting semaphore limits how many threads can simultaneously access
 * a shared resource (here: the "shared_memory_A" resource pool, capacity 2).
 */
typedef struct { int tid; sem_t *sem; int resource_id; int user_idx; } SemDemoArg;

static void *sem_demo_thread(void *arg)
{
    SemDemoArg *a = (SemDemoArg *)arg;
    printf("    [SemThread-%d] Waiting for semaphore slot...\n", a->tid);
    sem_wait(a->sem);
    printf("    [SemThread-%d] Acquired slot – accessing resource %d\n",
           a->tid, a->resource_id);
    usleep(300000);   /* simulate work */
    printf("    [SemThread-%d] Done – releasing slot\n", a->tid);
    sem_post(a->sem);
    free(a);
    return NULL;
}

static void semaphore_demo(int user_idx)
{
    print_header("SEMAPHORE DEMO (counting semaphore, capacity=2)");
    printf("Launching 4 threads competing for 2 semaphore slots...\n\n");

    sem_t pool_sem;
    sem_init(&pool_sem, 0, 2);   /* allow 2 concurrent accesses */

    pthread_t threads[4];
    for (int i = 0; i < 4; i++) {
        SemDemoArg *a = malloc(sizeof(SemDemoArg));
        a->tid         = i + 1;
        a->sem         = &pool_sem;
        a->resource_id = 5;   /* shared_memory_A */
        a->user_idx    = user_idx;
        pthread_create(&threads[i], NULL, sem_demo_thread, a);
        usleep(50000);
    }
    for (int i = 0; i < 4; i++) pthread_join(threads[i], NULL);
    sem_destroy(&pool_sem);

    printf("\nAll threads completed. Semaphore prevents more than 2 concurrent accesses.\n");
    log_action(user_idx >= 0 ? g_users[user_idx].username : "system",
               "semaphore_demo_completed", 1);
    printf("\nPress Enter to continue...\n");
    getchar();
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 13 – View activity log
 * ═══════════════════════════════════════════════════════════════════════ */

static void view_log(int user_idx)
{
    if (g_users[user_idx].role < ROLE_MANAGER) {
        printf("Insufficient permissions to view log.\n");
        log_action(g_users[user_idx].username, "VIEW_LOG_DENIED", 0);
        return;
    }

    /* Flush pending log entries */
    usleep(300000);

    pthread_mutex_lock(&g_logfile_mutex);
    FILE *f = fopen(LOG_FILE, "r");
    if (!f) { printf("Log file not found.\n"); pthread_mutex_unlock(&g_logfile_mutex); return; }

    print_header("ACTIVITY LOG");
    char line[256];
    int  count = 0;
    while (fgets(line, sizeof(line), f)) {
        fputs(line, stdout);
        count++;
    }
    fclose(f);
    pthread_mutex_unlock(&g_logfile_mutex);

    if (count == 0) printf("  (log is empty)\n");
    printf("\n%d log entries.\n", count);
    log_action(g_users[user_idx].username, "VIEW_LOG", 1);
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 14 – Menus
 * ═══════════════════════════════════════════════════════════════════════ */

static void show_resources_menu(int user_idx)
{
    print_header("AVAILABLE RESOURCES");
    printf("%-4s %-24s %-10s %-12s %-6s\n",
           "ID", "Name", "Type", "Min Role", "Perm");
    print_separator('-', 60);
    for (int i = 0; i < g_resource_count; i++) {
        printf("%-4d %-24s %-10s %-12s 0x%02X\n",
               i,
               g_resources[i].name,
               g_resources[i].type == RSRC_FILE  ? "FILE"  :
               g_resources[i].type == RSRC_LOG   ? "LOG"   :
               g_resources[i].type == RSRC_SHMEM ? "SHMEM" : "PROT",
               role_names[g_resources[i].min_role],
               g_resources[i].required_perm);
    }
    print_separator('-', 60);
    printf("Enter resource ID to access (or -1 to cancel): ");
    char buf[8]; safe_input(buf, sizeof(buf));
    int rid = atoi(buf);
    if (rid >= 0) access_resource(user_idx, rid);
}

static void main_menu(void)
{
    User *u = &g_users[g_logged_in_user];
    char choice[4];

    while (1) {
        clear_screen();
        print_header("RBAC OS LAB SYSTEM – MAIN MENU");
        printf("  Logged in as : %s  [%s]  (priority=%d, pid=%d)\n",
               u->username, role_names[u->role], u->priority, getpid());
        if (g_shm)
            printf("  SHM ops      : %d | Last: %s\n",
                   g_shm->total_operations, g_shm->last_action);
        print_separator('-', 60);
        printf("  1. Access a Resource\n");
        printf("  2. View Activity Log          [Manager+]\n");
        printf("  3. List Users                 [Manager+]\n");
        printf("  4. Add User                   [Admin only]\n");
        printf("  5. System Status (Shared Mem)\n");
        printf("  6. Semaphore Demo\n");
        printf("  7. Deadlock Prevention Demo\n");
        printf("  8. Fork + IPC Pipe Demo\n");
        printf("  9. Logout\n");
        print_separator('-', 60);
        printf("Choice: ");
        safe_input(choice, sizeof(choice));

        switch (atoi(choice)) {
        case 1: show_resources_menu(g_logged_in_user); break;
        case 2: view_log(g_logged_in_user); printf("\nPress Enter...\n"); getchar(); break;
        case 3: list_users(g_logged_in_user); printf("\nPress Enter...\n"); getchar(); break;
        case 4: add_user_admin(g_logged_in_user); printf("\nPress Enter...\n"); getchar(); break;
        case 5: show_system_status(); printf("\nPress Enter...\n"); getchar(); break;
        case 6: semaphore_demo(g_logged_in_user); break;
        case 7: deadlock_demo(); break;
        case 8: fork_ipc_demo(); break;
        case 9:
            log_action(u->username, "LOGOUT", 1);
            if (g_shm) {
                pthread_mutex_lock(&g_resource_hierarchy_mutex);
                g_shm->active_users--;
                pthread_mutex_unlock(&g_resource_hierarchy_mutex);
            }
            g_logged_in_user = -1;
            return;
        default: printf("Invalid choice.\n"); sleep(1);
        }
    }
}

static void login_menu(void)
{
    char uname[USERNAME_LEN], pass[PASSWORD_LEN];
    print_header("RBAC OS LAB – LOGIN");
    printf("Username: "); safe_input(uname, USERNAME_LEN);
    printf("Password: "); safe_input(pass,  PASSWORD_LEN);

    int idx = authenticate(uname, pass);
    if (idx < 0) {
        printf("\n  Authentication FAILED.\n");
        log_action(uname, "LOGIN_FAILED", 0);
        sleep(1);
        return;
    }

    g_logged_in_user = idx;
    if (g_shm) {
        pthread_mutex_lock(&g_resource_hierarchy_mutex);
        g_shm->active_users++;
        g_shm->last_pid = getpid();
        pthread_mutex_unlock(&g_resource_hierarchy_mutex);
    }

    char act[64];
    snprintf(act, 64, "LOGIN_SUCCESS role<%s>", role_names[g_users[idx].role]);
    log_action(uname, act, 1);

    /* Enqueue a login event in the scheduler */
    char req[64];
    snprintf(req, 64, "login-event:%s", uname);
    enqueue_request(idx, req);

    printf("\n  Welcome, %s! Role: %s\n", uname, role_names[g_users[idx].role]);
    sleep(1);
    main_menu();
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 15 – Graceful shutdown
 * ═══════════════════════════════════════════════════════════════════════ */

static void cleanup(void)
{
    stop_worker_threads();
    stop_log_threads();
    cleanup_shared_memory();
    for (int i = 0; i < g_resource_count; i++)
        pthread_mutex_destroy(&g_resources[i].mutex);
    pthread_mutex_destroy(&g_log_mutex);
    pthread_mutex_destroy(&g_logfile_mutex);
    pthread_mutex_destroy(&g_resource_hierarchy_mutex);
    pthread_cond_destroy(&g_log_cond);
}

static void signal_handler(int sig)
{
    (void)sig;
    printf("\n\nInterrupt received – shutting down cleanly...\n");
    cleanup();
    exit(0);
}

/* ═══════════════════════════════════════════════════════════════════════
 * SECTION 16 – main()
 * ═══════════════════════════════════════════════════════════════════════ */

int main(void)
{
    signal(SIGINT,  signal_handler);
    signal(SIGTERM, signal_handler);

    /* ── Initialise subsystems ───────────────────────────────────────── */
    load_users();
    seed_default_users();
    init_resources();
    init_shared_memory();

    start_log_threads();
    start_worker_threads();

    log_action("system", "RBAC_SYSTEM_STARTED", 1);

    /* ── Welcome banner ──────────────────────────────────────────────── */
    clear_screen();
    print_separator('*', 60);
    printf("*  RBAC Operating Systems Lab – C / Ubuntu Linux           *\n");
    printf("*  Demonstrates: fork, pthread, mutex, semaphore,          *\n");
    printf("*  shared memory, pipes, scheduling, deadlock prevention   *\n");
    print_separator('*', 60);
    printf("\n  Default accounts:\n");
    printf("    admin   / admin123   (Admin)\n");
    printf("    manager1/ mgr123     (Manager)\n");
    printf("    emp1    / emp123     (Employee)\n");
    printf("    guest1  / guest123   (Guest)\n\n");
    printf("Press Enter to continue...\n");
    getchar();

    /* ── Main loop ───────────────────────────────────────────────────── */
    char choice[4];
    while (1) {
        clear_screen();
        print_header("RBAC OS LAB SYSTEM");
        printf("  1. Login\n");
        printf("  2. Exit\n");
        print_separator('-', 60);
        printf("Choice: ");
        safe_input(choice, sizeof(choice));

        if (atoi(choice) == 1) {
            login_menu();
        } else if (atoi(choice) == 2) {
            printf("\nShutting down RBAC system...\n");
            log_action("system", "RBAC_SYSTEM_SHUTDOWN", 1);
            break;
        }
    }

    cleanup();
    printf("Goodbye.\n");
    return 0;
}
