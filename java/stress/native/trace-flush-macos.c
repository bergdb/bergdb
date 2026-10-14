/* Test-only dyld interposer. Trace actual force/write/create/delete calls of
 * the installed JVM; this library is never linked into BergDB. */
#ifndef __APPLE__
#error This interposer is for macOS; use strace on Linux.
#endif
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

/* dyld leaves this image's own references pointing to the original symbols.
 * Resolve them before constructors: early loader I/O can precede initialize. */
static int (*original_open)(const char *, int, ...) = open;
static int (*original_fcntl)(int, int, ...) = fcntl;
static int (*original_fsync)(int) = fsync;
static ssize_t (*original_write)(int, const void *, size_t) = write;
static int (*original_unlink)(const char *) = unlink;
static int log_fd = -1;
static unsigned long sequence;
static pthread_mutex_t log_lock = PTHREAD_MUTEX_INITIALIZER;

__attribute__((constructor)) static void initialize(void) {
    const char *path = getenv("BERGDB_FLUSH_TRACE");
    if (path) log_fd = original_open(path, O_CREAT | O_TRUNC | O_WRONLY, 0600);
}

static int is_data(const char *path) {
    size_t n = strlen(path);
    return n >= 7 && strcmp(path + n - 7, ".bergdb") == 0;
}

static void record(const char *operation, int fd, long result, long amount, const char *given) {
    if (log_fd < 0) return;
    int saved = errno;
    char path[PATH_MAX] = "?";
    struct stat info;
    const char *kind = "file";
    if (given) snprintf(path, sizeof(path), "%s", given);
    else original_fcntl(fd, F_GETPATH, path);
    if (!given && fstat(fd, &info) == 0 && S_ISDIR(info.st_mode)) kind = "dir";
    pthread_mutex_lock(&log_lock);
    char line[PATH_MAX + 160];
    int count = snprintf(line, sizeof(line), "%lu %s %s rc=%ld n=%ld path=%s\n",
                         ++sequence, operation, kind, result, amount, path);
    if (count > 0 && (size_t)count < sizeof(line)) original_write(log_fd, line, (size_t)count);
    pthread_mutex_unlock(&log_lock);
    errno = saved;
}

static int traced_open(const char *path, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list args; va_start(args, flags); mode = (mode_t)va_arg(args, int); va_end(args);
    }
    int absent = access(path, F_OK) != 0;
    int result = original_open(path, flags, mode);
    if (result >= 0 && absent && is_data(path)) record("CREATE", result, 0, 0, path);
    return result;
}

static ssize_t traced_write(int fd, const void *bytes, size_t length) {
    ssize_t result = original_write(fd, bytes, length);
    char path[PATH_MAX] = "?";
    if (fd != log_fd && original_fcntl(fd, F_GETPATH, path) == 0 && is_data(path)) {
        record("WRITE", fd, result, (long)length, path);
    }
    return result;
}

static int traced_fcntl(int fd, int command, ...) {
    int result;
    if (command == F_FULLFSYNC || command == F_GETFD || command == F_GETFL) {
        result = original_fcntl(fd, command);
    } else {
        va_list args; va_start(args, command); void *arg = va_arg(args, void *); va_end(args);
        result = original_fcntl(fd, command, arg);
    }
    if (command == F_FULLFSYNC) record("F_FULLFSYNC", fd, result, 0, NULL);
    return result;
}

static int traced_fsync(int fd) {
    int result = original_fsync(fd);
    record("FSYNC", fd, result, 0, NULL);
    return result;
}

static int traced_unlink(const char *path) {
    int result = original_unlink(path);
    if (is_data(path)) record("UNLINK", -1, result, 0, path);
    return result;
}

#define INTERPOSE(replacement, original) \
    __attribute__((used)) static struct { const void *replacement; const void *original; } \
    interpose_##original __attribute__((section("__DATA,__interpose"))) = { \
        (const void *)(unsigned long)&replacement, (const void *)(unsigned long)&original }
INTERPOSE(traced_open, open);
INTERPOSE(traced_write, write);
INTERPOSE(traced_fcntl, fcntl);
INTERPOSE(traced_fsync, fsync);
INTERPOSE(traced_unlink, unlink);
