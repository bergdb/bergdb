/* plat: the platform, POSIX and macOS's F_FULLFSYNC; see plat.h. */
#define _POSIX_C_SOURCE 200809L
#define _DARWIN_C_SOURCE        /* F_FULLFSYNC */
#include "plat.h"
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <unistd.h>

/* FileStream.listFiles' refusal (bergdb 020-20, T1, as Java's since release
 * 2026.4): a directory that cannot be listed, as Java's File.listFiles()
 * gives null for it. */
static enum err_code cannot_list(const char *dir, struct err *e) {
    return err_set(e, ERR_IO, "IOException",
            "Cannot list the directory %s: an I/O error, or no permission to read it.", dir);
}

enum err_code plat_list_dir(const char *dir, struct mem *m, struct plat_entry **out,
        int32_t *n, struct err *e) {
    struct plat_entry *list = NULL;
    int32_t count = 0;
    int32_t cap = 0;
    char path[4096];
    struct dirent *d;
    DIR *dp = opendir(dir);

    *out = NULL;
    *n = 0;
    if (dp == NULL) {
        return cannot_list(dir, e);
    }
    for (;;) {
        struct stat st;
        struct plat_entry *x;
        errno = 0;
        d = readdir(dp);
        if (d == NULL) {
            if (errno != 0) {       /* an I/O error in the listing, not its end */
                closedir(dp);
                plat_free_entries(m, list, cap);
                return cannot_list(dir, e);
            }
            break;
        }
        if (strcmp(d->d_name, ".") == 0 || strcmp(d->d_name, "..") == 0) {
            continue;
        }
        if (strlen(d->d_name) >= PLAT_NAME) {
            closedir(dp);
            plat_free_entries(m, list, cap);
            return err_set(e, ERR_IO, "IOException", "A name too long in %s", dir);
        }
        if (count == cap) {
            int32_t c2 = cap == 0 ? 16 : 2 * cap;
            struct plat_entry *l2 = mem_realloc(m, list, (size_t) cap * sizeof *list,
                    (size_t) c2 * sizeof *list, MEM_BUFFER);
            if (l2 == NULL) {
                closedir(dp);
                plat_free_entries(m, list, cap);
                return err_set(e, ERR_NOMEM, "OutOfMemoryError", "listing %s", dir);
            }
            list = l2;
            cap = c2;
        }
        x = &list[count++];
        memset(x, 0, sizeof *x);
        memcpy(x->name, d->d_name, strlen(d->d_name) + 1);     /* shorter than PLAT_NAME */
        snprintf(path, sizeof path, "%s/%s", dir, d->d_name);
        if (stat(path, &st) == 0) {
            x->size = (int64_t) st.st_size;
            x->is_dir = S_ISDIR(st.st_mode);
        }
    }
    closedir(dp);

    /* Sorted by name: an insertion sort, as directories hold few files. */
    for (int32_t i = 1; i < count; i++) {
        struct plat_entry t = list[i];
        int32_t j = i - 1;
        while (j >= 0 && strcmp(list[j].name, t.name) > 0) {
            list[j + 1] = list[j];
            j--;
        }
        list[j + 1] = t;
    }
    /* Shrunk to its count, so that the free knows its size. */
    if (count == 0) {
        plat_free_entries(m, list, cap);
        list = NULL;
    } else if (cap > count) {
        struct plat_entry *l2 = mem_realloc(m, list, (size_t) cap * sizeof *list,
                (size_t) count * sizeof *list, MEM_BUFFER);
        if (l2 == NULL) {
            plat_free_entries(m, list, cap);
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "listing %s", dir);
        }
        list = l2;
    }
    *out = list;
    *n = count;
    return ERR_OK;
}

void plat_free_entries(struct mem *m, struct plat_entry *entries, int32_t n) {
    mem_free(m, entries, (size_t) n * sizeof *entries, MEM_BUFFER);
}

enum err_code plat_open_read(const char *path, int *fd, struct err *e) {
    *fd = open(path, O_RDONLY);
    if (*fd < 0) {
        return err_set(e, ERR_IO, "IOException", "Cannot open %s: %s", path, strerror(errno));
    }
    return ERR_OK;
}

enum err_code plat_pread(int fd, int64_t off, uint8_t *buf, int32_t n, struct err *e) {
    while (n > 0) {
        ssize_t r = pread(fd, buf, (size_t) n, (off_t) off);
        if (r < 0) {
            if (errno == EINTR) {
                continue;
            }
            return err_set(e, ERR_IO, "IOException", "Read of %d bytes at %lld failed: %s",
                    (int) n, (long long) off, strerror(errno));
        }
        if (r == 0) {
            return err_set(e, ERR_IO, "EOFException", "End of file at %lld", (long long) off);
        }
        buf += r;
        off += r;
        n -= (int32_t) r;
    }
    return ERR_OK;
}

static void real_close(int fd) {
    if (fd >= 0) {
        close(fd);
    }
}

bool plat_is_dir(const char *path) {
    struct stat st;
    return stat(path, &st) == 0 && S_ISDIR(st.st_mode);
}

int64_t plat_file_length(const char *path) {
    struct stat st;
    return stat(path, &st) == 0 ? (int64_t) st.st_size : 0;
}

int64_t plat_time_millis(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (int64_t) tv.tv_sec * 1000 + (int64_t) tv.tv_usec / 1000;
}

void plat_random(uint8_t *buf, int32_t n) {
    arc4random_buf(buf, (size_t) n);
}

/* The parent of 'path' into out: "." for a name without a slash, "/" for
 * "/x"; false if path has none ("/" itself). */
static bool parent_of(const char *path, char *out, size_t size) {
    size_t n = strlen(path);
    while (n > 1 && path[n - 1] == '/') {
        n--;
    }
    while (n > 0 && path[n - 1] != '/') {
        n--;
    }
    if (n == 0) {
        snprintf(out, size, ".");
        return strcmp(path, ".") != 0;
    }
    while (n > 1 && path[n - 1] == '/') {
        n--;
    }
    if (n >= size) {
        return false;
    }
    memcpy(out, path, n);
    out[n] = '\0';
    return strcmp(out, path) != 0;
}

enum err_code plat_mkdirs(const char *dir, struct err *e) {
    char missing[16][1024];
    char path[1024];
    int nmissing = 0;
    struct stat st;

    if (strlen(dir) >= sizeof path) {
        return err_set(e, ERR_IO, "IOException", "Directory path too long: %s", dir);
    }
    if (stat(dir, &st) == 0) {
        char parent[1024];
        if (!S_ISDIR(st.st_mode)) {
            /* Java's text since release 2026.4 (bergdb 020-24-08, U8-11); C's own
             * was "Not a directory: DIR". */
            return err_set(e, ERR_IO, "IOException", "Directory %s could not be opened: it "
                    "exists and is not a directory.", dir);
        }
        if (parent_of(dir, parent, sizeof parent)) {
            return plat_force_dir(parent, e);
        }
        return ERR_OK;
    }
    /* mkdirs(): the missing directories, deepest first. */
    snprintf(path, sizeof path, "%s", dir);
    while (stat(path, &st) != 0) {
        char parent[1024];
        if (nmissing == 16) {
            return err_set(e, ERR_IO, "IOException", "Directory %s could not be created: too "
                    "many missing ancestors.", dir);
        }
        snprintf(missing[nmissing++], sizeof missing[0], "%s", path);
        if (!parent_of(path, parent, sizeof parent)) {
            break;
        }
        snprintf(path, sizeof path, "%s", parent);
    }
    for (int i = nmissing - 1; i >= 0; i--) {
        if (mkdir(missing[i], 0777) != 0 && errno != EEXIST) {
            return err_set(e, ERR_IO, "IOException", "Directory %s could not be created: %s",
                    dir, strerror(errno));
        }
    }
    for (int i = 0; i < nmissing; i++) {
        char parent[1024];
        enum err_code rc = plat_force_dir(missing[i], e);
        if (rc != ERR_OK) {
            return rc;
        }
        if (parent_of(missing[i], parent, sizeof parent)) {
            rc = plat_force_dir(parent, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }
    }
    return ERR_OK;
}

/* new RandomAccessFile(file, "rw"): its FileNotFoundException's message is
 * the path and the reason, "PATH (Is a directory)" (bergdb 022-02, D6). */
static enum err_code real_open_rw(const char *path, int *fd, struct err *e) {
    *fd = open(path, O_RDWR | O_CREAT, 0666);
    if (*fd < 0) {
        return err_set(e, ERR_IO, "FileNotFoundException", "%s (%s)", path, strerror(errno));
    }
    return ERR_OK;
}

static enum err_code real_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n, struct err *e) {
    while (n > 0) {
        size_t chunk = n > (int64_t) 1 << 30 ? (size_t) 1 << 30 : (size_t) n;
        ssize_t r = pwrite(fd, buf, chunk, (off_t) off);
        if (r < 0) {
            if (errno == EINTR) {
                continue;
            }
            return err_set(e, ERR_IO, "IOException", "Write of %lld bytes at %lld failed: %s",
                    (long long) n, (long long) off, strerror(errno));
        }
        buf += r;
        off += r;
        n -= r;
    }
    return ERR_OK;
}

enum err_code plat_fd_length(int fd, int64_t *length, struct err *e) {
    struct stat st;
    if (fstat(fd, &st) != 0) {
        return err_set(e, ERR_IO, "IOException", "Cannot stat an open file: %s",
                strerror(errno));
    }
    *length = (int64_t) st.st_size;
    return ERR_OK;
}

static enum err_code real_force(int fd, struct err *e) {
#ifdef F_FULLFSYNC
    if (fcntl(fd, F_FULLFSYNC) == 0) {
        return ERR_OK;
    }
    /* Not every file system has it; then as Java on Linux, fsync. */
#endif
    if (fsync(fd) != 0) {
        return err_set(e, ERR_IO, "IOException", "Force failed: %s", strerror(errno));
    }
    return ERR_OK;
}

/* The seam's force: the reason is for a model only. */
static enum err_code real_force_why(int fd, enum plat_force_why why, struct err *e) {
    (void) why;
    return real_force(fd, e);
}

static enum err_code real_force_dir(const char *dir, struct err *e) {
    int fd = open(dir, O_RDONLY);
    if (fd < 0) {
        return err_set(e, ERR_IO, "IOException", "Cannot open directory %s: %s", dir,
                strerror(errno));
    }
    enum err_code rc = real_force(fd, e);
    close(fd);
    return rc;
}

enum err_code plat_lock(const char *dir, const char *name, const char *text, int64_t pos,
        int *fd, struct err *e) {
    char path[4096];
    struct flock fl;
    int f;

    snprintf(path, sizeof path, "%s/%s", dir, name);
    /* createNewFile(), then the text. */
    f = open(path, O_WRONLY | O_CREAT | O_EXCL, 0666);
    if (f >= 0) {
        enum err_code rc = plat_pwrite(f, 0, (const uint8_t *) text, (int64_t) strlen(text), e);
        close(f);
        if (rc != ERR_OK) {
            return rc;
        }
    } else if (errno != EEXIST) {
        return err_set(e, ERR_IO, "IOException", "Cannot create %s: %s", path,
                strerror(errno));
    }
    /* new RandomAccessFile(file, "rw"), as real_open_rw. */
    f = open(path, O_RDWR);
    if (f < 0) {
        return err_set(e, ERR_IO, "FileNotFoundException", "%s (%s)", path, strerror(errno));
    }
    memset(&fl, 0, sizeof fl);
    fl.l_type = F_WRLCK;
    fl.l_whence = SEEK_SET;
    fl.l_start = (off_t) pos;
    fl.l_len = 1;
    if (fcntl(f, F_SETLK, &fl) != 0) {
        int err = errno;
        close(f);
        if (err == EACCES || err == EAGAIN) {
            return err_set(e, ERR_IN_USE, "DirectoryInUseException", "Directory %s is in use by"
                    " another BergDB database (%s is locked by another process).", dir, name);
        }
        return err_set(e, ERR_IO, "IOException", "Could not lock %s: %s", path, strerror(err));
    }
    *fd = f;
    return ERR_OK;
}

static enum err_code real_unlink(const char *path, struct err *e) {
    if (unlink(path) != 0) {
        return err_set(e, ERR_IO, "IOException", "Could not delete file %s: %s", path,
                strerror(errno));
    }
    return ERR_OK;
}

/* ======== The I/O seam (bergdb 012-14, 6.5) ========
 *
 * The persistence calls (plat_open_rw, plat_pwrite, plat_force,
 * plat_force_dir, plat_unlink, plat_close) are the real ones above, or, in
 * the test build after plat_io_set, a test's: the power-loss model of
 * test/stress/power.c. The release build calls the real ones directly. */

#ifdef BERGDB_TEST
/* The test build's seam: the one writable variable of the library, in the
 * test build only (P9 holds for the release build, which before-commit.sh
 * checks with nm). */
static const struct plat_io *plat_io_now = NULL;

static const struct plat_io PLAT_IO_REAL = {
    real_open_rw, real_pwrite, real_force_why, real_force_dir, real_unlink, real_close
};

void plat_io_set(const struct plat_io *io) {
    plat_io_now = io;
}

const struct plat_io *plat_io_real(void) {
    return &PLAT_IO_REAL;
}

/* SEAM(CALL, REAL): the seam's CALL when a test has set one, else REAL. */
#define SEAM(call, real) (plat_io_now != NULL ? plat_io_now->call : (real))
#else
#define SEAM(call, real) (real)
#endif

enum err_code plat_open_rw(const char *path, int *fd, struct err *e) {
    return SEAM(open_rw(path, fd, e), real_open_rw(path, fd, e));
}

enum err_code plat_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n, struct err *e) {
    return SEAM(pwrite(fd, off, buf, n, e), real_pwrite(fd, off, buf, n, e));
}

enum err_code plat_force(int fd, enum plat_force_why why, struct err *e) {
    return SEAM(force(fd, why, e), real_force_why(fd, why, e));
}

enum err_code plat_force_dir(const char *dir, struct err *e) {
    return SEAM(force_dir(dir, e), real_force_dir(dir, e));
}

enum err_code plat_unlink(const char *path, struct err *e) {
    return SEAM(unlink(path, e), real_unlink(path, e));
}

void plat_close(int fd) {
#ifdef BERGDB_TEST
    if (plat_io_now != NULL) {
        plat_io_now->close(fd);
        return;
    }
#endif
    real_close(fd);
}
