/* plat: the platform, POSIX; see plat.h. */
#define _POSIX_C_SOURCE 200809L
#include "plat.h"
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

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
        return err_set(e, ERR_IO, "IOException", "Cannot read directory %s: %s", dir,
                strerror(errno));
    }
    while ((d = readdir(dp)) != NULL) {
        struct stat st;
        struct plat_entry *x;
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
        snprintf(x->name, sizeof x->name, "%s", d->d_name);
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

void plat_close(int fd) {
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
