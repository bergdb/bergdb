/*
 * plat: the platform, in one place (bergdb 012-01, 4.2): what the library
 * needs of the operating system. So far (012-06) the reads of a database
 * directory: its entries, and files opened, read at a position and closed,
 * with POSIX's opendir, stat, open and pread. Writes, forces
 * (F_FULLFSYNC), the lock and the clock come with 012-09 and 012-10.
 * A port to another system replaces this module. Prefix plat_.
 */
#ifndef BERGDB_PLAT_H
#define BERGDB_PLAT_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"

/* The longest entry name that is kept; a longer one is refused (ERR_IO). */
#define PLAT_NAME 256

/* An entry of a directory, as Java's File gives it: its name, and its
 * length as File.length() (stat's st_size, following a symbolic link; 0 if
 * stat fails). */
struct plat_entry {
    char name[PLAT_NAME];
    int64_t size;
    bool is_dir;
};

/* The entries of directory 'dir', but "." and "..", sorted by name as
 * bytes (strcmp), into *out, an array of *n allocated through m (MEM_BUFFER)
 * that plat_free_entries frees. Java sorts by String.compareTo, UTF-16 code
 * units: the same order for every name but those that mix characters above
 * U+FFFF with ones from U+E000 to U+FFFF. ERR_IO if the directory cannot be
 * read; ERR_NOMEM. */
enum err_code plat_list_dir(const char *dir, struct mem *m, struct plat_entry **out,
        int32_t *n, struct err *e);

void plat_free_entries(struct mem *m, struct plat_entry *entries, int32_t n);

/* Opens the file at 'path' for reading; *fd is its descriptor. ERR_IO. */
enum err_code plat_open_read(const char *path, int *fd, struct err *e);

/* Reads exactly n bytes at offset 'off' of the file into buf. ERR_IO on an
 * error or the end of the file. */
enum err_code plat_pread(int fd, int64_t off, uint8_t *buf, int32_t n, struct err *e);

void plat_close(int fd);

/* Whether 'path' is a directory. */
bool plat_is_dir(const char *path);

/* The length of the file at 'path', as File.length(): 0 if stat fails. */
int64_t plat_file_length(const char *path);

#endif
