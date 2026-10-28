/*
 * plat: the platform, in one place (bergdb 012-01, 4.2): what the library
 * needs of the operating system. The reads of a database directory (012-06):
 * its entries, and files opened, read at a position and closed, with
 * POSIX's opendir, stat, open and pread. The writes (012-09): a directory
 * made with its ancestors, files opened for writing and written at a
 * position, forces with macOS's F_FULLFSYNC (as Java's force(true) on
 * macOS; fsync where the system has no F_FULLFSYNC), the directory's lock
 * (FileStream's, 005-63), and the system's time for the system clock.
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

/* System.currentTimeMillis(): milliseconds since 1970-01-01 00:00 UTC, from
 * the system's real-time clock (gettimeofday). */
int64_t plat_time_millis(void);

/* FileStream.createDirIfNeeded: if 'dir' exists, its parent is forced; else
 * it is made with its missing ancestors (mode 0777, less the umask), and
 * each new directory and its parent are forced, from the deepest up.
 * ERR_IO ("IOException") if it cannot be made, or 'dir' is not a
 * directory. */
enum err_code plat_mkdirs(const char *dir, struct err *e);

/* Opens 'path' for reading and writing, made if missing (Java's
 * RandomAccessFile "rw": mode 0666, less the umask). ERR_IO. */
enum err_code plat_open_rw(const char *path, int *fd, struct err *e);

/* Writes n bytes of buf at offset 'off' of the file, all of them. ERR_IO. */
enum err_code plat_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n, struct err *e);

/* The length of an open file (fstat). ERR_IO. */
enum err_code plat_fd_length(int fd, int64_t *length, struct err *e);

/* Forces the file's bytes and size to the disk: F_FULLFSYNC, as Java's
 * FileChannel.force(true) on macOS (FileStreamIo.forceFile); fsync where
 * the system has none. ERR_IO. */
enum err_code plat_force(int fd, struct err *e);

/* Forces a directory, its entries (FileStreamIo.forceDirectory): opened
 * for reading and forced as a file. ERR_IO. */
enum err_code plat_force_dir(const char *dir, struct err *e);

/* FileStream.lockDir (005-63): the file 'name' in 'dir', made with 'text'
 * if it does not exist (never changed after), opened for reading and
 * writing, and an exclusive lock of one byte at 'pos' taken without
 * waiting: fcntl's F_SETLK, as Java's FileChannel.tryLock on macOS, so
 * that Java and C exclude each other. *fd holds the lock until
 * plat_close. ERR_IN_USE ("DirectoryInUseException") if another process
 * holds it; ERR_IO. A POSIX lock is the process's: a second lock of the
 * same file in this process is not refused, and closing either descriptor
 * releases it (Java keeps a set of its own; a C caller opens a directory
 * once). */
enum err_code plat_lock(const char *dir, const char *name, const char *text, int64_t pos,
        int *fd, struct err *e);

#endif
