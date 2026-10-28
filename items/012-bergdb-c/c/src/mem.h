/*
 * mem: the allocator (bergdb 012-01, section 4.5, point 1). Every allocation
 * and free of the library goes through it, with a struct mem per database
 * (no global state, P9). It counts the live bytes, in total and by kind,
 * which gives the memory budget its exact figure (P8) and the tests an exact
 * leak check; a failed allocation is a null pointer, which the caller turns
 * into BERGDB's NOMEM; and allocation number N can be made to fail, for the
 * allocation-failure runs (012-01, 4.5; 012-14). Prefix mem_.
 *
 * The caller of mem_free and mem_realloc gives the block's size and kind,
 * as they were allocated (a sized free: no header in the release build).
 * The test build (BERGDB_TEST) puts a 16-byte header before each block and
 * checks the size and kind given at the free; a mismatch is a bug in the
 * library and aborts with a message.
 *
 * Who owns the struct: whoever needs its counts after the free of the last
 * block. A database uses the struct its opener gives, or one of its own;
 * a test gives its own, and checks after the close that the count is 0
 * (CHECK_MEM_ZERO in test/unit/test.h). The struct is not thread-safe, as a
 * database is used by one caller at a time (012-01, 4.2).
 */
#ifndef BERGDB_MEM_H
#define BERGDB_MEM_H

#include <stddef.h>
#include <stdint.h>

/* The kinds of memory (012-01, 4.5, point 1). */
enum mem_kind {
    MEM_INDEX,      /* index objects: key nodes, top nodes */
    MEM_VALUE,      /* values held by index objects */
    MEM_HANDLE,     /* handles */
    MEM_TABLE,      /* the node table */
    MEM_BUFFER,     /* buffers: the write buffer, read buffers */
    MEM_CALLER,     /* the caller's objects: transactions, read contexts, results */
    MEM_STATE,      /* the database's own state, D, reclaim's, the settings */
    MEM_KINDS
};

struct mem {
    int64_t live[MEM_KINDS];    /* live bytes by kind */
    int64_t live_total;         /* live bytes in all */
    int64_t peak_total;         /* the largest live_total so far */
    int64_t live_blocks;        /* live blocks */
    int64_t allocs;             /* allocations asked for, with reallocs and failures */
    int64_t failed;             /* allocations that failed, made to or not */
    int64_t fail_at;            /* allocation number fail_at fails (1 is the first); 0: none */
};

/* Sets every count to 0, and fail_at to 0.
 *
 * The allocation-failure runs (012-01, 4.5; SQLite's way): run a workload
 * with fail_at = 1, 2, 3, ... until a run makes fewer than fail_at
 * allocations (allocs < fail_at, failed == 0); every other run must give
 * NOMEM and free everything (live_total == 0 after the close). fail_at
 * works in both builds: it costs one comparison. */
void mem_init(struct mem *m);

/* A block of size bytes (0 allowed) of the kind; NULL on a failure, which
 * the caller turns into NOMEM (an error of the API, include/bergdb.h). */
void *mem_alloc(struct mem *m, size_t size, enum mem_kind kind);

/* As mem_alloc, the block zeroed. */
void *mem_zalloc(struct mem *m, size_t size, enum mem_kind kind);

/* Resizes p (NULL allowed, with old_size 0) from old_size to new_size bytes.
 * On a failure, returns NULL and p stays as it was. */
void *mem_realloc(struct mem *m, void *p, size_t old_size, size_t new_size, enum mem_kind kind);

/* Frees p (NULL allowed), of size bytes and the kind, as allocated. */
void mem_free(struct mem *m, void *p, size_t size, enum mem_kind kind);

/* The name of a kind, for reports. */
const char *mem_kind_name(enum mem_kind kind);

#endif
