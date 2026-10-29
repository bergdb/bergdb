/*
 * api: include/bergdb.h's functions (bergdb 012-03's API), on the modules
 * that 012-09 and 012-10 have: the open that creates a database or starts
 * an existing one (db.h; starter.h), transactions (trans.h), execute, the
 * reads, sync, the clock's times, the settings and the status. The
 * handles' structs are here; the caller sees them as opaque types.
 *
 * Not yet (later tasks; each refused or left undefined): eviction (012-12:
 * the cache size indicator is kept), bergdb_debug_print and
 * bergdb_debug_check (012-13).
 *
 * The rules of the header's top comment hold: one caller at a time; a
 * callback that calls its database gets BERGDB_STATE; the database's
 * memory (its state, its transactions and read contexts and their buffers)
 * is counted in the options' struct bergdb_mem, or in one of its own.
 * bergdb_errmsg's text begins with the name of Java's exception for the
 * same case and ": " (bergdb-run prints that name, as Java's Run does).
 */
#ifndef BERGDB_API_H
#define BERGDB_API_H

#include <stdint.h>
#include "bergdb.h"
#include "db.h"
#include "mem.h"
#include "trans.h"

struct bergdb_db {
    struct db db;
    struct mem own_mem;         /* the counts, when the options give none */
    struct mem *mem;
    bool in_callback;           /* a callback of a call on this database runs */
    char errmsg[ERR_TEXT + 64]; /* the last call's error: "JavaName: text" */
    struct bergdb_trans *trans_list;    /* the live transactions, for the close */
    struct bergdb_read *read_list;      /* the live read contexts */
};

struct bergdb_trans {
    struct bergdb_db *db;
    struct tr_builder b;
    struct trans t;
    struct bergdb_trans *prev;
    struct bergdb_trans *next;
};

struct bergdb_read {
    struct bergdb_db *db;
    uint8_t *buf;               /* the results' bytes (MEM_CALLER) */
    size_t cap;
    size_t used;
    struct bergdb_kvt *kvts;    /* getMany's pairs, getTrans's values */
    size_t kvt_cap;
    size_t nkvts;
    struct bergdb_read *prev;
    struct bergdb_read *next;
};

/* The API's code of a library error. */
int api_code(enum err_code code);

#endif
