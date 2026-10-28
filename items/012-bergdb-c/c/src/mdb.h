/*
 * mdb: a database of Level 0 in memory (bergdb 012-08; docs/levels.md,
 * Level 0): the Dag of Java's Db made as Db's creation makes it, fed by
 * transactions (puts and deletes at a transaction's time, as Db.putKvs
 * applies a transaction's pairs), read at a lookup time with
 * DbClock.lookupTime's clamp (Db.getOneInternal, Db.getMany). Every node
 * stays in memory and every pointer is a memory pointer: no stream, no
 * ids, no record. The unit tests and the model test use it; the full
 * replay (replay.h) feeds it a stream's records. Prefix mdb_.
 *
 * Memory (012-01, 4.5; 012-07, 6.4): the database's struct obj_ctx; the
 * Dag holds its nodes from the super root; a safe point (obj_collect)
 * after each put, at the end of each transaction and after each read.
 * mdb_free frees everything, the allocator's count 0 after it.
 */
#ifndef BERGDB_MDB_H
#define BERGDB_MDB_H

#include <stdbool.h>
#include <stdint.h>
#include "dag.h"
#include "getmany.h"
#include "mem.h"
#include "obj.h"
#include "vnode.h"

struct mdb {
    struct mem *mem;
    struct obj_ctx cx;
    struct dag dag;
    struct putdata pd;
    int32_t max_node_size;
    int64_t last_transaction_time;      /* DbClock.lastTransactionTime */
    bool in_trans;
    /* The value node that the next put or delete makes gets this position,
     * id and record (the replay's value node; Db's serializer gives them in
     * Java). Unset (have_value_pos false): the node keeps -1. */
    bool have_value_pos;
    int64_t value_spos;
    int64_t value_id;
    int64_t value_tpos;
};

/* The database as Db's creation makes it at time tt0 (Db.handleEmptyStream,
 * writePrimordialTransaction): the root key node KeyNode.nodeWithTime(tt0)
 * and the first top node, TopDs.createSuperRootFromFirstKeyNode; the clock's
 * last transaction time tt0. false: NOMEM (nothing is left allocated). */
bool mdb_create(struct mdb *db, struct mem *m, int64_t tt0, int32_t max_node_size);

/* Frees every object and buffer of the database. */
void mdb_free(struct mdb *db);

/* A transaction at time tt, later than the last one (asserted). */
void mdb_begin(struct mdb *db, int64_t tt);

/* One pair of the transaction (Db.putKvs: Dag.putKv, then clearFast): the
 * key's n segments, the value's len bytes, or a delete if value is NULL.
 * false: NOMEM. After a failure the database is to be freed only (P7). */
bool mdb_put(struct mdb *db, const int64_t *key, int32_t n, const uint8_t *value, int32_t len);

/* The transaction's end: the clock's last time is its time. */
void mdb_end(struct mdb *db);

/* DbClock.lookupTime: the wanted time, at most the last transaction's. */
int64_t mdb_lookup_time(const struct mdb *db, int64_t wanted);

/* Db.newGetData and newGetMany: their follower is the database's. */
void mdb_new_get_data(struct mdb *db, struct getdata *gd);
void mdb_new_get_many(struct mdb *db, struct getmany *g);

/* Db.getOneInternal, without reclaim's first available time (Level 0):
 * the actual lookup time from mdb_lookup_time, then Dag.getOne. *out: the
 * value node, borrowed until the next safe point. */
bool mdb_get_one(struct mdb *db, int64_t lookup_time, const int64_t *key, int32_t n,
        struct getdata *gd, struct vnode **out);

/* Db.getMany, likewise: g->actual_lookup_time set, then Dag.getMany. */
bool mdb_get_many(struct mdb *db, struct getmany *g);

/* The recount of 012-07, 6.4.1 from the database's roots: the number of
 * objects whose count is wrong (0: all right). */
int64_t mdb_recount(struct mdb *db);

#endif
