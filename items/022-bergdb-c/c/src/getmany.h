/*
 * getmany: Java's bergdb.dag.GetMany (bergdb 012-08): a range of pairs in
 * key order at a lookup time, forward or backward from a start key,
 * inclusive or not, with GetMany.Chain's walk and the stop conditions
 * DontStop, Endpoint, GetN (GetOne), Prefix and PrefixN, or a caller's;
 * and Dag.getMany, which runs it. Prefix gm_.
 *
 * Java's result list (GetMany.result, of Kvt with a new key array and the
 * value node's own bytes) is a sink here: a function that gets each pair to
 * add, valid during the call, and copies what it keeps (the API copies into
 * the read context's buffer, 012-03). The chain counts the key nodes it
 * holds (its links, 012-07, 6.4.2), so that the caller may set a safe
 * point between pairs (collect): a long range then frees what it has
 * passed, as 012-01, 4.5 says.
 */
#ifndef BERGDB_GETMANY_H
#define BERGDB_GETMANY_H

#include <stdbool.h>
#include <stdint.h>
#include "dag.h"
#include "knode.h"
#include "mem.h"
#include "obj.h"
#include "vnode.h"

/* Kvt: a pair found. key is the chain's buffer and value the value node
 * (borrowed): valid during the call that gets them. */
struct kvt {
    const int64_t *key;         /* the key's segments */
    int32_t key_n;
    struct vnode *value;        /* Kvt.value is value->value[0 .. len - 1] */
    int64_t time;               /* the key node entry's time; not the write time */
    int64_t spos;               /* the value node's position */
};

/* GetMany.StopCondition's answers */
#define GM_ADD 1
#define GM_STOP 2
#define GM_CONTINUE 3
#define GM_ADD_AND_STOP 4

/* GetMany.StopCondition: handleKvt (one of GM_ADD to GM_ADD_AND_STOP; an
 * answer below 0 is a failure of the caller's: the read stops and returns
 * false) and eod (called once, at the end of the database, NULL: nothing). */
struct gm_stop {
    int32_t (*handle_kvt)(void *ctx, const struct kvt *kvt);
    void (*eod)(void *ctx);
    void *ctx;
};

/* GetMany.result.add: false on a failure (NOMEM). NULL add: no result kept. */
struct gm_sink {
    bool (*add)(void *ctx, const struct kvt *kvt);
    void *ctx;
};

/* The stop conditions of Java, each a struct and its gm_stop. */
struct gm_endpoint {            /* GetMany.Endpoint */
    bool inclusive;
    bool backward;
    const int64_t *key;         /* the caller's, valid during the read (Java clones it) */
    int32_t key_n;
    bool eod;
};
struct gm_get_n {               /* GetMany.GetN; GetOne is GetN(1) */
    int32_t count;
    int32_t max_count;
    bool eod;
};
struct gm_prefix {              /* GetMany.Prefix */
    const int64_t *prefix;
    int32_t prefix_n;
    bool eod;
};
struct gm_prefix_n {            /* GetMany.PrefixN */
    const int64_t *prefix;      /* the caller's, valid during the read (Java clones it) */
    int32_t prefix_n;
    int32_t max_count;
    int32_t count;
    bool eod;
};

/* new DontStop() */
struct gm_stop gm_dont_stop(void);
/* new Endpoint(key, inclusive, backward); Endpoint(key) is (key, true, false). */
struct gm_stop gm_endpoint(struct gm_endpoint *s, const int64_t *key, int32_t key_n,
        bool inclusive, bool backward);
/* new GetN(maxCount): maxCount >= 0 (asserted). GetN and PrefixN give at most
 * maxCount pairs, none for 0 (bergdb 020-27, C1). */
struct gm_stop gm_get_n(struct gm_get_n *s, int32_t max_count);
struct gm_stop gm_prefix(struct gm_prefix *s, const int64_t *prefix, int32_t prefix_n);
struct gm_stop gm_prefix_n(struct gm_prefix_n *s, const int64_t *prefix, int32_t prefix_n,
        int32_t max_count);

/* GetMany: the input fields, the output fields, and the GetData. */
struct getmany {
    /* Input */
    int64_t lookup_time;        /* Long.MAX_VALUE by default */
    const int64_t *start_key;   /* NULL: from the first key (forward) or the last */
    int32_t start_key_n;
    bool inclusive;             /* true */
    bool forward;               /* true */
    struct gm_stop stop_condition;      /* DontStop */
    bool cache;                 /* true */
    struct gm_sink result;      /* GetMany.result.add */
    struct obj_ctx *collect;    /* not NULL: a safe point (obj_collect) after each pair */
    void (*safe_point)(void *ctx);  /* not NULL: called after each such obj_collect: the
                                       API's eviction (012-12) */
    void *safe_point_ctx;
    /* Output */
    int64_t actual_lookup_time; /* set by the database before Dag.getMany */
    int32_t get_op_count;
    /* The GetData; the caller sets its follower (Db.newGetMany). */
    struct getdata gd;
    struct mem *mem;            /* the chain's arrays */
};

/* new GetMany() as Dag.newGetMany makes it: the defaults above; m for the
 * chain's arrays. */
void gm_init(struct getmany *g, struct dag *d, struct mem *m);

/* GetMany.setBackward */
void gm_set_backward(struct getmany *g);

/* Dag.getMany: walks the chain at g->actual_lookup_time from the start key,
 * each pair to the stop condition and the added ones to the sink. false on
 * a failure (NOMEM, the follower, the sink, a stop condition's answer below
 * 0); the chain's holds are released in every case. */
bool dag_get_many(struct dag *d, struct getmany *g);

#endif
