/*
 * topds: Java's bergdb.dag.TopDs, the top data structure (bergdb 012-07):
 * the chain of top nodes, a skip list in time, whose newest, the super root,
 * is where a lookup starts; it finds the root key node of a lookup time.
 * Prefix tds_.
 *
 * struct topds holds the super root (counted; 012-07, 6.4.2). Java's
 * volatile and monitors are left out (one caller).
 */
#ifndef BERGDB_TOPDS_H
#define BERGDB_TOPDS_H

#include <stdbool.h>
#include <stdint.h>
#include "knode.h"
#include "obj.h"
#include "opdata.h"
#include "tnode.h"

struct topds {
    struct tnode *super_root;   /* counted */
    int64_t second_ordinal;     /* the ordinal of the top node after the first: 1, or a test's */
};

/* new TopDs(superRoot): super_root not NULL (Java throws
 * IllegalArgumentException; asserted). */
void tds_init(struct topds *ds, struct tnode *super_root);

/* Releases the super root (a field that stops holding it). */
void tds_free(struct obj_ctx *cx, struct topds *ds);

/* TopDs.createSuperRootFromFirstKeyNode: top node 0 with first_root as its
 * root, at first_time; the listener's pointerCreated. NULL on NOMEM or a
 * listener's failure. */
struct tnode *tds_create_super_root_from_first_key_node(struct obj_ctx *cx, int64_t first_time,
        struct knode *first_root, int64_t access_data,
        const struct op_pointer_created_listener *pcl);

/* TopDs.createFromFirstRoot: as new TopDs(createSuperRootFromFirstKeyNode(...)).
 * false on NOMEM or a listener's failure. */
bool tds_create_from_first_root(struct obj_ctx *cx, struct topds *ds, int64_t first_time,
        struct knode *first_root, int64_t access_data,
        const struct op_pointer_created_listener *pcl);

/* TopDs.setSecondOrdinal: 1 to the maximum; false (Java's
 * IllegalArgumentException) else. */
bool tds_set_second_ordinal(struct topds *ds, int64_t ordinal);

/* TopDs.newSuperRoot: a new super root at time, with new_root as its root
 * and the skip pointers its ordinal needs; or, at the super root's own
 * time, the super root's root pointer changed. false on NOMEM or a
 * listener's failure. */
bool tds_new_super_root(struct obj_ctx *cx, struct topds *ds, int64_t time, struct knode *new_root,
        int64_t access_data, const struct op_pointer_created_listener *pcl,
        const struct op_node_change_listener *ncl);

/* TopDs.getSuperRoot */
struct tnode *tds_get_super_root(const struct topds *ds);

/* TopDs.findRoot: the root key node at time, into *out (NULL if there is
 * none that old). false on the follower's or the listener's failure. */
bool tds_find_root(struct topds *ds, int64_t time, struct opdata *op, struct knode **out);

/* TopDs.findSuperRootAtTime: the top node that was super root at time,
 * into *out (NULL if none). false on a failure. */
bool tds_find_super_root_at_time(struct topds *ds, int64_t time, struct opdata *op,
        struct tnode **out);

#endif
