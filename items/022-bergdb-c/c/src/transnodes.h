/*
 * transnodes: the nodes of one record, ported from Java's
 * bergdb.core.TransNodes (bergdb 012-09; 012-02, 8.3 and 8.7). Prefix tns_.
 *
 * Three arrays, each in the order of addition: the top nodes and the key
 * nodes that the take chose (TransSeq.take adds each taken transaction's
 * got-dirty nodes, top nodes to the top array, key nodes to the key array),
 * and the transaction's value and delete nodes, in the order they were made,
 * each with its key. A node is in the record at most once: its OBJ_IN_TRANS
 * flag (isInTransNodes, ValueNode.isInTransactionNodes) says that it is.
 * The record holds its top nodes first, then its key nodes, then its value
 * nodes (the serializer, serial.h).
 *
 * Memory (012-07, 6.4.2): the arrays are counted holders of their nodes,
 * until tns_clear; a delete node has no other holder. A value node's key is
 * borrowed: the transaction's pair's (valid until the transaction ends,
 * when the record is cleared). The arrays are MEM_STATE. Java's shrinking
 * of long arrays every few hundred records changes no byte and is left out.
 */
#ifndef BERGDB_TRANSNODES_H
#define BERGDB_TRANSNODES_H

#include <stdbool.h>
#include <stdint.h>
#include "knode.h"
#include "mem.h"
#include "obj.h"
#include "tnode.h"
#include "vnode.h"

struct transnodes {
    struct obj_ctx *cx;
    struct mem *mem;
    int64_t kv_size;            /* kvSize: the keys' and values' bytes */
    int64_t value_record_bytes; /* valueRecordBytes: the value nodes' bytes (005-17) */
    struct tnode **top_nodes;
    int32_t top_count;
    int32_t top_cap;
    struct knode **key_nodes;
    int32_t key_count;
    int32_t key_cap;
    struct vnode **value_nodes;
    const int64_t **keys;       /* each value node's key (borrowed) */
    int32_t *key_n;
    int32_t value_count;
    int32_t value_cap;
};

/* new TransNodes(): empty; nothing allocated until the first add. */
void tns_init(struct transnodes *tn, struct obj_ctx *cx, struct mem *m);

/* Frees the arrays (after tns_clear). */
void tns_free(struct transnodes *tn);

/* addTopNode, addKeyNode: the node at the end unless it is in the record
 * (OBJ_IN_TRANS); retained. false on NOMEM (nothing changed). The top node's
 * ordinal differs from every other top node's in the record (asserted, as
 * Java's assertNoDuplicateTopNodeId). */
bool tns_add_top_node(struct transnodes *tn, struct tnode *node);
bool tns_add_key_node(struct transnodes *tn, struct knode *node);

/* addValueNode: the value or delete node and its key (key_n segments,
 * borrowed), unless it is in the record; valueRecordBytes grows by
 * StoredValueNode.getByteSizeLong. false on NOMEM. */
bool tns_add_value_node(struct transnodes *tn, struct vnode *node, const int64_t *key,
        int32_t key_n);

/* size(): all three counts. */
int32_t tns_size(const struct transnodes *tn);

/* get(index): the top nodes, then the key nodes, then the value nodes;
 * the index nodes are 0 to top_count + key_count - 1 (indexNodeIterator). */
struct node *tns_get(const struct transnodes *tn, int32_t index);

/* clean(): every top and key node clean (setDirty(false)). */
void tns_clean(struct transnodes *tn);

/* clear(): empty again, the nodes' flags cleared and released. */
void tns_clear(struct transnodes *tn);

#endif
