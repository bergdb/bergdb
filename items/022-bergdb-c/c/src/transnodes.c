/* transnodes: the nodes of one record; see transnodes.h. */
#include "transnodes.h"
#include <assert.h>
#include <string.h>
#include "keys.h"
#include "node.h"
#include "nwrite.h"
#include "spos.h"

#define INITIAL_SIZE 64     /* TransNodes.INITIAL_SIZE */

void tns_init(struct transnodes *tn, struct obj_ctx *cx, struct mem *m) {
    memset(tn, 0, sizeof *tn);
    tn->cx = cx;
    tn->mem = m;
}

void tns_free(struct transnodes *tn) {
    assert(tns_size(tn) == 0);
    mem_free(tn->mem, tn->top_nodes, (size_t) tn->top_cap * sizeof *tn->top_nodes, MEM_STATE);
    mem_free(tn->mem, tn->key_nodes, (size_t) tn->key_cap * sizeof *tn->key_nodes, MEM_STATE);
    mem_free(tn->mem, tn->value_nodes, (size_t) tn->value_cap * sizeof *tn->value_nodes,
            MEM_STATE);
    mem_free(tn->mem, tn->keys, (size_t) tn->value_cap * sizeof *tn->keys, MEM_STATE);
    mem_free(tn->mem, tn->key_n, (size_t) tn->value_cap * sizeof *tn->key_n, MEM_STATE);
    tn->top_nodes = NULL;
    tn->key_nodes = NULL;
    tn->value_nodes = NULL;
    tn->keys = NULL;
    tn->key_n = NULL;
    tn->top_cap = tn->key_cap = tn->value_cap = 0;
}

/* The new capacity of an array of cap elements that is full. */
static int32_t next_cap(int32_t cap) {
    return cap == 0 ? INITIAL_SIZE : cap * 2;
}

bool tns_add_top_node(struct transnodes *tn, struct tnode *node) {
    assert(!spos_is_null(node->n.id) && "bad node id, addTopNode()");
    if (node_is_in_trans_nodes(&node->n)) {
        return true;
    }
    /* assertNoDuplicateTopNodeId */
    for (int32_t i = 0; i < tn->top_count; i++) {
        assert(tn->top_nodes[i]->top_node_id != node->top_node_id
                && "Cannot add TopNode with same topNodeId as existing one");
    }
    if (tn->top_count == tn->top_cap) {
        int32_t ncap = next_cap(tn->top_cap);
        struct tnode **n = mem_realloc(tn->mem, tn->top_nodes,
                (size_t) tn->top_cap * sizeof *n, (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        tn->top_nodes = n;
        tn->top_cap = ncap;
    }
    node_set_in_trans_nodes(&node->n, true);
    obj_retain(&node->n.o);
    tn->top_nodes[tn->top_count++] = node;
    return true;
}

bool tns_add_key_node(struct transnodes *tn, struct knode *node) {
    assert(!spos_is_null(node->n.id) && "bad node id, addKeyNode()");
    if (node_is_in_trans_nodes(&node->n)) {
        return true;
    }
    if (tn->key_count == tn->key_cap) {
        int32_t ncap = next_cap(tn->key_cap);
        struct knode **n = mem_realloc(tn->mem, tn->key_nodes,
                (size_t) tn->key_cap * sizeof *n, (size_t) ncap * sizeof *n, MEM_STATE);
        if (n == NULL) {
            return false;
        }
        tn->key_nodes = n;
        tn->key_cap = ncap;
    }
    node_set_in_trans_nodes(&node->n, true);
    obj_retain(&node->n.o);
    tn->key_nodes[tn->key_count++] = node;
    return true;
}

bool tns_add_value_node(struct transnodes *tn, struct vnode *node, const int64_t *key,
        int32_t key_n) {
    assert(!spos_is_null(node->n.id) && "bad node id, addValueNode()");
    if (node_is_in_trans_nodes(&node->n)) {
        return true;
    }
    if (tn->value_count == tn->value_cap) {
        int32_t cap = tn->value_cap;
        int32_t ncap = next_cap(cap);
        struct vnode **nv = mem_alloc(tn->mem, (size_t) ncap * sizeof *nv, MEM_STATE);
        const int64_t **nk = mem_alloc(tn->mem, (size_t) ncap * sizeof *nk, MEM_STATE);
        int32_t *nn = mem_alloc(tn->mem, (size_t) ncap * sizeof *nn, MEM_STATE);
        if (nv == NULL || nk == NULL || nn == NULL) {
            mem_free(tn->mem, nv, (size_t) ncap * sizeof *nv, MEM_STATE);
            mem_free(tn->mem, nk, (size_t) ncap * sizeof *nk, MEM_STATE);
            mem_free(tn->mem, nn, (size_t) ncap * sizeof *nn, MEM_STATE);
            return false;
        }
        if (cap > 0) {
            memcpy(nv, tn->value_nodes, (size_t) cap * sizeof *nv);
            memcpy(nk, tn->keys, (size_t) cap * sizeof *nk);
            memcpy(nn, tn->key_n, (size_t) cap * sizeof *nn);
        }
        mem_free(tn->mem, tn->value_nodes, (size_t) cap * sizeof *nv, MEM_STATE);
        mem_free(tn->mem, tn->keys, (size_t) cap * sizeof *nk, MEM_STATE);
        mem_free(tn->mem, tn->key_n, (size_t) cap * sizeof *nn, MEM_STATE);
        tn->value_nodes = nv;
        tn->keys = nk;
        tn->key_n = nn;
        tn->value_cap = ncap;
    }
    node_set_in_trans_nodes(&node->n, true);
    obj_retain(&node->n.o);
    tn->value_nodes[tn->value_count] = node;
    tn->keys[tn->value_count] = key;
    tn->key_n[tn->value_count] = key_n;
    tn->value_count++;
    tn->value_record_bytes += nw_value_byte_size_long(node->len, key_n);
    tn->kv_size += (int64_t) key_n * 8;
    tn->kv_size += node->len < 0 ? 16 : node->len;
    return true;
}

int32_t tns_size(const struct transnodes *tn) {
    return tn->top_count + tn->key_count + tn->value_count;
}

struct node *tns_get(const struct transnodes *tn, int32_t index) {
    if (index < tn->top_count) {
        return &tn->top_nodes[index]->n;
    } else if (index < tn->top_count + tn->key_count) {
        return &tn->key_nodes[index - tn->top_count]->n;
    }
    return &tn->value_nodes[index - (tn->top_count + tn->key_count)]->n;
}

void tns_clean(struct transnodes *tn) {
    for (int32_t i = 0; i < tn->top_count; i++) {
        node_set_dirty(&tn->top_nodes[i]->n, false);
    }
    for (int32_t i = 0; i < tn->key_count; i++) {
        node_set_dirty(&tn->key_nodes[i]->n, false);
    }
}

void tns_clear(struct transnodes *tn) {
    tn->kv_size = 0;
    tn->value_record_bytes = 0;
    for (int32_t i = 0; i < tn->top_count; i++) {
        node_set_in_trans_nodes(&tn->top_nodes[i]->n, false);
        obj_release(tn->cx, &tn->top_nodes[i]->n.o);
        tn->top_nodes[i] = NULL;
    }
    tn->top_count = 0;
    for (int32_t i = 0; i < tn->key_count; i++) {
        node_set_in_trans_nodes(&tn->key_nodes[i]->n, false);
        obj_release(tn->cx, &tn->key_nodes[i]->n.o);
        tn->key_nodes[i] = NULL;
    }
    tn->key_count = 0;
    for (int32_t i = 0; i < tn->value_count; i++) {
        node_set_in_trans_nodes(&tn->value_nodes[i]->n, false);
        obj_release(tn->cx, &tn->value_nodes[i]->n.o);
        tn->value_nodes[i] = NULL;
        tn->keys[i] = NULL;
    }
    tn->value_count = 0;
}
