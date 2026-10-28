/* opdata: Java's OpData and the Dag's interfaces; see opdata.h. */
#include "opdata.h"
#include <assert.h>
#include <string.h>

void op_init(struct opdata *op) {
    memset(op, 0, sizeof *op);
    op->access_data = 0;
    ptr_reset(&op->temp_pointer);
    kwp_init(&op->kwi);
}

/* OpData.followPointer */
struct node *op_follow_pointer(struct opdata *op, struct node *predecessor, int32_t index) {
    assert(op->pointer_follower.follow != NULL && "OpData.pointerFollower is null, not allowed");
    return op->pointer_follower.follow(op->pointer_follower.ctx, predecessor, index, op);
}

static bool nothing_followed(void *ctx, struct node *predecessor, int32_t index,
        struct node *result, int32_t pointer_type) {
    (void) ctx, (void) predecessor, (void) index, (void) result, (void) pointer_type;
    return true;
}

static bool nothing_accessed(void *ctx, struct tnode *super_root) {
    (void) ctx, (void) super_root;
    return true;
}

static bool nothing_created(void *ctx, struct node *from, int32_t index, struct node *to) {
    (void) ctx, (void) from, (void) index, (void) to;
    return true;
}

static bool nothing_top(void *ctx, struct tnode *node) {
    (void) ctx, (void) node;
    return true;
}

static bool nothing_key(void *ctx, struct knode *node) {
    (void) ctx, (void) node;
    return true;
}

static bool nothing_value(void *ctx, struct vnode *node, const int64_t *key, int32_t key_n) {
    (void) ctx, (void) node, (void) key, (void) key_n;
    return true;
}

const struct op_pointer_listener OP_DO_NOTHING_POINTER_LISTENER = {
    nothing_followed, nothing_accessed, NULL
};

const struct op_pointer_created_listener OP_DO_NOTHING_POINTER_CREATED_LISTENER = {
    nothing_created, NULL
};

const struct op_node_change_listener OP_DO_NOTHING_NODE_CHANGE_LISTENER = {
    nothing_top, nothing_key, nothing_value, nothing_key, nothing_key, nothing_top, NULL
};

bool op_pointer_created(const struct op_pointer_created_listener *l, struct node *from,
        int32_t index, struct node *to) {
    return l->pointer_created == NULL || l->pointer_created(l->ctx, from, index, to);
}

bool op_top_node_created(const struct op_node_change_listener *l, struct tnode *node) {
    return l->top_node_created == NULL || l->top_node_created(l->ctx, node);
}

bool op_top_node_replaced(const struct op_node_change_listener *l, struct tnode *node) {
    return l->top_node_replaced == NULL || l->top_node_replaced(l->ctx, node);
}

bool op_super_root_accessed(const struct op_pointer_listener *l, struct tnode *super_root) {
    return l->super_root_accessed == NULL || l->super_root_accessed(l->ctx, super_root);
}
