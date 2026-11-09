/*
 * ncoll: Java's bergdb.core.NodeCollection (bergdb 012-10): the followers
 * of pointers for the readers and the writer, which load a node that is not
 * in memory from the stream when a pointer leads to it (the slow path of
 * 009-02, 4.4: the node's id, Rule R, its live handle, the version read and
 * installed, the swizzle, the canonical object for the writer), with the
 * startup section's Rule R (docs/sis-model.md, 6.2) and, while the startup
 * rebuilds the database, the cut back of the section's key node versions
 * to the startup time (M22); resolvePointers, the writer's references
 * before a node is written; linkToCanonical, rule 4 by position (005-57).
 * Prefix nc_.
 *
 * One caller: no monitors, no LOADING state (012-07, 6.3), the maintenance
 * follower without its map of versions read (reclaim's, 012-11), no listeners of loads and first touches
 * (tests and eviction's, 012-12). idOf's cache of node headers (Java's
 * LinkedHashMap of 100,000 by access order) is a map cleared when it
 * reaches 100,000 entries: it decides how many headers are read again,
 * never a byte.
 *
 * A follower returns NULL on a failure, its error in nc->err: NOMEM, the
 * stream's read errors, a corrupt node ("StreamFormatException",
 * "StreamChecksumException"...), or Java's StreamFormatException for a
 * pointer to a node that is neither in memory nor in the stream. The
 * caller (the Dag) returns false, and the database decides (a read that
 * fails on the storage fails it, 005-30).
 */
#ifndef BERGDB_NCOLL_H
#define BERGDB_NCOLL_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "lmap.h"
#include "mem.h"
#include "node.h"
#include "nstream.h"
#include "ntable.h"
#include "obj.h"
#include "opdata.h"
#include "snode.h"
#include "stream.h"

/* For tests: nodes served by the test in place of the stream (Java's tests'
 * TestStream, a NodeStream that serves nodes from a map). read_node gives
 * the object of the version at pos (pending or held by the test);
 * read_header its type and id. NULL functions: the stream. */
struct nc_source {
    enum err_code (*read_node)(void *ctx, int64_t pos, struct node **out, struct err *e);
    enum err_code (*read_header)(void *ctx, int64_t pos, int32_t *type, int64_t *id,
            struct err *e);
    void *ctx;
};

struct ncoll {
    struct obj_ctx *cx;
    struct mem *mem;
    struct stream *s;               /* the stream that nodes are read from */
    struct ntable *nt;              /* the node table, the database's */
    /* Rule R, setStartupSection: newById, the section's first position and
     * the startup time; have_section false before. */
    bool have_section;
    struct lmap new_by_id;
    int64_t section_start_pos;
    int64_t section_startup_time;
    bool reconstructing;            /* from setStartupSection to endReconstruction */
    bool check_link;                /* linkToCanonical's check by node id (Java's -ea) */
    struct lmap id_by_pos;          /* idOf's cache */
    struct ns_buf buf;              /* readNode's buffer */
    /* Counts of what was read: the followers' loads (NodeCollection.loads()),
     * the nodes read by others (nc_read_node), the headers read. */
    int64_t loads;
    int64_t reads;
    int64_t header_reads;
    struct err err;                 /* a follower's failure */
    struct nc_source source;        /* tests only */
};

void nc_init(struct ncoll *nc, struct obj_ctx *cx, struct mem *m, struct stream *s,
        struct ntable *nt);

/* Frees the maps and the buffer. */
void nc_free(struct ncoll *nc);

/* The followers, for struct op_follower with ctx the struct ncoll: the
 * readers' (NodeCollection.followPointer) and the writer's
 * (NodeCollection.writer(), which makes every node it reaches canonical). */
struct node *nc_follow_reader(void *ctx, struct node *predecessor, int32_t index,
        struct opdata *op);
struct node *nc_follow_writer(void *ctx, struct node *predecessor, int32_t index,
        struct opdata *op);

/* NodeCollection.MaintenanceFollower's follow (reclaim's, 012-11): no
 * reference raised, no handle made, nothing installed or swizzled; what it
 * reads is kept by nothing (freed at the next safe point). */
struct node *nc_follow_maintenance(void *ctx, struct node *predecessor, int32_t index,
        struct opdata *op);

/* NodeStream.readNode, made an object (pending, obj.h): the node at pos,
 * read and parsed; counted in reads. ERR_NOMEM or the read's errors. */
enum err_code nc_read_node(struct ncoll *nc, int64_t pos, struct node **out, struct err *e);

/* NodeStream.readNodeHeader's id; counted in header_reads. */
enum err_code nc_read_node_header(struct ncoll *nc, int64_t pos, int32_t *type, int64_t *id,
        struct err *e);

/* The object of a parsed node (StoredTopNode.parse, StoredKeyNode.parse,
 * StoredValueNode.parse), pending; NULL: NOMEM. */
struct node *nc_node_from_sn(struct obj_ctx *cx, const struct sn_node *sn);

/* setStartupSection: Rule R for the rest of the process. *newById is moved
 * into the collection (the caller's map is left empty); the reconstruction
 * begins. */
void nc_set_startup_section(struct ncoll *nc, struct lmap *newById, int64_t sectionStartPos,
        int64_t startupTime);

/* endReconstruction: from now on no version read is cut back. Rule R stays. */
void nc_end_reconstruction(struct ncoll *nc);

/* newestInSection: the position of the newest version of node id in the
 * startup section; false if none. */
bool nc_newest_in_section(const struct ncoll *nc, int64_t id, int64_t *pos);

/* pointsToIndexNode: pointer i of node leads to a key node or a top node. */
bool nc_points_to_index_node(const struct node *node, int32_t i);

/* checkPointeeType (bergdb 019-32, as Java's since release 2026.3): pointee,
 * the node at pos that pointer i of node names, is of the type the pointer
 * names: a top node's root pointer (0) a key node and its skip pointers top
 * nodes; a key node's pointers key nodes, and values where
 * nc_points_to_index_node says no. Else ERR_FORMAT, "StreamFormatException":
 * a damaged node (its checksum right) whose pointer names a node of another
 * type, which C read as the type it expected (Java: a ClassCastException).
 * Called by the follows on what they read or find in the handle, by the
 * start's memory pointers, and where a pointer is linked by node id:
 * nc_resolve_pointers and nc_link_to_canonical (bergdb 021-11, as Java's
 * since release 2026.4). */
enum err_code nc_check_pointee_type(const struct node *node, int32_t i,
        const struct node *pointee, int64_t pos, struct err *e);

/* DbStarter.validateKeyNode (bergdb 021-12, as Java's since release 2026.4):
 * a key node version that the start reads, validated
 * (kn_validate_stream_node), and if 'before', a version from before the
 * startup section, none of its times after the startup time. Else
 * ERR_FORMAT, "StreamFormatException", with Java's text. Called for the
 * section's nodes (starter.c's validate_node), and before a version is cut
 * back: by the follows during the reconstruction, for each key node version
 * read, and by the start for the version of a node of D that it reads
 * (canonical_node). Before, a damaged version from before the section, its
 * checksum right, gave the start's check of its nodes (post_startup_check,
 * Java's Db.checkNodes) an AssertionError, or failed an assert of the
 * rerun's put, an abort (kn_add_klong, Java's KeyNode.addKlong; dag.c's
 * append_delete_klong and append_klongs). */
struct knode;
enum err_code nc_validate_key_node(const struct knode *node, int64_t startup_time, bool before,
        struct err *e);

/* newerPos: the newer of reference ref and position w (-1: none). */
int64_t nc_newer_pos(int64_t ref, int64_t w);

/* resolvePointers: before an index node is written, each of its pointers to
 * an index node of the pinned set (canonical and dirty) gets the node's live
 * handle, after nc_check_pointee_type (bergdb 021-11); any other gets its
 * reference after Rule R. ERR_NOMEM, a header read's error, or ERR_FORMAT,
 * "StreamFormatException", for a pinned node of another type, which fails
 * the database (the writer's). */
enum err_code nc_resolve_pointers(struct ncoll *nc, struct node *node, struct err *e);

/* linkToCanonical: rule 4 by position (005-57). ids: posToId; byPos: the
 * live handle of each canonical object by its position (the handle as a
 * long). Each link after nc_check_pointee_type (bergdb 021-11): a pointer
 * that names a node of another type is ERR_FORMAT, "StreamFormatException",
 * and the start refuses the stream. With nc->check_link, each link is
 * checked against rule 4 by node id (a header read): the node by node id of
 * another type is that StreamFormatException; else a difference is
 * ERR_FORMAT, "AssertionError". */
enum err_code nc_link_to_canonical(struct ncoll *nc, struct node *node, const struct lmap *ids,
        const struct lmap *byPos, struct err *e);

#endif
