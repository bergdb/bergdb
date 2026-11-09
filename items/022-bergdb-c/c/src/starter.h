/*
 * starter: the start of an existing database, Level 2's bounded startup,
 * ported from Java's Db.startInner (its checks and its recovery, the
 * startup position, the startup section read) and DbStarter (bergdb 012-10;
 * 012-02, sections 4.3 to 4.6 and 8.14; docs/sis-model.md, 6.2 and 6.3):
 *
 *   1. sr_check_and_recover (Db.startInner before handleStartParams):
 *      refuseIncompleteCreation (005-33), refuseOtherNodeSize (005-50),
 *      nodeStream.recover() with its fill (recover.h), BadMagicBytes as a
 *      StreamFormatException (sr_bad_magic_bytes; BadCryptoKey until
 *      release 2026.4). The creation on an empty stream (handleEmptyStream)
 *      is the caller's (012-09), before this.
 *   2. sr_start: handleStartParams (the format of the in-memory meta block,
 *      the startup position from the last record, walked from the record
 *      the block names; lastTrans set to the last committed record; the
 *      startup distance from the block), readTransactions (the section, from
 *      the startup position), setLastTransTimeOfDbClock (its last time), and
 *      DbStarter in Java's order: validateTransactions; the primordial
 *      startup, or createMaps (posMap, newById, posToId),
 *      updateStreamPointers, changeKeyNodesToStateAtStartupTime,
 *      checkStreamPointers, createMemoryPointers, registerSectionNodes,
 *      findSuperNodeAtStartupTime (topPos, 011-11 M18), prepareDb,
 *      rerunTransactions (the section's transactions rerun at their times,
 *      with the ids and positions of their nodes; D rebuilt from the stored
 *      got-dirty ids), linkD (rule 4 by position, 005-57),
 *      postStartupCheck; then endReconstruction.
 *
 * What the start reads: the records from the one the last valid meta block
 * names to the end (the startup position), the section's records, and the
 * nodes its steps read (topPos's top node, the canonical objects of D's
 * nodes, the loads of the followers); nothing else (Level 2, 007-01). The
 * counts are in struct sr_result and the node collection.
 *
 * The caller (Db, 012-09; sdb.h for reads) owns the parts in struct sr_env:
 * the stream with its in-memory meta block, the node table, the node
 * collection, the Dag (made here, prepareDb), D. After sr_start it sets the
 * clock's last transaction time, makes its PutData and GetData
 * (createPutAndGetData), takes the newest written top node, and runs
 * reclaim's initFromDb (012-11). The rerun uses a PutData of its own, the
 * Dag's with the writer's follower and the rerun's listener: Java's rerun
 * uses Db.newPutData, whose marking does nothing without a transaction
 * (markAtEndOfOp: x.transInfo is null), and whose pointer-created listener
 * feeds the residents and eviction only (no byte). The residents are the
 * allocator's counts in C; eviction's part, the admission list of the large
 * values (Eviction.largeValueCreated), is the caller's listener in struct
 * sr_env, which Db then drains (ev_record_written_start, as Java's start
 * since release 2026.3: bergdb 015-68), with the resident key nodes as the
 * written nodes, for the large values of the section's first transaction,
 * which create_memory_pointers links and the listener does not see (bergdb
 * 019-47, as Java's since release 2026.4).
 *
 * Memory (012-01, 4.5; 012-07, 6.4.4): sr_start makes safe points
 * (obj_collect) between the records it validates, after each put of the
 * rerun and at its end, so the caller holds nothing uncounted when it calls
 * it. The section's records are held (their bytes and parsed views) until
 * sr_start returns, as Java's list of StoredTrans; posMap's objects are
 * counted by the starter until the node table holds them.
 *
 * Errors: Java's, as codes with Java's exception names (err.h): a stream
 * that Java refuses is refused here with the same name (ERR_FORMAT
 * "StreamFormatException", "VersioningStreamException";
 * ERR_NOT_CREATED "DatabaseNotCreatedException"), the stream's errors, or
 * ERR_NOMEM. On an error the caller frees what the env holds (close's walk).
 * Prefix sr_.
 */
#ifndef BERGDB_STARTER_H
#define BERGDB_STARTER_H

#include <stdbool.h>
#include <stdint.h>
#include "dag.h"
#include "err.h"
#include "lmap.h"
#include "mem.h"
#include "ncoll.h"
#include "ntable.h"
#include "obj.h"
#include "rstream.h"
#include "tnode.h"
#include "transseq.h"

/* Db.CREATION_LENGTH: the first meta block and the primordial record. */
#define SR_CREATION_LENGTH (128 + 136)

/* What DbStarter and Db.startInner reach through db.internal(). */
struct sr_env {
    struct mem *mem;
    struct obj_ctx *cx;
    struct rs *rs;              /* the stream (rs->s) and the in-memory meta block */
    struct ntable *nt;          /* Cache3 */
    struct ncoll *nc;           /* NodeCollection, on nt and rs->s */
    struct dag *dag;            /* Db.dag: made by sr_start (prepareDb) */
    struct ts_seq *ts;          /* TransSeq, D: rebuilt by sr_start's rerun */
    int32_t max_node_size;      /* the start's (DbBuilder's) */
    int64_t second_top_ordinal; /* DbBuilder.secondTopOrdinal (005-02, tests); 0: 1. Db's
                                   setDag gives it to the Dag's TopDs before the rerun */
    /* The rerun's pointer-created listener, Db.newPutData's: eviction's
     * admission list of the large values the rerun makes (bergdb 015-68);
     * NULL for none (sdb's start, for reads, which has no eviction). */
    const struct op_pointer_created_listener *pointer_created;
};

/* What the start sets in Db, and Java's StartInfo. */
struct sr_result {
    struct tnode *newest_written_top;   /* setNewestWrittenTop: retained for the caller,
                                           who keeps or releases it */
    bool dag_made;              /* *env->dag was made (dag_init): the caller frees it */
    int64_t startup_pos;        /* x.startupPos: the last record's startupPos */
    int32_t startup_distance;   /* Db.startupDistance: the meta block's */
    int64_t last_trans_time;    /* setLastTransTimeOfDbClock: the last record's time */
    /* StartInfo */
    int64_t start_pos;          /* the startup position (0: the first record) */
    int64_t start_time;         /* the section's first record's time */
    int32_t trans_count;        /* its records */
    int64_t last_pos;           /* the last record's last byte */
    /* What the start read: the records walked (from the meta block's record,
     * then the section) and their bytes. */
    int64_t walk_records;
    int64_t walk_bytes;
    int64_t section_records;
    int64_t section_bytes;
    int64_t rerun_pairs;        /* value and delete nodes rerun */
};

/* Db.startInner's refusal of a stream whose magic bytes are wrong (the
 * storage's BadMagicBytes, ERR_FORMAT): a StreamFormatException with Java's
 * text, the BadMagicBytes its cause (bergdb 020-28, as Java's since release
 * 2026.4; it was the Pub API's BadCryptoKey, which 2026.4 removed with the
 * encryption). C has no encryption, so the text is Java's for a start
 * without a key. Returns ERR_FORMAT. */
enum err_code sr_bad_magic_bytes(struct err *e);

/* Db.startInner's checks and the recovery, before the startup position is
 * read (see above). *plan: what the recovery found and appended. */
enum err_code sr_check_and_recover(struct sr_env *env, struct rs_recovery *plan,
        struct err *e);

/* The rest of the start (see above), after sr_check_and_recover. */
enum err_code sr_start(struct sr_env *env, struct sr_result *out, struct err *e);

/* DbStarter's checks that name a node, Java's texts (also for tests): each
 * names the node by Node.name, "KIND ID at SPOS" (node_kind), the same in
 * every run (bergdb 021-15, as Java's since release 2026.4; before, Java's
 * printed the node, with Object.toString's identity hash, and C's were its
 * own). StreamFormatException but where said. */
struct sn_node;
struct st_record;
/* validateNode: a node of the section, its position ("Bad spos of KIND ID
 * at SPOS.") and a key node's validation (nc_validate_key_node). */
enum err_code sr_validate_node(struct obj_ctx *cx, const struct sn_node *sn,
        int64_t startup_time, struct err *e);
/* checkPrimordialTransaction: two nodes, a top node and a key node
 * ("Expected TopNode, got KIND ID at SPOS."). */
enum err_code sr_check_primordial_transaction(const struct st_record *t, struct err *e);
/* checkStreamPointers(node): each stream pointer of the node names a
 * version in the stream, not Spos.NULL or a vpos ("Unexpected stream
 * pointer S, index I of KIND ID at SPOS."). */
enum err_code sr_check_stream_pointers(const struct node *node, struct err *e);
/* checkThatValueNodesHaveSpos, for the value nodes of key node k: an
 * AssertionError ("value node got no spos during startup, value node ID at
 * SPOS."). */
enum err_code sr_check_value_nodes_have_spos(const struct knode *k, struct err *e);

/* StoredTrans.findNode(id) of record t, for the rerun's nodeCreated: its node
 * of the id in *out, or NULL; the first of the nodes, in their order, if
 * several have it. A scan of the nodes, as before bergdb 021-16, when they
 * are at most SR_FIND_NODE_SCAN_LIMIT, as in most records; otherwise a
 * lookup in ids, a map from an id to the index of its first node, made
 * when *indexed is false (then set), at the first call for the record
 * (021-16, Q2, as Java's since release 2026.4). The rerun calls it for
 * every node it makes, a key node per 7 bytes of a new key: with a scan
 * only, a database with a key of 100,000 bytes and then one of 1,000,000
 * with the same start took seconds to start, in this scan. false: NOMEM,
 * in e (the map is made again at the next call). */
#define SR_FIND_NODE_SCAN_LIMIT 64      /* StoredTrans.FIND_NODE_SCAN_LIMIT */
bool sr_find_node(const struct st_record *t, struct lmap *ids, bool *indexed, int64_t id,
        const struct sn_node **out, struct err *e);

#endif
