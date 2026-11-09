/*
 * starter: the start of an existing database, Level 2's bounded startup,
 * ported from Java's Db.startInner (its checks and its recovery, the
 * startup position, the startup section read) and DbStarter (bergdb 012-10;
 * 012-02, sections 4.3 to 4.6 and 8.14; docs/sis-model.md, 6.2 and 6.3):
 *
 *   1. sr_check_and_recover (Db.startInner before handleStartParams):
 *      refuseIncompleteCreation (005-33), refuseOtherNodeSize (005-50),
 *      nodeStream.recover() with its fill (recover.h), BadMagicBytes as
 *      BadCryptoKey. The creation on an empty stream (handleEmptyStream)
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
 * feeds the residents and eviction only (no byte).
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
 * "StreamFormatException", "VersioningStreamException", "BadCryptoKey";
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

/* Db.startInner's checks and the recovery, before the startup position is
 * read (see above). *plan: what the recovery found and appended. */
enum err_code sr_check_and_recover(struct sr_env *env, struct rs_recovery *plan,
        struct err *e);

/* The rest of the start (see above), after sr_check_and_recover. */
enum err_code sr_start(struct sr_env *env, struct sr_result *out, struct err *e);

#endif
