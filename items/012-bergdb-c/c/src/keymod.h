/*
 * keymod: the STM's conflict set, ported from Java's
 * bergdb.core.KeyModSet (bergdb 012-09, part 1): a fixed maximum number of
 * (hash of a key, time) pairs, in up to 4 bins of 32,000 pairs each (of
 * 128,000 in all), newest first. A transaction with a read set is refused
 * (RerunException) when kms_modified_after says that a key it read was
 * written after its read time (Db.stmCheckConflicts); every committed
 * write adds its key's hash and time. Prefix kms_.
 *
 * As Java's, a set is in memory only, and a start makes a new one, whose
 * first bin is empty with firstTime -1: it then holds nothing before the
 * start, and answers "not modified" for any read time older than it
 * (012-02, 10.3, C4; Java bug 005-70, which C follows until Java is fixed).
 * A read time older than every bin's first time is answered "modified"
 * ("Too old time, not enough information, we must be on the safe side").
 *
 * Memory (MEM_STATE): a bin is an array of subSize = maxSize / 4 sub-bins,
 * each NULL or an array of (time, hash) pairs, 2 longs a pair, 4 longs at
 * first, doubled when full, with time -1 for a free pair. Java's structure
 * exactly, so that the answers are Java's.
 */
#ifndef BERGDB_KEYMOD_H
#define BERGDB_KEYMOD_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"

#define KMS_BIN_COUNT 4                     /* KeyModSet.BIN_COUNT */
#define KMS_INITIAL_SIZE_OF_LONG_ARRAY 4    /* KeyModSet.INITIAL_SIZE_OF_LONG_ARRAY */
#define KMS_DEFAULT_SIZE (128 * 1000)       /* KeyModSet() */

/* A sub-bin: an array of len longs, (time, hash) pairs; NULL if none. */
struct kms_sub {
    int64_t *a;
    int32_t len;
};

/* KeyModSet.Bin. */
struct kms_bin {
    int32_t maxSize;
    int32_t subSize;
    int64_t firstTime;
    int32_t size;
    struct kms_sub *subBins;    /* subSize of them */
};

struct kms {
    struct mem *mem;
    int32_t totalSize;
    struct kms_bin *bins[KMS_BIN_COUNT];    /* bins[0] the newest; NULL: none yet */
};

/* KeyModSet(): a set of 128,000 pairs, its first bin made. ERR_NOMEM, and
 * nothing allocated. */
enum err_code kms_init(struct kms *s, struct mem *m, struct err *e);

/* KeyModSet(int totalSize), Java's tests': a multiple of 4 (else ERR_ARG,
 * "IllegalArgumentException"); asserted above 0. */
enum err_code kms_init_size(struct kms *s, struct mem *m, int32_t totalSize, struct err *e);

/* Frees the bins. */
void kms_free(struct kms *s);

/* KeyModSet.getFirstTime: the first time of the oldest bin, -1 if it is
 * empty. */
int64_t kms_first_time(const struct kms *s);

/* KeyModSet.modifiedAfter: whether the key of 'hash' was written after
 * 'time': true if a bin from the newest to the oldest whose first time is
 * at or before 'time' has the hash with a later time, or if no bin's first
 * time is at or before 'time' (too old). The hash is not negative
 * (asserted). */
bool kms_modified_after(const struct kms *s, int64_t time, int64_t hash);

/* KeyModSet.add: when the newest bin is full, a new one becomes the newest
 * and the oldest of 4 goes; then the pair goes into the newest bin, in
 * place of the hash's pair if the sub-bin has one. Times are added in
 * order (asserted, as the hash not negative). ERR_NOMEM, and the set as it
 * was. */
enum err_code kms_add(struct kms *s, int64_t time, int64_t hash, struct err *e);

#endif
