/* keymod: ported from Java's KeyModSet; see keymod.h. */
#include "keymod.h"
#include <assert.h>
#include <stddef.h>
#include "jsem.h"

static void bin_free(struct mem *m, struct kms_bin *bin) {
    if (bin == NULL) {
        return;
    }
    for (int32_t i = 0; i < bin->subSize; i++) {
        mem_free(m, bin->subBins[i].a, (size_t) bin->subBins[i].len * sizeof(int64_t),
                MEM_STATE);
    }
    mem_free(m, bin->subBins, (size_t) bin->subSize * sizeof *bin->subBins, MEM_STATE);
    mem_free(m, bin, sizeof *bin, MEM_STATE);
}

/* Bin(maxSize). */
static struct kms_bin *bin_new(struct mem *m, int32_t maxSize) {
    assert(maxSize > 0);
    struct kms_bin *bin = mem_alloc(m, sizeof *bin, MEM_STATE);
    if (bin == NULL) {
        return NULL;
    }
    bin->maxSize = maxSize;
    bin->subSize = maxSize / 4;
    if (bin->subSize == 0) {
        bin->subSize = 1;
    }
    bin->subBins = mem_zalloc(m, (size_t) bin->subSize * sizeof *bin->subBins, MEM_STATE);
    if (bin->subBins == NULL) {
        mem_free(m, bin, sizeof *bin, MEM_STATE);
        return NULL;
    }
    bin->size = 0;
    bin->firstTime = -1;
    return bin;
}

static bool bin_is_full(const struct kms_bin *bin) {
    assert(bin->size <= bin->maxSize);
    return bin->size == bin->maxSize;
}

/* Bin.add; false on a failed allocation, the bin as it was. */
static bool bin_add(struct mem *m, struct kms_bin *bin, int64_t time, int64_t hash) {
    assert(time >= bin->firstTime);
    assert(hash >= 0);
    assert(!bin_is_full(bin));

    int32_t index = j_l2i(j_rem64(hash & INT64_MAX, bin->subSize));  /* never negative (005-21) */
    struct kms_sub *sub = &bin->subBins[index];

    if (sub->a == NULL) {
        int64_t *array = mem_alloc(m, KMS_INITIAL_SIZE_OF_LONG_ARRAY * sizeof(int64_t),
                MEM_STATE);
        if (array == NULL) {
            return false;
        }
        for (int32_t i = 0; i < KMS_INITIAL_SIZE_OF_LONG_ARRAY; i++) {
            array[i] = 0;
        }
        for (int32_t i = 0; i < KMS_INITIAL_SIZE_OF_LONG_ARRAY; i += 2) {
            array[i] = -1;
        }
        sub->a = array;
        sub->len = KMS_INITIAL_SIZE_OF_LONG_ARRAY;
    }

    bool set = false;
    const int32_t len = sub->len;
    int64_t *array = sub->a;
    for (int32_t i = 0; i < len; i += 2) {
        if (array[i] == -1 || array[i + 1] == hash) {
            array[i] = time;
            array[i + 1] = hash;
            set = true;
            break;
        }
    }

    if (!set) {
        int64_t *newArray = mem_realloc(m, array, (size_t) len * sizeof(int64_t),
                (size_t) len * 2 * sizeof(int64_t), MEM_STATE);
        if (newArray == NULL) {
            return false;
        }
        for (int32_t i = len; i < 2 * len; i += 2) {
            newArray[i] = -1;
            newArray[i + 1] = 0;
        }
        newArray[len] = time;
        newArray[len + 1] = hash;
        sub->a = newArray;
        sub->len = 2 * len;
    }

    /* Java counts the pair and sets firstTime first; the same, as nothing
     * above reads them. Here after the allocations, so that a failed one
     * leaves the bin as it was. */
    if (bin->size == 0) {
        bin->firstTime = time;
    }
    bin->size++;
    return true;
}

/* Bin.getTime: the hash's last time, or -1 if it is not in the bin. */
static int64_t bin_get_time(const struct kms_bin *bin, int64_t hash) {
    assert(hash >= 0);
    int32_t index = j_l2i(j_rem64(hash & INT64_MAX, bin->subSize));  /* never negative (005-21) */
    const struct kms_sub *sub = &bin->subBins[index];

    if (sub->a == NULL) {
        return -1;
    }
    for (int32_t i = 0; i < sub->len; i += 2) {
        if (sub->a[i + 1] == hash && sub->a[i] != -1) {
            return sub->a[i];
        }
    }
    return -1;
}

enum err_code kms_init_size(struct kms *s, struct mem *m, int32_t totalSize, struct err *e) {
    assert(totalSize > 0);
    s->mem = m;
    for (int i = 0; i < KMS_BIN_COUNT; i++) {
        s->bins[i] = NULL;
    }
    if (totalSize % KMS_BIN_COUNT != 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException",
                "size was %d, must be dividable by %d.", (int) totalSize, KMS_BIN_COUNT);
    }
    s->totalSize = totalSize;
    /* The other bins are NULL to start with. */
    s->bins[0] = bin_new(m, totalSize / KMS_BIN_COUNT);
    if (s->bins[0] == NULL) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a KeyModSet");
    }
    return ERR_OK;
}

enum err_code kms_init(struct kms *s, struct mem *m, struct err *e) {
    return kms_init_size(s, m, KMS_DEFAULT_SIZE, e);
}

void kms_free(struct kms *s) {
    for (int i = 0; i < KMS_BIN_COUNT; i++) {
        bin_free(s->mem, s->bins[i]);
        s->bins[i] = NULL;
    }
}

int64_t kms_first_time(const struct kms *s) {
    int64_t result = -1;
    for (int i = KMS_BIN_COUNT - 1; i >= 0; i--) {
        const struct kms_bin *bin = s->bins[i];
        if (bin == NULL) {
            continue;
        }
        result = bin->firstTime;
        break;
    }
    return result;
}

bool kms_modified_after(const struct kms *s, int64_t time, int64_t hash) {
    int endBin = -1;

    for (int i = 0; i < KMS_BIN_COUNT; i++) {
        const struct kms_bin *bin = s->bins[i];
        if (bin == NULL) {
            break;
        }
        if (time >= bin->firstTime) {
            endBin = i;
        }
    }

    if (endBin == -1) {
        /* Too old time, not enough information, we must be on the safe
         * side and report that it was modified. */
        return true;
    }

    int64_t t;
    bool result = false;
    for (int i = 0; i <= endBin; i++) {
        t = bin_get_time(s->bins[i], hash);
        if (t == -1) {
            continue;
        }
        if (t > time) {
            result = true;
            break;
        }
    }
    return result;
}

enum err_code kms_add(struct kms *s, int64_t time, int64_t hash, struct err *e) {
    if (bin_is_full(s->bins[0])) {
        /* System.arraycopy(bins, 0, bins, 1, BIN_COUNT - 1), then a new
         * bin 0 and the pair in it. Here the new bin is made and given
         * the pair first, so that a failure changes nothing. */
        struct kms_bin *bin = bin_new(s->mem, s->totalSize / KMS_BIN_COUNT);
        if (bin == NULL || !bin_add(s->mem, bin, time, hash)) {
            bin_free(s->mem, bin);
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a KeyModSet bin");
        }
        bin_free(s->mem, s->bins[KMS_BIN_COUNT - 1]);
        for (int i = KMS_BIN_COUNT - 1; i > 0; i--) {
            s->bins[i] = s->bins[i - 1];
        }
        s->bins[0] = bin;
        return ERR_OK;
    }

    if (!bin_add(s->mem, s->bins[0], time, hash)) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a KeyModSet entry");
    }
    return ERR_OK;
}
