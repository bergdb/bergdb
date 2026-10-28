/* mem: the allocator; see mem.h. */
#include "mem.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef BERGDB_TEST
/* The test build's header before each block: the size and kind given at the
 * allocation, checked at the free. 16 bytes keep the block aligned. */
#define HEADER 16
#define MAGIC 0x6267646dU      /* "bgdm" */
struct header {
    uint64_t size;
    uint32_t kind;
    uint32_t magic;
};
#else
#define HEADER 0
#endif

void mem_init(struct mem *m) {
    memset(m, 0, sizeof *m);
}

static const char *const kind_names[MEM_KINDS] = {
    "index", "value", "handle", "table", "buffer", "caller", "state"
};

const char *mem_kind_name(enum mem_kind kind) {
    return (unsigned) kind < MEM_KINDS ? kind_names[kind] : "?";
}

/* True if this allocation is the one to fail. */
static int fails(struct mem *m) {
    m->allocs++;
    if (m->fail_at != 0 && m->allocs == m->fail_at) {
        m->failed++;
        return 1;
    }
    return 0;
}

static void count(struct mem *m, enum mem_kind kind, int64_t bytes, int64_t blocks) {
    m->live[kind] += bytes;
    m->live_total += bytes;
    m->live_blocks += blocks;
    if (m->live_total > m->peak_total) {
        m->peak_total = m->live_total;
    }
}

#ifdef BERGDB_TEST
static void check_header(void *p, size_t size, enum mem_kind kind) {
    struct header h;
    memcpy(&h, (char *) p - HEADER, sizeof h);
    if (h.magic != MAGIC || h.size != size || h.kind != (uint32_t) kind) {
        fprintf(stderr, "mem: bad free of %p: given size %zu kind %s, allocated %s"
                " size %llu kind %s\n", p, size, mem_kind_name(kind),
                h.magic == MAGIC ? "with" : "(no header)", (unsigned long long) h.size,
                mem_kind_name((enum mem_kind) h.kind));
        abort();
    }
}

static void *set_header(void *raw, size_t size, enum mem_kind kind) {
    struct header h;
    h.size = size;
    h.kind = (uint32_t) kind;
    h.magic = MAGIC;
    memcpy(raw, &h, sizeof h);
    return (char *) raw + HEADER;
}
#endif

void *mem_alloc(struct mem *m, size_t size, enum mem_kind kind) {
    if (fails(m)) {
        return NULL;
    }
    /* malloc(0) may give NULL, which would read as a failure: 1 byte then. */
    void *raw = size > SIZE_MAX - HEADER - 1 ? NULL
            : malloc(size + HEADER == 0 ? 1 : size + HEADER);
    if (raw == NULL) {
        m->failed++;
        return NULL;
    }
    count(m, kind, (int64_t) size, 1);
#ifdef BERGDB_TEST
    return set_header(raw, size, kind);
#else
    return raw;
#endif
}

void *mem_zalloc(struct mem *m, size_t size, enum mem_kind kind) {
    void *p = mem_alloc(m, size, kind);
    if (p != NULL) {
        memset(p, 0, size);
    }
    return p;
}

void *mem_realloc(struct mem *m, void *p, size_t old_size, size_t new_size, enum mem_kind kind) {
    if (p == NULL) {
        return mem_alloc(m, new_size, kind);
    }
#ifdef BERGDB_TEST
    check_header(p, old_size, kind);
#endif
    if (fails(m)) {
        return NULL;
    }
    void *raw = new_size > SIZE_MAX - HEADER - 1 ? NULL
            : realloc((char *) p - HEADER, new_size + HEADER == 0 ? 1 : new_size + HEADER);
    if (raw == NULL) {
        m->failed++;
        return NULL;
    }
    count(m, kind, (int64_t) new_size - (int64_t) old_size, 0);
#ifdef BERGDB_TEST
    return set_header(raw, new_size, kind);
#else
    return raw;
#endif
}

void mem_free(struct mem *m, void *p, size_t size, enum mem_kind kind) {
    if (p == NULL) {
        return;
    }
#ifdef BERGDB_TEST
    check_header(p, size, kind);
    memset((char *) p - HEADER, 0, HEADER);
#endif
    count(m, kind, -(int64_t) size, -1);
    free((char *) p - HEADER);
}
