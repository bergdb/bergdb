/* strmap: ported from Java's StringMap, with HashMap's order; see
 * strmap.h. */
#include "strmap.h"
#include <assert.h>
#include <string.h>
#include "jsem.h"

#define TREEIFY_THRESHOLD 8         /* HashMap.TREEIFY_THRESHOLD */
#define MIN_TREEIFY_CAPACITY 64     /* HashMap.MIN_TREEIFY_CAPACITY */

void sm_init(struct sm *m, struct mem *mem) {
    m->mem = mem;
    m->entries = NULL;
    m->n = 0;
    m->cap = 0;
    m->tableSize = 0;
    m->threshold = 0;
}

void sm_free(struct sm *m) {
    for (int32_t i = 0; i < m->n; i++) {
        mem_free(m->mem, m->entries[i].key, m->entries[i].key_size, MEM_STATE);
        mem_free(m->mem, m->entries[i].value, m->entries[i].value_size, MEM_STATE);
    }
    mem_free(m->mem, m->entries, (size_t) m->cap * sizeof *m->entries, MEM_STATE);
    sm_init(m, m->mem);
}

/* The next UTF-16 code unit(s) of UTF-8 text: returns the bytes used, and
 * the units in u[0] and, for a supplementary character, u[1] (*nu). */
static size_t next_units(const unsigned char *s, size_t n, int32_t u[2], int *nu) {
    unsigned c = s[0];
    int32_t cp;
    size_t len;
    *nu = 1;
    if (c < 0x80) {
        u[0] = (int32_t) c;
        return 1;
    } else if (c >= 0xc2 && c < 0xe0) {
        len = 2;
        cp = (int32_t) (c & 0x1f);
    } else if (c >= 0xe0 && c < 0xf0) {
        len = 3;
        cp = (int32_t) (c & 0x0f);
    } else if (c >= 0xf0 && c < 0xf5) {
        len = 4;
        cp = (int32_t) (c & 0x07);
    } else {
        u[0] = 0xfffd;
        return 1;
    }
    if (len > n) {
        u[0] = 0xfffd;
        return 1;
    }
    for (size_t i = 1; i < len; i++) {
        if ((s[i] & 0xc0) != 0x80) {
            u[0] = 0xfffd;
            return 1;
        }
        cp = (cp << 6) | (int32_t) (s[i] & 0x3f);
    }
    if ((len == 3 && (cp < 0x800 || (cp >= 0xd800 && cp < 0xe000)))
            || (len == 4 && (cp < 0x10000 || cp > 0x10ffff))) {
        u[0] = 0xfffd;
        return 1;
    }
    if (cp >= 0x10000) {
        cp -= 0x10000;
        u[0] = 0xd800 + (cp >> 10);
        u[1] = 0xdc00 + (cp & 0x3ff);
        *nu = 2;
    } else {
        u[0] = cp;
    }
    return len;
}

int32_t sm_string_hash(const char *s, size_t n) {
    const unsigned char *p = (const unsigned char *) s;
    int32_t h = 0;
    size_t i = 0;
    while (i < n) {
        int32_t u[2];
        int nu;
        i += next_units(p + i, n - i, u, &nu);
        for (int k = 0; k < nu; k++) {
            h = 31 * h + u[k];
        }
    }
    return h;
}

/* HashMap.hash. */
static int32_t spread(int32_t h) {
    return h ^ j_ushr32(h, 16);
}

static char *copy(struct mem *mem, const char *s, size_t n, size_t *size) {
    char *c = mem_alloc(mem, n + 1, MEM_STATE);
    if (c != NULL) {
        memcpy(c, s, n);
        c[n] = '\0';
        *size = n + 1;
    }
    return c;
}

static int32_t find(const struct sm *m, const char *key, size_t klen) {
    for (int32_t i = 0; i < m->n; i++) {
        if (m->entries[i].key_size == klen + 1 && memcmp(m->entries[i].key, key, klen) == 0) {
            return i;
        }
    }
    return -1;
}

static void resize(struct sm *m) {
    m->tableSize *= 2;
    m->threshold *= 2;
}

/* HashMap.put of a key and a value of the given lengths. */
static enum err_code put_n(struct sm *m, const char *key, size_t klen, const char *value,
        size_t vlen, struct err *e) {
    assert(klen > 0);
    int32_t i = find(m, key, klen);
    size_t vsize;
    char *v = copy(m->mem, value, vlen, &vsize);
    if (v == NULL) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a StringMap value");
    }
    if (i >= 0) {
        mem_free(m->mem, m->entries[i].value, m->entries[i].value_size, MEM_STATE);
        m->entries[i].value = v;
        m->entries[i].value_size = vsize;
        return ERR_OK;
    }

    if (m->n == m->cap) {
        int32_t c2 = m->cap == 0 ? 16 : 2 * m->cap;
        struct sm_entry *e2 = mem_realloc(m->mem, m->entries, (size_t) m->cap * sizeof *e2,
                (size_t) c2 * sizeof *e2, MEM_STATE);
        if (e2 == NULL) {
            mem_free(m->mem, v, vsize, MEM_STATE);
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a StringMap");
        }
        m->entries = e2;
        m->cap = c2;
    }
    size_t ksize;
    char *k = copy(m->mem, key, klen, &ksize);
    if (k == NULL) {
        mem_free(m->mem, v, vsize, MEM_STATE);
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a StringMap key");
    }

    /* The table: made at the first put (HashMap.resize: 16, threshold 12). */
    int32_t tableSize = m->tableSize == 0 ? 16 : m->tableSize;
    int32_t threshold = m->tableSize == 0 ? 12 : m->threshold;
    const int32_t hash = spread(sm_string_hash(key, klen));
    int32_t inBin = 0;
    for (int32_t j = 0; j < m->n; j++) {
        inBin += (m->entries[j].hash & (tableSize - 1)) == (hash & (tableSize - 1));
    }
    if (inBin + 1 > TREEIFY_THRESHOLD && tableSize >= MIN_TREEIFY_CAPACITY) {
        mem_free(m->mem, k, ksize, MEM_STATE);
        mem_free(m->mem, v, vsize, MEM_STATE);
        return err_set(e, ERR_ARG, "IllegalArgumentException", "A StringMap bucket of %d keys "
                "in a table of %d: Java's HashMap makes it a tree, whose order is not ported.",
                (int) (inBin + 1), (int) tableSize);
    }
    m->tableSize = tableSize;
    m->threshold = threshold;

    struct sm_entry *x = &m->entries[m->n];
    x->key = k;
    x->key_size = ksize;
    x->value = v;
    x->value_size = vsize;
    x->hash = hash;
    x->order = m->n;
    /* A ninth key in a bucket: HashMap.treeifyBin resizes a small table. */
    if (inBin + 1 > TREEIFY_THRESHOLD) {
        resize(m);
    }
    if (++m->n > m->threshold) {
        resize(m);
    }
    return ERR_OK;
}

enum err_code sm_put(struct sm *m, const char *key, const char *value, struct err *e) {
    assert(key != NULL && value != NULL);
    return put_n(m, key, strlen(key), value, strlen(value), e);
}

const char *sm_get(const struct sm *m, const char *key) {
    int32_t i = find(m, key, strlen(key));
    return i < 0 ? NULL : m->entries[i].value;
}

bool sm_parse_long(const char *s, size_t n, int64_t *out) {
    size_t i = 0;
    bool negative = false;
    if (n > 0 && (s[0] == '+' || s[0] == '-')) {
        negative = s[0] == '-';
        i = 1;
    }
    if (i == n) {
        return false;
    }
    /* Accumulated negatively, as Long.parseLong does, so that MIN fits. */
    int64_t result = 0;
    for (; i < n; i++) {
        if (s[i] < '0' || s[i] > '9') {
            return false;
        }
        int64_t digit = s[i] - '0';
        if (result < INT64_MIN / 10 || result * 10 < INT64_MIN + digit) {
            return false;
        }
        result = result * 10 - digit;
    }
    if (!negative) {
        if (result == INT64_MIN) {
            return false;
        }
        result = -result;
    }
    *out = result;
    return true;
}

bool sm_has_long(const struct sm *m, const char *key) {
    const char *v = sm_get(m, key);
    int64_t x;
    return v != NULL && sm_parse_long(v, strlen(v), &x);
}

enum err_code sm_get_long(const struct sm *m, const char *key, int64_t *out, struct err *e) {
    const char *v = sm_get(m, key);
    if (v == NULL) {
        return err_set(e, ERR_FORMAT, "NumberFormatException", "No value for key %s", key);
    }
    if (!sm_parse_long(v, strlen(v), out)) {
        return err_set(e, ERR_FORMAT, "NumberFormatException", "For input string: \"%s\"", v);
    }
    return ERR_OK;
}

enum err_code sm_parse(struct sm *m, const char *s, size_t n, struct err *e) {
    size_t start = 0;
    while (start <= n) {
        size_t end = start;
        while (end < n && s[end] != '\n') {
            end++;
        }
        /* line = line.trim(). */
        size_t a = start, b = end;
        while (a < b && (unsigned char) s[a] <= ' ') {
            a++;
        }
        while (b > a && (unsigned char) s[b - 1] <= ' ') {
            b--;
        }
        const char *eq = memchr(s + a, '=', b - a);
        if (eq != NULL && eq != s + a) {
            size_t index = (size_t) (eq - (s + a));
            enum err_code rc = put_n(m, s + a, index, eq + 1, b - a - index - 1, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }
        start = end + 1;
    }
    return ERR_OK;
}

enum err_code sm_serialize(const struct sm *m, char **out, size_t *n, struct err *e) {
    size_t total = 0;
    for (int32_t i = 0; i < m->n; i++) {
        total += m->entries[i].key_size + m->entries[i].value_size;    /* '=' and '\n' */
    }
    char *text = mem_alloc(m->mem, total + 1, MEM_BUFFER);
    if (text == NULL) {
        return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a StringMap's text");
    }
    /* HashMap's iteration: the buckets in order, each in the order its keys
     * were first put. */
    size_t at = 0;
    const int32_t mask = m->tableSize - 1;
    for (int32_t bucket = 0; bucket < m->tableSize; bucket++) {
        for (int32_t i = 0; i < m->n; i++) {
            const struct sm_entry *x = &m->entries[i];
            if ((x->hash & mask) != bucket) {
                continue;
            }
            memcpy(text + at, x->key, x->key_size - 1);
            at += x->key_size - 1;
            text[at++] = '=';
            memcpy(text + at, x->value, x->value_size - 1);
            at += x->value_size - 1;
            text[at++] = '\n';
        }
    }
    text[at] = '\0';
    *out = text;
    *n = at;
    return ERR_OK;
}
