/*
 * bergdb-power: power loss under a model (bergdb 012-14, done item 2; the
 * design in 14-robustness.md, 6.5). tools/run.c's runner (Java's Run, the
 * same text and bytes) runs a workload on C's database while the test
 * build's I/O seam (plat.h, struct plat_io) gives every write, force,
 * directory force and delete of the stream to a model, Java's ModelIo of
 * FileStreamPowerLossTester in C: per file, the bytes written (passed on to
 * the real file, so that the database runs as usual) and the bytes forced;
 * the durable names (a new name is durable after a force of the directory;
 * a delete survives at once, as Java's model has it, "adversarial but
 * allowed"). At each event the model takes an *image*, the files that a
 * power loss then leaves: the forced bytes of each durable name. Images:
 *
 *   after_write       after each write (the written bytes lost)
 *   torn_half         after a write, a durable file with the unforced tail
 *   torn_random       cut at half (Java's partial_write) and at a random length
 *   after_file_force  after each force of a file
 *   after_dir_force   after each force of the directory
 *   after_delete      after each delete
 *   unpersisted_delete  the delete rolled back (the file with its forced bytes)
 *   unordered_delete  earlier unforced deletes rolled back, this one kept
 *   after_sync        after each acknowledged sync or close
 *
 * An image equal to an earlier one (the same names, forced lengths and tear)
 * is not written again. Each is written as a directory IMAGES/NNNNNN with
 * its .bergdb files and image.txt: "event=E ack=A first=F end=X lost=L",
 * where A is the acknowledged length (the stream's durable length after the
 * last bergdb_sync, or its length before the last bergdb_close, that
 * returned BERGDB_OK before the image: every transaction there was
 * committed and synced), F the image's first position, X the end of its
 * contiguous files from F, and L 1 if X < A: an acknowledged byte lost. The
 * script (test/stress/power.sh) then starts each image by C and Java and
 * compares.
 *
 * Usage: bergdb-power [-seed N] [-omit file|dir] IMAGES WORKLOAD DIR
 *   -seed N     the seed of the random tear lengths (1)
 *   -omit file  the negative control: after the first acknowledged sync,
 *               file forces are not modelled (the bytes stay volatile);
 *               -omit dir: directory forces are not (new names stay
 *               volatile), as Java's testWeakenedForceOrderingIsDetected
 * Prints the run's text (bergdb-run's) on standard output, and on standard
 * error "power images=N lost=K ..." at the end and a "power LOST" line for
 * each image that lost an acknowledged byte. Exit status: run's; 4 if an
 * image lost an acknowledged byte (without -omit).
 *
 * Built by build.sh in the test build only (the seam is BERGDB_TEST's):
 * tools/run.c compiled with its main renamed run_main and its calls of
 * bergdb_sync and bergdb_close renamed power_sync and power_close, which
 * note the acknowledgements.
 */
#define _DARWIN_C_SOURCE
#include <dirent.h>
#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#include "bergdb.h"
#include "plat.h"

int run_main(int argc, char **argv);
int power_sync(bergdb_db *db, int64_t pos, int level);
int power_close(bergdb_db *db);

#define MAXFILES 4096
#define MAXFD 4096

struct mfile {
    char name[64];
    int64_t index;          /* the name's index: the file starts at index * 100,000 */
    uint8_t *shadow;        /* the bytes written (the real file's) */
    int64_t len, cap;
    uint8_t *forced;        /* the bytes forced */
    int64_t forced_len;
    bool exists;            /* in the real directory */
    bool durable;           /* the name survives a power loss */
    bool pending;           /* deleted since the last directory force */
};

static struct {
    const char *images;
    const char *dir;
    struct mfile files[MAXFILES];
    int nfiles;
    int fdmap[MAXFD];
    int64_t ack;
    int nimages, lost;
    int64_t writes, forces, dirforces, unlinks, torn, dups;
    uint64_t *sigs;
    int nsigs, capsigs;
    bool omit_file, omit_dir;
    uint64_t rnd;
} M;

static void *xalloc(size_t n) {
    void *p = malloc(n == 0 ? 1 : n);
    if (p == NULL) {
        fprintf(stderr, "power: out of memory\n");
        exit(2);
    }
    return p;
}

static uint64_t next_random(void) {
    /* splitmix64 */
    uint64_t z = (M.rnd += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}

/* The model's file of PATH, made if needed; -1 if PATH is not a stream file
 * of the database's directory. */
static int file_of(const char *path, bool make) {
    const char *slash = strrchr(path, '/');
    if (slash == NULL || (size_t) (slash - path) != strlen(M.dir)
            || strncmp(path, M.dir, (size_t) (slash - path)) != 0) {
        return -1;
    }
    const char *name = slash + 1;
    size_t n = strlen(name);
    if (n != 21 || strcmp(name + 14, ".bergdb") != 0) {
        return -1;
    }
    for (int i = 0; i < M.nfiles; i++) {
        if (strcmp(M.files[i].name, name) == 0) {
            return i;
        }
    }
    if (!make || M.nfiles == MAXFILES) {
        return -1;
    }
    struct mfile *f = &M.files[M.nfiles];
    memset(f, 0, sizeof *f);
    memcpy(f->name, name, n + 1);
    f->index = strtoll(name, NULL, 10);
    return M.nfiles++;
}

/* ======== Images ======== */

struct img_file {
    int file;
    int64_t len;            /* the bytes the image holds: forced, or a torn prefix */
    bool torn;              /* from the shadow (unforced bytes) */
};

static int cmp_img(const void *a, const void *b) {
    const struct img_file *x = a, *y = b;
    int64_t ix = M.files[x->file].index, iy = M.files[y->file].index;
    return ix < iy ? -1 : ix > iy;
}

static bool seen_sig(uint64_t h) {
    for (int i = 0; i < M.nsigs; i++) {
        if (M.sigs[i] == h) {
            return true;
        }
    }
    if (M.nsigs == M.capsigs) {
        M.capsigs = M.capsigs == 0 ? 256 : 2 * M.capsigs;
        uint64_t *s2 = realloc(M.sigs, (size_t) M.capsigs * sizeof *s2);
        if (s2 == NULL) {
            fprintf(stderr, "power: out of memory\n");
            exit(2);
        }
        M.sigs = s2;
    }
    M.sigs[M.nsigs++] = h;
    return false;
}

static uint64_t fnv(uint64_t h, int64_t v) {
    for (int i = 0; i < 8; i++) {
        h ^= (uint64_t) (v >> (8 * i)) & 0xff;
        h *= UINT64_C(0x100000001b3);
    }
    return h;
}

/* Writes the image of the durable files, with file 'tear' (or -1) holding
 * 'tear_len' bytes of its shadow, and file 'back' (or -1) back with its
 * forced bytes (a delete rolled back), and the pending deletes but 'keep'
 * back if 'unordered'. */
static void image(const char *event, int tear, int64_t tear_len, int back, bool unordered,
        int keep) {
    static struct img_file in[MAXFILES];
    int n = 0;
    for (int i = 0; i < M.nfiles; i++) {
        struct mfile *f = &M.files[i];
        bool there = f->durable || i == back || (unordered && f->pending && i != keep);
        if (!there) {
            continue;
        }
        in[n].file = i;
        in[n].len = f->forced_len;
        in[n].torn = false;
        if (i == tear) {
            in[n].len = tear_len;
            in[n].torn = true;
        }
        n++;
    }
    qsort(in, (size_t) n, sizeof in[0], cmp_img);
    uint64_t h = UINT64_C(0xcbf29ce484222325);
    for (int i = 0; i < n; i++) {
        h = fnv(h, M.files[in[i].file].index);
        h = fnv(h, in[i].len);
        h = fnv(h, in[i].torn);
    }
    h = fnv(h, M.ack);
    if (seen_sig(h)) {
        M.dups++;
        return;
    }
    /* The contiguous files from the first: their end. */
    int64_t first = n > 0 ? M.files[in[0].file].index * 100000 : 0;
    int64_t end = first;
    for (int i = 0; i < n; i++) {
        int64_t start = M.files[in[i].file].index * 100000;
        if (start != end) {
            break;
        }
        end += in[i].len;
    }
    bool lost = end < M.ack;
    char path[4096];
    snprintf(path, sizeof path, "%s/%06d", M.images, M.nimages);
    if (mkdir(path, 0777) != 0) {
        fprintf(stderr, "power: cannot make %s: %s\n", path, strerror(errno));
        exit(2);
    }
    for (int i = 0; i < n; i++) {
        struct mfile *f = &M.files[in[i].file];
        snprintf(path, sizeof path, "%s/%06d/%s", M.images, M.nimages, f->name);
        FILE *o = fopen(path, "wb");
        const uint8_t *bytes = in[i].torn ? f->shadow : f->forced;
        if (o == NULL || (in[i].len > 0 && fwrite(bytes, 1, (size_t) in[i].len, o)
                != (size_t) in[i].len) || fclose(o) != 0) {
            fprintf(stderr, "power: cannot write %s\n", path);
            exit(2);
        }
    }
    snprintf(path, sizeof path, "%s/%06d/image.txt", M.images, M.nimages);
    FILE *o = fopen(path, "w");
    if (o == NULL) {
        fprintf(stderr, "power: cannot write %s\n", path);
        exit(2);
    }
    fprintf(o, "event=%s ack=%" PRId64 " first=%" PRId64 " end=%" PRId64 " lost=%d\n", event,
            M.ack, first, end, lost ? 1 : 0);
    fclose(o);
    if (lost) {
        M.lost++;
        fprintf(stderr, "power LOST image=%06d event=%s ack=%" PRId64 " first=%" PRId64
                " end=%" PRId64 "\n", M.nimages, event, M.ack, first, end);
    }
    M.nimages++;
}

static void checkpoint(const char *event) {
    image(event, -1, 0, -1, false, -1);
}

/* ======== The seam ======== */

static enum err_code m_open_rw(const char *path, int *fd, struct err *e) {
    enum err_code rc = plat_io_real()->open_rw(path, fd, e);
    if (rc == ERR_OK && *fd >= 0 && *fd < MAXFD) {
        int i = file_of(path, true);
        M.fdmap[*fd] = i;
        if (i >= 0 && !M.files[i].exists) {
            /* A new file, or one that a restart opens again. */
            struct stat st;
            M.files[i].exists = true;
            if (fstat(*fd, &st) == 0 && st.st_size > M.files[i].len) {
                fprintf(stderr, "power: %s has bytes the model did not see\n", path);
                exit(2);
            }
        }
    }
    return rc;
}

static void shadow_write(struct mfile *f, int64_t off, const uint8_t *buf, int64_t n) {
    if (off + n > f->cap) {
        int64_t c2 = f->cap == 0 ? 65536 : f->cap;
        while (c2 < off + n) {
            c2 *= 2;
        }
        uint8_t *s2 = realloc(f->shadow, (size_t) c2);
        if (s2 == NULL) {
            fprintf(stderr, "power: out of memory\n");
            exit(2);
        }
        f->shadow = s2;
        f->cap = c2;
    }
    if (off > f->len) {
        memset(f->shadow + f->len, 0, (size_t) (off - f->len));
    }
    memcpy(f->shadow + off, buf, (size_t) n);
    if (off + n > f->len) {
        f->len = off + n;
    }
}

static enum err_code m_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n,
        struct err *e) {
    int i = fd >= 0 && fd < MAXFD ? M.fdmap[fd] : -1;
    enum err_code rc = plat_io_real()->pwrite(fd, off, buf, n, e);
    if (i < 0 || rc != ERR_OK) {
        return rc;
    }
    struct mfile *f = &M.files[i];
    shadow_write(f, off, buf, n);
    M.writes++;
    checkpoint("after_write");
    /* A power loss may keep a prefix of the unforced tail (Java's
     * partial_write): half of it, and a random length. */
    if (f->durable && f->len - f->forced_len >= 2) {
        int64_t span = f->len - f->forced_len;
        image("torn_half", i, f->forced_len + span / 2, -1, false, -1);
        image("torn_random", i, f->forced_len + 1 + (int64_t) (next_random()
                % (uint64_t) (span - 1)), -1, false, -1);
        M.torn += 2;
    }
    return rc;
}

static enum err_code m_force(int fd, struct err *e) {
    int i = fd >= 0 && fd < MAXFD ? M.fdmap[fd] : -1;
    enum err_code rc = plat_io_real()->force(fd, e);
    if (i < 0 || rc != ERR_OK) {
        return rc;
    }
    struct mfile *f = &M.files[i];
    M.forces++;
    if (!(M.omit_file && M.ack > 0)) {
        free(f->forced);
        f->forced = xalloc((size_t) f->len);
        memcpy(f->forced, f->shadow, (size_t) f->len);
        f->forced_len = f->len;
    }
    checkpoint("after_file_force");
    return rc;
}

static enum err_code m_force_dir(const char *dir, struct err *e) {
    enum err_code rc = plat_io_real()->force_dir(dir, e);
    if (rc != ERR_OK || strcmp(dir, M.dir) != 0) {
        return rc;
    }
    M.dirforces++;
    if (!(M.omit_dir && M.ack > 0)) {
        for (int i = 0; i < M.nfiles; i++) {
            M.files[i].durable = M.files[i].exists;
            M.files[i].pending = false;
        }
    }
    checkpoint("after_dir_force");
    return rc;
}

static enum err_code m_unlink(const char *path, struct err *e) {
    int i = file_of(path, false);
    enum err_code rc = plat_io_real()->unlink(path, e);
    if (i < 0 || rc != ERR_OK) {
        return rc;
    }
    struct mfile *f = &M.files[i];
    bool was = f->durable;
    f->exists = false;
    f->durable = false;         /* the delete survives at once */
    f->pending = was;
    M.unlinks++;
    checkpoint("after_delete");
    if (was) {
        image("unpersisted_delete", -1, 0, i, false, -1);
        image("unordered_delete", -1, 0, -1, true, i);
    }
    /* The bytes stay in the model for those images; the name is gone. */
    return rc;
}

static void m_close(int fd) {
    if (fd >= 0 && fd < MAXFD) {
        M.fdmap[fd] = -1;
    }
    plat_io_real()->close(fd);
}

static const struct plat_io MODEL = {
    m_open_rw, m_pwrite, m_force, m_force_dir, m_unlink, m_close
};

/* ======== The acknowledgements ======== */

int power_sync(bergdb_db *db, int64_t pos, int level) {
    int rc = bergdb_sync(db, pos, level);
    struct bergdb_stats s;
    if (rc == BERGDB_OK && level != BERGDB_SYNC_NONE && bergdb_stats(db, &s) == BERGDB_OK) {
        M.ack = s.durable_length;
        checkpoint("after_sync");
    }
    return rc;
}

int power_close(bergdb_db *db) {
    struct bergdb_stats s;
    int64_t length = -1;
    if (db != NULL && bergdb_stats(db, &s) == BERGDB_OK) {
        length = s.stream_length;
    }
    int rc = bergdb_close(db);
    if (rc == BERGDB_OK && length >= 0) {
        M.ack = length;
        checkpoint("after_sync");
    }
    return rc;
}

int main(int argc, char **argv) {
    int i = 1;
    M.rnd = 1;
    for (; i < argc && argv[i][0] == '-'; i++) {
        if (strcmp(argv[i], "-seed") == 0 && i + 1 < argc) {
            M.rnd = strtoull(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "-omit") == 0 && i + 1 < argc) {
            i++;
            M.omit_file = strcmp(argv[i], "file") == 0;
            M.omit_dir = strcmp(argv[i], "dir") == 0;
            if (!M.omit_file && !M.omit_dir) {
                fprintf(stderr, "power: -omit file|dir\n");
                return 2;
            }
        } else {
            break;
        }
    }
    if (argc - i != 3) {
        fprintf(stderr, "Usage: bergdb-power [-seed N] [-omit file|dir] IMAGES WORKLOAD DIR\n");
        return 2;
    }
    M.images = argv[i];
    M.dir = argv[i + 2];
    for (int k = 0; k < MAXFD; k++) {
        M.fdmap[k] = -1;
    }
    if (mkdir(M.images, 0777) != 0 && errno != EEXIST) {
        fprintf(stderr, "power: cannot make %s\n", M.images);
        return 2;
    }
    plat_io_set(&MODEL);
    char *args[] = { argv[0], argv[i + 1], argv[i + 2], NULL };
    int status = run_main(3, args);
    plat_io_set(NULL);
    fprintf(stderr, "power images=%d lost=%d writes=%" PRId64 " forces=%" PRId64 " dirforces=%"
            PRId64 " unlinks=%" PRId64 " torn=%" PRId64 " dups=%" PRId64 " ack=%" PRId64 "\n",
            M.nimages, M.lost, M.writes, M.forces, M.dirforces, M.unlinks, M.torn, M.dups,
            M.ack);
    for (int k = 0; k < M.nfiles; k++) {
        free(M.files[k].shadow);
        free(M.files[k].forced);
    }
    free(M.sigs);
    if (status == 0 && M.lost > 0 && !M.omit_file && !M.omit_dir) {
        return 4;
    }
    return status;
}
