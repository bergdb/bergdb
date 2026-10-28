/*
 * bergdb-reappend: re-appends the records of a stream that Java wrote
 * through C's append path, and compares the directory that C writes with
 * Java's, file by file and byte by byte (bergdb 012-09, part 1). It checks
 * what lies below the index: RecoverableStream's framing and its meta
 * blocks (written where the records reach them, with their fields as Java
 * sets them), FileStream's files (names, capacities, the open rule at a
 * restart, 012-02, 9.3, C1), the lock file, the write buffer and the
 * forces. The records' own bytes are Java's (the serializer is 012-09
 * proper's), taken with C's parser (012-06).
 *
 * The in-memory meta block is set as Java sets it:
 *
 *   - at the creation, a new block (rs_init) given the database id, the
 *     startup distance, the node size and the time of Java's block at 0,
 *     as Db.writePrimordialTransaction sets them;
 *   - after each record, lastTrans its position (rs_append_record, as
 *     NodeStream.appendNodes);
 *   - at a record of setStartupDistance's dummy transaction (a value node
 *     of /#i/-dummy), the startup distance that Java's block inside it
 *     holds, as setStartupDistance sets it before the dummy (the only
 *     input taken from Java's blocks after the creation);
 *   - at a restart (-run: the stream's length at each segment's end, from
 *     Run's output, "status length=L" before "end segment=S"), the stream
 *     is synced and closed, opened again by C's open rule, the block a copy
 *     of C's last valid block (rs_use_last_valid_meta_block) and lastTrans
 *     the last record (Db.getStartupPosFromLastTransaction).
 *
 * A stream that reclaim cut at the front (its first file is not at 0) is
 * skipped, and one with a failed record (recovery's fill, 012-10's) or a
 * torn one (a crash cut).
 *
 * Usage: bergdb-reappend [-buffer N] [-run RUN.txt] SRC DST
 *   SRC  Java's database directory, read only
 *   DST  a directory that does not exist or holds no .bergdb file
 *   -buffer N  the write buffer's size (default 10,000,000, Java's)
 * Prints "reappend SRC records=R restarts=K files=F bytes=B equal", or the
 * first difference. Exit status: 0 equal; 1 a difference or an error; 2 bad
 * usage; 3 skipped (a cut or a failed record).
 */
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bytes.h"
#include "keys.h"
#include "mem.h"
#include "meta.h"
#include "nstream.h"
#include "plat.h"
#include "rstream.h"
#include "snode.h"
#include "stream.h"
#include "strans.h"

#define MAX_RESTARTS 100000

static struct mem mem;
static struct err err;
static int64_t restarts[MAX_RESTARTS];
static int32_t nrestarts;

static int fail(const char *src, const char *what) {
    printf("reappend %s DIFFERENCE %s\n", src, what);
    return 1;
}

/* The lengths at the segments' ends, from Run's output. */
static bool read_run(const char *path) {
    char line[4096];
    int64_t last = -1;
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        return false;
    }
    while (fgets(line, sizeof line, f) != NULL) {
        if (strncmp(line, "status length=", 14) == 0) {
            last = strtoll(line + 14, NULL, 10);
        } else if (strncmp(line, "end segment=", 12) == 0 && last >= 0
                && nrestarts < MAX_RESTARTS) {
            restarts[nrestarts++] = last;
        }
    }
    fclose(f);
    return true;
}

/* Whether the record holds a value node of the dummy key, /#i/-dummy
 * (DbConstants.DUMMY_KEY). */
static bool has_dummy(const struct st_record *r) {
    static const char ikey[] = "/#i/-dummy";
    uint8_t bkey[sizeof ikey];
    int64_t seg[4];
    const int32_t n = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, n, bkey);
    const int32_t ns = keys_segment_count(n);
    keys_to_segments(bkey, n, seg);
    /* setStartupDistance's dummy transaction puts one value: a record of
     * one value node of the dummy key (reclaim's steps rewrite the dummy's
     * value too, among others). */
    int32_t values = 0;
    for (int32_t i = 0; i < r->nnodes; i++) {
        values += r->nodes[i].type == NODE_VALUE || r->nodes[i].type == NODE_DELETE;
    }
    if (values != 1) {
        return false;
    }
    for (int32_t i = 0; i < r->nnodes; i++) {
        const struct sn_node *x = &r->nodes[i];
        if (x->type != NODE_VALUE || x->key_n != ns) {
            continue;
        }
        bool same = true;
        for (int32_t k = 0; k < ns && same; k++) {
            same = sn_seg(x, k) == seg[k];
        }
        if (same) {
            return true;
        }
    }
    return false;
}

/* The startup distance of SRC's last valid block at or before pos. */
static bool sd_before(struct stream *src, int64_t pos, int32_t *sd) {
    for (int64_t m = pos / META_BLOCK_DISTANCE * META_BLOCK_DISTANCE; m >= 0;
            m -= META_BLOCK_DISTANCE) {
        struct meta mb;
        if (rs_read_meta_block(src, m, &mb, &err) != ERR_OK) {
            return false;
        }
        if (meta_is_valid(&mb)) {
            *sd = meta_startup_distance(&mb);
            return true;
        }
    }
    return false;
}

/* Compares the two directories: the .bergdb files' names, sizes and bytes,
 * and bergdb.lock's bytes. */
static int compare_dirs(const char *a, const char *b, int64_t *nfiles, int64_t *nbytes) {
    struct plat_entry *ea = NULL, *eb = NULL;
    int32_t na = 0, nb = 0;
    char pa[4096], pb[4096], what[8192];
    static uint8_t ba[1 << 16], bb[1 << 16];
    int status = 0;

    if (plat_list_dir(a, &mem, &ea, &na, &err) != ERR_OK
            || plat_list_dir(b, &mem, &eb, &nb, &err) != ERR_OK) {
        printf("reappend %s error listing: %s\n", a, err.text);
        plat_free_entries(&mem, ea, na);
        return 1;
    }
    int32_t i = 0, k = 0;
    while (status == 0 && (i < na || k < nb)) {
        const char *x = i < na ? ea[i].name : NULL;
        const char *y = k < nb ? eb[k].name : NULL;
        bool xs = x != NULL && (strstr(x, ".bergdb") != NULL || strcmp(x, "bergdb.lock") == 0);
        bool ys = y != NULL && (strstr(y, ".bergdb") != NULL || strcmp(y, "bergdb.lock") == 0);
        if (x != NULL && !xs) {
            i++;
            continue;
        }
        if (y != NULL && !ys) {
            k++;
            continue;
        }
        if (x == NULL || y == NULL || strcmp(x, y) != 0) {
            snprintf(what, sizeof what, "files: Java's %s, C's %s", x ? x : "(none)",
                    y ? y : "(none)");
            status = fail(a, what);
            break;
        }
        if (ea[i].size != eb[k].size) {
            snprintf(what, sizeof what, "file %s: Java's %lld bytes, C's %lld", x,
                    (long long) ea[i].size, (long long) eb[k].size);
            status = fail(a, what);
            break;
        }
        snprintf(pa, sizeof pa, "%s/%s", a, x);
        snprintf(pb, sizeof pb, "%s/%s", b, y);
        FILE *fa = fopen(pa, "rb");
        FILE *fb = fopen(pb, "rb");
        int64_t off = 0;
        if (fa == NULL || fb == NULL) {
            status = fail(a, "cannot open a file");
        }
        while (status == 0) {
            size_t ra = fread(ba, 1, sizeof ba, fa);
            size_t rb = fread(bb, 1, sizeof bb, fb);
            if (ra != rb) {
                status = fail(a, "a short read");
                break;
            }
            if (ra == 0) {
                break;
            }
            if (memcmp(ba, bb, ra) != 0) {
                size_t j = 0;
                while (ba[j] == bb[j]) {
                    j++;
                }
                snprintf(what, sizeof what, "file %s at %lld: Java's byte %d, C's %d", x,
                        (long long) (off + (int64_t) j), ba[j], bb[j]);
                status = fail(a, what);
                break;
            }
            off += (int64_t) ra;
            *nbytes += (int64_t) ra;
        }
        if (fa != NULL) {
            fclose(fa);
        }
        if (fb != NULL) {
            fclose(fb);
        }
        (*nfiles)++;
        i++;
        k++;
    }
    plat_free_entries(&mem, ea, na);
    plat_free_entries(&mem, eb, nb);
    return status;
}

/* A restart: synced and closed, opened again, the block a copy of the last
 * valid one and lastTrans the last record. */
static bool restart(struct stream *dst, struct rs *r, const char *dir, int32_t buffer,
        int64_t lastTpos) {
    if (stream_finish(dst, &err) != ERR_OK) {
        return false;
    }
    if (stream_open_dir_rw(dst, dir, buffer, &mem, &err) != ERR_OK) {
        return false;
    }
    rs_init(r, dst);
    if (rs_use_last_valid_meta_block(r, &err) != ERR_OK) {
        return false;
    }
    meta_set_last_trans(&r->meta, lastTpos);
    return true;
}

int main(int argc, char **argv) {
    const char *run = NULL;
    int32_t buffer = 0;
    int i = 1;
    for (; i < argc && argv[i][0] == '-'; i++) {
        if (strcmp(argv[i], "-run") == 0 && i + 1 < argc) {
            run = argv[++i];
        } else if (strcmp(argv[i], "-buffer") == 0 && i + 1 < argc) {
            buffer = (int32_t) strtol(argv[++i], NULL, 10);
        } else {
            break;
        }
    }
    if (argc - i != 2) {
        fprintf(stderr, "Usage: bergdb-reappend [-buffer N] [-run RUN.txt] SRC DST\n");
        return 2;
    }
    const char *srcdir = argv[i];
    const char *dstdir = argv[i + 1];
    mem_init(&mem);
    err_clear(&err);
    if (run != NULL && !read_run(run)) {
        fprintf(stderr, "bergdb-reappend: cannot read %s\n", run);
        return 2;
    }

    struct stream src, dst;
    struct rs r;
    struct ns_iter it;
    struct st_record rec;
    bool has;
    int status = 0;
    int64_t records = 0, done_restarts = 0, lastTpos = -1;
    int32_t next_restart = 0;

    if (stream_open_dir(&src, srcdir, &mem, &err) != ERR_OK) {
        printf("reappend %s error: %s: %s\n", srcdir, err.java, err.text);
        return 1;
    }
    if (stream_first_pos(&src) != 0 || stream_length(&src) < META_BLOCK_SIZE) {
        if (stream_first_pos(&src) != 0) {
            printf("reappend %s skipped: the stream begins at %lld (a cut)\n", srcdir,
                    (long long) stream_first_pos(&src));
        } else {
            printf("reappend %s skipped: %lld bytes, no whole meta block (an incomplete "
                    "creation)\n", srcdir, (long long) stream_length(&src));
        }
        stream_close(&src);
        return 3;
    }
    struct meta block0;
    if (rs_read_meta_block(&src, 0, &block0, &err) != ERR_OK) {
        printf("reappend %s error: %s\n", srcdir, err.text);
        stream_close(&src);
        return 1;
    }
    if (stream_open_dir_rw(&dst, dstdir, buffer, &mem, &err) != ERR_OK) {
        printf("reappend %s error opening %s: %s: %s\n", srcdir, dstdir, err.java, err.text);
        stream_close(&src);
        return 1;
    }
    if (stream_length(&dst) != 0) {
        printf("reappend %s error: %s is not empty\n", srcdir, dstdir);
        stream_close(&dst);
        stream_close(&src);
        return 1;
    }
    /* The creation (Db.writePrimordialTransaction). */
    rs_init(&r, &dst);
    meta_set_id(&r.meta, meta_id(&block0));
    meta_set_startup_distance(&r.meta, meta_startup_distance(&block0));
    meta_set_max_node_size(&r.meta, meta_max_node_size(&block0));
    meta_set_time(&r.meta, meta_time(&block0));

    st_init(&rec);
    ns_iter_init(&it, &src, &mem, 0, false);
    enum err_code rc;
    while ((rc = ns_iter_next(&it, &has, &err)) == ERR_OK && has) {
        char what[512];
        while (next_restart < nrestarts && restarts[next_restart] <= stream_length(&dst)) {
            if (restarts[next_restart] != stream_length(&dst)) {
                snprintf(what, sizeof what, "a restart at %lld, C's stream is %lld long",
                        (long long) restarts[next_restart], (long long) stream_length(&dst));
                status = fail(srcdir, what);
                goto end;
            }
            if (!restart(&dst, &r, dstdir, buffer, lastTpos)) {
                printf("reappend %s error at a restart: %s: %s\n", srcdir, err.java, err.text);
                status = 1;
                goto end;
            }
            next_restart++;
            done_restarts++;
        }
        int64_t expect = rs_next_spos(stream_length(&dst));
        if (it.tpos != expect) {
            if (it.tpos > expect) {
                printf("reappend %s skipped: a failed record before %lld (recovery's fill)\n",
                        srcdir, (long long) it.tpos);
                status = 3;
            } else {
                snprintf(what, sizeof what, "record %lld, C's stream is at %lld",
                        (long long) it.tpos, (long long) expect);
                status = fail(srcdir, what);
            }
            goto end;
        }
        if (st_parse(&rec, it.tpos, it.buf.p, it.size, &mem, &err) != ERR_OK) {
            printf("reappend %s error: record %lld: %s\n", srcdir, (long long) it.tpos,
                    err.text);
            status = 1;
            goto end;
        }
        if (has_dummy(&rec)) {
            int32_t sd;
            if (sd_before(&src, rec.last_pos, &sd)) {
                meta_set_startup_distance(&r.meta, sd);
            }
        }
        int64_t tpos;
        if (rs_append_record(&r, it.buf.p, it.size, &tpos, &err) != ERR_OK) {
            printf("reappend %s error: record %lld: %s: %s\n", srcdir, (long long) it.tpos,
                    err.java, err.text);
            status = 1;
            goto end;
        }
        lastTpos = tpos;
        records++;
    }
    if (rc != ERR_OK) {
        if (strcmp(err.java, "EOFException") == 0) {
            printf("reappend %s skipped: a torn last record (a crash cut; recovery is "
                    "012-10's): %s\n", srcdir, err.text);
            status = 3;
        } else {
            printf("reappend %s error: the walk: %s: %s\n", srcdir, err.java, err.text);
            status = 1;
        }
        goto end;
    }
    if (stream_length(&dst) < stream_length(&src)) {
        /* A failed record at the end: recovery's fill. */
        printf("reappend %s skipped: bytes after the last committed record, from %lld "
                "(recovery's fill, 012-10's)\n", srcdir, (long long) stream_length(&dst));
        status = 3;
        goto end;
    }
    /* The restarts at the end (an empty segment, the last close). */
    while (next_restart < nrestarts) {
        if (restarts[next_restart] != stream_length(&dst)) {
            char what[512];
            snprintf(what, sizeof what, "a restart at %lld, C's stream is %lld long",
                    (long long) restarts[next_restart], (long long) stream_length(&dst));
            status = fail(srcdir, what);
            goto end;
        }
        if (!restart(&dst, &r, dstdir, buffer, lastTpos)) {
            printf("reappend %s error at a restart: %s: %s\n", srcdir, err.java, err.text);
            status = 1;
            goto end;
        }
        next_restart++;
        done_restarts++;
    }

end:
    ns_iter_free(&it);
    st_free(&rec, &mem);
    if (stream_finish(&dst, &err) != ERR_OK && status == 0) {
        printf("reappend %s error at the close: %s\n", srcdir, err.text);
        status = 1;
    }
    stream_close(&src);
    if (status == 0) {
        int64_t nfiles = 0, nbytes = 0;
        status = compare_dirs(srcdir, dstdir, &nfiles, &nbytes);
        if (status == 0) {
            printf("reappend %s records=%lld restarts=%lld files=%lld bytes=%lld equal\n",
                    srcdir, (long long) records, (long long) done_restarts, (long long) nfiles,
                    (long long) nbytes);
        }
    }
    if (mem.live_total != 0) {
        printf("reappend %s error: %lld bytes live at the end\n", srcdir,
                (long long) mem.live_total);
        status = 1;
    }
    return status;
}
