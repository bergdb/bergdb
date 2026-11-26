// efault2 DIR K GAPMS M SEED [EXTLOG]: EfaultProbe's write, with the device's blocks (macOS,
// F_LOG2PHYS_EXT). K files of 8 MiB of 0x5a are written, forced (F_FULLFSYNC), their device extents
// recorded, and deleted; GAPMS ms later, M writes of 8 MiB into new files, each from an anonymous
// mapping of its own byte value whose pages from a random cutoff (a multiple of 16 KiB above 1 MiB)
// on are unmapped, so that the kernel's copy faults there (EFAULT). For each: the write's result,
// the file's length, the bytes within it that the write did not supply (zero, 0x5a, other), the
// allocated bytes, and how many of those bytes lie in device blocks that deleted files held: this
// run's K files and, with EXTLOG, the files of earlier runs (their written ranges; appended to it).
// A helper of bergdb 035-02. Build: cc -O2 -o efault2 efault2.c. 2026-11-26.
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#define SZ (8 << 20)
#define PG 16384
typedef struct { long long dev, len; } ext_t;
static ext_t ex[100000]; static int nex = 0;
static void extents(int fd, long long size, void (*cb)(long long off, long long dev, long long len, void *), void *arg) {
    long long off = 0;
    while (off < size) {
        struct log2phys l = {0}; l.l2p_contigbytes = size - off; l.l2p_devoffset = off;
        if (fcntl(fd, F_LOG2PHYS_EXT, &l) < 0 || l.l2p_contigbytes <= 0) { off += 4096; continue; }
        cb(off, l.l2p_devoffset, l.l2p_contigbytes, arg);
        off += l.l2p_contigbytes;
    }
}
static void rec(long long off, long long dev, long long len, void *arg) { ex[nex].dev = dev; ex[nex].len = len; nex++; }
static long long ov;
static long long lo, hi;
static void cmp(long long off, long long dev, long long len, void *arg) {
    long long a = off > lo ? off : lo, b = off + len < hi ? off + len : hi;
    if (a >= b) return;
    long long d0 = dev + (a - off), d1 = d0 + (b - a);
    for (int i = 0; i < nex; i++) {
        long long x = d0 > ex[i].dev ? d0 : ex[i].dev, y = d1 < ex[i].dev + ex[i].len ? d1 : ex[i].dev + ex[i].len;
        if (y > x) ov += y - x;
    }
}
static FILE *logf;
static void logext(long long off, long long dev, long long len, void *arg) { if (logf) fprintf(logf, "%lld %lld\n", dev, len); }
int main(int argc, char **argv) {
    int k = atoi(argv[2]), gap = atoi(argv[3]), m = atoi(argv[4]); srand(atoi(argv[5]));
    if (argc > 6) {
        FILE *in = fopen(argv[6], "r");
        long long d, l;
        if (in) { while (fscanf(in, "%lld %lld", &d, &l) == 2 && nex < 100000) { ex[nex].dev = d; ex[nex].len = l; nex++; } fclose(in); }
        logf = fopen(argv[6], "a");
    }
    char p[1024];
    char *fill = malloc(SZ); memset(fill, 0x5a, SZ);
    char *rd = malloc(SZ);
    for (int i = 0; i < k; i++) {
        snprintf(p, sizeof p, "%s/old%d", argv[1], i);
        int fd = open(p, O_CREAT | O_TRUNC | O_RDWR, 0644);
        write(fd, fill, SZ); fcntl(fd, F_FULLFSYNC);
        extents(fd, SZ, rec, NULL);
        extents(fd, SZ, logext, NULL);
        close(fd);
    }
    for (int i = 0; i < k; i++) { snprintf(p, sizeof p, "%s/old%d", argv[1], i); unlink(p); }
    usleep(gap * 1000);
    long tot_bad = 0, tot_zero = 0, tot_old = 0, tot_other = 0, tot_ov = 0, files_old = 0;
    for (int j = 0; j < m; j++) {
        long cutoff = (long) (PG * (65 + rand() % (SZ / PG - 66)));
        char *mm = mmap(NULL, SZ, PROT_READ | PROT_WRITE, MAP_ANON | MAP_PRIVATE, -1, 0);
        unsigned char fb8 = (unsigned char) (0x60 + (rand() % 150));    // this file's own byte, never 0 or 0x5a
        memset(mm, fb8, SZ);
        munmap(mm + cutoff, SZ - cutoff);
        snprintf(p, sizeof p, "%s/new%d", argv[1], j);
        int fd = open(p, O_CREAT | O_TRUNC | O_RDWR, 0644);
        ssize_t w = write(fd, mm, SZ);
        struct stat st; fstat(fd, &st);
        long long len = st.st_size;
        fcntl(fd, F_FULLFSYNC);
        pread(fd, rd, len, 0);
        long fb = -1, z = 0, old = 0, other = 0;
        for (long q = 0; q < len; q++) {
            if ((unsigned char) rd[q] == fb8) continue;
            if (fb < 0) fb = q;
            if (rd[q] == 0) z++; else if (rd[q] == 0x5a) old++; else other++;
        }
        ov = 0; lo = 0; hi = len;
        extents(fd, len, cmp, NULL);
        long long ovall = ov;
        ov = 0; lo = fb < 0 ? len : fb; hi = len;
        extents(fd, len, cmp, NULL);
        fstat(fd, &st);
        printf("%d cutoff=%ld write=%zd len=%lld firstbad=%ld zero=%ld old=%ld other=%ld blocks=%lld in_deleted=%lld file_in_deleted=%lld\n",
               j, cutoff, w, len, fb, z, old, other, (long long) st.st_blocks * 512, ov, ovall);
        tot_bad += (fb < 0 ? 0 : len - fb); tot_zero += z; tot_old += old; tot_other += other; tot_ov += ov; files_old += old > 0;
        extents(fd, fb < 0 ? len : fb, logext, NULL);    // only the range that holds this file's bytes
        munmap(mm, cutoff); close(fd); unlink(p);
    }
    printf("total: wrong %ld (zero %ld, old %ld, other %ld), in deleted files' blocks %ld; files with old bytes %ld of %d\n",
           tot_bad, tot_zero, tot_old, tot_other, tot_ov, files_old, m);
    return 0;
}
