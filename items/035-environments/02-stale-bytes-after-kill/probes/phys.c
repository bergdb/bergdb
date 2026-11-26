// phys FILE: prints the file's extents on its device, one line each: the offset in the file, the
// offset on the device and the length, by fcntl(F_LOG2PHYS_EXT) (macOS). An optional helper of
// StaleBytesProbe (bergdb 035-02), its option phys=PATH. Build: cc -O2 -o phys phys.c. 2026-11-26.
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
int main(int argc, char **argv) {
    int fd = open(argv[1], O_RDONLY);
    if (fd < 0) { perror("open"); return 1; }
    struct stat st; fstat(fd, &st);
    off_t off = 0;
    while (off < st.st_size) {
        struct log2phys l = {0};
        l.l2p_contigbytes = st.st_size - off;
        l.l2p_devoffset = off;
        if (fcntl(fd, F_LOG2PHYS_EXT, &l) < 0) { printf("%lld hole-or-error\n", (long long) off); off += 4096; continue; }
        printf("%lld %lld %lld\n", (long long) off, (long long) l.l2p_devoffset, (long long) l.l2p_contigbytes);
        if (l.l2p_contigbytes <= 0) break;
        off += l.l2p_contigbytes;
    }
    return 0;
}
