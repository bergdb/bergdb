/*
 * Prints the bytes a process has read from and written to the device, from macOS's
 * proc_pid_rusage (ri_diskio_bytesread, ri_diskio_byteswritten), for ScaleBench (bergdb
 * item 004, 004-02; after 005-14's procstat.c). Usage: pidio PID
 * Build: cc -O2 -o pidio pidio.c
 */
#include <libproc.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: pidio PID\n");
        return 2;
    }
    int pid = atoi(argv[1]);
    struct rusage_info_v4 ri;
    if (proc_pid_rusage(pid, RUSAGE_INFO_V4, (rusage_info_t *) &ri) != 0) {
        printf("error\n");
        return 1;
    }
    printf("%llu %llu\n", ri.ri_diskio_bytesread, ri.ri_diskio_byteswritten);
    return 0;
}
