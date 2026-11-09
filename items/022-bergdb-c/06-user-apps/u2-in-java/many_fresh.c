/* bergdb 022-06 (f2): one transaction of N new keys of 16 random bytes (3 segments, the
 * first distinct and new), in memory: the execute's time. Usage: many_fresh N */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "bergdb.h"
static double now(void) { struct timespec a; clock_gettime(CLOCK_MONOTONIC, &a); return a.tv_sec + a.tv_nsec / 1e9; }
int main(int argc, char **argv) {
    int n = atoi(argv[1]);
    bergdb_db *db;
    if (bergdb_open(NULL, NULL, &db, NULL, NULL) != BERGDB_OK) return 2;
    bergdb_trans *t;
    bergdb_trans_new(db, &t);
    srand(5);
    for (int i = 0; i < n; i++) {
        uint8_t k[16];
        for (int j = 0; j < 16; j++) k[j] = (uint8_t) rand();
        k[0] = 0x10;
        bergdb_trans_put(t, k, 16, (const uint8_t *) "v", 1);
    }
    double a = now();
    int rc = bergdb_execute(db, t, NULL);
    printf("one transaction of %d new keys of 16 bytes: %s in %.3f s\n", n, bergdb_errname(rc), now() - a);
    bergdb_trans_free(t);
    bergdb_close(db);
    return 0;
}
