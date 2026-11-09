/* bergdb 022-06 (f2): the 16 keys of u1's long_key_memory.c (srand(3), rand()) into a
 * file, for U1_2.java. Usage: keys16 FILE */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    size_t n = 1u << 20;
    unsigned char *k = malloc(n);
    FILE *f = fopen(argv[1], "wb");
    srand(3);
    for (int i = 0; i < 16; i++) {
        for (size_t j = 0; j < n; j++) k[j] = (unsigned char) rand();
        fwrite(k, 1, n, f);
    }
    fclose(f);
    return 0;
}
