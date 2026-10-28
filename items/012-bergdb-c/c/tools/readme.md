The tools (bergdb 012-01, 6.3), one `.c` file each, built by `build.sh` into `build/*/bergdb-NAME`:

* `bergdb-scan PATH` (012-06, `scan.c`): Java's `StreamScan`, "streamscan 1".
* `bergdb-dump [-maxnode N] [-large] DIR SCAN` (012-08, `dump.c`): Java's `Dump`, "bergdb-dump 1", by a full replay of the stream.
* `bergdb-run [-v] [-segments A[-B]] WORKLOAD DIR` (012-09, `run.c`): Java's `Run`, "bergdb-run 1", through `include/bergdb.h` only; exit status 3, nothing written, for a workload that C cannot run yet (a start of an existing database, 012-10; reclaim, 012-11).
* `bergdb-takecheck DIR...`, `bergdb-reappend [-buffer N] [-run RUN.txt] SRC DST`, `bergdb-clockcheck WORKLOAD DIR RUN.txt` (012-09, part 1; `takecheck.c`, `reappend.c`, `clockcheck.c`): the take, the append path and the clock replayed on Java's directories (`test/cross/writecheck.sh`).
