The tools (bergdb 012-01, 6.3), one `.c` file each, built by `build.sh` into `build/*/bergdb-NAME`:

* `bergdb-scan PATH` (012-06, `scan.c`): Java's `StreamScan`, "streamscan 1".
* `bergdb-dump [-maxnode N] [-large] [-replay] [-check] DIR SCAN` (012-08, 012-10, `dump.c`): Java's `Dump`, "bergdb-dump 1", the database opened by the bounded startup (`-replay`: by a full replay of the stream); `bergdb-dump -probe [-maxnode N] [-check] DIR`: one line of what a start rebuilt and read (012-10).
* `bergdb-run [-v] [-segments A[-B]] WORKLOAD DIR` (012-09, 012-10, `run.c`): Java's `Run`, "bergdb-run 1", through `include/bergdb.h` only, restarts included; exit status 3, nothing written, for a workload that C cannot run yet (reclaim, 012-11).
* `bergdb-takecheck DIR...`, `bergdb-reappend [-buffer N] [-run RUN.txt] SRC DST`, `bergdb-clockcheck WORKLOAD DIR RUN.txt` (012-09, part 1; `takecheck.c`, `reappend.c`, `clockcheck.c`): the take, the append path and the clock replayed on Java's directories (`test/cross/writecheck.sh`).
