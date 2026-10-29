012-14. Task: robustness and scale
==================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: in progress, started 2026-10-29 05:00** (a
first pass, by a subagent of 012's conductor, in the night's last 90
minutes, ended 06:20; its state in 6.9); approved with 012-01 by Frans's
go (012-01, 9.1).
Phase E (012-01, section 8). Effort: high; max to diagnose a failure.
After: 012-13.


# 1. The goal

Confidence beyond the standard sets: many random workloads, crashes and
power loss, corrupt input, long runs and a large database.

Done when:

1. **Random runs by the thousand**: `Gen.java`'s workloads over a wide
   range of parameters (node sizes, startup distances, retain durations,
   value sizes, transaction sizes, restarts, setter calls), Java against
   C: the same files and dumps. A failing seed is kept as a workload in the
   full set once fixed.
2. **Power loss**, through an I/O seam in C as Java's `FileStreamIo`
   (011-07, `PowerLossTest`): writes that were not forced are lost or
   torn at chosen points; C recovers to a state that Java also recovers
   to from the same files, and no committed and synced transaction is
   lost.
3. **Corrupt input**: bit flips, cut and missing files, files with wrong
   names or sizes, garbage meta blocks: C refuses them with an error code
   as Java does, never crashes, never writes into a database it refuses
   (under the sanitizers).
4. **Long runs**: 100,000 transactions and more with restarts, reclaim and
   a small budget, under the sanitizers and `leaks`: no failure, no leak,
   and the directory's size bounded.
5. **Scale**: the 10M-key workload (`cross.sh scale`), at a startup
   distance of 50 MB and of 200 MB: C and Java write the same bytes; C
   starts Java's database and reads it; Java starts C's.
6. **A second compiler**, if cheap: the code builds and the tests pass
   with Homebrew's gcc 16, as a check of portable C.
7. **Allocation failures** (012-01, 4.5), through 012-04's allocator: for
   small workloads, each allocation made to fail in turn, one run each.
   The call gives NOMEM; before the go point the database is as it was,
   and the run goes on to the same bytes as without the failure; after it
   the database has failed (P7); close frees everything, the allocator's
   count is 0, under the sanitizers. A short version runs in the gate.


# 2. Read first

* `java/stress/PowerLossTest.java`, `CrashTest.java`, `DagFuzz.java`,
  `RestartStress.java`, `Soak.java`; 011-07 (durability and the fault
  model); 005-46 (the file stream's reads and the cut).
* The memory notes on F53's timing etiquette (other sessions' timed runs,
  quiet blocks) before the long and the large runs.


# 3. The work

1. The I/O seam in C's platform module, and the power-loss runs.
2. The corrupt-input runs.
3. The random runs, in batches, in the background, outside other
   sessions' timed blocks.
4. The long runs and the large one, the same.
5. The allocation-failure runs (done item 7), and their short version in
   `before-commit.sh`.
6. Each failure: a minimal workload, the cause, the fix (in C), or a 005
   entry (in Java).


# 4. Tests

This task is tests. Its new workloads join the full set when they are
cheap enough, or a `cross.sh night` set if Frans wants one in `night.sh`.


# 5. Notes

* The large runs take minutes and all cores for a while: not while
  another session times anything (012-01, section 9).
* Startup distances of 50 MB or more for large runs, as for Java's
  measurements; small ones are for the small workloads.


# 6. Progress

**2026-10-29 05:00, a first pass** (Claude, Opus 5.5, a subagent of 012's
conductor; in a clone of main at 0c910bc; the conductor runs done item 5,
the scale set, itself). In order of value: done items 1, 6, 4, then 2 and
3 as time allows. Hard stop at 06:30.

## 6.1 Random runs (done item 1)

`test/stress/random.sh FROM TO [BATCH] [JOBS]` runs Gen's seeds in
batches, each batch one run of a new set of cross.sh, `random`
(`SPECFILE=` the export specs, `OUTDIR=` the output directory): the same
runs, files, scans and dumps as the full set, 3 random crash cuts per
workload (for one that reclaims, of C's directory after its last sync,
as in the full set), and C's runs under the budgets 1 and 64000; no
hand-written workloads, corrupt variants or turns. The Java build is
done once by random.sh, so that batches run at once. Each seed gets
parameters wider than Gen's own draws by its number modulo 6 (random.sh's
header): 0 Gen's draws; 1 restarts 5 to 20, setters 3 to 10, reads 3 to
10; 2 reclaim (retain 1 to 3 s, startup distance 100 to 2000, restarts 0
to 10); 3 node size 8, startup distance 100 to 1000, 1,000 to 4,000
transactions; 4 large values (valmax 1,000 to 5,000, huge 5 to 30 per
mille, big 10 to 30 %); 5 deletes 30 to 70 %, long keys 50 to 90 %,
empty 5 to 20 %, 5 to 50 keys. Raw output:
`/Users/f/fl/bench/012/14-out/random/` (summary.txt, a line a batch).

A try, seeds 100001 to 100012: 12 workloads, 21 crash cuts, 24 budget
runs, no difference, 63 s.

**The run** (05:09 to 06:13, batches of 50 seeds, 4 at once, beside the
conductor's runs; C's test build, under the sanitizers): **seeds 100001
to 101800, 1,800 workloads** (300 of each mode), 916 of them with
reclaim, all run by C: **36 batches, every one CROSS random OK, no
difference**: the runs' text, the files (from the decided cut with
reclaim), the four scans and four dumps of each, 2,652 crash cuts
recovered and run on by both, 3,600 runs of C under the budgets 1 and
64,000, and each batch's planted difference found. A batch took 330 to
420 s. No failing seed, so none joins the full set. With the try and
gcc's batch (6.2), 1,845 random workloads tonight.

## 6.2 A second compiler (done item 6)

Homebrew's gcc 16.2.0 (`/opt/homebrew/bin/gcc-16`), on a copy of `c/`
(`/Users/f/fl/bench/012/14-out/gcc/c`, so that the clone's build/ stays
the random runs'), at 0c910bc:

* **`CC=gcc-16 ./build.sh` fails**, on `-Werror`: gcc warns where clang
  does not. Every module, tool, test and example compiled with build.sh's
  warnings at `-O2`, at the test build's `-O1 -g -DBERGDB_TEST`, and at
  `-O3` (`14-out/gcc/warnings.txt`), gives 40 warnings, at 13 places:
  * In the library, 4, none a bug: `starter.c:627` and `rstream.c:351`,
    `-Wmaybe-uninitialized` of `lastSuperNode` and `remaining`, both set
    by the callee on every path that returns `ERR_OK`, the only path that
    reads them; `rstream.c:309`, `-Wstringop-overflow`, in
    `trans_header_fix_bytes` inlined into `rs_plan_recovery`: gcc assumes
    `remaining` may be negative, but it is `rs_trans_pos(length) -
    rs_trans_pos(spos)` with `spos <= length` (else an error), so 1 to 4
    there; `plat.c:55`, `-Wformat-truncation` of a directory entry's name
    (macOS's `d_name` is 1,024 bytes, `plat_entry.name` 256): a name
    longer than 255 bytes is cut, and no such name is a stream file's or
    `bergdb.lock` (a cut name can only be a longer file's, which the
    listing ignores either way).
  * In tests and examples, 9 places of `-Wformat-truncation` (paths and
    lines into fixed buffers by `snprintf`, as meant).
  * Not fixed: none is a portability bug. To build with gcc under
    `-Werror`, initialize the two variables and give the fix's length an
    explicit range, or leave `-Werror` to clang (a question for Frans).
* **Without `-Werror`** (build.sh's copy with it removed), gcc builds
  both builds, its AddressSanitizer and UndefinedBehaviorSanitizer
  included, and every test passes: the unit tests (test build 345 tests,
  9,450,685 checks; release 344), the functional tests (23 tests, 30,443
  checks; both builds, the kill tests of `f_durable.c` included).
* **Cross with gcc's tools**: `cross.sh random` with
  `C=14-out/gcc/c/build/test` (gcc's test build, under its sanitizers) on
  Gen seeds 200001 to 200030 and quick's seeds 3, 4 and 8: 33
  workloads, 66 crash cuts, 66 budget runs, the planted difference found;
  no difference (175 s). gcc's C writes Java's bytes as clang's does.

## 6.3 A leak in bergdb-run (fixed)

The long run's `leaks` (6.8) found 4 leaks of 32 bytes in
`build/release/bergdb-run`, the tool, not the library: the workload's
reader kept the copy of every `set` line (since `fraction` points into
the copy of its own), and freed none. Fixed in `tools/run.c`: the copy
of the line that `fraction` points into is kept in
`workload.fraction_line` and freed at the end; the other `set` lines'
copies are freed at once. The test that fails before it: `leaks --atExit
-- bergdb-run -budget 20000 W DIR` on the long run's workload of 3,000
transactions (4 `set` lines): 4 leaks for 128 bytes before, 0 after;
`test/stress/long.sh` checks it on every long run. The gate's leaks runs
cover the unit and functional tests only, not the tools.

## 6.4 Corrupt input at the start (done item 3, a first part)

`test/stress/corrupt.sh`: four bases (Gen 501: node size 8, startup
distance 100, 2 restarts; 502: large values, 3 restarts, 18 MB in many
files; 503: reclaim, retain 2 s; 504: 1,500 transactions, big ones), run
by Java; 36 variants of each (32 for the base of one file): garbage and
zeroed meta blocks (the first, the last, a middle one), a bit flip in the
last meta block, the last file cut by 1 and by 1,000 bytes, made longer,
emptied, a directory in its place; the first file removed or emptied; a
middle file removed, cut by a byte, made longer; a file renamed past a
gap, to a name of 15 digits, to an odd index; an extra file of garbage
after the end; every file emptied; `bergdb.lock` as garbage, missing, a
directory; and 12 bit flips in the stream's last 400 kB, where a start
reads. Each variant is started by both dumpers (Java's Dump, C's
`bergdb-dump` of the test build, under the sanitizers, `ASAN_OPTIONS=
exitcode=86`). cross.sh's corrupt variants (012-06) scan only; these
start.

Result (126 s): **144 variants; no crash, no sanitizer report.** 91
refused by both, with the same exit status and the same `start
error=NAME`, and C's copy unchanged, every name and byte (Java changed
none of its refused copies either); 37 started by both, with the same
dumps and the same directories after the starts (the recoveries); 16
started by both, then a read failed (checksums of nodes that the start
does not read; a missing first file below the startup position): Java's
text is a prefix of C's and both name the same stream position (C's
`bergdb-dump` prints a getMany's pairs as it walks, Java's `getMany`
returns all or throws, so this is the tools' difference, not the
library's).

**One difference, open (C at fault):** 501 with its first file removed:
Java's start fails with `StreamIoException`, C's with
`ReadBelowFirstPosException` (both refuse; the same position, 143928,
below the first position 200000). Java's `RecoverableStream.read` (and
`readRaw`, and the other reads of that class) wraps every `IOException`
of the file stream in `StreamIoException`; C's `rs_read` (rstream.c)
passes the file stream's error on with its own name. The likely fix:
`rs_read` and its siblings in rstream.c name an `IOException` of the
stream (`ReadBelowFirstPosException`, `EOFException`, `IOException`)
`StreamIoException`, keeping the code, as Java wraps (every read of
`RecoverableStream` does: `readRaw`, `read`, `readMetaBlock`,
`fixMetaBlockIfNeeded`). C names the inner exception on purpose today:
`t_rstream.c` (line 223) checks `EOFException` from `rs_read` past the
end, and `tools/reappend.c` (line 376) tells a torn last record by that
name; both change with the fix (the unit test to `StreamIoException`,
reappend to the code and the text, or a cause name kept in `struct err`).
Then `cross.sh full`, as the crash variants compare start errors by
name. Not made tonight: a choice of how C names wrapped exceptions, for
the conductor or Frans (option A: wrap in rstream.c as Java; option B: a
`cause` in `struct err`, the tools printing the outer name).
Probe: `/Users/f/fl/bench/012/14-out/probes/corrupt-501-first-missing/`
(the workload `501.wl`, the variant's directory `src`, both dumps); or
`test/stress/corrupt.sh`, which reports it.

**Six more bases** (`BASES="601:n=400 602:n=800 603:n=300
604:n=1200,retain=1 605:n=600,maxnode=62 606:n=2000,huge=20"`, Gen's own
draws otherwise; corrupt.sh now takes a stream that reclaim has cut at
its front): 216 variants; no crash; 123 refused by both, C's copies
unchanged; 77 started by both alike; 16 with a later read failing alike.
19 differences: the first-missing one above again (603), and 18 bit flips
with one cause, a Java bug (6.7).

**Eight more bases** (`BASES="701:n=500,maxnode=8,sd=100,retain=1
702:n=1500,maxnode=14,retain=3,restarts=5 703:n=300,maxnode=62,sd=200000
704:n=900,del=60,long=80,keys=30 705:n=2500,maxnode=8,sd=400
706:n=700,valmax=5000,huge=30,big=30 707:n=1200,setters=8,restarts=8
708:n=200,empty=50"`, 171 s): 285 variants; 178 refused by both, 83
started by both alike, 23 with a later read failing alike; 23
differences: **a crash (6.6)**; 10 flips of 6.7's cause; 708 with its
first file removed, 6.4's `StreamIoException`; and 703, a database of
one file, with that file emptied or removed (5 variants): Java's start
makes a new database there (an empty stream), and C's `bergdb-dump`
refuses it (exit 3, "C cannot read this database: an empty stream, which
Java's start creates", 012-09), after its stream's open made an empty
`00000000000000.bergdb` (no corrupt input: the tool does not create
databases).

**Sixteen more bases** (corrupt4: `801:n=300 802:n=600,maxnode=8
803:n=400,maxnode=62,sd=100000 804:n=900,retain=1,sd=500
805:n=250,maxnode=14,sd=300 806:n=1800,restarts=0
807:n=500,maxnode=30,sd=50000 808:n=350,maxnode=62,sd=5000,retain=2`;
corrupt5: `901:n=200,maxnode=62,sd=300000 902:n=450,maxnode=8,sd=200
903:n=700,maxnode=14,retain=1 904:n=320,maxnode=30,sd=100000,del=40
905:n=600,maxnode=62,sd=1000000 906:n=1000,huge=10,maxnode=8
907:n=280,maxnode=62,sd=150000,restarts=4
908:n=380,maxnode=30,sd=250000`): 573 variants; 348 refused by both, 192
started by both alike, 32 with a later read failing alike; **a second
crash (6.6)**; and the classes above only: 27 flips of 6.7's cause, 12
`StreamIoException` names (first or middle file missing), and 904's
one-file database emptied (5).

**In all (with 6.6's header flips): 2,199 starts by both of corrupt
variants (2,055 distinct) of 36 bases; 50 distinct aborts of C, all of
one cause, the record header's unchecked time (6.6); no sanitizer
report otherwise; C wrote into a database that it refused only where
Java wrote the same bytes (6.6, the size field) or into a directory left
without stream files (the tool's empty-stream case); the differences
fall into 4 classes, all open: the names of wrapped exceptions (6.4),
the aborts (6.6), getTrans of corrupt data (6.7), and that case.**

## 6.5 The I/O seam for power loss (done item 2): the design, not made

Java's seam is `FileStreamIo` (open, write, forceFile, openRead,
forceDirectory, delete, rename), replaced in `FileStreamPowerLossTester`
by `ModelIo`: volatile bytes, forced bytes and durable names kept apart;
an *image* (the files a power loss leaves) taken at each event; each
image recovered in a new directory by a new `Db`. C's persistence
boundary is already narrow: `stream.c` calls `plat_open_rw` (2 places),
`plat_pwrite` (1), `plat_force` (1), `plat_force_dir` (2) and
`plat_unlink` (1); reads are `plat_open_read` and `plat_pread`.

1. **What.** `struct plat_io` in plat.h: a function pointer for each of
   those seven calls, and `plat_io_set(const struct plat_io *)`, which
   replaces them for the process (NULL: the real ones). `stream.c` calls
   through it. Compiled in the test build only (`#ifdef BERGDB_TEST`);
   the release build calls `plat_*` directly, so nothing changes there.
   **Who** sets it: a test only (`test/func/f_power.c`, through a test
   header, not bergdb.h). **Checked by** the release build's unit and
   functional tests unchanged, and a unit test that the default seam is
   the plat functions.
2. **The model** (`test/func/powermodel.c`, as `ModelIo`): per file name,
   the volatile bytes and the forced bytes; the durable names (a new
   name is durable after `plat_force_dir`, a deletion may survive without
   it, as Java's model). An image at an event, *when*: before and after
   each write, each force of a file, each force of the directory, each
   unlink; *what*: the forced bytes of each durable name, plus, for the
   chosen torn write, a prefix of its volatile bytes cut at a chosen or
   random length (as `perEvent`). Writes pass through to real files too,
   so the database runs as usual.
3. **The runs.** A workload (Gen's, with syncs and reclaim) run by C
   through the API under the model; at each event, a few images written
   as directories. For each image: C starts it (`bergdb-dump`, the test
   build) and Java starts a copy (`Dump`); checked: the same exit, the
   same dump, the same files after the starts (recovery is byte for byte
   Java's), and every transaction acknowledged by a `sync` before the
   image (the model's acknowledged frontier, from the workload's `sync`
   lines and their statuses) is in the dump's state. Then the other way:
   Java's `PowerLossTest` images (its `Image.restore()` directories,
   exported by a small Java probe) started by C's `bergdb-dump` and
   compared with Java's own recovery of them.
4. **Negative control**, as Java's `testWeakenedForceOrderingIsDetected`:
   a model that drops a `plat_force_dir` after a file's creation must make
   the frontier check fail.
5. **Size.** About 300 lines of C (seam 60, model 200, the test 100) and
   a script beside `corrupt.sh`; a session.

## 6.6 A crash: a record's time not after its predecessor's (open)

**C aborts** (`assert`, exit 134, in the test and the release build)
when it starts 703 (Gen 703 n=300 maxnode=62 sd=200000, one file) with
one bit flipped at stream position 39,123: bit 27 of the time of the
record at 39,112 (653,011 becomes 134,870,739). The record header's
time is under no checksum, so the start reruns that record, and the next
record's time, 653,120, comes before it: `kn_add_klong` (knode.c, line
415) asserts that a key node's times increase. **Java fails too**, not
with a refusal: under `-ea` an `AssertionError` at the same check
(`lastTimeIndex=40, lastTime: 134870739, time=653120`), without it
`bergdb.common.Bug: Bad state of node, arrayTime > transaction time`
(`Dag.appendDeleteKlong`), an Error that escapes `Db.start`. So neither
refuses the database as `StreamFormatException`; Java's process can
catch its Error, C's process dies, the application with it.

**The cause is known: 012-10, 6.4, F1.** Java's
`DbStarter.validateTransactions` has the check ("non-increasing tt",
`StreamFormatException`), but its locals `tpos` and `tt` stay −1, so it
never refuses; C copies it on purpose (starter.c, the comment after the
check: "C does as Java"). F1 showed wrong reads and an `AssertionError`
under `-ea`; this run adds that **in C the same input aborts the process**
(release build included), from one flipped bit. The fix is F1's, Java
first (a 005 entry: update `tpos` and `tt` in the loop; then 703/flip-3
is refused with `StreamFormatException` before the rerun), and C's
starter.c the same two lines; until then C keeps Java's behaviour, which
for C is an abort. Not made tonight (Java is not this task's; the choice
of C refusing before Java does is the conductor's or Frans's). **A
prototype** of C's half, in a copy (`14-out/f1proto/c`; the diff is
`f1-fix-prototype.diff` beside the probe): the probe is then refused,
`start error=StreamFormatException` ("non-increasing tt, tpos=39392,
tt=653028"), exit 1, no abort; the unit tests (345) and the functional
tests (23) pass; not run: the cross sets. **Probe**:
`/Users/f/fl/bench/012/14-out/probes/crash-703-flip-3/` (`db/` the
flipped directory, `703.wl`, `scan.txt`; C: `bergdb-dump -maxnode 62 COPY
scan.txt`; Java: `java [-ea] -cp build/java/classes bergdb.cross.Dump
-maxnode 62 COPY scan.txt`; the four outputs kept). corrupt.sh finds it
with the eight bases above (`BASES=...`, variant `703/flip-3`).

**A second crash, the same family**: 902 (n=450, node size 8, startup
distance 200) with bit 59 of the time of the record at 640,280 flipped
(876,977 becomes more than 2^59): C aborts at `kl_create_time` (klong.c,
line 8: `time <= KL_MAX_TIME`, 2^56 − 1), Java under `-ea` asserts at
`Klong.createTime`, in the rerun (`DbStarter.rerunTransaction`). With
the F1 prototype, C refuses it (`non-increasing tt` at the next record,
640,512). But a record's time over 2^56 − 1 at the end of the section
has no next record to betray it: the full fix also refuses a record
time above the klong's maximum (and below the previous one), in Java's
`validateTransactions` and C's. Probe:
`/Users/f/fl/bench/012/14-out/probes/crash-902-flip-8/` (`db/`,
`902.wl`, `scan.txt`, both dumps' errors; `-maxnode 8`).

**Every byte of the record header, flipped** (corrupt.sh `HEADERS=4`:
one bit in each of the 32 header bytes of the last 4 committed records;
bases 501, 703, 902, 905 and two new, 1001 `n=400,retain=1,sd=1000`,
1002 `n=800,maxnode=14,sd=50000`; 981 variants with the usual ones, 381
s): **50 aborts of C, all from a flip in the time field** (header bytes 8
to 15), at four assertions: `kl_create_time` (a time over 2^56 − 1),
`kn_add_klong` (times not increasing), `dag_put_kv` ("Found no root
node", a time before the startup root's) and `append_delete_klong`
(`arrayTime > tTime`); Java asserts at the same places under `-ea`. **With
the prototype** (F1's two lines and a check that a record's time is at
most `KL_MAX_TIME`; 28 lines of diff in
`probes/crash-703-flip-3/f1-fix-prototype.diff`): all 50 refused,
`StreamFormatException`, exit 1, no abort, and the unit and functional
tests pass (`f1res.txt` without the maximum check: 44 of 50 refused, the
6 others the last record's byte 15; `f1res2.txt` with it: 50 of 50). So
the whole family is the unchecked record time, and F1's fix with the
maximum closes it, in Java and in C.

The other differences of that run: 41 refused starts named
`StreamIoException` by Java and `EOFException` by C (6.4's naming,
another inner exception); 6 getTrans of 6.7's cause; 1 getTrans where
Java throws `ArrayIndexOutOfBoundsException` (1001/flip-7: the parse
outside Java's `try` again, and an exception that is not even an SFE)
where C fails the database; and **10 starts that both refuse after
writing**: a flip in the size field (header bytes 0 and 1) makes the last
record look torn and longer, the recovery fills it with zeros, about 1
MB of new files, and the start then refuses (`Bad lastByte`). Java and
C write the same bytes (5 of 5 compared), so C keeps Java's behaviour;
005-40 (done) made a start refused for its meta blocks write nothing (it
reads before it writes); a start refused after the recovery's zero fill
of a record whose size is corrupt is a case it did not cover: a Java
finding for a 005 entry, which would decide how the recovery tells a
torn record from a corrupt size before it fills. Probe:
`probes/refused-start-writes/` (`db/`, 501 with byte 0 of the record at
1,057,744 flipped; `501.wl`, `scan.txt`).

## 6.7 getTrans of a record with a bad checksum: a Java bug (open)

The 18 flips of 6.4's six more bases: a record whose node fails its
checksum. Java's `Db.getTrans` throws `StreamChecksumException` and the
database stays active (the next getTrans reads on); C's fails the database
(`DbFailedException`, then every later read too), as 005-34 says
("corrupt data, as for the other reads") and as 03-c-api.md's error
table says (`BERGDB_FORMAT`: after the open, corrupt data fails the
database). The cause is in Java: `getTrans` maps `StreamIoException` and
`StreamFormatException` to `failOnStorage` around `ti.next()` only;
`ti.getStoredTrans()` (`StoredTrans.parse`, which checks each node's
checksum, `NodeStream.checkChecksum`) is outside that `try`, so its
`StreamChecksumException` (an SFE) escapes as it is. C's `sdb_get_trans`
and the API's `bergdb_get_trans` parse inside (`st_parse`, then
`fail_on_storage`). The same holds for any SFE of the parse.

**Probe**: `/Users/f/fl/bench/012/14-out/probes/gettrans-checksum/`
(`src/GetTransChecksumProbe.java`, against `build/java/classes`; `db/`, a
copy of Gen 601 with one bit flipped at stream position 714,948, in the
record at 714,416):

    javac -cp CLASSES -d classes src/GetTransChecksumProbe.java
    cp -R db run && java -ea -cp CLASSES:classes GetTransChecksumProbe run 714416 717096
    getTrans 714416: StreamChecksumException
    getTrans 717096: tt=151882: the database was not failed

**Not changed in C**: keeping Java's behaviour here would break 005-34
and C's documented API (and `f_api.c`'s and `f_settings.c`'s tests of a
getTrans inside a record, which fail in Java too, at `ti.next()`). The
recommendation: a 005 entry, the parse moved into Java's `try` (one
line), after which the two agree; the alternative, C copying Java until
then, is the conductor's or Frans's call.

## 6.8 Long runs (done item 4)

`test/stress/long.sh SEED N [BUDGET] [GENPARAMS]`: Gen's workload of N
transactions run at once by C's test build (sanitizers, the allocator's
checks, `-budget`, `-mem`), C's release build under `leaks --atExit`
(`-budget`), and Java's Run; checked: exit 0, C's text is Java's (both
builds), the stream from reclaim's decided cut and the other files are
Java's (both builds), 0 leaks, and the directory's size (sampled every 2
s in the test build's run). C's builds: the clone's at 0c910bc with 6.3's
fix of bergdb-run (`14-out/cfix/c/build`).

| Seed | Transactions | Shape | C's budget | Stream written | C's directory, most / end | Java's | Time |
|---|---|---|---|---|---|---|---|
| 1 | 100,000 | node 30, sd 50,000, retain 1 s, 20 restarts, 6 setters | 20,000 | 165 MB | 20 MB / 14.5 MB | 12.6 / 12.6 MB | 17 s |
| 3 | 200,000 | node 8, sd 1,000, retain 2 s, 30 restarts, 8 setters, 10 reads | 1 | 552 MB | 83 MB / 7.5 MB | 29 / 7.5 MB | 113 s |
| 2 | 1,000,000 | node 30, sd 50,000, retain 1 s, 50 restarts, 10 setters | 4,000 | 2.49 GB | 213 MB / 35 MB | 36.5 / 34.6 MB | 480 s |

Each run was made twice, the second time with Java's directory sampled
too (`long.sh` since then); the C figures of the second are within 4 %
of the first's (C's most 20.0, 82.1 and 206 MB).

All three: **LONG RUN OK**: Java's text and files byte for byte in both
C builds, 0 leaks (after 6.3's fix), no sanitizer report. The library's
memory stays flat: the allocator's live bytes 11 to 16 MB at every
segment's end of the million-transaction run, its peak 37 MB (the test
build's RSS 1.4 GB is AddressSanitizer's). **The directory is bounded,
by the syncs**: its most, sampled, is 1.4 to 11 times its size at the end,
since C frees a decided cut's disk at the next sync or open only (012-11,
6.4 Q1, a question for Frans); Gen's workloads sync only at some restarts and
at the end, 20,000 transactions apart in the million run. With C forcing
when a cut is pending (Q1's recommendation), the most would be near the
end's size, as Java's is: Java's directory, sampled the same way, stays
within 1.0 to 3.9 times its end (C's: 1.4 to 11), and at most 36.5 MB in
the million run where C's reaches 206 to 213 MB. The figures support
Q1's recommendation.

**An observation, open** (not a byte difference): in seed 3's run
(budget 1, reclaim at a startup distance of 1,000), `-mem`'s `maxOver`,
the most resident bytes over the budget plus the pinned after a line, is
up to 20,063 bytes in 23 of 31 segments; 012-12 found it 0 in all its
runs. Reproduced on 20,000 transactions of the same parameters (Gen 3
n=20000 retain=2 restarts=30 sd=1000 maxnode=8 huge=0 setters=8 reads=10,
`-budget 1`): after 25 `t` lines, 23 of them in a row (lines 2,889 to
2,911 of 20,000, over growing from 1,704 to 3,366 bytes), then 0 again;
with setters=0 (another draw), none. Likely reclaim's reads after the
execute's eviction (which runs before reclaim's `transactionCompleted`,
as Java's; 012-12, 6.1, point 4); but the excess grows over 23
transactions, so each execute's eviction did not take the previous
one's either. **The excess is evictable**: with `RUN_OVER_EVICT`, the
probe calls `bergdb_set_cache_size_indicator` with the budget in force
right after the first line over (it evicts at its end, and resets the
trigger's floor to the budget): resident 66,123 bytes, pinned 64,418,
over 1,704 before; resident 52,112, pinned 57,872, over −5,761 after; the
run's text unchanged, and only one more line over in the whole run. So it
looks like a lag of the trigger (the floor, `pinnedOfLastRound + (high -
low)`, kept while reclaim's loads accumulate), a third of the kind 012-12
fixed two of, not memory that cannot go; for 012-12's mechanism to look
at, with Java's controller beside it. Probe: `14-out/probes/maxover/`
(the workload `w3.wl`; `run.c` with a `RUN_OVER` print of each line
over and the `RUN_OVER_EVICT` eviction; its binaries `run-over`,
`run-over2`; their outputs `w3.err`, `w3e.err`).

**The gate** on the clone's tree at the end (tools/run.c's fix, the new
scripts, cross.sh's random set): **C BEFORE COMMIT OK (144 s)**: 345
unit tests, 23 functional, the quick set (22 workloads, 93 crash cuts,
85 corrupt variants, 2 in turns, 44 budget runs), writecheck, the
examples.

## 6.9 The state at the first pass's end, and what is left

Done items, as this pass leaves them:

1. **Random runs**: running (6.1); a set that a later session extends by
   seeds (`random.sh FROM TO`); no failing seed, so none joined the full
   set. Left: more seeds in quiet hours; turns and corrupt variants are
   not in the random set.
2. **Power loss**: the seam's design only (6.5). Left: all of it.
3. **Corrupt input**: `corrupt.sh` (6.4, 6.6); C never crashed under the
   sanitizers but in one family, the unchecked record time, which F1's fix
   (012-10, 6.4) with a maximum closes (prototype, not in src). Left:
   decide and make that fix (Java first or both), the naming of wrapped
   exceptions (6.4), getTrans of corrupt data (6.7), the refused start
   that writes (6.6, Java); then a short corrupt run in the gate.
4. **Long runs**: done at 100,000, 200,000 and 1,000,000 transactions
   (6.8). Left: the directory's bound, which waits on 012-11's Q1; the
   `maxOver` lag (6.8) for 012-12's mechanism.
5. **Scale**: the conductor's.
6. **gcc**: builds and passes without `-Werror`; four false warnings in
   the library (6.2). Left: Frans's choice on `-Werror` under gcc.
7. **Allocation failures**: not started (the unit test
   `evict_alloc_failures` exists since 012-12).

Scripts, all in `c/test/stress/` (and cross.sh's random set):
`random.sh`, `long.sh`, `corrupt.sh`. Raw output and probes:
`/Users/f/fl/bench/012/14-out/` (`random/`, `long*/`, `corrupt*/`,
`gcc/`, `probes/`).
