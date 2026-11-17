012-05. Task: the cross harness, Java's side
============================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: in progress, started 2026-10-28 13:58**;
approved with 012-01 by Frans's go (012-01, 9.1).
Phase A (012-01, section 8). Effort: high. After: 012-02's `StreamScan`
(its step 2).


# 1. The goal

Everything the cross tests (012-01, 6.4) need on Java's side, and the
scripts that compare: a workload format that both runners read, Java's
runner and dumper, the workloads, and `cross.sh`. Until C has a runner, the
scripts compare Java with Java, which checks the harness and P2 across JVM
runs.

Done when:

1. The workload format is written in this file, with an example of each
   line.
2. `Run.java` runs a workload on a directory, and `Dump.java` dumps a
   database, both through `Db`'s public API only, plus `StreamScan`
   (012-02).
3. The workloads exist: `StreamDigest`'s twelve configurations in its
   three modes, `CoreSame`'s, and a generator of random workloads from a
   seed and parameters.
4. `cross.sh quick`, `full` and `scale` run Java on every workload of the
   set, twice in two JVMs, and compare: the same files and bytes (from
   reclaim's decided cut), the same dumps, the same scans. All pass.
5. The scripts take the C side as an option (`C=path-to-tools`), so that
   012-06 onwards only add C's runner, dumper and scanner.
6. The crash variants and the runs in turns (below) are in the scripts,
   Java with Java for now.


# 2. Read first

* 012-01, sections 3.2 and 6.4.
* `java/stress/StreamDigest.java` (its configurations, its workload
  generator draw for draw, its modes, and why it compares from the decided
  cut), `RestartInvariance.java`, `CrashTest.java`, 006-08's
  `CoreSame.java`.
* `DbBuilder` (`testSetupExceptStream`, `id`, `clock`), `TestClock`,
  `CoreTestClock`, `FileStream`.


# 3. The work

1. **The workload format**, a UTF-8 text, one item a line, `#` comments:

       bergdb-workload 1
       set maxnode 30          # 8, 14, 30 or 62
       set sd 100              # the startup distance
       set retain forever      # or a number of time units
       set fraction 0.25       # reclaim's internal fraction
       set budget 64000        # the cache budget; does not change the bytes
       clock 500               # the test clock, read by the creation
       t 1000 p /k/1 s:v1 p /k/2 x:00ff d /k/3
       t 1010 p /big z:300000  p /r r:7:5000
       now                     # currentTime(), printed
       t - p /k/4 s:v4         # at the clock's time as it is
       sync
       restart
       setsd 400000
       check 1005              # reads at time 1005 into the dump
       check latest

   A transaction line gives its time and its operations: `p KEY VALUE`, a
   put, and `d KEY`, a delete. Time is the test clock's (012-01, 4.4):
   `t T` sets it to T, which must be later than its time, as
   `CoreTestClock.setTime` requires, and then executes; `t -` executes at
   the clock's time as it is, so that `DbClock` gives the transaction a
   later one; `clock T` sets the clock alone; `now` calls `currentTime()`
   and prints it, which can move the next transaction's time. The
   creation reads the clock too, when the first segment starts: at 0 if
   no `clock` line comes first, which gives the primordial transaction
   the time 1. Keys are ikeys, converted as `Keys.toBytes(String)` (an
   escape such as `%20` for spaces and odd bytes). Values: `s:` text,
   `x:` hex, `z:N` N zero bytes, `r:SEED:N` N bytes from a generator
   written down here (xorshift64*, so that both runners make the same
   bytes without large files). The settings come before the first
   transaction; `setsd`, `setretain`, `setfraction` and `setbudget` are
   the setters of `Db`. The database id is the test id
   (`DatabaseId.TEST_ID`). A read set may come later, as `t ... rs TIME
   KEY...`, if a task needs refused transactions in the cross set.
2. **`Run.java`**: the test clock (`CoreTestClock`), set as the clock
   lines say and kept across restarts; one start of `Db` per segment
   between `restart` lines; it prints, per transaction, the time and the
   positions (`tt`, `tpos`, `lastPos`), the `now` times, and the `check`
   reads. Options to run only some segments, for the runs in turns.
3. **`Dump.java`**: starts a database (on a copy, as a start may write the
   torn record's fill) and prints a canonical text: the status (stream
   length, first available position and time), the latest state through
   `getMany` forward and backward, `getOne` of sampled keys at sampled
   times, and `getTrans` of every transaction from the first available
   position, found with the scanner's positions. Values as length and
   SHA-256.
4. **The exporters**: `StreamDigest`'s configurations through its own
   class (same package, its constructor's lists of keys, values and
   times), with `restart` lines for its third mode and `check` lines for
   its second; `CoreSame`'s draws; and `Gen.java`, random workloads from
   a seed: the number of transactions and keys, value sizes, the share of
   deletes, big transactions, long keys (more than one segment), empty
   transactions, node sizes 8 to 62, startup distances from 100 bytes to
   1 MB, retain durations, restarts, and calls of the setters.
5. **`cross.sh`**: compiles the Core Layer and the harness into
   `build/java/`; for each workload, runs side A and side B (Java and
   Java now; Java and C later), each in a directory of its own, and
   compares:
   * the files: names, sizes and bytes; with reclaim, from the decided
     cut, as `StreamDigest` does (012-01, 3.2, point 8);
   * `Run`'s output (times and positions), the dumps and the scans;
   * on a difference: the first differing position, and the scanner's
     lines of both sides around it.
6. **Crash variants**: copies of a finished directory cut at chosen
   positions (inside a record's header, its body, its last byte, a meta
   block, a file's end) and at random ones; both sides dump them (which
   recovers them), and then run more transactions on them; the files and
   dumps compared.
7. **Runs in turns**: a workload's segments run alternately by side A and
   side B on one directory, compared with a run of A alone and of B alone.
8. **The sets.** `quick` (a minute or so: small configurations, a few
   seeds, a few crash cuts), `full` (all configurations at full size, a
   few hundred seeds, a thousand crash cuts, turns), `scale` (10M keys).


# 4. Tests

The harness tests itself: Java against Java must pass every comparison,
and a difference planted on purpose (one byte flipped in a copy) must be
found and explained.


# 5. Notes

* Only `Db`'s public API in the runner and the dumper; the scanner reaches
  the parsers. So they keep working while Java's internals change.
* Java reads some settings from system properties (`stepreserve`, `evict`,
  `evictbudget`, `evictseed`, `audit`; see `DbBuilder`, `Eviction` and
  `Audit`). The runner leaves them unset,
  so that Java runs with its defaults, but for the audit when a check
  wants it (it changes no byte). `stepreserve` changes reclaim's records.
* Build outputs and the reference directories go under `build/`, never
  into the repository; the vector files of 012-04 are the exception.
* The JVMs of the cross tests must not run during another session's timed
  block (012-01, section 9).


# 6. The formats and the harness, as built

The definitions that C's tools follow (012-06 to 012-09). Java's classes
are in `c/test/cross/java/`; their headers point here. A change of a
format is a new version number and a line in Progress.

## 6.1 The workload, "bergdb-workload 1"

A UTF-8 text, one item a line. Words are separated by spaces or tabs; a
word that starts with `#` ends the line (a comment), so a `#` inside a
key or a value is written `%23`. Blank lines are allowed. The first
line that is not blank is the header:

    bergdb-workload 1
    # comments and blank lines anywhere
    set maxnode 8           # 8, 14, 30 or 62; 30 if not set
    set sd 100              # the startup distance (DbBuilder.startupDistance)
    set retain 50000000     # the retain duration in time units, or "forever"
    set fraction 0.25       # reclaim's internal fraction
    set budget 64000        # the cache budget (cacheSizeIndicator); none: no eviction
    clock 500               # the test clock, read by the creation
    t 1000 p /k/1 s:v1 p /k/2 x:00ff d /k/3
    t 1010 p /big z:300000 p /r r:7:5000
    now                     # currentTime(), printed
    t - p /k/4 s:v4         # at the clock's time as it is
    sync
    restart
    setsd 400000
    setretain forever
    setfraction 0.1
    setbudget 1000000
    check 1005              # the whole state at time 1005, as a digest
    check latest
    get latest /k/1 /k/2 /big
    get 1005 /k/1

`c/test/cross/workloads/example.wl` has every kind of line, with
escapes, an empty transaction, a delete and a put of one key in one
transaction, and an empty segment; cross.sh runs it in quick and full.

* **Settings.** `set NAME VALUE` lines come before every other line but
  `clock`. They apply at every start of the database (the creation and
  each restart): `maxnode`, `sd`, `budget` and `retain` through the
  builder, `fraction` through `setReclaimInternalFraction` right after
  the start. Every start also has the test setup (`testSetupExceptStream`:
  no eviction unless `budget`, retain forever unless `retain`, the test
  id `DatabaseId.TEST_ID`) and the runner's test clock.
* **Segments.** `restart` lines split the workload into segments, 0, 1,
  2 and on. The database starts at the first line of a segment that is
  not `clock` (so `clock` lines before it set the time that the creation
  reads), or at the end of the segment if it has no such line. A segment
  ends at its `restart` line, or at the end of the workload: the runner
  then prints the segment's end and closes the database (`Db.close`,
  which writes and forces everything).
* **The clock** is `CoreTestClock`'s: it starts at 0, is set only by
  `clock T` and `t T`, each T later than its time (else the workload is
  bad), and is kept across restarts: a runner that starts at segment k
  sets it to the last time that the lines of segments 0 to k-1 set.
* **`t T OPS`** sets the clock to T, then executes a transaction of the
  operations, in order: `p KEY VALUE`, a put, and `d KEY`, a delete
  (`Trans.Builder.put` and `delete`, so a later operation on the same key
  replaces an earlier one, but a delete does not replace a put; Java's
  `Trans.Builder.build`). **`t - OPS`** executes at the clock's time as it
  is, so that `DbClock` gives the transaction a later time. No operations:
  an empty transaction. Java writes no value node for a delete of a key
  that has no value (the first test's `d /k/3`).
* **`now`** calls `currentTime()` and prints it; it can move the next
  transaction's time (012-01, 4.4).
* **`sync`** is `sync(SyncLevel.STRONG)`, and prints the status.
* **Setters**: `setsd N` is `setStartupDistance(N)` (clamped by Java to at
  least 400,000, and a 200 kB dummy transaction unless N is the value in
  force); `setretain N|forever` is `setRetainDuration`; `setfraction F` is
  `setReclaimInternalFraction` (F parsed as Java's `Double.parseDouble`,
  C's `strtod`: decimal text gives the same double); `setbudget N` is
  `setCacheSizeIndicator`. A setter lasts until the next start, where the
  settings apply again.
* **`check T|latest`**: `getMany` forward from the first key, no stop
  condition, at time T (`latest` is `Long.MAX_VALUE`); the runner prints
  its digest (6.2).
* **`get T|latest KEY...`**: `getOne` of each key at time T; the results
  go into the segment's digest of reads (6.2).
* **Keys** are ikeys. A key word is the ikey's UTF-8 bytes, where `%XX`
  (two hex digits) is the byte XX; the bytes must be valid UTF-8 and not
  empty. The bkey is `Keys.toBytes(String)` of it: `/` becomes 1, every
  other byte b becomes b + 2.
* **Values**: `s:TEXT`, the bytes of TEXT with `%XX` escapes (`s:` is the
  empty value); `x:HEX`, bytes in hex (even length, may be empty); `z:N`,
  N zero bytes; `r:SEED:N`, N bytes of xorshift64*: SEED a decimal from 0
  to 2^64 − 1, the state x = SEED, or 0x9E3779B97F4A7C15 if SEED is 0;
  for each 8 bytes, `x ^= x >>> 12; x ^= x << 25; x ^= x >>> 27;` and the
  word `x * 0x2545F4914F6CDD1D` (64-bit, wrapping) gives 8 bytes, least
  significant first; the last word is cut to what N needs.
* **Not yet**: read sets (`t ... rs TIME KEY...`), for refused
  transactions, when a task needs them.

## 6.2 Run's output, "bergdb-run 1"

`Run [-v] [-segments A[-B]] [-audit N] WORKLOAD DIR` (C: `bergdb-run`,
the same arguments but `-audit`). One line per item; numbers decimal:

    bergdb-run 1
    segment i=S                          a segment begins
    start create=0|1 startPos=P startupDistance=D startTime=T transCount=N lastPos=P
                                         Db.start()'s StartInfo; create=1 if DIR had no
                                         .bergdb file
    start error=NAME                     the start threw (NAME: Java's exception class);
                                         the run ends with exit status 1
    trans i=I tt=T tpos=P lastPos=P      a t line executed: I counts the workload's t
                                         lines from 0; Trans.tt, tpos and lastPos
    refused trans i=I cmd=t error=NAME   a t line, or another line ("refused line=L
    refused line=L cmd=C error=NAME      cmd=C"), threw; exit status 1 at the end
    now time=T
    check at=T|latest actual=A count=N sha256=H
                                         a check: GetMany.actualLookupTime, the number of
                                         pairs, and SHA-256 of their kv lines (below), each
                                         followed by a newline
    check at=T unavailable               LookupTimeNotAvailableException
    reads n=N sha256=H                   at a segment's end, if it had gets: SHA-256 of
                                         the get lines (below), each followed by a newline
    status length=L firstAvailablePos=P firstAvailableTime=T startupDistance=D
                                         at sync and at a segment's end: getStreamLength,
                                         getFirstAvailablePos, getFirstAvailableLookupTime,
                                         getStartupDistance
    end segment=S                        the segment ended; the database is closed

    kv key=K len=L sha256=H time=T pos=P a pair of a getMany: the key's text (below), the
                                         value's length and SHA-256, Kvt.time (the key node
                                         entry's time) and Kvt.spos (the value node's
                                         position)
    get at=T|latest key=K len=L sha256=H time=T tpos=P
    get at=T|latest key=K none           a get: the value, GetData.kvTime and tpos; none for
    get at=T|latest key=K unavailable    null; unavailable for LookupTimeNotAvailableException

With `-v` the kv lines of checks and the get lines are printed too,
indented by two spaces. **The text of a key** (`K`): for each bkey byte
b, `/` if b is 1; else c = b − 2 (mod 256), printed as the character c
if it is 0x21 to 0x7e but `%`, `/`, `=` and `#`, else as `%XX` (upper-case
hex). One text per bkey. Exit status: 0; 1 if anything was refused or a
start failed; 2 for a bad workload or usage.

## 6.3 Dump's output, "bergdb-dump 1"

`Dump [-maxnode N] [-audit N] [-large] DIR SCAN` (C: `bergdb-dump`, the
same arguments but `-audit`). It starts the database in DIR (with the
node size N, 30 by default; a test clock at 0; nothing written but what
the start writes, so cross.sh gives it a copy) and prints:

    bergdb-dump 1
    start startPos=P startupDistance=D startTime=T transCount=N lastPos=P
    start error=NAME                     the start threw; nothing more, exit status 1
    status length=L firstAvailablePos=P firstAvailableTime=T startupDistance=D
    kv ...                               the latest state, forward (none with -large)
    latest count=N sha256=H              its digest
    backward count=N sha256=H            the digest of the kv lines of the latest state
                                         read backward (forward=false, no start key)
    state at=T|latest actual=A count=N sha256=H
    state at=T unavailable               the whole state at each sampled time
    range at=T|latest start=K incl=0|1 fwd=0|1 stop=S count=N
      kv ...                             a getMany from start key K; S is get5 (GetN(5)),
                                         "to=K2 endIncl=1|0" (Endpoint), or prefix10
                                         (PrefixN(K, 10))
    range ... unavailable
    one at=T|latest key=K len=L sha256=H time=T tpos=P
    one at=T|latest key=K none|unavailable
                                         getOne of each sampled key at each sampled time
    trans pos=P tt=T lastPos=P startupPos=P topPos=P values=N
      value key=K len=L sha256=H         getTrans of each committed record of the scan at
      delete key=K                       or after firstAvailablePos: StoredTrans's fields
                                         and its value and delete nodes, in record order
    trans pos=P unavailable|error=NAME
    end

**The samples** come from SCAN, a "streamscan 1" text (side A's scan of
side A's directory, the same file for every dumper):

* *Keys*: the `key=` field of every `value` and `delete` line, distinct,
  sorted by their bytes (unsigned; a prefix first); at most 48: when
  there are more (n), those at index ⌊i·n/48⌋ for i = 0 to 47.
* *Times*: the `time=` of each committed `record` line (one with a
  `time=` field) at a position at or after firstAvailablePos, in stream
  order; at most 12 by the same rule. For each, t − 1 and then t; then
  latest (`Long.MAX_VALUE`); then firstAvailableTime − 1 if
  firstAvailableTime > 0; a time already in the list is not added again.
* *States*: one `state` line per time of the list; with `-large`, only
  at latest and at M (below), in that order.
* *Ranges*: the range keys are at most 12 of the sampled keys, by the
  same rule. For T in (latest, M), M being the list's time at index
  ⌊size/2⌋ if the list has more than 2 times, else latest: for each range
  key k: for each start s in (k, k followed by the byte 0x23): for incl
  in (1, 0): for fwd in (1, 0): a `get5` range. Then, if the first of
  these ranges (s = k, inclusive, forward) has 2 pairs or more, k2 being
  its last key: a range from k forward, inclusive, to k2 inclusive
  (`Endpoint(k2, true)`), and one from k2 backward, inclusive, to k
  exclusive (`Endpoint(k, false, true)`). Then a range from p forward,
  inclusive, with `PrefixN(p, 10)` (a pair with the prefix p ends the
  range when it is the tenth), p being the first ⌈len/2⌉ bytes of k. Every
  range has at most 10 pairs, also in a large database.
* *Records*: with `-large`, at most 1,000 of the record positions, by the
  same rule.
* *Gets*: for each sampled key, for each time of the list, a `one` line.

Exit status: 0; 1 if the start failed; 2 on bad usage.

## 6.4 The scan

`StreamScan PATH` (C: `bergdb-scan PATH`), 012-02's "streamscan 1"
(StreamScan's header). Exit status 0, or 1 if it printed an `error` line.

## 6.5 cross.sh

As `cross.sh` is at 012-11's end (`main` at `e068fba`); brought up to
date by 012-13 (2026-10-29) from 09-write-path.md, 6.9 and 11-reclaim.md,
6.5. 012-12 adds runs of side B with memory budgets (its own file says
which).

`test/cross/cross.sh quick|full|scale [C=DIR] [SCALE=N] [KEEP=1]`, from
any directory. It builds Java (`java-build.sh`), exports the set's
workloads (`Export.java`: `sd:NAME:MODE[:n=N]`, `coresame[:n=N][:plain]`,
`gen:SEED[:K=V,...]`, `scale:KEYS`), copies the hand-written ones of
`test/cross/workloads/` (both sets) and of `test/cross/workloads/full/`
(the full set only) into `build/cross/SET/wl/`, and then:

0. The script is one compound command (`{ ... }`), which `sh` reads
   whole before it runs, so that an edit of the file does not change a
   run in progress. Every JVM gets `JAVA_OPTS`, by default `-Xmx2g`
   (scale: `-Xmx12g`), to stay small beside other sessions' runs.
1. **Runs**: side A and side B run each workload into
   `build/cross/SET/{a,b}/W/db`, at the same time.
2. **The decided cut**: the `firstAvailablePos` of side A's last `status`
   line. Each side's *view* holds its stream's bytes from a common
   position at or before the cut, cut at side A's file boundaries
   (`split_view`), and its other files (`bergdb.lock`), so that two
   directories whose reclaim cut their front files at different moments
   compare. In scale, the view is the stream's bytes from the meta block
   2 MB or less before its end, so that the scans stay small: a stream of
   gigabytes is compared byte for byte, and scanned only at its end.
3. **Scans**: each view by both scanners; **dumps**: a copy (`cp -R`) of
   each directory by both dumpers, sampled with side A's scan of side A.
   With `C=`, Java's dumps of side B's directories run Java's audit
   (`-audit 1`; C to Java, 012-01, section 1).
4. **Compare**, per workload: both runs exit 0 and print the same text;
   the files: for a workload without reclaim, the same names, sizes and
   bytes; for one that reclaims (`compare_db`, `compare_stream`), the
   stream's bytes from the decided cut and the other files, as each run
   makes its physical cut at its own moments (a cut is made when the
   decision's bytes are durable: 012-01, 3.2, point 8; 005-72, option A);
   the four scans equal; the four dumps equal; the dumped copies' files
   equal (again from the cut); for StreamDigest's workloads, the SHA-256
   of side A's stream from the cut equals StreamDigest's own `sha256` for
   the same run (Export writes it beside the workload, `W.digest`), which
   checks the export draw for draw. On a difference: the first differing
   stream position, and both sides' scan lines around it.
5. **Crash variants**: copies of a finished directory cut at chosen
   positions (for records spread over the stream: 3 and 17 bytes in, the
   middle, without its last byte, whole; meta blocks: 1 before, at, 1,
   127, 128 and 129 after; the first file's end is a meta block's
   position) and random ones (awk's `rand`, seeded per workload). For a
   workload without reclaim, copies of side A's directory. For one that
   reclaims, only with `C=`: copies of side B's (C's) directory, cut at or
   after the stream's length at its last sync, since C's stream is
   durable after a sync only, so every physical cut it made had its
   decision durable by then and such a copy is a crash (Java's directory
   makes its cuts at its own moments, and a copy of it cut earlier might
   not be). Side A scans each cut copy; each side dumps its own copy
   (which recovers it), then runs the workload's *after-workload* on it
   (its settings, a `restart`, 20 transactions a million time units after
   its last time, `check latest`, `sync`; `-segments 1`). Compared: the
   exit statuses, the dumps, the runs, the files (from the decided cut).
6. **Corrupt variants** (012-06): copies of a few workloads' directories
   with bits flipped, files cut short or removed; both scanners scan each:
   a stream that Java refuses, C refuses at the same place, and C's
   scanner never crashes.
7. **Runs in turns**: segment k of a workload is run by side A if k is
   even, by side B if odd (each in a process of its own), all on one
   directory; the outputs, joined, equal side A's whole run, and the files
   equal both sides' (from the decided cut).
8. **A planted difference**: a copy of side B's directory of the first
   workload with one byte changed, 20 bytes into the first value node
   1,000 bytes or more after the cut; the comparison must report that
   position, and the report shows both scans around it.
9. The last line: `CROSS SET OK: ...` (exit 0) or `CROSS SET FAILED: ...`
   (exit 1). The directories of a passed run are deleted unless `KEEP=1`;
   `build/cross/SET/report.txt` keeps the report.

**The C side** (`C=DIR`): side B uses `DIR/bergdb-run`, `bergdb-dump` and
`bergdb-scan` where they exist and are executable, Java's tools
otherwise. Each is called once per job, with the job's arguments, its
standard output to the job's output file. Since 012-11 C has all three:
`bergdb-scan` (012-06), `bergdb-dump` by the bounded startup with
reclaim's table and cut (012-08, 012-10, 012-11), `bergdb-run` with
restarts and reclaim (012-09 to 012-11), so every run, dump and scan of
side B is C's; `c_runs` answers 1 for every workload and is kept as the
place to send a kind of workload to Java (its outputs then listed in
`java-only.txt` and counted in the report). Java runs a side's jobs in one
JVM (`Batch.java`: "run|dump|scan OUT ARGS" a line; `OUT.exit` holds each
job's exit status). `test/cross/java-tools/` holds the three tools as
wrappers of Java's classes, one JVM a job, which checks the plumbing of
`C=` without C. The C gate runs `cross.sh quick C=build/test KEEP=1`, then
`writecheck.sh` on its Java directories (012-09, part 1: C's take and
append path replayed on Java's records).

**The sets** (at `e068fba`):

| Set | Workloads | Crash cuts | Corrupt | Turns |
|---|---|---|---|---|
| quick | StreamDigest's `l2-sd100` (restarts, 300 transactions), `l2-sd1000-node8` (reads, 300), `l3-node14` (restarts and plain, 600), `l2-idle-1` (plain, 200), `l3-every1` (reads, 400); CoreSame (1,500, and plain); Gen seeds 1 to 4 (3 with a retain of 2 s, 4 with node size 8, startup distance 100, 3 restarts, no reclaim), 5 and 6 without restarts and reclaim (6 with node size 8, startup distance 100), 7 and 8 without restarts with a retain of 1 s (8 with node size 8, startup distance 100); the hand-written `example.wl`, `clock.wl`, `nowmoves.wl`, `sdcut.wl`, `reclaim-sync.wl`, `reclaim-crash.wl` | 3 workloads (`reclaim-crash` among them); per workload 4 records and 4 meta blocks cut as in point 5, and 3 random cuts | 2 workloads, 40 flips | 2 (`gen-4-...`, `sd-l3-node14-restarts-n600`) |
| full | StreamDigest's twelve configurations at full size, three modes each; CoreSame (6,000, and plain); Gen seeds 1 to 200; 201 to 240 with node size 8, startup distance 100 and no reclaim; 241 to 280 without restarts and reclaim; 281 to 300 the same with node size 8 and startup distance 100; 301 to 340 without restarts (random retain durations, forever in about 6 of 10); 341 to 380 without restarts with a retain of 2 s; 381 to 400 the same with 1 s, node size 8 and startup distance 100; quick's hand-written workloads and `full/sdcut-large.wl`, `full/reclaim-sync-large.wl` | 9 workloads (`reclaim-crash` among them); per workload 15 records and 15 meta blocks, and 25 random cuts | 6 workloads, 80 flips | 6 |
| scale | `Export scale:SCALE` (10M keys by default): transactions of 100 consecutive keys `/k/i` with 40-byte values, node size 30, startup distance 50 MB, a restart halfway, then a pass that deletes or puts every 97th key, a check and gets; dumps with `-large` | none | none | none |

012-11's last `cross.sh full C=build/test` (in its clone): 446 workloads,
181 of them with reclaim, all run by C; 1,368 crash cuts, 498 corrupt
variants, 6 in turns; no difference; 1,751 s.


# 7. Progress

**Clone:** `/Users/f/fl/bench/012/05-cross-harness/`, a clone of `bergdb`
at `b439af9`. **Java reference:** `main` at `b439af9` (`java/` as of
`decc677`).

2026-10-28 13:58. Started: the plans and the Java classes read.

2026-10-28 14:20. **Built** (commits `89f1218` to `643f6fb` in the
clone), all in `c/test/cross/`:

* `java/Workload.java` (package `bergdb.cross`): the parser of 6.1, the
  keys, the values, xorshift64*, the text of a key.
* `java/Run.java` and `java/Dump.java` (package `bergdb.cross`, so that
  the compiler holds them to public API: `Db`, `DbBuilder`,
  `CoreTestClock`, `FileStream`, `Trans.Builder`, `GetData`, `GetMany`,
  `Kvt`, `StoredTrans`, `StartInfo`, `Keys`): 6.2 and 6.3.
* `java/Batch.java` (package `bergdb.core`): many jobs in one JVM, and
  StreamScan through its package-level API (its constructor, `run`,
  `View.open`; an error line means status 1), without changing it; each
  job's time in the batch's log.
* `java/Export.java` (package `bergdb.core`, for StreamDigest's
  package-private lists): StreamDigest's configurations in their three
  modes, draw for draw, with StreamDigest's own digest of the same run
  beside each; CoreSame's draws; Gen's; the scale workload.
* `java/Gen.java`: random workloads from a seed (every parameter of the
  plan's step 4, each drawn when not given).
* `workloads/example.wl`: every kind of line, by hand.
* `java-tools/`: Java's classes as side-B tools, for `C=` (6.5).
* `cross.sh`: 6.5. `java-build.sh` now compiles
  `java/stress/StreamDigest.java` too (still `build/java/classes` and
  `JAVA BUILD OK`).

**Checks.** The exported StreamDigest workloads give StreamDigest's own
stream: `l2-sd100` (300 transactions) in all three modes has
StreamDigest's SHA-256, `7cacf1b6...`; cross.sh checks it for every
StreamDigest workload, and all 36 of full matched. The planted
difference (one byte changed, 20 bytes into a value node) is reported at
its position, with side A's scan line (the value node, `sumOk=true`) and
the planted copy's (`sumOk=false`, a bad key size). Results:

| When | Run | Result line |
|---|---|---|
| 14:23 | `cross.sh quick` | `CROSS quick OK: 10 workloads, 64 crash cuts, 1 in turns, the planted difference at 1164 was found and explained; side B: Java; 30 s` |
| 14:20 | `cross.sh scale SCALE=100000` | `CROSS scale OK: 1 workloads, 0 crash cuts, 0 in turns; side B: Java; 10 s` |
| 14:22 to 14:51 | `cross.sh full` (1st) | `CROSS full OK: 278 workloads, 1262 crash cuts, 6 in turns, the planted difference at 1164 was found and explained; side B: Java; 1700 s` |
| 14:51 | `cross.sh quick`, after the speed-up (`0366ed0`) | `CROSS quick OK: ...; 19 s` |
| 14:52 | `cross.sh quick C=test/cross/java-tools` | `CROSS quick OK: ...; side B: .../java-tools; 52 s` (one JVM a job; Java's dumps of side B with `-audit 1`) |
| 14:53 to 15:06 | `cross.sh full` (2nd, after the speed-up) | `CROSS full OK: 278 workloads, 1262 crash cuts, 6 in turns, the planted difference at 1164 was found and explained; side B: Java; 790 s` |

The first full run spent 830 s of its 1700 on the shell's comparisons
(a subprocess or five per file listed); `0366ed0` lists a directory with
one `ls`, compares two directories with one `diff -rq` before the
file-by-file walk, which now runs only on a difference, and takes the
first differing byte from `cmp`; quick went from 30 to 19 s.

**Findings in Java**: none. P2 held across JVM runs for every workload of
full, every crash cut (recovery, dumps, and the transactions after it)
and the runs in turns.

**Notes for C** (Java's behaviour, not bugs): a delete of a key that has
no value writes no value node (example.wl's `d /k/3`); `GetData.kvTime`
and `Kvt.time` are the key node entry's time (a time split's time after
a split), which the dumps compare, so C's Dag must split at the same
times; `StartInfo.startupDistance` is -1 after every start; a cut copy
whose cut is inside a record leaves the start to write the torn record's
zero fill (a dump's length beyond the cut).

**Caveat**: two runs of cross.sh (or of `java-build.sh`) in one C
directory at once break each other: both use `build/java/classes` and
`build/cross/SET/`. The gate and a hand run must take turns.

The second full run's time, by phase: export 33 s; runs 145 s (each
side's batch 143 s of jobs); scans and dumps 193 s (scans 77 s and dumps
66 s a side); compare 59 s; crash variants 332 s (side A's scans of the
cuts 100 s, dumps 91 s a side, runs after 38 s a side); turns 20 s; 790 s
in all, within the plan's 10 to 20 minutes.

2026-10-28 15:07. Stopped at the conductor's request (the usage window):
no new work started. **"Done when"**: items 1 to 6 hold, with scale run
only at 100,000 keys (its 10M-key run belongs to 012-14, in a quiet
window). **Next** (on resume): the report to the conductor; open points
for later: crash variants of reclaiming workloads (a `kill -9` of a run
rather than a cut, as a cut before reclaim's durable bytes is no crash),
and read sets in the workload format when a task needs refused
transactions.
