012-05. Task: the cross harness, Java's side
============================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: not started**; approved with 012-01 by Frans's
go (012-01, 9.1).
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


# 6. Progress

Not started.
