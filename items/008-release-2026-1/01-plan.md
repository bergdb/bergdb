008-01. Plan: release 2026.1
============================

Created 2026-10-25 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "Propose how to make this release. Item 008 perhaps. Should
have a jar file, release notes, more?" Revised the same day, at his
request: "simplify. Make it take no more than 2 hours total. Limit
performance testing as necessary. s1 perf testing is good, if within time
budget. Also, I want everything in the repo. As long as it is small. Few
files, not more than 30 MB or so. Zip as you find suitable. Include the
source code in the release. And the jar."

**Status: planned; waits for Frans's command.** Two hours from the command
to the tag.


The goal
--------

BergDB 2026.1: an internal release, not published, made as a real one, and
the baseline before handles (004) and gradual eviction. A later version is
compared with 2026.1 by running both on one machine, in turns, so the
release keeps the jar and the source; the numbers measured on the day are
the record, and a check of later reruns.


The release in the repository
-----------------------------

A directory `releases/2026.1/` of five files, at most about 20 MB, and the
tag `release-2026.1` on the release commit (as `release-2013.1.130606` to
`release-2015.4-2` in F1-007's `bergdb-git.bundle`).

| File | What | Size |
|---|---|---|
| `readme.md` | The release notes, the baseline's numbers, how to compare a later version | small |
| `bergdb-2026.1.jar` | `java/build.sh`'s jar of the release commit: the production code, `src-dev` (Props, the tests), ICU 50; Java 8 class files | 3.2 MB |
| `bergdb-2026.1-src.zip` | `git archive` of the release commit, the whole tree | 6.8 MB |
| `baseline.zip` | The outputs of the gates and of the baseline runs; the GC logs too, unless the zip would pass 10 MB | up to 10 MB |
| `SHA256SUMS` | Of the jar and the two zips | small |

Version 2026.1, version int 261, build id `2026.1.YYMMDD.HHMM`, by the
rules in `java/src-dev/bergdb/dev/package.html` ("Versions and releases").

**readme.md**:

1. What 2026.1 is: internal, the baseline before 004, not for production;
   the date.
2. Its identity: the tag, the commit, the jar's SHA-256, the JDK, the build
   (`java/build.sh`, `--release 8`).
3. What it does: the status by level (README's table); the defaults that
   matter (startup distance 50 MB, buffer time 20 ms, infinite retention,
   eviction on).
4. The changes since 2015.4, the last release (July 2015), and since the
   2017 import, short, with links to `docs/log.md` and 005's closed list:
   the faults fixed (ISSUE151111 and the other restart bugs, M18, M46,
   M49, 005-15 to 005-45); Levels 2 to 4 working; the API changes
   (`Kv.time()` and `Connection.time()` removed; `stop()` and `close()`; a
   failure fails the database; `DatabaseNotCreatedException` for a
   database whose creation did not complete, 005-33; `transactionInfo()`
   without internal KVs, 005-42); record format 5 since 2026-10-15, so
   streams of 2015.4 and 2017 are refused.
5. Its verification: each step of the night run, the axioms of the Lean
   theorems, the tests on the jar.
6. Release Props, as in 2015: Props (MEM, CORE, SS) beside 2015.4's (MEM
   161, CORE 0.78, SS 1.48, on cissi), the line counts of Java and Lean,
   the test counts.
7. The baseline: the numbers, with the machine, the JDK and the flags.
8. How to compare a later version (below).
9. Known issues and limits:
   * The sweep: stop-the-world, 0.5 s to 266 s (004-02); G1's full
     collections under eviction (004-04).
   * The read path's pointer lock, stamp and `readSync`: about 2 million
     gets a second at most (004-02).
   * Writes at scale (005-38). A cold startup on a slow disk: minutes at
     10M keys on s1 (`DbStarter.linkD`).
   * Startup is not yet bounded for BergDB's own take: the section reached
     2.21 times the startup distance (007-01, 4.1); the deadline (007-03)
     comes after 2026.1.
   * Replication is experimental, with known faults (005-11).
   * `BufferedStream` does not wake its consumer when the buffer is full;
     it matters only at buffer times of about 200 ms or more, set through
     the core API (005-13); the default is 20 ms.
   * Power loss on real hardware not established; tested on JDK 27 only.
10. Post-release notes: empty at the release.

**The release commit** has only these changes on top of main:

* `BuildInfo.java`, which says 2017.1 (prepared in 2017, never released):
  `RELEASE` "2026.1", `RELEASE_INT` 261, `BUILD` "2026.1.YYMMDD.HHMM".
  `bergdb.dev.Info` prints them, and `Db` writes the release into
  `created.txt`.
* `created.txt` loses its "see bergdb.com", a site that has not been
  BergDB's since 2023.
* `docs/levels.md`, Level 2, says "startup distance 20 MB"; the default is
  50 MB since 2026-10-13 (noted 2026-10-25; unless fixed by then).

None of them changes a stream. The commit after the tag sets "2026.2-dev"
and 262, so that a jar of later code never says 2026.1.

**Not made**: javadoc; the 2017 build's other jars (`bergdb-no-icu.jar`,
and `bergdb-versioned-NNN.jar`: jarjar 1.4 renames only ICU's classes in
today's jar, tried 2026-10-25); a .NET build; Maven coordinates; a website.


The baseline runs
-----------------

With the release jar, and the parameters of 004-02 and 004-04, so that
their figures check today's. On F53 (Homebrew's OpenJDK 27), one block of
about 40 minutes, after a quiet check of 3 minutes (no other JVM than the
editor's, no gate or build, no other Claude session busy, a load below
2.0), with this session idle, as its own work disturbs the timing. On s1
(OpenJDK 27+35), unattended, at the same time as the gates and that block.
Every value read is checked (`SCALEBENCH OK`, `PERF OK`).

| Run | Machine | Collector | What | Time |
|---|---|---|---|---|
| Props, 5 runs | F53 | G1 | MEM, CORE, SS: the history since 2015 | 4 min |
| `performance.sh quick` | F53 | G1 | 200k keys of 1,000 bytes: warm gets, updates with infinite and finite retention, a restart; the references of 2026-10-14 to 18 | 15 min |
| ScaleBench, 10M key24 keys | F53 | G1, ZGC | in memory (M): the load, the heap per key, gets from 1 to 8 threads; from the OS cache with eviction (C) at 665 MB (both collectors) and 133 MB (G1): gets, sweeps, pauses | 21 min |
| StreamDigest `all` | F53 | — | the stream digests of the standard workloads | during the gates |
| ScaleBench, 10M keys | s1 | G1 | the load with a budget of 600 MB (about an hour on s1's disk); from the device (D) at 133 MB, with its startup from a cold cache | 75 min |
| ScaleBench, 1M keys | s1 | G1 | M; C at 66 MB; D at 66 MB | 13 min, if time is left |

What s1 has not finished at 1:45 is left out.

Left out, to keep to two hours: the soak; 1M, 50M and 100M keys and
random keys on F53; the principal suite and its thresholds; `perf.sh`;
`night.sh large` and Lean's random runs; ZGC on s1; Shenandoah.


How to compare a later version
------------------------------

Run 2026.1 again beside the later version, in turns, rather than compare
with today's numbers: the machine, the OS and the JDK change. In
readme.md, tool by tool:

* Props: `java -cp JAR bergdb.dev.props.Props` with each jar.
* `performance.sh`: `performance.sh build 2026.1` in a clone at the tag,
  then `performance.sh ab 2026.1 current`.
* StreamDigest: 2026.1's class against both jars, then `compare`, as its
  header says. The stream does not depend on eviction (EvictionInvariance;
  T-CACHE in Lean), and handles do not change the records (004-03, 2.2),
  so 004 should give 2026.1's digests.
* ScaleBench, in item 004: both jars, in turns. It reads internals that
  handles change (the eviction's figures, the resident bytes, the load
  listener); 004 ports those reads and keeps the workload.


The steps
---------

Times from Frans's command. Before it: everything meant for 2026.1
committed, main clean. During it: the other Claude sessions idle (no
builds, gates or timing runs). The work is in scratch clones; nothing is
pushed.

| Time | What |
|---|---|
| 0:00 | Checks: main clean, no gate or JVM running, the other sessions idle. A clone of main. |
| 0:05 | The release commit's changes; `before-commit.sh` (2 min). Commit A, the release commit, on main. |
| 0:10 | In a clean clone of A: `java/build.sh`, the jar. On the jar itself, the release tests of 2013 to 2017: `bergdb.dev.Unit`, `F` and `Night` with `-ea`; `bergdb.core.BuildInfo` prints 2026.1. |
| 0:15 | s1: the jar, and ScaleBench compiled against it, to `/opt/bergdb-bench/2026.1/` (SHA-256 checked); its block started. F53: `java/night.sh` in a clone at A, 45 minutes: `before-commit.sh`, `level1.sh` to `level4.sh` (their `lake build` checks every proof), the night tests, the medium conformance set. Beside it: StreamDigest; `#print axioms` of lean/README.md's theorems; the line counts; the source zip; readme.md written, all but the numbers. |
| 1:00 | The quiet check, then the F53 block, about 40 minutes; this session idle. |
| 1:45 | s1's outputs fetched, its databases deleted. The numbers into readme.md, with a glance beside 004-02's and 004-04's; `baseline.zip`; `SHA256SUMS`. |
| 1:55 | Commit B: `releases/2026.1/`; README, a line on `releases/`; `docs/log.md`; this item's log; `BuildInfo` to 2026.2-dev, with `before-commit.sh`. The tag `release-2026.1` on A. |
| 2:00 | Done. |

A failure in the gates stops the release, and Frans decides. A block that
cannot start quietly waits, and the release takes longer: no numbers from
a busy machine.


Decision for Frans
------------------

The commits A and B and the tag: by the session, in Frans's name and
without AI attribution, as part of his command (recommended, to keep to
two hours); or by Frans, at 0:05 and 1:55.
