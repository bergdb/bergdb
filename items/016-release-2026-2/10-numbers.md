016-10. Plan: the numbers against 2026.1
=========================================

Created 2026-11-03 by Frans Lundberg. Status: planned, not started.

The plan for W7 of 016-01 (section 5): 2026.2's numbers against 2026.1,
with both jars run in turns, on F53 and s1, for the release notes and
`baseline.zip`. It fits the one night of the coordinator's timeline
(Frans, 15:40: "finish this work by 07:00 tomorrow"), with commit A at
01:45, `night.sh` at 02:10 and the quiet block in window 2 only.

Who: one agent (the tools agent of 016-09) prepares everything in the
evening, in `/Users/f/fl/bench/016/numbers/`, about 5.5 agent-hours, and
hands the scripts to the coordinator; `prep-a.sh` writes the READY
markers at about 02:00 (N6). The runs are unattended: the conductor (013-01, section 7)
runs the F53 steps; the s1 chain is started over `ssh` at about 01:55.
The coordinator writes the tables into the notes in the morning (016-03).


## 1. Facts found on 2026-11-03

What the tools need, checked against `releases/2026.1/bergdb-2026.1.jar`
(javap) and `git show release-2026.1:...`. 016-01, section 5 (W7, "First")
assumed that the tools likely still run; four of five do not, as they are.

* **Props** runs as is: `java -cp JAR bergdb.dev.props.Props`. Props is in
  each jar (`src-dev`), so each version runs its own. It prints `MEM:`,
  `CORE:` and `SS:` lines.
* **`performance.sh ab`** does not run on 2026.1 as it is.
  * `ab REF CAND` takes two preserved builds in `java/build/perf/builds/`
    (`resolve_build`, line 153), and alternates them ABBA within each
    scenario. The suite comes only from `SUITE` (default principal), so the
    quick suite is `SUITE=quick performance.sh ab 2026.1 2026.2`.
  * The harness (`Perf.java`, `PerfUtil.java`, `PerfTool.java`) always
    comes from the running tree's `java/stress` and is compiled against
    each build's jar (`prepare_target`, lines 165 to 177), into
    `builds/LABEL/harness-SHA12`; `ab` dies if the two harness hashes
    differ (line 452).
  * `Perf.java` line 20 imports `bergdb.pub.util.SyncLevel` (005-56,
    `04f1546`), which 2026.1's jar does not have (it has
    `bergdb.core.SyncLevel`). The compile against 2026.1 fails.
  * The fix, used before by 005-48's `night/run-s1.sh`: compile the
    running tree's harness with that import changed to
    `bergdb.core.SyncLevel`, against 2026.1's jar, into
    `builds/2026.1/harness-SHA12`, where SHA12 is the running tree's
    harness hash; `prepare_target` then skips the compile.
  * The defaults differ inside the comparison: Perf's buffer time 0 means
    each jar's default, 20 ms in 2026.1 and 50 ms in 2026.2 (005-64). This
    is what a user gets, and the notes say it.
  * The 2026.1 preserved builds that exist
    (`/Users/f/fl/repos/bergdb-009/java/build/perf/builds/2026.1`, and
    `/Users/f/fl/bench/006-09/w1/head/...`) are rebuilds of `a42947c` with
    older harness hashes. A new one is made (step N2).
* **ScaleBench** (`items/004-indirect-swizzling/02-scale-tests/`, package
  `bergdb.core`) is in no jar and is compiled per jar.
  * The raw source does not compile on 2026.2 (`KeyNode.setPointerAccessData`,
    line 946, gone with handles), nor with `--release 17`
    (`Thread.threadId()`, line 851), and its unqualified `SyncLevel`
    (line 577) resolves only on 2026.1.
  * The template that works on both: 005-65's
    `items/005-todo/65-gets-with-8-readers/night/prep.sh`. It applies
    `items/009-handles/03-measurements/ScaleBench-009.diff` and
    `ScaleBench-065.diff`, makes a `src-pub/` copy with the
    `bergdb.pub.util.SyncLevel` import for jars that have that class, and
    compiles with `--release 17` per jar. It last compiled against
    `988fe1a` and `5a6befd` (2026-10-29, in
    `/Users/f/fl/bench/006-10/e65-builds`).
  * Its startup distance is `sb.sd`, default 10,000,000. 2026.1's baseline
    passed none, so its ScaleBench figures are at 10 MB. Both versions'
    own default is 50 MB (2026.1: `DbBuilder` line 66 at the tag).
  * `sb.sh` does not call `quiet.sh`. 2026.1's `f53.sh` did, and
    `quiet.sh` refuses any block that overlaps 02:00 to 05:00 (its `busy`,
    `m < 300 && m + NEED > 120`). No step of this plan calls `quiet.sh`;
    the conductor checks.
* **PauseProbe** (`java/stress/PauseProbe.java`) does not compile against
  2026.1 since `eaec93e` (005-46): `TimedIo` extends
  `bergdb.stream.FileStreamIo` and calls `new FileStream(dir, io)`, both
  package-private in 2026.1 (javap). The last version that runs on both is
  `e23c96e`'s, which 009-03 used; it imports only `bergdb.stream.FileStream`
  and reads `cacheStats` and `takeWriteBufferWaits` by reflection.
* **StreamDigest** (`java/stress/StreamDigest.java`, compiled into
  `build/stress` by `build.sh`, not in the jar) imports
  `bergdb.pub.util.SyncLevel` (line 11). So one compiled copy no longer runs
  on both jars, in either direction, as 2026.1's readme says it does.
  * No reference file is committed and no gate runs it. 2026.1's digests
    are `baseline/f53/digests.txt` in `releases/2026.1/baseline.zip`.
  * 2026.2's digests differ from 2026.1's by design: 005-50 (the node size
    in the meta block, masked by `metamask=44:2`), 007-07 (all 36 changed,
    `items/007-bounds/07-step3-paced-take/digest-summary.txt`) and 005-79
    (the take in integers); 005-78 may add a change.
* **Databases.** 2026.2 refuses 2026.1's databases (005-50), so each
  version loads its own. That measures the loads too: 2026.1's 10M load on
  s1 took 3,015 s at 10 MB; 2026.2's took about 732 s (005-76's runs).
* **s1** (2026-11-03, 15:44): idle (load 0.10), no `java` running, 33 GB
  free, 2 CPUs, 3.8 GB. `/opt/bergdb-bench/` has `jdk-27`, `jdk-17`
  (17.0.21, installed today at 15:43, with `javac`), and `2026.1/` with
  `bergdb-2026.1.jar`, `classes/`, `sb.sh`, `s1.sh` and 2026.1's outputs in
  `out/`.
* **F53** has 439 GB free. Homebrew's JDK 27 is
  `/opt/homebrew/opt/openjdk`; no JDK 17 at 15:48 (016-09 installs it).
* **`night.sh`** took 41 minutes on 2026-11-03 (02:10 to 02:51). Window 2
  starts at about 02:55.


## 2. What is measured, and what is cut

The runs of 2026.1's readme ("Baseline"), in turns, cut to fit window 2.

| Run                            | Where | Both jars | Minutes |
|--------------------------------|-------|-----------|---------|
| Props, 3 runs each, ABABAB     | F53   | yes       | 8       |
| ScaleBench 10M, M, G1 and ZGC  | F53   | yes       | 22      |
| ScaleBench 10M, C 665 and 133  | F53   | yes       | 32      |
| Pause probe, G1 and ZGC        | F53   | yes       | 10      |
| `performance.sh ab`, quick     | F53   | yes       | 22      |
| StreamDigest `all`             | F53   | 2026.2    | 3       |
| ScaleBench 10M load and D 133  | s1    | yes       | 90      |
| ScaleBench 1M, M, C and D 66   | s1    | yes       | 30      |

The F53 steps take 94 minutes, with about 3 minutes of quiet check
before each, so about 109 minutes. The conductor is the coordinator's, in
`/Users/f/fl/bench/016/night1/` (running since 15:42, window 1 empty,
`W2_END` 06:05; 016-05, section 6). After 005-65's and 005-52's steps
(their `# minutes` 30 and 25, about 21 and 17 in fact), these start
between about 03:45 and 04:01 and end between about 05:34 and 05:50,
before 06:05.

**A conflict with 016-05's schedule.** 016-05, section 7 starts 005-65's
and 005-52's write-ups by two agents when their steps end, at about
04:00. Agents at work make the coordinator's session busy, and the
conductor's quiet check (013-01, section 7: no busy Claude session) then
holds each W7 step for up to 30 minutes and runs it `NOT QUIET`. The
conductor's script cannot be changed while it runs (AGENTS.md). Decision
for the coordinator:

* **A, recommended**: the write-ups start when the conductor's
  `status.txt` says the block is over (about 05:50), and what is not
  written by 06:45 stays in the entries' State. The release needs from
  them only docs/levels.md's line on 005-65 (016-04, D5), which can stay
  "not yet explained".
* **B**: the write-ups at 04:00, and W7 on F53 cut to what ends before
  them: none, as 005-65's and 005-52's steps come first. W7 then has s1's
  runs only, and the notes have no F53 numbers against 2026.1.
* **C**: W7's F53 steps first, from about 03:00 to 04:50, then 005-65's
  and 005-52's (to about 05:45), and their write-ups after: the same
  problem for the write-ups, later.

**The startup distance.** Every ScaleBench run is at 200 MB
(`-Dsb.sd=200000000`), both jars.

* Why: only distances of 50 MB or more are cited, and 200 to 1000 MB are
  the documented range from about 10M keys (010-01, P10). In turns, both
  jars at one distance are the comparison.
* Cut: the runs at 2026.1's 10 MB (016-01, W7). They would compare with
  2026.1's published figures, which in-turns runs make unnecessary, and
  their figures may not be cited. They would add about 45 minutes.
* The quick suite keeps its own setting (each jar's default, 50 MB).
* Decision for the coordinator, recommended: 200 MB. The alternative is
  50 MB, both versions' default, which suits up to about 10M keys.

**Also cut**, beyond 2026.1's own cuts (the soak, 1M, 50M and 100M keys on
F53, the principal suite, ZGC on s1, Shenandoah):

* Props from 5 runs to 3 each.
* A second `ab` round. `performance.sh` asks for two before an alert is
  called a regression; an alert of the one round is reported as "seen
  once, not confirmed".
* Generational Shenandoah in the pause probe (009-03 ran it; it stops,
  and docs/levels.md says so).
* The quick `ab` with 2 runs a scenario (`RUNS=2`, ABBA gives two of
  each), not the suite's 3: 22 minutes instead of 35.

**What cannot fit**: nothing else of 016-01's W7. If window 2 starts late
(night.sh after 03:15, or a quiet check that waits), the conductor skips
the steps that would end after 06:05, from the end of the list: the quick
`ab` first, then the pause probe. Recommended: accept that, and say in the
notes which runs were skipped.


## 3. The steps

Times are tonight's, 2026-11-03 to 04. "Agent" is the numbers agent, in
`/Users/f/fl/bench/016/numbers/` (N below). Each step names its check.

### N1. The clones and the 2026.1 side (agent, 17:00 to 18:00)

* `git clone /Users/f/fl/repos/bergdb N/tag` and `git -C N/tag checkout
  release-2026.1`; `git clone /Users/f/fl/repos/bergdb N/cand` at `main`
  (the candidate, for the smoke tests; from 01:45, 016-09's clone of A
  takes its place).
* `cp releases/2026.1/bergdb-2026.1.jar N/jars/2026.1.jar`; check its
  SHA-256 against `releases/2026.1/SHA256SUMS`
  (`4d90eb92...5ad5892`).
* Check: `shasum -a 256 -c` prints OK for the jar.

### N2. performance.sh's builds (agent, 18:00 to 19:00)

* In `N/tag`: `JAVA_HOME=/opt/homebrew/opt/openjdk java/stress/performance.sh
  build 2026.1`. The build's jar is a rebuild of the tag, not the release
  jar. Compare their classes (`unzip -q` each into a directory, `diff -r`):
  * the same classes: keep the rebuild, and the notes say that its classes
    are the release jar's;
  * otherwise: put the release jar in its place
    (`N/tag/java/build/perf/builds/2026.1/java/build/bergdb.jar`) and set
    the jar's SHA-256 in that build's `identity.env` to the release jar's,
    so that the session records the release jar.
* Copy the build to the candidate: `cp -R N/tag/java/build/perf/builds/2026.1
  N/cand/java/build/perf/builds/`.
* In `N/cand`: `performance.sh build 2026.2-cand`.
* `N/harness131.sh BUILDDIR TREE`: computes the harness hash as
  `prepare_target` does (the same files, the same `sha256`), copies
  `Perf.java`, `PerfUtil.java` and `PerfTool.java` from TREE's
  `java/stress` to a temporary directory, changes the line
  `import bergdb.pub.util.SyncLevel;` to `import bergdb.core.SyncLevel;`,
  and compiles them with `javac --release 17 -cp BUILDDIR/java/build/bergdb.jar`
  into `BUILDDIR/harness-SHA12`.
* Check: `SUITE=smoke RUNS=1 FORCE=1 performance.sh ab 2026.1 2026.2-cand`
  in `N/cand` ends with its comparison and no `die`; the session's
  `summary.txt` names both builds. A few minutes; not timed.

### N3. ScaleBench, PauseProbe and StreamDigest compiled per jar (agent, 19:00 to 20:00)

* `N/prep-tools.sh JAR OUTDIR`, after 005-65's `prep.sh`:
  * ScaleBench with the 009 and 065 diffs; `src-pub/` with the
    `bergdb.pub.util.SyncLevel` import if `unzip -l JAR` lists
    `bergdb/pub/util/SyncLevel.class`; compiled with `javac --release 17
    -cp JAR` together with `java/stress/PerfUtil.java`, into `OUTDIR/sb`;
  * PauseProbe from `git show e23c96e:java/stress/PauseProbe.java`, the same
    way, into `OUTDIR/pp`;
  * StreamDigest from the running tree, with the import changed for a jar
    without `bergdb/pub/util/SyncLevel.class`, into `OUTDIR/sd`.
* Run it for 2026.1's jar into `N/tools/2026.1` and for the candidate's
  jar (`N/cand/java/build/bergdb.jar`, from `java/build.sh`) into
  `N/tools/cand`.
* `pidio` for ScaleBench's I/O counts: `cc -O2 -o N/tools/pidio
  items/004-indirect-swizzling/02-scale-tests/pidio.c`.
* Check: each compile exits 0, and each OUTDIR has `bergdb/core/ScaleBench.class`,
  `bergdb/core/PauseProbe.class` and `bergdb/core/StreamDigest.class`.

### N4. The step scripts (agent, 20:00 to 22:30)

In `N/night/`, one script per step of section 2. Each:

* has a line `# minutes: N` with the minutes of section 2;
* takes `REL=DIR`, the directory that `prep-a.sh` fills (step N6), and
  uses only what is there: the jars, the compiled tools, the preserved
  builds; it compiles nothing (013-01, section 7);
* checks its needs first and exits with status 2, having run nothing, if
  one fails: the jars and classes present, 30 GB free on F53
  (`df -g`), AC power (`pmset -g batt | grep -q "AC Power"`);
* runs the two jars in turns, in ABBA order where a run is repeated
  (2026.1, 2026.2, 2026.2, 2026.1, ...);
* uses Homebrew's JDK 27, `export JAVA_HOME=/opt/homebrew/opt/openjdk`;
* starts no `caffeinate` of its own: the coordinator runs the conductor
  under `caffeinate -i -s`; a script that starts a background child waits
  for it by its PID, never with a bare `wait` (008-01's lesson: `f53.sh`
  hung for an hour on its own `caffeinate`);
* writes its outputs to `N/night/out/LABEL/`;
* ends by parsing its own outputs: one line `W7 LABEL OK` with the values
  it read, or `W7 LABEL FAILED: what is missing` and exit status 1;
* with `SMOKE=1`, runs the same code paths in about a minute (small sizes,
  1 run each) and parses those outputs the same way (013-01, section 9:
  Props once exited 1 at night because its CORE line was not parsed).

The scripts:

* **`props.sh`** (8 minutes). `java -cp JAR bergdb.dev.props.Props`, 3 runs
  each, ABABAB. Parses `MEM:`, `CORE:` and `SS:` from each run; prints the
  medians per version. SMOKE: one run of each jar, parsed.
* **`sb-m.sh`** (22 minutes). With `sb.sh` (`. $SB/sb.sh`, `CP`, `DATA`,
  `THREADS=1,2,4,8`, `SAMPLED=4`, `PIDIO`), as 2026.1's `f53.sh`:
  `sb_load NAME key24 10000000 6g 0 warm,uniform,hot,threads` with
  `SBFLAGS="-XX:+UseG1GC -Dsb.sd=200000000"`, then with ZGC; in the order
  2026.1 G1, 2026.2 G1, 2026.2 ZGC, 2026.1 ZGC. One data directory per
  version, `N/night/data/VER`, kept for `sb-c.sh`. Parses
  `SCALEBENCH OK` and the load time, puts a second, heap per key, gets a
  second and the 4- and 8-thread figures. SMOKE: 100k keys, G1 only.
* **`sb-c.sh`** (32 minutes). Exits 2 if a version's data directory from
  `sb-m.sh` is missing. `sb_get NAME key24 10000000 2660m 665000000 C P`
  with G1 and ZGC, and `600m 133000000` with G1, each jar, ABBA within each
  configuration, `-Dsb.sd=200000000`. Then deletes `N/night/data`. Parses
  gets a second, p50, p99, the longest get, the longest batch
  (`Eviction.stats()`'s "sweep", which is a batch of at most 2 ms in
  2026.2), the longest GC pause and the full collections. SMOKE: 100k keys,
  one C run per jar.
* **`pp.sh`** (10 minutes). Each version's compiled `e23c96e` PauseProbe:
  `-cp JAR:TOOLS/pp bergdb.core.PauseProbe` with `-Dkeys=1000000
  -Dbudget=100 -Dreaders=4 -Dseconds=60 -Dtsize=1,1000`,
  `-Xms1200m -Xmx1200m -XX:+AlwaysPreTouch`, G1 then ZGC, ABBA, a fresh
  database each run (as 009-03's `f53-009.sh`, lines 29 to 44). Tables
  with `items/009-handles/03-measurements/ppsum.py`. Parses each run's
  longest get and longest commit. SMOKE: 5 s, 50k keys.
* **`quick-ab.sh`** (22 minutes). In the clone of A:
  `FORCE=1 SUITE=quick RUNS=2 JAVA_HOME=... java/stress/performance.sh ab
  2026.1 2026.2`. `FORCE=1`, because the conductor has checked, and
  `performance.sh`'s own quiet check (90 percent idle CPU) refused
  005-48's runs at night (013-01, section 9). Then `performance.sh summary
  SESSION --md` into the output. Parses `PERF OK` and the comparison's
  lines. SMOKE: `SUITE=smoke RUNS=1`.
* **`s1-w7.sh`** (the s1 chain's second half, 120 minutes; started by
  016-09's `s1-chain.sh`, not by the conductor). On s1, in
  `/opt/bergdb-bench/016/w7/` (016-08's H4 uses `016/h4/` and `016/bin/`),
  as 2026.1's `s1.sh` with `DEADLINE`:
  * first `ps -eo args | grep -E '[j]ava|[s]b\.sh'`: if another run is
    there, wait up to 30 minutes, then exit 2;
  * the 10M load, budget 600 MB, `2500m`, and D at 133 MB with its cold
    start (`600m 133000000 D`), for 2026.2, then the database deleted;
    then the same for 2026.1. Both with `-Dsb.sd=200000000`;
  * then 1M keys: M, C at 66 MB and D at 66 MB, for 2026.1, then 2026.2;
  * no run starts after `DEADLINE`, 05:15 (epoch seconds, an argument);
  * the default collector (G1), `THREADS=1,2,4`, `SAMPLED=2`, `DISK=sda`;
  * parses each run's `SCALEBENCH OK` line into `out/w7-s1.txt`, and
    writes `S1 W7 DONE` last.
  * SMOKE: 100k keys, the load and D, both jars.
* **`tables.sh`** (for the morning, not a step). Reads `N/night/out/` and
  the s1 outputs and writes `N/night/tables.md`: the tables of 016-03's
  Baseline section, each row with both versions side by side, in the
  layout of 2026.1's readme. Smoke-tested on the SMOKE outputs.

Check of N4: each script run with `SMOKE=1` against 2026.1's jar and the
candidate's prints `W7 LABEL OK`, and `tables.sh` makes a table from
those outputs. The smoke runs are not timed, and may run in the evening.

### N5. The steps file (agent, by 22:30; the coordinator owns it)

The conductor's `steps.txt` (013-01, section 7) is the coordinator's,
shared with 005-65's and 005-52's steps. This plan's lines, after theirs,
in this order (the order is the priority):

    8|f53|/Users/f/fl/bench/016/numbers/night/props.sh|w7-props
    22|f53|/Users/f/fl/bench/016/numbers/night/sb-m.sh|w7-sb-m
    32|f53|/Users/f/fl/bench/016/numbers/night/sb-c.sh|w7-sb-c
    10|f53|/Users/f/fl/bench/016/numbers/night/pp.sh|w7-pp
    22|f53|/Users/f/fl/bench/016/numbers/night/quick-ab.sh|w7-quick-ab

The agent hands them to the coordinator, who writes a new `steps.txt`
and moves it over the old one. For the conductor of this night (the
coordinator's), recommended:

* it is the conductor already running in `/Users/f/fl/bench/016/night1/`
  (016-05, section 6): window 1 empty (02:00 to 02:00), so that no F53
  step runs in the evening while the agents work; `NIGHT_LATEST` 03:15;
  `W2_END` 06:05. Its script is not edited while it runs; only
  `steps.txt` changes, by a new file moved over the old;
* the s1 chain is not a conductor step (016-09, step R5).

### N6. `prep-a.sh`: the tools on A's jar (the coordinator runs it, 01:50 to 02:00)

A script written by the numbers agent, run once A's jar exists (016-09,
step R3). In `REL=/Users/f/fl/bench/016/numbers/rel` it:

* links `jars/2026.1.jar` and A's jar `jars/2026.2.jar`;
* runs `prep-tools.sh` for A's jar into `tools/2026.2` (a minute);
* in the clone of A that 016-09 makes (`/Users/f/fl/bench/016/release/rel`):
  copies the `2026.1` preserved build in, runs `performance.sh build
  2026.2` (a minute), then `harness131.sh` for 2026.1, and the same
  compile without the import change for 2026.2, each into
  `harness-SHA12` with A's harness hash, so that `performance.sh`
  compiles nothing in the block;
* checks that both builds' harness directories have A's hash, and that
  each tool's classes are there;
* runs `props.sh`, `pp.sh` and `quick-ab.sh` with `SMOKE=1` on A's jar,
  about a minute each, not timed; `quick-ab.sh`'s smoke is `SUITE=smoke
  RUNS=1 ONLY=` one small scenario (the full `ab` smoke ran in the
  evening, step N2);
* writes the `.READY` marker of each F53 script of N5 whose smoke passed,
  and prints `PREP A OK` or the scripts that failed.

The coordinator reads its output. A script without its marker does not
run; the coordinator writes a line in 016-02.

### N7. The block runs (unattended, about 03:00 to 05:50)

* The conductor runs 005-65's and 005-52's steps, then these, each after
  its quiet check. The coordinator is idle: no tool calls, no agents.
* s1's chain runs from about 01:55 (016-09, R5): the tests on the jar,
  then `s1-w7.sh`, ending by about 04:30.
* Check: `results.txt` has `exit 0` for each step; `out/LABEL.txt` ends
  with `W7 LABEL OK`; a step marked `NOT QUIET` is reported so in the
  notes.

### N8. StreamDigest's new reference (the coordinator, 01:55 to 02:00)

Deterministic, so it runs outside the block, beside the tests on the jar.
In the clean clone of A:

* `java -cp build/bergdb.jar:build/stress bergdb.core.StreamDigest all >
  digests-2026.2.txt`;
* check: every configuration's modes give the same stream (StreamDigest's
  header, the three modes), and there are at least 2026.1's 12
  configurations;
* the same workloads on 2026.1's jar, with N3's copy of A's StreamDigest
  (the import changed): `java -cp jars/2026.1.jar:tools/2026.1/sd
  bergdb.core.StreamDigest all > digests-2026.1-now.txt`. Check that it
  equals 2026.1's own (`unzip -p releases/2026.1/baseline.zip
  baseline/f53/digests.txt`) where the configurations are the same, which
  shows that the workloads did not change;
* then `... StreamDigest compare digests-2026.1-now.txt digests-2026.2.txt`.
  Expected: they differ, by design (section 1), also when both `all` runs
  take `-Dmetamask=44:2` (005-50's node size masked), as 007-07 and 005-79
  changed the records. The notes record how many differ, and why;
* the file goes into 2026.2's `baseline.zip` as `f53/digests.txt`. It is
  2026.2's reference: a later version compares with it, or better, runs
  2026.2's jar again beside its own, with one compiled copy per jar.

A digest that differs between the modes is a fault: the coordinator
registers it in 015 and it is a stop for Frans (the release waits).

### N9. The morning (coordinator, 06:05 to 06:20)

* Fetch s1's outputs: `scp -r root@s1:/opt/bergdb-bench/016/w7/out
  N/night/out/s1`; then delete s1's data directory
  (`/opt/bergdb-bench/016/w7/data`).
* `sh N/night/tables.sh` writes `tables.md`; its tables go into 016-03's
  Baseline section of `releases/2026.2/readme.md`.
* A glance beside 2026.1's published figures and 009-03's: a figure that
  moved by more than its spread gets a sentence.
* The outputs, without the GC logs if the zip would pass 10 MB, go into
  `baseline.zip` (016-09, R8): `f53/` and `s1/`, and the scripts in
  `tools/`.


## 4. Stops for Frans

* A digest that differs between StreamDigest's modes (N8).
* None for the numbers themselves: a regression is reported in the notes
  and 016-02, with the run that shows it, and the release goes on. A
  regression larger than 20 percent in a figure that the notes cite gets
  `news.sh "needs a look"`.


## 5. Done when

* `results.txt` of the conductor shows each W7 step's exit code, or the
  notes say which step was skipped and why;
* s1's `out/w7-s1.txt` ends with `S1 W7 DONE`, or the notes say which runs
  the deadline cut;
* `releases/2026.2/readme.md`'s Baseline section has the tables of both
  versions, with the machine, the JDK, the flags and the startup distance;
* `baseline.zip` holds the outputs, the digests and the scripts;
* the notes' "How to compare a later version" says how 2026.2's tools run
  on both jars (one compiled copy per jar, section 1).


## 6. State

2026-11-03, 16:05: the plan is written; nothing is prepared. Open: the
coordinator's choices of the startup distance (section 2, 200 MB
recommended) and of the write-ups' time (section 2, A recommended); who
runs N1 to N5 (recommended: the tools agent of 016-09, from about 17:00,
about 5.5 hours, then 016-09's R0).

2026-11-03, 16:05: the coordinator chose 200 MB only, `ab` with 2 runs a
scenario and one round, Props 3 runs each, no Shenandoah, the write-ups
after the block (A). The tools agent started.

2026-11-03, 16:30, the tools agent (all in `/Users/f/fl/bench/016/numbers/`,
N below):

* N1 done: `N/tag` (release-2026.1), `N/cand` (main at 323a54a), and
  `N/jars/2026.1.jar` (SHA-256 OK).
* N2 done: `N/tag`'s `performance.sh build 2026.1` has the release jar's
  classes (`diff -r` of both unzipped: the same), so the rebuild is kept;
  copied to `N/cand`; `N/harness131.sh` compiles the harness against both
  builds (2026.1 with the import changed). The `ab` smoke is still to run.
* N3 done: `N/prep-tools.sh JAR OUTDIR [TREE]` compiles ScaleBench (both
  diffs), e23c96e's PauseProbe, StreamDigest and pidio against 2026.1's jar
  and the candidate's (`N/tools/2026.1`, `N/tools/cand`).
* N4: the scripts are in `N/night/` (`lib.sh`, `props.sh`, `sb-m.sh`,
  `sb-c.sh`, `pp.sh`, `quick-ab.sh`, `s1-w7.sh`, `tables.sh` with
  `tables.py`); smoke OK on the candidate (`REL=N/rel-cand`): `pp.sh`,
  `sb-m.sh`, `sb-c.sh`, `tables.sh`. N6's `N/prep-a.sh` and N8's
  `N/digests.sh` (with a copy of 005-79's `digest-compare.py`: decided
  digests only, 015-08) are written; their rehearsal on a scratch commit A
  waits for a gap in the other agents' gates.
* 16:52: `prep-a.sh` rehearsed on a scratch commit A (`b90eff7`: main's
  `f2cb23b` with BuildInfo at 2026.2, in `R/cand` only; `MARK=0`, `REL=N/rel-rehearsal`):
  `PREP A OK: 5 of 5 steps would be READY`, 256 s with the other agents'
  load. It found that ScaleBench no longer compiled on main's jar: 005-79
  (`dde82e8`) replaced `Eviction.LOW` by `Eviction.lowOf(budget)`;
  `prep-tools.sh` now uses `lowOf` in that one line for a jar without `LOW`.
* 16:35: the s1 half rehearsed with `SMOKE=1` (016-09's `s1-chain.sh`):
  `S1 W7 DONE (SMOKE): 4 runs OK`.
* 16:53: N8 rehearsed: `DIGESTS OK` in 52 s: 2026.2 has 12 configurations,
  whose modes agree; 2026.1 now equals its release's decided digests (36 of
  36); 2026.1 against 2026.2: the decided digests differ in 36 of 36, by
  design. N2's check: the smoke suite in turns, 2026.1 against the
  candidate, `W7 quick-ab OK (SMOKE): ab exit 0; 7 of 7 scenarios
  compared`. `tables.sh` makes the tables from the smoke outputs.
* 17:00: N5 done: the coordinator put the five lines into the conductor's
  `steps.txt`, after `65-rerun` and `52-lowered`; and chose 3 runs a
  scenario for the quick `ab` (`quick-ab.sh` changed; still 22 minutes).
  Open: N6 (`prep-a.sh`, about 4 minutes, writes the markers) and N8
  (`digests.sh`) at about 01:50, after 016-09's `build-a.sh`.
* 17:18: 016-09's `rehearse.sh` on main's `437cb48`: `PREP A OK` (5 of 5)
  and `DIGESTS OK`.

2026-11-03, 17:20, the tools agent stopped (usage). N1 to N5 are done.
Left: N6 and N8 at about 01:50 (016-09's State has the commands); N7
unattended; N9 at 06:05 is 016-09's `collect.sh`, which fetches s1's
outputs, deletes s1's data and runs `night/tables.sh` (into
`N/night/tables.md` and the baseline). Before the freeze, if java/stress,
ScaleBench or its diffs changed after 17:18, run 016-09's `rehearse.sh`
again.
* Found: with 2 runs a scenario PerfTool raises no alert ("fewer than 3
  runs: no conclusion"), so the quick `ab` gives medians and changes only;
  2026.1's quick suite took about 34 s a run (its `runs.txt`), so 3 runs a
  scenario would take about 17 minutes, not 35.
