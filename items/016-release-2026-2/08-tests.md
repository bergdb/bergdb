016-08. Plan: tests beyond the gates, H4
========================================

Created 2026-11-03 by Frans Lundberg.

**Status: planned, not started.** The detailed plan of 016-01, section 6's
H4, cut to fit tonight's run. Frans, 15:40: "try your best to finish this
work by 07:00 tomorrow in the morning ... instead of in three days or so.
Note, you only need before-commit.sh to be successful to commit your
work." His answer to Q2 (15:27) allows a JDK 17 on F53 (Homebrew's
`openjdk@17`) and on s1 (in `/opt/bergdb-bench/`, beside its JDK 27). His
change of 15:31 (D7) takes the C clone out of the release, so the C clone's
cross tests after 005-79 are dropped (section 7).


## 1. In short

* **One heavy run at a time on F53**, from now to 01:30, beside the fix
  agents' gates; nothing heavy on F53 from about 01:30 (the release commit
  about 01:45, `night.sh` at 02:10, window 2 from about 03:00 to 06:15 as
  a quiet block for timed runs).
* **s1 has its own queue**, from now to 01:45, when it is left for W7's
  timed runs.
* **Fits tonight** (section 3): the JDK 17 installs (now); jcstress on
  today's code (now) and with H3's new tests (23:30); `before-commit.sh`
  and the night tests on JDK 17 (17:00); the stress programs with fresh
  seeds, 2 hours in the evening and 1 hour after the fixes; a shorter soak;
  the large conformance set without its two longest traces; on s1, the
  gates, `level1.sh` and the night tests on JDK 27 and 17, jcstress, and
  the stress programs on disk.
* **Does not fit**: `night.sh large`, about 6 hours. Section 6 gives the
  options; recommended: the large set without the two `l-big62` traces
  tonight (about an hour), and the whole of `night.sh large` on the release
  commit when window 2 ends (about 06:15).
* **Found while planning** (section 8): `build.sh` takes `javac` from the
  PATH, not from `JAVA_HOME`; s1 has no `unzip`, which `build.sh` needs; two
  stress programs take no seed.


## 2. Rules for every run

* **Heavy** means a run that keeps most of a machine's cores busy for more
  than 10 minutes: `night.sh`, jcstress, the stress programs, the soak, the
  conformance sets. One at a time on each machine.
  * Who: the H4 runner (section 2, "Who") starts each, after the previous
    one has ended (`ps` shows no `java` of it).
  * Checked: the State table (section 9) has one row running per machine.
* **The fixes' gates may run beside a heavy run**: they are not timed. To
  keep them quick and their timing tests calm, the stress programs on F53
  run at most 5 JVMs at once, and the soak with 3 readers.
* **No timed run**: none of H4 is timed. Window 2 is not used.
* **s1 is checked first**: `ssh root@s1 'ps -eo pid,etime,pcpu,args
  --sort=-pcpu | head'`. A `java` that is not H4's means another session
  is timing: the step waits 10 minutes and checks again, and is skipped
  after 30 minutes (a line in the State).
* **The code**: each run names its commit. On F53 a scratch clone of `main`
  (`git clone -q /Users/f/fl/repos/bergdb repo`) under
  `/Users/f/fl/bench/016/h4-NAME/`; on s1 a `git archive` of the commit
  (section 4.3). Never the main tree.
* **The outputs**: the raw output stays in the run's directory, outside the
  repository (013-01, section 4). The summary (the command, the commit, the
  seeds, the pass line or the failure's first lines, the minutes) goes into
  `08-tests/results.md`.
* **A failure**:
  * a failure of BergDB with its seed and command is a failing test, so it
    is verified (016-06, section 2.4) once the coordinator has rerun the
    command once. It becomes a 015 entry, Kind: Fix, and is fixed by
    01:00 or goes to Frans (016-06, section 8, steps 5 and 6);
  * a failure of the environment (an out-of-memory kill on s1's 3 GB, a
    missing tool) is recorded, worked around if a line does it, and is not
    a fault of BergDB;
  * a failure that happens only on Linux or only on JDK 17 is a fault like
    any other.
* **Who**: the commands below are plain, and most of H4 is waiting, so
  an agent slot for the whole evening would be wasted:
  * the **H4 runner**: the coordinator itself, which starts each step in
    the background (`run_in_background`), checks its pass line, and fills
    in section 9; or, if the coordinator is busy, one agent at xhigh for
    F0, L0 and the smoke run of `stress.sh` (about 45 minutes), which then
    hands the queue back;
  * a failure that needs reading goes to an agent in a fix slot.
* **News**: a failure that is a fault, and the end of H4: `tools/news.sh`
  with `016-08`.
* **Stops for Frans** (`news.sh "needs a look"` and a line in 016-02's "For
  Frans to decide"; the other runs go on):
  * section 6's choice for `night.sh large` (not blocking: A meanwhile);
  * an install that would change the JDK 27 that the gates and timings use
    (F0, L0);
  * a fault from a run whose fix changes the stream format or a Pub API
    signature, needs a design choice, or is not fixed by 01:00 (016-06,
    section 8, step 5);
  * a fault on JDK 17 only whose fix is not small: fix it, or state a
    higher minimum than README's "JDK 17 or later".


## 3. The runs in time order

Times from `date`; each run starts when the one before it on its machine
has ended. F53:

| Step | When        | What                                              | Length    |
|---|---|---|---|
| F0   | now         | JDK 17 on F53, the jcstress jars, the smoke run   | 20 min    |
| F1   | after F0    | jcstress, the five tests, default mode, `main`    | 20–40 min |
| F2   | about 16:50 | JDK 17: `before-commit.sh`, the night tests       | 10 min    |
| F3   | about 17:10 | the stress programs, fresh seeds, part 1          | 2 h       |
| F4   | about 19:10 | the large conformance set without `l-big62`       | about 1 h |
| F5   | about 20:15 | the soak, ZGC with eviction, 1 measured hour      | 1.5–2 h   |
| –    | 22:00–23:30 | nothing heavy from H4: the fixes' gates           |           |
| F6   | about 23:30 | jcstress with H3's new tests, default mode        | 20–40 min |
| F7   | about 00:15 | the stress programs, fresh seeds, part 2          | 1 h       |
| –    | from 01:30  | nothing from H4 (release commit, `night.sh`, W7)  |           |

s1:

| Step | When        | What                                              | Length     |
|---|---|---|---|
| L0   | now         | JDK 17 on s1, the `unzip` shim, the code          | 15 min     |
| L1   | after L0    | JDK 27: `before-commit.sh`, `level1.sh`, night tests | 30–60 min |
| L2   | after L1    | JDK 17: `before-commit.sh`, the night tests       | about 45 min |
| L3   | after L2    | jcstress, the five tests, default mode            | about 20 min |
| L4   | after L3    | the stress programs on disk, fresh seeds          | to 23:30   |
| L5   | about 23:40 | jcstress with H3's new tests                      | about 20 min |
| L6   | about 00:30 | JDK 27: `before-commit.sh` on the latest `main`   | about 20 min |
| –    | from 01:45  | nothing from H4: s1 is W7's                       |            |

If a step ends late, the next starts late; a step that would run past its
machine's end (01:30 on F53, 01:45 on s1) is cut to fit (the stress loops
take a deadline) or skipped, with a line in the State. When F53's queue is
late, it gives way in this order:

1. F4, the large subset, is skipped first (it is the one that section 6's
   choice A repeats after window 2);
2. F5's soak is shortened (`measure=1800`), or skipped;
3. F3 and F7 are shortened, never below one hour together.

The gap from 22:00 to 23:30 gives the fixes' gates the cores. A run that
reaches into it may go on if it uses at most 5 cores (the soak, a stress
loop); jcstress and the conformance set may not.


## 4. The steps

### 4.1. F0: JDK 17 on F53, and the jcstress jars

* What: Homebrew's `openjdk@17`, without changing the JDK 27 that the
  timings and the gates use. The jcstress jars of 009 copied from s1.
* Files: none in the repository; `/opt/homebrew/opt/openjdk@17`,
  `/Users/f/fl/bench/016/jcstress-lib/`.
* Commands:

```
mkdir -p /Users/f/fl/bench/016/h4 && cd /Users/f/fl/bench/016/h4
{ java -version; brew list --versions openjdk openjdk@27; } > jdk-before.txt 2>&1
HOMEBREW_NO_AUTO_UPDATE=1 HOMEBREW_NO_INSTALL_UPGRADE=1 \
  HOMEBREW_NO_INSTALLED_DEPENDENTS_CHECK=1 brew install openjdk@17
{ java -version; brew list --versions openjdk openjdk@27; } > jdk-after.txt 2>&1
diff jdk-before.txt jdk-after.txt && echo "JDK 27 unchanged"
/opt/homebrew/opt/openjdk@17/bin/java -version
mkdir -p /Users/f/fl/bench/016/jcstress-lib
scp -q 'root@s1:/opt/bergdb-bench/009/jcs/dl/*.jar' /Users/f/fl/bench/016/jcstress-lib/
ls /Users/f/fl/bench/016/jcstress-lib/
```

* Do not `brew link` it: it stays keg-only, so the PATH's `java` stays 27.
* If Homebrew has no `openjdk@17`: Adoptium's Temurin 17 for macOS AArch64,
  unpacked into `/Users/f/fl/bench/016/jdk-17/` (as for s1 in section 4.3,
  with `os=mac&architecture=aarch64`), and `JAVA_HOME` set to its
  `Contents/Home`. No system install.
* Check: `jdk-after.txt` equals `jdk-before.txt`; `java -version` of 17
  prints `17.0.`; the five jars are there (`jcstress-core-0.16.jar`,
  `jopt-simple-4.6.jar`, `jna-5.8.0.jar`, `jna-platform-5.8.0.jar`, and
  `jcstress-result-gen-0.16.jar`, unused).
* Then the smoke run of `stress.sh` (section 4.6), about 5 minutes.
* Who: the H4 runner. When: at once. Size: 20 minutes with the smoke run.
* Stop for Frans: if the install would change JDK 27 (the diff is not
  empty): stop, restore with `brew` if a line does it, and `news.sh "needs
  a look"`.

### 4.2. F1 and F6: jcstress on F53

* What: `java/stress/jcstress/run.sh` in default mode against the jar of
  the commit. F1: the five tests on today's `main`, their first run since
  `fb0c770` (016-07, section 5.1). F6: the same with H3's new tests, from
  the jcstress agent's clone (016-07, section 5.4), after its sanity run.
* Commands (from the clone's `java/`, after `sh build.sh`):

```
sh stress/jcstress/run.sh /Users/f/fl/bench/016/jcstress-lib default > ../jcstress-F1.txt 2>&1
echo $?; sed -n '/^RUN RESULTS:/,$p' build/jcstress/out.txt | grep -E 'OK|FAILED|ERROR'
```

* `run.sh` takes `javac` and `java` from the PATH (JDK 27 on F53).
* Check: exit code 0; every test `[OK]`; the control `PlainPublication`
  sees its race on F53 (outcome 0 with a count above zero), which shows
  that the harness can see one.
* A forbidden outcome is a fault (016-07, section 5.3).
* Who: the H4 runner. When: F1 at once after F0; F6 at about 23:30, when
  the jcstress agent's sanity run passed. Size: 20 to 40 minutes each (s1
  took 16 minutes for the five on 2026-10-25; F53's time is not recorded).

### 4.3. L0: s1 prepared

* What: a JDK 17 in `/opt/bergdb-bench/jdk-17`; a stand-in for `unzip`
  (s1 has none, and `build.sh` uses it to unpack the ICU jar); the code.
* Commands:

```
S1=root@s1
ssh $S1 'ps -eo pid,etime,pcpu,args --sort=-pcpu | head -5'
ssh $S1 'set -e; cd /opt/bergdb-bench
  curl -fsSL -o jdk-17.tar.gz "https://api.adoptium.net/v3/binary/latest/17/ga/linux/x64/jdk/hotspot/normal/eclipse"
  curl -fsSL "https://api.adoptium.net/v3/assets/latest/17/hotspot?architecture=x64&image_type=jdk&os=linux&vendor=eclipse" \
    | python3 -I -c "import sys, json; print(json.load(sys.stdin)[0][\"binary\"][\"package\"][\"checksum\"])" > jdk-17.sha256
  echo "$(cat jdk-17.sha256)  jdk-17.tar.gz" | sha256sum -c
  mkdir jdk-17 && tar -xzf jdk-17.tar.gz -C jdk-17 --strip-components=1 && rm jdk-17.tar.gz
  jdk-17/bin/java -version'
```

The `unzip` stand-in, [08-tests/unzip-standin.sh](08-tests/unzip-standin.sh),
does what `build.sh`'s one call (`unzip -q -o ZIP -x 'META-INF/*'`) asks,
with python3, which s1 has. Installed on s1 from F53:

```
T=/Users/f/fl/repos/bergdb/items/016-release-2026-2/08-tests/unzip-standin.sh
ssh $S1 'mkdir -p /opt/bergdb-bench/016/bin && cat > /opt/bergdb-bench/016/bin/unzip \
  && chmod +x /opt/bergdb-bench/016/bin/unzip' < $T
```

The code of a commit C (on F53):

```
C=$(git -C /Users/f/fl/repos/bergdb rev-parse --short=7 main)
ssh $S1 "mkdir -p /opt/bergdb-bench/016/h4/$C"
git -C /Users/f/fl/repos/bergdb archive $C java tools | ssh $S1 "tar -x -C /opt/bergdb-bench/016/h4/$C"
```

* Installing `unzip` with `apt-get` would be simpler, but Q2 allowed a JDK
  only; the stand-in installs nothing.
* Check: `jdk-17/bin/java -version` prints `17.0.`; the checksum line says
  `OK`; `/opt/bergdb-bench/jdk-27/bin/java -version` still prints 27; the
  stand-in unpacks the ICU jar in a test directory (`cd /tmp/x &&
  /opt/bergdb-bench/016/bin/unzip -q -o .../java/in/icu-for-bergdb.jar -x
  'META-INF/*' && ls`).
* Who: the H4 runner. When: at once. Size: 15 minutes.

### 4.4. L1, L2 and L6: the gates and the night tests on Linux

* What: `before-commit.sh`, `level1.sh` (full) and `night.sh tests` on s1,
  with JDK 27 (L1, L6) and JDK 17 (L2). The first run of the unit tests,
  the f-tests and a level script on Linux on record (016-01, section 2).
  s1's `/bin/sh` is dash, so this also checks the scripts outside macOS's
  sh. `level2.sh` to `level4.sh` are not run: s1 has no Lean, and their
  parallel JVMs (`-Xmx2g`, `-Xmx3g`) do not fit in its 3 GB.
* Commands, on s1, in the background (`nohup`), one after another:

```
cd /opt/bergdb-bench/016/h4/$C/java
J=/opt/bergdb-bench/jdk-27          # L2: /opt/bergdb-bench/jdk-17
export JAVA_HOME=$J PATH=/opt/bergdb-bench/016/bin:$J/bin:$PATH
{ command -v java javac; java -version; javac -version; } > ../env-$(basename $J).txt 2>&1
sh before-commit.sh > ../bc-$(basename $J).txt 2>&1
sh stress/level1.sh > ../level1-$(basename $J).txt 2>&1     # L1 only
sh night.sh tests > ../night-$(basename $J).txt 2>&1
```

* `JAVA_HOME` alone is not enough: the scripts take `java` from it, but
  `build.sh` takes `javac` and `jar` from the PATH (section 8). So both are
  set, and `env-*.txt` shows which JDK compiled and ran.
* Check: `BEFORE COMMIT OK`; `LEVEL 1 OK`; the night tests' `SUCCESS`
  line. On JDK 17, `level1.sh` prints MEM without checking it (no compact
  object headers), as the script says; on JDK 27 it checks it.
* A JVM killed by the out-of-memory killer (`dmesg | tail`) is an
  environment limit: rerun that step alone, and record it.
* L6 repeats L1's `before-commit.sh` on the latest `main` (about 00:30), so
  that the evening's fixes have one Linux run before the release.
* Who: the H4 runner. When: L1 after L0; L2 after L1; L6 at about 00:30.
  Size: L1 about 30 to 60 minutes (2 cores; F53 does the three in about 6
  minutes on 10), L2 about 30 to 45 minutes, L6 about 20 minutes. All
  estimates.

### 4.5. F2: JDK 17 on F53

* Commands:

```
mkdir -p /Users/f/fl/bench/016/h4-jdk17 && cd /Users/f/fl/bench/016/h4-jdk17
git clone -q /Users/f/fl/repos/bergdb repo && cd repo/java
export JAVA_HOME=/opt/homebrew/opt/openjdk@17 PATH=/opt/homebrew/opt/openjdk@17/bin:$PATH
{ command -v java javac; java -version; javac -version; } > ../../env.txt 2>&1
sh before-commit.sh > ../../bc17.txt 2>&1; tail -3 ../../bc17.txt
sh night.sh tests > ../../night17.txt 2>&1; tail -2 ../../night17.txt
```

* Check: `env.txt` names JDK 17 for both; `BEFORE COMMIT OK`; the night
  tests' `SUCCESS` line.
* Who: the H4 runner. When: after F1, about 16:50. Size: about 10 minutes.

### 4.6. F3 and F7 (F53), L4 (s1): the stress programs with fresh seeds

* What: the stress programs of the level scripts, with seeds that no
  script uses, in loops with a deadline. Each run is the level script's own
  line (the flags, the pass line), with a new first seed and more rounds.
* The seeds: F3 from 110310000, F7 from 110320000, L4 from 110330000, so
  that no two runs repeat a seed; each loop adds the rounds it ran.
  PowerLossTest parses an `int`, so the seeds stay below 2^31.
* The runner: [08-tests/stress.sh](08-tests/stress.sh), `sh stress.sh OUT
  DEADLINE BASE MAXJOBS [PROGRAM ...]`, its usage in its header. It deals
  the programs to MAXJOBS lanes, so that at most MAXJOBS JVMs run at once;
  each lane runs its programs' chunks of rounds in turn, each from the
  program's next seed, until DEADLINE (`date +%s`); each JVM's output in
  `OUT/NAME-SEED.txt`, one line per chunk in `OUT/summary.txt`; a program
  stops at its first failed chunk. Written with this plan and checked with
  `sh -n` only, so its first use is a smoke run: `SMOKE=1`, one small chunk
  of each program, about 5 minutes, on F53 in F0's time.
* Commands (F3; F7 and L4 the same with their BASE, deadline and lanes):

```
mkdir -p /Users/f/fl/bench/016/h4-stress && cd /Users/f/fl/bench/016/h4-stress
git clone -q /Users/f/fl/repos/bergdb repo && cd repo/java && sh build.sh > /dev/null
T=/Users/f/fl/repos/bergdb/items/016-release-2026-2/08-tests/stress.sh
SMOKE=1 sh $T ../../smoke $(( $(date +%s) + 600 )) 110300000 5; tail -1 ../../smoke/summary.txt
sh $T ../../f3 $(( $(date +%s) + 7200 )) 110310000 5
```
* The programs, from `java/` of a clone at the commit, after `sh
  build.sh`, with `CP=build/bergdb.jar:build/stress`; each is started as
  the level script's line, with its flags and its pass line:

| Program            | As in                        | Pass line                |
|---|---|---|
| DagFuzz            | `level1.sh`, lines 62 to 68  | `Done: .* 0 failures`    |
| RestartStress      | `level2.sh`, line 85         | `Done: .* 0 failures`    |
| RestartStress disk | `level1.sh`, line 92         | `Done: .* 0 failures`    |
| CrashTest          | `level2.sh`, line 142        | `Done: .* 0 failures`    |
| ReclaimStress      | `level3.sh`, line 99         | `Done: .* 0 failures`    |
| ReclaimReaders     | `level4.sh`, lines 133 to 142 | `Done: .* 0 failures`   |
| EvictionInvariance | `level4.sh`, lines 88 to 100 | `EVICTION INVARIANCE OK` |
| PowerLossTest      | `level3.sh`, line 161        | `POWERLOSS OK`           |
| InterruptStress    | `level3.sh`, line 173        | `INTERRUPT STRESS OK`    |
| LargerThanMemory   | `level4.sh`, line 157        | `LARGER THAN MEMORY OK`  |

* The arguments: `firstSeed rounds` for DagFuzz, RestartStress,
  CrashTest, ReclaimStress and ReclaimReaders (with ReclaimReaders'
  variants `-Devict=every|random|budget`, `-Ddisk=1`, `-Dreaders=8`);
  one seed a run for EvictionInvariance (its configurations of
  `level4.sh`, and `-Devictseed=` the same seed); `firstSeed rounds 1500 3`
  for PowerLossTest.
* Two programs take no seed: InterruptStress (fixed seeds, 100 + i and
  7; its interleavings come from timing, so a longer run, 1,800 s, is the
  fresh part), and LargerThanMemory (`new Random(1)`): it runs with other
  sizes than `level4.sh` (`-Xmx1g -Dkeys=4000000 -Dbudget=80 -Dmaxnode=14
  -Drestarts=2`, about 4M keys, on disk). Section 8 lists both.
* Where each runs:
  * F3 (2 hours, `MAXJOBS=5`): all ten, in memory and on F53's disk.
  * F7 (1 hour, `MAXJOBS=5`, on `main` at about 00:15, with the evening's
    fixes): RestartStress, CrashTest, ReclaimStress, ReclaimReaders and
    EvictionInvariance, the ones closest to what the fixes touch, unless
    the fixes say otherwise.
  * L4 (on s1 until 23:30, `MAXJOBS=2`, `-Xmx1g` in place of `-Xmx2g` and
    `-Xmx3g`, LargerThanMemory with `-Xmx768m` as in `level4.sh`): the disk
    ones, on Linux's file system: RestartStress disk, CrashTest,
    ReclaimReaders with `-Ddisk=1`, PowerLossTest, InterruptStress (600 s),
    LargerThanMemory.
* Check: every chunk printed its pass line; `results.md` gets, per
  program, the seeds run (from, to), the rounds and the failures.
* A failure: its seed and command into `results.md` and to the coordinator
  at once (section 2, "A failure").
* Who: the H4 runner. When: F3 at about 17:10; L4 after L3; F7 at about
  00:15. Size: as their deadlines.

### 4.7. F4: the large conformance set without `l-big62`

* What: `conformance.sh large`, 2 seeds, without its configuration
  `l-big62`: 10 traces of 1,000 to 5,000 transactions (l-mixed, l-long,
  l-5000, l-hot, l-few). The large set has not run since handles (016-01,
  section 6). In 001-02 the 10 traces' checks took 2,626 s in all; the
  checker has grown since (night.sh says about 5 hours for the whole set,
  most of it the two `l-big62` traces, which once took 45 to 49 minutes),
  so about an hour with `PAR=4`, an estimate.
* Commands, in a scratch clone at `main` (the copy of the script is in the
  clone only, never committed):

```
mkdir -p /Users/f/fl/bench/016/h4-large && cd /Users/f/fl/bench/016/h4-large
git clone -q /Users/f/fl/repos/bergdb repo
cp -R /Users/f/fl/repos/bergdb/lean/.lake repo/lean/ 2>/dev/null
(cd repo/lean && lake build) > lake.txt 2>&1
cd repo/java && sh build.sh > /dev/null
sed '/^ *echo "l-big62 /d' stress/conformance.sh > stress/conformance-h4.sh
grep -c l-big62 stress/conformance-h4.sh      # 0
PAR=4 sh stress/conformance-h4.sh large 2 > ../../large.txt 2>&1; tail -3 ../../large.txt
```

* Check: `lake build` ends without error; `CONFORMANCE OK`, with 10 traces
  listed.
* Who: the H4 runner. When: after F3, about 19:10; if it runs past 20:30,
  stop it (`kill` its JVMs and the checker) and record the traces that
  finished. Size: about 1 hour.

### 4.8. F5: the soak

* What: `soak.sh`, Level 3 on disk with readers, restarts and reclaim's
  cuts, under ZGC with eviction (Soak's database is built with `noEvict()`,
  so eviction needs `-Devictbudget`), with a fresh seed. 016-01 asked for
  two hours; tonight one measured hour fits, with P4's settings of 009-03
  and 006-09.
* Commands, in a scratch clone at `main`, after `sh build.sh`:

```
cd /Users/f/fl/bench/016/h4-soak/repo/java
HEAP=8g GC=zgc JFLAGS="-Devictbudget=1600000000" sh stress/soak.sh h4-soak \
  seed=110311 rate=200 warmup=300 warmupmax=1800 measure=3600 extend=900 \
  restarts=2 mincuts=2 > ../../soak.txt 2>&1
echo $?; tail -3 build/soak/h4-soak/stdout.txt
```

* Check: exit code 0 and `SOAK OK`. The pauses in `result.json` are not
  judged: the machine is not quiet.
* Who: the H4 runner. When: after F4, about 20:15; it must end by about
  22:15 (warm-up up to 30 minutes, 60 measured, up to 15 more). Size: 1.5
  to 2 hours.

### 4.9. L3 and L5: jcstress on s1

* As section 4.2, on s1 (x86, which hides most reorderings, so F53's runs
  count more; 009-03, section 2), with the jars of
  `/opt/bergdb-bench/009/jcs/dl` and `PATH=/opt/bergdb-bench/jdk-27/bin:$PATH`.
  L5 copies the new tests from the jcstress agent's clone with `scp` into
  the s1 copy's `java/stress/jcstress/`.
* Check: exit code 0, every test `[OK]`. Size: about 20 minutes each.


## 5. What fits tonight, and what not

Fits, and planned above: the JDK 17 installs, its `before-commit.sh` and
night tests on F53 and s1; jcstress twice on each machine; the Linux runs
(the gates, `level1.sh`, the night tests); the stress programs with fresh
seeds, 3 hours on F53 and about 4 on s1; a soak of one measured hour; the
large conformance set without `l-big62`.

Does not fit: `night.sh large` (about 6 hours); the soak's two measured
hours; `level2.sh` to `level4.sh` on JDK 17 (they run on JDK 27 in the
02:10 `night.sh` on the release commit); the level scripts on s1 beyond
`level1.sh`.


## 6. Decision for Frans: `night.sh large`

It takes about 6 hours, and F53 has no 6 hours without other heavy runs
before 01:30, nor after it (the release commit, `night.sh` at 02:10, window
2's timed runs to 06:15).

* **A. Tonight the large set without `l-big62` (F4, about an hour); the
  whole of `night.sh large` on the release commit when window 2 ends,
  about 06:15** (recommended). The ten smaller traces check handles at the large set's
  scale tonight; the two `l-big62` traces (node size 62, 3,000 keys, the
  slowest case) and the rest follow on the tag. A failure there is a fault
  of 2026.2 found after its release: it goes into 2026.2's post-release
  notes, as 2026.1's readme provides, and to Frans.
* **B. `night.sh large` from about 17:00 to 23:00**, as the evening's one
  heavy run, on the code of 17:00. F3 to F5 then do not run on F53 (the
  stress programs run on s1 only), and the evening's fixes are not in it.
* **C. Not for 2026.2.** The notes say that the large set did not run with
  handles.

The H4 runner goes on with A unless Frans says otherwise; the choice is a
line in 016-02's "For Frans to decide".

A's run from about 06:15, in a scratch clone at the tag, or at the release
commit A if the tag is not yet set (`night.sh` clones the HEAD of the
repository it is in, and copies its `lean/.lake`):

```
mkdir -p /Users/f/fl/bench/016/h4-large-tag && cd /Users/f/fl/bench/016/h4-large-tag
git clone -q /Users/f/fl/repos/bergdb repo && cd repo
git checkout -q -b h4-large release-2026.2     # or A's commit
cp -R /Users/f/fl/repos/bergdb/lean/.lake lean/ 2>/dev/null
sh java/night.sh large > ../large.txt 2>&1; tail -3 ../large.txt
```

* Check: `NIGHT OK` in `java/build/night/RUN/report.txt` of the clone, with
  the line `conformance-large ok`.
* It must not overlap the next 02:10 `night.sh`; it ends about 12:15. Its
  `news.sh` line lands in the clone's `news.md`; the coordinator, or
  Frans, copies the result to the main tree's news and to 016-02.
* Who: started by the coordinator before it ends its night, or by Frans.
  Size: about 6 hours, unattended.


## 7. The C clone's cross tests: dropped

Frans, 15:31: "The C code does not need to be updated for 2026.2 in this
work. Only Java code will be included in the release." After 005-79 the
Java take is in integers while the C clone's is not, so their bytes differ
by design, and the cross tests (`items/012-bergdb-c/c/test/cross/cross.sh`)
would report that difference, not a fault. The step is dropped. Running
`cross.sh` without `C=`, Java against Java, adds nothing that `night.sh`'s
determinism checks do not.


## 8. Found while planning

Not numbered; for the coordinator to register after the release:

* `build.sh` takes `javac` and `jar` from the PATH (or `JAVAC`, `JAR`), not
  from `JAVA_HOME`, though `before-commit.sh`, `night.sh` and the level
  scripts say "Set JAVA_HOME or PATH for the JDK" and take `java` from
  `JAVA_HOME`. A run with only `JAVA_HOME` set to 17 compiles with the
  PATH's JDK 27 and runs on 17. `stress/jcstress/run.sh` takes both from
  the PATH.
* `build.sh` needs `unzip`, which a minimal Linux (s1, Ubuntu 26.04) does
  not have; README.md names only the JDK. The JDK's `jar` could do it.
* InterruptStress and LargerThanMemory take no seed, so a run with a fresh
  seed is not possible; a `-Dseed` property would allow it.
* The jcstress jars are kept only on s1 (`/opt/bergdb-bench/009/jcs/dl/`);
  `run.sh` names no place for them on F53.
* 009-02, section 3.5 planned jcstress tests of a re-resolve against an
  eviction and of two loaders; they were not made (016-07, section 5.2).


## 9. State

**Not started** (2026-11-03, when this plan was written). A fresh agent
resumes from this table: the first row not done on each machine is the
next. The H4 runner fills it in, with the times from `date` and the
commit of each run.

| Step | Machine | Commit | Started | Ended | Result |
|---|---|---|---|---|---|
| F0   | F53     |        |         |       |        |
| F1   | F53     |        |         |       |        |
| F2   | F53     |        |         |       |        |
| F3   | F53     |        |         |       |        |
| F4   | F53     |        |         |       |        |
| F5   | F53     |        |         |       |        |
| F6   | F53     |        |         |       |        |
| F7   | F53     |        |         |       |        |
| L0   | s1      |        |         |       |        |
| L1   | s1      |        |         |       |        |
| L2   | s1      |        |         |       |        |
| L3   | s1      |        |         |       |        |
| L4   | s1      |        |         |       |        |
| L5   | s1      |        |         |       |        |
| L6   | s1      |        |         |       |        |

Unfinished in this plan: the stress runner `08-tests/stress.sh` is
written but has not run; its smoke run comes first (section 4.6). The
lengths on s1, of F1, F4 and F5 are estimates.


## 10. Done when

* Each step of section 9 has a result, or a line saying why it was
  skipped; `08-tests/results.md` holds the summaries.
* Each failure of BergDB is a 015 entry, and is fixed or with Frans.
* Section 6's choice is made, and, if A, `night.sh large` on the release
  commit has its report, read and summarized in 016-02.
* The JDK 17 and Linux results are in a form the notes can cite: tested on
  JDK 27 and 17, on macOS and Linux, with the commits.
