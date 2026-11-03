016-09. Plan: the release
=========================

Created 2026-11-03 by Frans Lundberg. Status: planned, not started.

The plan for W6 of 016-01 (section 5): the release itself, by 008-01's
steps, with 016-01's changes. It fits the one night of the coordinator's
timeline (Frans, 15:40: "finish this work by 07:00 tomorrow"): commit A by
01:45, `night.sh` at 02:10 as its gate, the quiet block in window 2, and
commit B and the tag by 07:00. Frans, 15:31: "Only Java code will be
included in the release"; the Lean model and the C clone are tools, not
outputs, so the release's files are the Java jar, the source and the
Javadoc.

Who: an agent (the tools agent, which also prepares 016-10) writes the
scripts in the evening, in `/Users/f/fl/bench/016/release/` (R below). The coordinator makes the
commits, the tag, and starts the night's runs. 016-10 (the numbers) and
016-03 (the notes) feed into steps R8 and R9.


## 1. Facts found on 2026-11-03

* `BuildInfo` (`java/src/bergdb/core/BuildInfo.java`, lines 19 to 29)
  says `RELEASE` "2026.2-dev", `RELEASE_INT` 262, `BUILD` "2026.2-dev".
  So commit A changes two strings, and `RELEASE_INT` stays 262.
* 2026.1's commit A (`a42947c`) changed `BuildInfo.java` and two lines of
  `docs/levels.md`. Its tag is annotated: "BergDB 2026.1, internal release,
  2026-10-25", by Frans Lundberg.
* 2026.1's files: `bergdb-2026.1.jar` (3.2 MB), `bergdb-2026.1-src.zip`
  (6.9 MB), `baseline.zip` (0.96 MB), `SHA256SUMS`, `readme.md`.
* **The source zip would hold the last release.** `git archive` of A
  includes `releases/2026.1/`, about 11 MB of jar and zips, so 2026.2's
  source zip would be about 18 MB, and each later release's would hold all
  earlier ones (decision R-1, section 4).
* `java/javadoc-pub.sh` builds the Pub API's Javadoc (`bergdb.pub` and
  `bergdb.pub.util`) into `java/build/javadoc-pub/` with doclint, and
  prints `JAVADOC PUB OK` or `JAVADOC PUB FAILED`.
* `night.sh` clones HEAD of the main tree at its start (02:10) and gates
  that commit; its report names it (`Commit:`). It took 41 minutes on
  2026-11-03 (8 steps, `NIGHT OK`).
* JDKs: F53 has Homebrew's OpenJDK 27 (`/opt/homebrew/opt/openjdk`), and
  no JDK 17 at 15:48. s1 has `/opt/bergdb-bench/jdk-27` and
  `/opt/bergdb-bench/jdk-17` (17.0.21, with `javac`, installed today at
  15:43), and `git`.
* 2026.1's tests on the jar ran `bergdb.dev.Unit`, `F` and `Night` with
  `-ea`, in parallel, from the jar alone, and read `^(SUCCESS|FAILURE)`
  from each output (`baseline/tools/f53.sh`).


## 2. The files of `releases/2026.2/`

* `readme.md`: the release notes (016-03).
* `bergdb-2026.2.jar`: `java/build.sh`'s jar of A: the production code,
  `src-dev` (Props, the tests, the demos), ICU 50; class files for Java 17.
* `bergdb-2026.2-src.zip`: `git archive` of A, in `bergdb-2026.2/`.
* `bergdb-2026.2-javadoc.zip`: `javadoc-pub.sh`'s output, in
  `bergdb-2026.2-javadoc/` (D6).
* `baseline.zip`: the outputs of the gates, the tests on the jar and the
  numbers (016-10), with the scripts in `tools/`; at most about 10 MB,
  without the GC logs if it would pass that.
* `SHA256SUMS`: of the jar and the three zips.


## 3. The steps

Times are tonight's, 2026-11-03 to 04, from `date`. At a glance, with
016-03, 016-04 and 016-10:

| Time           | Who            | What                                          |
|----------------|----------------|-----------------------------------------------|
| 17:00 to 22:30 | tools agent    | 016-10's N1 to N5                             |
| 22:30 to 01:15 | tools agent    | R0, the release's scripts                     |
| 17:00 to 01:20 | notes agent    | 016-04's D1 to D6; 016-03's N1 to N4          |
| evening        | 016-08's agent | R0b, JDK 17 on F53 and s1                     |
| 01:25 to 01:45 | coordinator    | R1, the freeze; R2, commit A                  |
| 01:45 to 02:07 | coordinator    | R3, the jar; R4, F53's tests; 016-10's N6, N8 |
| 01:52 to 04:30 | s1, unattended | R5: the tests on the jar, then 016-10's runs  |
| 02:10 to 02:55 | launchd        | R6, `night.sh` on A                           |
| 03:00 to 05:50 | conductor      | 005-65, 005-52, then 016-10's F53 steps       |
| 06:05 to 06:55 | coordinator    | R8, the files; R9, commit B and the tag       |
| by 07:00       | coordinator    | R10, news                                     |

One tools agent does 016-10's preparation and R0, about 8 agent-hours;
the coordinator may give R0 to a fresh agent at 22:30, with this plan's
State, or start R0 earlier in a second slot if one is free. The
coordinator's own steps take about 1.5 hours.

### R0. The scripts (tools agent, 22:30 to 01:15; about 2.75 hours)

In `R/`, smoke-tested on a candidate jar (`java/build.sh` in a clone of
`main`, `R/cand`). Each script prints one result line and exits non-zero
on failure.

* **`build-a.sh A`** (R3). `git clone /Users/f/fl/repos/bergdb R/rel`,
  `git -C R/rel checkout --detach A`; `git -C R/rel status --porcelain` is
  empty; `java/build.sh`; `java -cp java/build/bergdb.jar
  bergdb.core.BuildInfo` prints `release: 2026.2` and `releaseInt: 262`;
  `java/javadoc-pub.sh` prints `JAVADOC PUB OK`; then, in `R/out/`:
  * `bergdb-2026.2.jar`, a copy of `java/build/bergdb.jar`;
  * `bergdb-2026.2-javadoc.zip`, of `java/build/javadoc-pub/` under the
    directory name `bergdb-2026.2-javadoc/`;
  * `bergdb-2026.2-src.zip`, by `git archive --format=zip
    --prefix=bergdb-2026.2/` of A, without `releases/2026.1/` (decision
    R-1); check with `unzip -l` that it has `java/build.sh` and no
    `releases/2026.1/`.
  * Prints `BUILD A OK` and the jar's SHA-256.
* **`tests-f53.sh JAR`** (R4). For JDK 27 (`/opt/homebrew/opt/openjdk`),
  then JDK 17 (`/opt/homebrew/opt/openjdk@17`): `Unit`, `F` and `Night`
  with `java -ea -cp JAR`, each in a directory of its own
  (`R/jartest/JDK/CLASS/`), the three in parallel; each started with `&`,
  its PID kept, and waited for by `wait PID` (008-01's lesson: a bare
  `wait` also waited for the script's own `caffeinate` and hung for an
  hour). It starts no `caffeinate`. It reads each output's
  `^(SUCCESS|FAILURE)` line and the test counts, and runs the user's
  program (below) with each JDK. Prints `TESTS F53 OK` with the counts.
* **`userprog/UserProgram.java`**, the user's program (W6). Written from
  the Javadoc zip only, using only `bergdb.pub` and `bergdb.pub.util`
  (`Factory.database()`, `DatabaseBuilder.dir`, `start`, `Database`,
  `Connection`, `Transaction`, `close`):
  * `create DIR`: starts a new database in an empty directory, commits
    1,000 KVs in 10 transactions, `sync()`s and closes it, in a
    try-with-resources block;
  * `check DIR`: starts it again in a new JVM, reads the 1,000 values and
    compares them, writes one more, closes;
  * prints `USERPROG OK` or the first difference, and exits 1 on one.
  * Built with `javac --release 17 -cp bergdb-2026.2.jar
    UserProgram.java`, nothing else on the class path; run with each JDK.
* **`s1-chain.sh`** (R5), started on F53, which:
  * checks s1 with `ssh root@s1 'ps -eo args'`: no `java`, no
    `sb.sh`; if busy, waits up to 30 minutes, then exits 2;
  * copies the jar, the user's program, 016-10's tools for both jars
    (`tools/2026.1`, `tools/2026.2`), `sb.sh` and `s1-w7.sh` to
    `/opt/bergdb-bench/016/rel/` with `scp` (016-08's H4 uses `016/h4/` and
    `016/bin/`), and checks the jar's SHA-256
    there;
  * starts, with `ssh ... nohup sh /opt/bergdb-bench/016/rel/run.sh DEADLINE >
    /opt/bergdb-bench/016/rel/chain.txt 2>&1 &`, a script `run.sh` that runs
    `Unit`, `F` and `Night` with `-ea`, one after another (2 CPUs, 3.8 GB),
    with JDK 27 and then JDK 17, the user's program with each, writes
    `S1 TESTS OK` or `S1 TESTS FAILED`, then runs 016-10's `s1-w7.sh
    DEADLINE`;
  * returns at once; its output names the remote PID.
* **`finish.sh`** (R8). Makes `R/out/baseline.zip` from `R/out/baseline/`
  (`gates/`, `f53/`, `s1/`, `tools/`), drops `*.gc.log` if the zip passes
  10 MB, writes `SHA256SUMS` with `shasum -a 256` of the jar and the three
  zips, and checks it with `shasum -a 256 -c SHA256SUMS`. Prints
  `FINISH OK` and the sizes.

Check of R0: `build-a.sh` on a candidate commit (with `BuildInfo` set in
the clone only, not committed), `tests-f53.sh` on its jar with JDK 27 and,
once installed, JDK 17, and `run.sh`'s test part on s1 (with SMOKE=1 for
`s1-w7.sh`), each print their OK line. The candidate's runs are not timed
and may run in the evening. s1 is 016-08's until 01:45 (its section 3,
H4's queue, with jobs at `-Xmx1g` on 3.8 GB): the s1 smoke runs only in a
gap of that queue, after `ps` shows no `java`, with the user's program and
`s1-w7.sh`'s SMOKE (a few minutes, `-Xmx512m`). Without a gap it is
skipped, and the chain's first minutes at 01:52 are its smoke: a failure
there shows in `chain.txt` by about 02:00.

### R0b. JDK 17 on F53 and s1 (016-08's agent, in the evening)

* 016-08 installs both (Q2: yes): Homebrew's `openjdk@17` on F53, or, if
  Homebrew has none, Temurin 17 in `/Users/f/fl/bench/016/jdk-17/`; and
  `/opt/bergdb-bench/jdk-17` on s1 (there since 15:43, 17.0.21).
* The tools agent checks, and sets `tests-f53.sh`'s JDK 17 path to the
  one installed: `JDK17/bin/java -version` prints 17.
* If either cannot be had, the notes say "tested on JDK 27 only", and the
  release goes on.

### R1. The freeze (coordinator, 01:25 to 01:35)

* 016-01, section 6's exit and 016-01, section 4.1 are met, or what is not
  met is in the notes with Frans's agreement, or is a stop for him.
* `main` is clean (`git status --porcelain` shows only other sessions'
  untracked files, which are left alone), and the last commit passed
  `java/before-commit.sh`.
* `releases/next.md`, 2026.1's post-release notes (016-03, N1, N3 and N4)
  and 016-04's documents are committed; the draft of
  `releases/2026.2/readme.md`, all but the numbers, is ready in
  `/Users/f/fl/bench/016/notes/out/` (016-03, N2), and goes into commit B.
* Every agent has stopped: from 01:45 until the block's end, only the
  release's own runs use F53.

### R2. Commit A (coordinator, 01:35 to 01:45)

* In a clone of `main`: `BuildInfo.java`'s `RELEASE` "2026.2" and `BUILD`
  "2026.2.YYMMDD.HHMM", the date and time from `date` at that moment
  (for example `2026.2.261104.0138`). Nothing else.
* Gate: `java/before-commit.sh` prints `BEFORE COMMIT OK` (about 2
  minutes).
* Check that `java/` and `lean/` in `main` are still what was gated
  (Frans may commit meanwhile: 013-01, section 4); copy the file in, stage
  it alone, and commit in Frans's name with no AI attribution: "Release
  2026.2: BuildInfo says 2026.2 (version int 262, build 2026.2.YYMMDD.HHMM),
  where it said 2026.2-dev".
* No commit to `main` after A until `night.sh` has cloned it (02:10).

### R3. The jar (coordinator runs `build-a.sh A`, 01:45 to 01:50)

* `BUILD A OK`; the jar's SHA-256 into 016-02.

### R4. The tests on the jar on F53 (coordinator starts them, 01:50 to 02:05)

At the same time, in the background, each waited for by its PID:

* `tests-f53.sh R/out/bergdb-2026.2.jar` (about 7 minutes);
* 016-10's `prep-a.sh` (step N6) and StreamDigest (N8), about 5 minutes.

Check: `TESTS F53 OK`, `PREP A OK`, and the digests' modes agree. All
end by 02:07, so that nothing runs beside `night.sh`. If the JDK 17
runs are not done by 02:05, they are stopped and rerun at 06:05 (R8).

### R5. s1's chain (coordinator starts `s1-chain.sh`, about 01:52)

* It starts once `prep-a.sh` (016-10, N6) has made `tools/2026.2`, about a
  minute after R4 begins, as it copies those tools to s1.
* The tests on the jar on s1 with JDK 27 and 17 (about 25 minutes), then
  016-10's `s1-w7.sh` (about 2 hours), with `DEADLINE` 05:15.
* Check in the morning: `chain.txt` has `S1 TESTS OK` and `S1 W7 DONE`.

### R6. `night.sh` on A (launchd, 02:10 to about 02:55)

* The release's gate. Check, at its end, before the block begins (the
  coordinator reads one file and is idle again):
  `java/build/night/2026-11-04-0210/report.txt` ends with `NIGHT OK`, and
  its `Commit:` line is A.
* `NIGHT FAILED`, or another commit than A: a stop for Frans. No tag and
  no commit B; the files stay prepared in `R/out/`; `news.sh "needs a
  look"` and a line in 016-02's "For Frans to decide" (016-01, section 8).
  The block still runs, so that the numbers are there when he decides.

### R7. The quiet block (conductor, about 03:00 to 05:50)

016-10, step N7. The coordinator is idle.

### R8. The files (coordinator, 06:05 to 06:35)

* 016-10's morning step (N9): s1's outputs fetched, `tables.md` written.
* `R/out/baseline/`:
  * `gates/`: `night.sh`'s `report.txt` and each step's output from
    `java/build/night/2026-11-04-0210/`, without the trace logs if they
    make the zip too large;
  * `f53/`: the tests on the jar, the user's program, `digests.txt`
    (016-10, N8), the conductor's `results.txt` and each W7 step's output;
  * `s1/`: `chain.txt` and the s1 outputs;
  * `tools/`: the scripts of R0 and of 016-10.
* The Lean axioms (as 2026.1's verification; a check, not an output): in a
  clone of A with `lean/.lake` copied from the main tree, as `night.sh`
  does, the `#print axioms` file of lean/README.md, run with `lake env
  lean`, at most 10 minutes. Each theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound`. If it does not run in 10 minutes,
  the notes say that it was not checked; if a theorem has `sorryAx` or
  another axiom, it is a stop for Frans.
* `sh R/finish.sh`: `FINISH OK`.
* 016-03, step N6: the numbers, the verification and the identity into
  `readme.md`; `releases/next.md` folded and emptied.

### R9. Commit B and the tag (coordinator, 06:35 to 06:55)

* In a clone of `main`:
  * `releases/2026.2/`: `readme.md`, the jar, the three zips,
    `SHA256SUMS`;
  * `releases/next.md`, emptied (016-03);
  * `releases/2026.1/readme.md`'s post-release notes, if not committed
    before (016-03, W2);
  * README.md's line on `releases/` and docs/log.md's entry (016-04);
  * 016's readme log and 016-02;
  * `BuildInfo.java`: `RELEASE` "2026.3-dev", `RELEASE_INT` 263, `BUILD`
    "2026.3-dev".
* Gate: `java/before-commit.sh` prints `BEFORE COMMIT OK`.
* Check that `main` is still what was gated; commit B in Frans's name, with
  a path list.
* The tag, on A: `git tag -a release-2026.2 A -m "BergDB 2026.2, internal
  release, 2026-11-04"`. Check: `git cat-file -t release-2026.2` prints
  `tag`, and `git rev-parse 'release-2026.2^{commit}'` is A.
* Nothing is pushed; Frans pushes (016-01, section 3).

### R10. News (coordinator, by 07:00)

* `tools/news.sh OK coordinator "Release 2026.2 tagged on A; releases/2026.2/
  committed in B (016-09)."`, or `needs a look` with what stopped. Then
  013-01, section 8's summary.


## 4. Decisions

* **R-1. The source zip without `releases/2026.1/`.** Recommended: yes.
  The zip is about 7 MB instead of 18, and a later release does not hold
  every earlier one. The earlier release stays in the repository and its
  tag. The alternative is the whole tree, as 2026.1 did, which was then
  small.
* **R-2. If commit A is late.** If A is not committed by 01:50, the 02:10
  `night.sh` runs on the commit before it, whose code differs from A only
  in `BuildInfo`'s two strings.
  * Recommended: commit A at once after `night.sh` has cloned (after
    02:11), gated by `before-commit.sh`; run R3 and R4 after `night.sh`
    ends, before the block, which then starts about 15 minutes later; the
    notes say that `night.sh` gated A's parent, the same code but for the
    version strings.
  * The alternative is a stop: no release until a `night.sh` has run on A
    itself, the next night or by hand (45 minutes on a quiet F53).
* **R-3. The JDK 17 runs on F53**, if R4 is short of time: stop them at
  02:05 and run them at 06:05 (recommended), rather than let them run
  beside `night.sh`.


## 5. What is a stop for Frans

* `night.sh` on A not `NIGHT OK` (R6).
* A test on the jar that fails, on any machine or JDK (R4, R5). On JDK 17
  only, the notes may instead say that JDK 17 is not supported; that is
  his choice.
* A Lean theorem of the release's list with an axiom beyond the standard
  three (R8).
* `SHA256SUMS` that does not check (R8).

Each stop gets `news.sh "needs a look"` and a line in 016-02's "For Frans
to decide". The other steps go on, up to commit B and the tag, which
wait.


## 6. 2026.1's lessons, applied

* The F53 script hung for an hour on a `wait` that also waited for its own
  `caffeinate` (008's log): every script waits for each child by its PID
  and starts no `caffeinate` (R0).
* The quiet check waited half an hour for other work: the block is in
  window 2, when the agents have stopped (R1), and the steps are ordered
  by priority, so that a late start cuts the last ones (016-10, section 2).
* It took three hours, not two: everything that can be made before A is
  made and smoke-tested in the evening (R0), and the morning's steps are
  scripts (R8).


## 7. Done when

* The tag `release-2026.2` is on A, annotated, local.
* Commit B holds `releases/2026.2/` with its six files, the emptied
  `next.md`, README's line, docs/log.md's entry, and `BuildInfo` at
  2026.3-dev and 263.
* `night.sh` printed `NIGHT OK` on A, and the tests on the jar passed on
  F53 with JDK 27 and 17, and on s1 with JDK 27 and 17, or the notes say
  which did not run.
* `shasum -a 256 -c SHA256SUMS` passes in `releases/2026.2/`.
* `news.md` has the summary.


## 8. State

2026-11-03, 16:05: the plan is written; nothing is prepared. Open:
decisions R-1 to R-3 (the coordinator's, recommendations above); the
tools agent's start (recommended: from about 17:00 or the first free
slot, 016-10's N1 to N5 first, then R0, done by 01:15); JDK 17 on F53,
which 016-08 installs (R0b).

2026-11-03, 16:05: R-1, R-2 and R-3 yes (the coordinator). R0b done by
016-08 at 15:43: `/opt/homebrew/opt/openjdk@17` (17.0.21.0.3) on F53,
`/opt/bergdb-bench/jdk-17` on s1.

2026-11-03, 16:30, the tools agent: R0's scripts are written in
`/Users/f/fl/bench/016/release/` (R): `build-a.sh`, `tests-f53.sh`,
`userprog/UserProgram.java`, `s1-chain.sh` with s1's `run.sh`,
`collect.sh` (R8's files and 016-10's N9), `finish.sh`, and `axioms.sh`
(R8's Lean check). `build-a.sh` rehearsed on a scratch commit with
BuildInfo set (`R/cand`, not in main; outputs in `R/rehearsal/`):
`BUILD A OK`; the source zip is 12 MB without `releases/2026.1/` (the
tree has grown since 2026.1's 6.9 MB), the Javadoc zip 4.1 MB. The user's
program runs on the candidate's jar with JDK 27 and 17. The other
rehearsals follow.

2026-11-03, 16:52, the tools agent:

* `s1-chain.sh` with `SMOKE=1` (16:28 to 16:31): the files copied and
  checked, `run.sh` started; the user's program OK with JDK 27 and 17,
  `s1-w7.sh`'s smoke OK. Unit FAILED on s1 with both JDKs
  (`CapacityTester.testBudgetLoweredAndRaisedUnderReads`, then the
  stopped-databases check), passed a third run and alone; 016-08's runs
  were on s1 at the same time. Handed to the coordinator (a 015 entry).
  Fixed: `s1-chain.sh` waited for `run.sh` to end (the background list
  kept ssh's channel); it now returns at once.
* `axioms.sh` on main's HEAD: `AXIOMS OK: 44 theorems` in 40 s (all three
  lists of lean/README.md, `Check.Steps` included).
* Also written: `set-buildinfo.sh CLONE VERSION INT` (A: `2026.2 262`,
  B: `2026.3-dev 263`), tested in a scratch clone; `stage-b.sh CLONE`
  (R9's release files and BuildInfo in a clone of main).
* 17:04: `tests-f53.sh` on the scratch A's jar: `TESTS F53 OK: JDK 27
  (187 s): Unit 1098; F 78; Night 8; userprog OK; JDK 17 (204 s): Unit
  1098; F 78; Night 8; userprog OK`, with the other agents' load.
* 17:08: `collect.sh` and `finish.sh` rehearsed (`R=R/rehearsal`, the
  smoke outputs, last night's `night.sh` report): `FINISH OK`, the
  baseline zip 0.14 MB with the smoke outputs, `SHA256SUMS` checks.
* `rehearse.sh` repeats 01:45 to 02:00 (build-a, prep-a with `MARK=0`,
  digests; `JARTESTS=1` also the jar's tests) on main's current HEAD in
  scratch clones, about 6 minutes; run again during the evening, so
  that a commit that breaks a tool is found before the freeze.
* 17:18: `rehearse.sh` on main's `437cb48`: `REHEARSAL OK` (BUILD A OK,
  PREP A OK 5 of 5, DIGESTS OK).

2026-11-03, 17:20, the tools agent stopped (usage). R0 is done; nothing
of it runs. Left, for a fresh agent after 19:30 or the coordinator:

1. Before the freeze, after the last fixes (about 00:45), once no gate
   runs: `sh /Users/f/fl/bench/016/release/rehearse.sh` (about 6 minutes;
   `JARTESTS=1` adds the jar's tests, 7 more). It must print `REHEARSAL OK`;
   a failure names the script and the step (as 005-79 broke ScaleBench's
   compile).
2. The commands from 01:35 and from 06:05, in order (each prints one
   result line):
   * R2: in a clone of main, `sh /Users/f/fl/bench/016/release/set-buildinfo.sh CLONE 2026.2 262`;
     `java/before-commit.sh`; commit A as R2 says.
   * R3: `sh /Users/f/fl/bench/016/release/build-a.sh A` → `BUILD A OK`.
   * R4, N6 and N8 together, in the background:
     `STOP_AT=$(date -j -f "%Y-%m-%d %H:%M" "2026-11-04 02:05" +%s) sh /Users/f/fl/bench/016/release/tests-f53.sh /Users/f/fl/bench/016/release/out/bergdb-2026.2.jar`
     (`TESTS F53 OK`, about 7 minutes; `INCOMPLETE`: run again at 06:05
     with `JDKS=17`); `sh /Users/f/fl/bench/016/numbers/prep-a.sh`
     (`PREP A OK: 5 of 5 steps READY`, about 4 minutes);
     `sh /Users/f/fl/bench/016/numbers/digests.sh` (`DIGESTS OK`).
   * R5, once prep-a's tools are made (it waits for them):
     `sh /Users/f/fl/bench/016/release/s1-chain.sh` → `S1 CHAIN STARTED`.
   * R8 at 06:05: `sh /Users/f/fl/bench/016/release/collect.sh` (`COLLECT
     OK`; it fetches s1's outputs and writes the tables);
     `sh /Users/f/fl/bench/016/release/axioms.sh A` (`AXIOMS OK: 44
     theorems`); `sh /Users/f/fl/bench/016/release/finish.sh` (`FINISH OK`).
   * R9: in a clone of main, `sh /Users/f/fl/bench/016/release/stage-b.sh CLONE`
     (`STAGE B OK`: the six files in releases/2026.2/, BuildInfo at
     2026.3-dev and 263); the coordinator's files of B; before-commit;
     commit B; the tag on A.
3. Not rehearsed: s1's tests on the jar in full (only the smoke, Unit
   alone, at 16:28, with 016-08's runs beside it: the CapacityTester
   failure handed to the coordinator), and `run.sh`'s F and Night on s1.
