018-09. Plan: the release
=========================

Created 2026-11-06 by Frans Lundberg. Status: the scripts are written and
rehearsed (2026-11-06, 13:00); the release is not started.

The plan for W5 of 018-01 (section 7): release 2026.3, made as 2026.2 was
(016-09, by 008-01's steps), with 016-09's scripts adapted to 2026.3. Frans,
2026-11-06, 12:14: "Hopefully release 2026.3 can be made tomorrow in the
morning. That is our goal." The frame is the coordinator's plan for the
night (006-13, section 5): `main` frozen at 20:15, the release's commit A
about 20:30, `night.sh large` on A from 20:45 (about 6 hours, the gate of
R6), and in the morning, at Frans's word, the files (R8), commit B and the
tag (R9).

The scripts are in `/Users/f/fl/bench/018/release/` (S below). Their
outputs go to `$S/out/`, the clone of A to `$S/rel/`. Each script prints one
result line, and exits non-zero on a failure. They are copied into
`baseline.zip`'s `tools/`.


## 1. What changed from 2026.2's procedure

* **No numbers.** 016-10's W7 (the runs in turns, the quiet block) is not
  part of 2026.3's release: W7's rerun moved to another night (006-13).
  No `prep-a.sh`, no ScaleBench or Props, and s1's chain runs only the
  tests on the jar. The notes say that the numbers come later.
* **The gate is `night.sh large`** (018-01, "Ready", 2), started by the
  coordinator's night chain at 20:45
  (`/Users/f/fl/bench/006-13/night/chain.sh`, under the gate lock).
  `collect.sh` requires its `conformance-large` step.
* **StreamDigest against 2026.2's decided digests** (018-01, "Ready", 3),
  `digests.sh`: A's StreamDigest on A's jar in its four modes, and on
  2026.2's release jar in 2026.2's three modes, and the comparison with
  `releases/2026.2/baseline.zip`'s `f53/digests.txt`. Each configuration
  whose decided digests differ is listed with the bullets of
  `releases/next.md` that name it (`next-match.py`).
* **Commit A and commit B by script**: `commit-a.sh` and `commit-b.sh`
  gate in a clone under the gate lock, commit in Frans's name, and bring
  the commit into `main` by a fast-forward only if `main`'s HEAD has not
  moved (2026.2's coordinator did these steps by hand).
* **A morning remake of A** (Frans, 2026-11-06, 12:31: a Core fault found
  tonight is fixed at once, and the release's commit is made again from
  `main` in the morning, with `night.sh` on it): `commit-a.sh` makes A
  again when `main`'s `BuildInfo` already says 2026.3 (only the build
  changes); `s1-chain.sh` takes `CLASSES="Unit F"`; `collect.sh` takes
  `NIGHT_LARGE`, the large run on the first A (section 4).
* **The release notes by script**: `notes.sh` fills
  `$S/notes/readme-template.md` (2026.2's form) from A's `releases/next.md`
  and the runs' outputs. A part it cannot fill is a `[[ ... ]]` marker,
  and `stage-b.sh` refuses notes with a marker.
* **The user's program** uses 2026.3's `create(p)` and `open(p)` (015-05;
  `dir(p)` is gone), and checks that `open(p)` refuses an empty directory
  and writes nothing.
* **The source zip** leaves out both earlier releases' directories,
  `releases/2026.1/` and `releases/2026.2/` (016-09, R-1).
* **2026.2's lessons kept**: every script waits for its children by PID
  and starts no `caffeinate` (2026.1); `s1-chain.sh` returns at once; s1's
  tests run with `java.io.tmpdir` on the disk (015-11); `STOP_AT` stops the
  F53 tests before another run starts (016-09, R-3).


## 2. The scripts

| Script                | Step | What                                                      | Time   |
|-----------------------|-----|-----------------------------------------------------------|--------|
| `freeze.sh`           | R1  | main, BuildInfo, the gate lock, java runs, open entries   | 5 s    |
| `commit-a.sh`         | R2  | A gated in a clone under the lock, ff into main           | 3 min  |
| `build-a.sh A`        | R3  | the jar and the two zips from a clean clone of A          | 30 s   |
| `tests-f53.sh JAR`    | R4  | Unit, F, Night on the jar, JDK 27 then 17; user's program | 16 min |
| `digests.sh`          | R4b | StreamDigest of A against 2026.2's decided digests        | 30 s   |
| `axioms.sh A`         | R8  | Lean `#print axioms` of lean/README.md's theorems         | 10 s   |
| `s1-chain.sh`         | R5  | the jar's tests on s1, JDK 27 and 17, unattended          | 50 min |
| `collect.sh A`        | R8  | `out/baseline/`: gates, f53, s1, tools                    | 10 s   |
| `finish.sh`           | R8  | `baseline.zip`, `SHA256SUMS`                              | 5 s    |
| `notes.sh`            | R8  | `out/readme.md`, the release notes                        | 5 s    |
| `stage-b.sh CLONE`    | R9  | B's files in a clone; next.md, README, 2026.4-dev         | 5 s    |
| `commit-b.sh CLONE A` | R9  | B gated in the clone, ff into main, the tag on A          | 3 min  |
| `rehearse.sh`         | -   | R2, R3, R4b on main's HEAD in scratch clones              | 30 s   |

Also: `set-buildinfo.sh` (used by commit-a and stage-b), `run.sh` (s1's
side), `next-match.py`, `digest-compare.py` (005-79's),
`userprog/UserProgram.java`, `notes/notes.py`,
`notes/readme-template.md`. Each script's header says what it does, its
environment and its result lines.


## 3. The steps

Times are tonight's and tomorrow's, 2026-11-06 to 07. The coordinator runs
each command in the main tree's shell, after
`S=/Users/f/fl/bench/018/release`.

### Tonight

| Time           | Step                                                        |
|----------------|-------------------------------------------------------------|
| 20:15          | R1: `sh $S/freeze.sh`                                       |
| 20:17 to 20:21 | R2: `COMMIT=1 sh $S/commit-a.sh`: A                         |
| 20:21 to 20:22 | R3: `sh $S/build-a.sh A`                                    |
| 20:22 to 20:38 | R4: `tests-f53.sh` and `digests.sh`, `axioms.sh` beside it  |
| 20:23 to 21:15 | R5: `sh $S/s1-chain.sh`, on s1 unattended                   |
| 20:45 to 02:45 | R6: `night.sh large` on A (the chain), then jcstress on F53 |

* **R1, the freeze (20:15).** `sh $S/freeze.sh` prints `FREEZE OK` or
  `FREEZE NEEDS A LOOK` with its list: tracked changes in main (there
  should be none), the gate lock (free), the java processes (other
  agents' runs should have stopped), `releases/next.md`, and every open
  entry of 015 and 019, marked `outside` when 018-01, section 3.2 puts it
  outside the goal and `JUDGE` otherwise. A `JUDGE` entry that is a fault
  of the Core, not fixed and not one of Frans's exceptions (018-01,
  section 5), means that "Ready", 1 does not hold: the release can still
  be prepared, but it is a stop for Frans (section 5).
* **R2, commit A (20:17).** `COMMIT=1 sh $S/commit-a.sh` prints
  `COMMIT A OK: A (full hash) on main ...`. It must be done before 20:45,
  when the chain takes the gate lock and `night.sh large` clones main's
  HEAD. If main's HEAD moved during the gate, it says so and is run again.
  No commit to main after A until `night.sh large` has cloned it (20:46).
* **R3 (20:21).** `sh $S/build-a.sh A`: `BUILD A OK`, the jar's SHA-256.
* **R4 (20:22).** In the background, each waited for:
  * the F53 tests, stopped at 20:44 at the latest:

        STOP_AT=$(date -j -f "%Y-%m-%d %H:%M" "2026-11-06 20:44" +%s) \
            sh $S/tests-f53.sh $S/out/bergdb-2026.3.jar

    (`TESTS F53 OK`, about 16 minutes with both JDKs on a quiet F53, 24
    under the day's load; `INCOMPLETE`: the JDK 17 runs again in the
    morning at 06:00, after block-q, with `JDKS=17`, about 8 minutes);
  * `sh $S/digests.sh` (`DIGESTS OK`, 30 s): its result line names the
    configurations whose decided digests differ from 2026.2's, and
    `$S/out/digests/differing-configs.txt` has each with the bullets of
    next.md that name it. The coordinator reads those bullets: each must
    explain the configuration ("Ready", 3). `DIGESTS NEEDS A LOOK`: a
    configuration that no bullet names; `DIGESTS FAILED`: the modes differ
    (a fault, a stop for Frans);
  * `sh $S/axioms.sh A` (`AXIOMS OK: 44 theorems`, seconds).
* **R5 (20:23).** `sh $S/s1-chain.sh`: `S1 CHAIN STARTED`. It waits up to
  30 minutes for s1 to be free (no `java`, no `sb.sh`: agent q1 may
  measure 019-36 there); if it exits 2, start it again when s1 is free.
  Check after about 50 minutes: `ssh root@s1 tail
  /opt/bergdb-bench/018/rel/chain.txt` has `S1 TESTS OK` and `S1 CHAIN
  END`.
* **R6 (20:45 to about 02:45).** The chain's `night.sh large`. Check its
  end: `java/build/night/2026-11-06-20*/report.txt` ends with `NIGHT OK`,
  its `Commit:` line is A, and it has the `conformance-large` step.

### The morning, at Frans's word (about 35 minutes)

| Step | Command                                                                       |
|-----|-------------------------------------------------------------------------------|
| R8  | `sh $S/collect.sh A` (`COLLECT OK`)                                           |
| R8  | `sh $S/finish.sh` (`FINISH OK`)                                               |
| R8  | `sh $S/notes.sh` (`NOTES OK`, or `NOTES NEED EDITS`: edit `$S/out/readme.md`) |
| R9  | `git clone -q /Users/f/fl/repos/bergdb $S/B && sh $S/stage-b.sh $S/B`         |
| R9  | the coordinator's files of B, in `$S/B` (below)                               |
| R9  | `COMMIT=1 sh $S/commit-b.sh $S/B A` (`COMMIT B OK`)                           |
| R10 | `tools/news.sh OK coordinator "Release 2026.3 tagged ... (018-09)"`           |

* **R8.** `collect.sh A` finds `night.sh large`'s run of A by its
  `Commit:` line, fetches s1's outputs, and says what is missing
  (`COLLECT INCOMPLETE`). `notes.sh` writes the notes; read them once
  whole: the intro, the Lean paragraph and the known issues were written on
  2026-11-06 from next.md as it was at 12:30, and a fix that landed later
  may need a sentence there. Its markers say what to write by hand (a run
  that did not happen or failed, an exception of Frans's). Then
  `finish.sh` again only if the baseline changed.
* **R9.** In `$S/B`, a clone of main after A: `stage-b.sh` puts
  `releases/2026.3/` (the six files), empties `releases/next.md`, sets
  README.md's latest release and `BuildInfo` to 2026.4-dev and 264. The
  coordinator writes, in `$S/B` (not in the main tree: the fast-forward
  refuses a file changed in both): docs/log.md's entry (as 2026.2's,
  eed4ca9), 018's readme log, 018-01's log, and this plan's State. Then
  `COMMIT=1 sh $S/commit-b.sh $S/B A`: the gate, commit B, the fast-forward
  into main, the annotated tag `release-2026.3` on A ("BergDB 2026.3,
  internal release, 2026-11-07"), and its checks. Nothing is pushed:
  Frans pushes.


## 4. If a fault of the Core is fixed tonight

Frans, 2026-11-06, 12:31: "If the bug is in Core, register it and fix it to
your best ability. Do not wait for me." A fix that lands after A means
that A is not the release. In the morning, after block-q (06:00), on main
with the fix:

| Time           | Step                                                                         |
|----------------|------------------------------------------------------------------------------|
| 06:00          | `sh $S/freeze.sh`; `COMMIT=1 sh $S/commit-a.sh` (a remake: "made again")     |
| 06:04          | `sh $S/build-a.sh A2`; `tests-f53.sh`, `digests.sh`, `axioms.sh A2` as in R4 |
| 06:05          | `CLASSES="Unit F" sh $S/s1-chain.sh` (about 15 minutes)                      |
| 06:05 to 06:55 | `night.sh` on A2, under the gate lock (below)                                |
| 07:00          | R8 with `NIGHT_LARGE=2026-11-06-20xx sh $S/collect.sh A2`, then as above     |

`night.sh` from the main tree: `lockf /Users/f/fl/bench/006-13/gate.lock
sh java/night.sh`. The F53 tests and `night.sh` overlap here (they did not
in 2026.2's plan); `night.sh`'s timing tests may suffer from it. If time allows,
start `night.sh` after the F53 tests (about 06:20, done about 07:10).
The notes get a marker for the paragraph on what changed after the large
run; s1's night tests ran only on the first A.


## 5. What is a stop for Frans

* An open fault of the Core at the freeze that is not one of his
  exceptions ("Ready", 1; `freeze.sh`'s `JUDGE` lines).
* `night.sh large` on A not `NIGHT OK`, or on another commit (R6).
* A test on the jar that fails, on any machine or JDK (R4, R5). On JDK 17
  only, the notes may instead say that JDK 17 is not supported; that is
  his choice.
* StreamDigest: A's modes differ, or a configuration that differs from
  2026.2's and that no line of next.md explains (R4b; "Ready", 3).
* A Lean theorem of lean/README.md's lists with an axiom beyond the
  standard three (R8).
* `SHA256SUMS` that does not check (R8).
* "Ready", 6: Frans says that it is ready. The release is made at his
  command.

Each stop gets `news.sh "needs a look"` and a line in the morning report.
The other steps go on up to R8; commit B and the tag wait.


## 6. The rehearsal (2026-11-06, afternoon)

On a scratch commit: main's `2691750` in a clone
(`$S/rehearsal`, branch `scratch-2026.3`), outputs in `$S/rehearsal-run/`.

On a scratch commit: main's `2691750` in a clone (`$S/rehearsal`, branch
`scratch-2026.3`), from 12:22 to 12:54; outputs kept in
`$S/rehearsal-1225/`. Every step from R2 to R9 ran, with commit A, commit
B and the tag on the scratch branch only (the tag deleted after). F53 was
loaded by the day's agents (load average 7 to 20).

* R1: `freeze.sh` on main: `FREEZE NEEDS A LOOK`: a gate ran, and six open
  entries of 019 to judge (019-32, 35, 36, 39, 40, 41 at 12:30).
* R2: `commit-a.sh`: `COMMIT A OK` (a6935ab), with `BEFORE COMMIT OK
  (146 s)` under the gate lock; 2.5 minutes. The remake (section 4) also
  ran, without a commit: "Release 2026.3, made again: BuildInfo's build
  2026.3.261106.1239, where it said 2026.3.261106.1222".
* R3: `build-a.sh`: `BUILD A OK` in 10 s: the jar 3.4 MB, the source zip
  13 MB (without `releases/2026.1/` and `releases/2026.2/`), the Javadoc
  zip 4.1 MB.
* R4b: `digests.sh`: `DIGESTS OK` in 28 s. **The decided digests differ
  from 2026.2's in 4 configurations, `l3-every1`, `l3-node8`, `l3-node14`
  and `l3-node62` (12 of 36 digests: plain, reads and restarts), and are
  2026.2's in the 8 others.** Each is named by two bullets of next.md:
  015-54 (Reliability, reclaim's pSafe) and 015-87 (Format, the retain
  duration in the stream). 2026.2's jar run again with today's
  StreamDigest gives its release's digests, 36 of 36, so the workloads are
  2026.2's; and A's digests are 015-87's `digests-new.txt`, 48 of 48, so
  nothing after 015-87 moved the bytes. The same at 12:55 on main's
  `8996de0` (`rehearse.sh`: `REHEARSAL OK`, 4 configurations, the same).
* R4: `tests-f53.sh` (24 minutes under the day's load, 743 and 707 s):
  JDK 27: Unit 1,244, F 87, Night 15, the user's program OK. **JDK 17:
  Unit and F passed, the night tests FAILED**: StorageFaultTester's
  `testStreamLayerAll`, "STREAM STOP at 9, reopened: the storage had
  failed (the fault at STREAM call 9, READ), no call reported it, and
  close() returned normally". The user's program OK with both.
* R5: `s1-chain.sh` with `SMOKE=1` (12:26 to 12:29): the copy and the
  start OK; JDK 27: Unit 1,244 passed (84 s); **JDK 17: Unit FAILED**,
  StorageFaultTester's `testSample`, the same finding at STREAM call 1;
  the user's program OK with both. The sample run alone on s1 failed once
  in 19 runs. Both failures are 019-43, registered by the coordinator at
  12:34 (2914fa3), an agent on it. s1's full chain (with the night
  tests, about 50 minutes) was not rehearsed: s1 was wanted by other
  agents.
* R8: `axioms.sh`: `AXIOMS OK: 44 theorems` (7 s). `collect.sh` with a
  copy of the 02:10 night report made to name the scratch A (the
  rehearsal's only made-up input): `COLLECT INCOMPLETE`, as it should be
  (s1's smoke). `finish.sh`: `FINISH OK`, `SHA256SUMS` checks. `notes.sh`:
  908 lines; `NOTES NEED EDITS` with 3 markers, as it should be (JDK 17's
  failure, s1's smoke, 019's open entries).
* R9: `stage-b.sh` refused the notes with markers; with the markers taken
  out of a copy: `STAGE B OK` (six files, next.md emptied, README.md's
  line, `BuildInfo` 2026.4-dev and 264). `commit-b.sh`: `COMMIT B OK`,
  `BEFORE COMMIT OK (121 s)`, the annotated tag on A, checked.


## 7. Is "Ready" in reach by the morning?

Not as main stands at 13:00. In order of risk:

1. **019-43 fails the jar's tests on JDK 17** ("Ready", 2), on F53 (night
   tests) and on s1 (unit tests), now and then: a STOP at an early read
   that no call reports. A Core fault, or the harness's oracle; either way
   it must be fixed or decided by 20:15, or R4, R5 and `night.sh large`
   can fail on it. With the fix landing before 20:15 the plan holds.
2. **"Ready", 1**: open entries at 13:00 that `freeze.sh` will list: 019-40
   (R6's C findings), 019-43, 019-44 (four small Pub API faults), and the
   Investigates 019-35 and 019-36 (Frans: not blocking). Each Fix must be
   done, or be one of Frans's exceptions, by 20:15. A fault fixed after A
   brings the morning remake (section 4), whose `night.sh` is the plain
   one: then `night.sh large` ran on the first A, not on the release
   commit, which "Ready", 2 asks for. That is for Frans to accept (his
   12:31 words suggest he does).
3. **Time at 20:22**: the F53 tests took 24 minutes under today's load;
   on a quiet F53 about 16. With `STOP_AT` 20:44, JDK 17 may be cut and
   run in the morning (06:00, 8 minutes). They must not run beside
   `night.sh large`.
4. **s1**: its full chain was not rehearsed (2026.2's was, at 01:52 on
   the night). If s1 is busy at 20:23, `s1-chain.sh` waits 30 minutes; the
   chain takes about 50 minutes; it can also run in the morning.
5. **The notes** need a read in the morning (10 minutes): the template's
   prose was written at 12:30 from next.md then; fixes landed since (019-32,
   019-39, 019-41, 019-42 and more by 20:15) are in next.md and so in the
   Changes, but the intro and known issues must agree with them. "Ready",
   4 (the documentation) is agent d30's (8996de0).

"Ready", 3 is met at `8996de0`: every differing configuration is named.


## 8. State

2026-11-06, 13:00: the scripts are written in `S` and rehearsed from R2
to R9 on scratch commits (section 6); nothing of the release has run on
main. `rehearse.sh` (2 minutes; `JARTESTS=1` adds the F53 tests) should run
again at about 20:00, after the last fixes, so that a commit that breaks a
script is found before the freeze. Left: 019-43 (section 7, point 1); the
full s1 chain, not rehearsed.
