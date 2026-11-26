028-64. Change: week.sh in about 10 hours, at most 12
=====================================================

Status: done: three lanes at once, about 6 hours, no coverage cut; a
whole-run hang guard of 12 hours. Kind: Change. Frans: none.
Created 2026-11-26 by Frans Lundberg.

What: `java/week.sh` ran its steps one after another. Its last run
(2026-11-25-1409) took 579 minutes for every step but the large reclaim
run, which failed at once that night (028-63); the large reclaim run
(`java/stress/large.sh full`) then took 19,922 s, 5.5 hours, alone on
F53 with seed 20782 (2026-11-26). So a whole run would take about 15
hours. Frans set the aim on 2026-11-26: about 10 hours on F53 (10
cores, 32 GB), at most 12.

Why: `week.sh` runs before every release and on demand; a run of 15
hours does not fit a night, and holds the machine for most of a day.

Frans: none.

Done when: `week.sh`'s time, estimated from measured step times, is at
most 12 hours, about 10, with its coverage kept where possible and each
cut stated with what it loses; `java/week.sh short` passes; the texts that
state the week run's or the large run's time are updated.

First step: the step times of the week reports of 2026-11-19 to 25, and
the large run's log of 2026-11-26.


Result
------

Three lanes at once, no coverage cut (2026-11-26). After before-commit,
`week.sh` starts its two longest steps in the background, each in a
clone of its own, and runs the other steps one after another beside
them, as before:

* Lane L: large-reclaim (`stress/large.sh full`, the day's seed).
* Lane C: conformance-large (`stress/conformance.sh large`, 12 traces,
  4 at once as before).
* Lane S: apps-quick, apps-soak-cc, apps-kill-cc, kill-restart-week,
  kill-restart-cc, fuzz-week, unlinkfuzz-week, harness-soak-week,
  harness-soak-cc, apptraces-week, android, in the run's clone.

The steps, their seeds, sizes and durations are those of before: the
same tests, so no coverage is lost. The report keeps one line per step
with its time; the lanes' two lines come last, and a line after the JDK
names the lanes and the guard. The run's minutes on the last line are the
wall time, less than the sum of the steps'.

Why a clone each. `build.sh` deletes `build/classes`, `build/stress` and
both jars before it writes them again, and most steps call it at their
start (`apps.sh`, `kill-restart.sh`, `android.sh`, `apptraces.sh`,
`large.sh`, week.sh's `conformance`); `fuzz.sh`, `unlinkfuzz.sh`,
`harness-soak.sh` and `TraceExport` start JVMs on `build/bergdb.jar` and
`build/stress` throughout their runs. In one tree a build in one lane
would remove the jar under a JVM that another lane starts. Each lane's
clone (`build/week/RUN/repo-NAME`, made from the run's clone, so of the
same commit, with `lean/.lake` copied) has its own `java/build/` and
`lean/.lake/`; `run_finish` collects their logs into `RUN/logs/` as
before and deletes them. The machinery is `stress/runlib.sh`'s
(`step_bg`, `step_wait`); `night.sh` uses none of it, and its steps run
as before.

Why not more traces of conformance-large at once. Its time is mostly one
trace: on 2026-11-25 the longest check took 13,991 s of the step's
17,048 (the checks 38,236 s in all, at most 215 MB each). `conformance.sh`
runs its traces in batches of 4, each batch as long as its longest
trace, so the other two batches took about 3,000 s together; with all
12 at once the step would take about 14,000 s, still less than lane L,
which is the longer one either way. PAR stays 4, which also keeps lane
C at 4 cores, and its memory at 4 exports of up to 1.7 GB each at a
batch's start.

The hang guard: added (2026-11-26). If the run has not ended `GUARD_S`
seconds after its start (default 43,200, 12 hours; `short` 7,200),
`stress/runlib.sh`'s `run_guard` writes `RUN/hang.txt` and kills the
processes of the steps then running (TERM, then KILL after 10 s to those
left); each such step fails with a line that starts with HANG, the steps
not yet started are not run, and the report ends `WEEK FAILED: ...
hang-guard`; `run_finish` then copies the logs, removes the clones and
adds the news entry as always. Reasons:

* With three lanes, a hang in any of them holds the whole run at its
  end: no report and no news entry, and the machine held.
* Some steps have no guard of their own: a conformance trace's Lean
  checker (one check takes about 3.9 hours, so a per-trace limit would
  be close to its time), `lake build`, the fuzzers' JVMs, and
  `harness-soak.sh` where `timeout` is missing (it is on F53, from
  Homebrew). The others' waits are hang guards already (`apps.sh`,
  `kill-restart.sh`, `android.sh`'s boot, `LargeReclaimRun`'s 12-hour
  guard and its waits).
* 12 hours is the most that Frans set for the run, and about twice the
  estimate below: only a hang, or a machine about twice as slow as F53
  alone, reaches it; `GUARD_S` raises it for such a machine. That keeps it
  a hang guard of a functional script (028-23), not a limit of speed.

The guard spares itself and the background steps' own shells (so that
they write their lines), and kills only the processes that exist when it
fires and their children, so not `run_finish`'s. An interrupt of
`week.sh` (INT, TERM) kills every step's processes the same way
(`run_stop`): the background lanes ignore SIGINT, as every asynchronous
command of a non-interactive `sh` does, so without it a Ctrl-C would
leave them running. Checked with fake steps in a scratch repository
(2026-11-26): the normal path, the guard (two steps killed with their
children, one not run, the report and its last line as above), a TERM to
the process group and an INT as from a terminal; and on the real steps
in the trial of the full run below.


Times: measured and estimated
-----------------------------

Measured, the steps one after another (week reports 2026-11-20-1550 and
2026-11-25-1409; the second partly beside `night.sh` and other agents'
gates), and the large run alone:

* Lane S, the sum of its 11 steps: 14,858 s (4.1 hours) and 17,597 s
  (4.9 hours); its longest steps kill-restart-week (2,745 and 5,295 s),
  fuzz-week (3,606 s, a fixed 60 minutes) and apps-soak-cc (2,366 and
  2,271 s).
* Lane C, conformance-large: 14,391 s (4.0 hours) and 17,048 s (4.7
  hours).
* Lane L, large-reclaim: 19,922 s (5.5 hours), seed 20782, alone on F53
  (2026-11-26 00:19 to 05:51, log of `large.sh full 20782`): 40 epochs of
  420 to 600 s each. Seed 20778's order took 79 minutes (028-43); the
  fills that 028-63 measured wrote 211 to 724 bytes a key, 20782's the
  most, so 5.5 hours is near the longest of the seeds measured (the
  harness allows a fill of up to 1,000 bytes a key).
* before-commit 63 to 83 s, before the lanes start.

Measured, the lanes at once: a trial of the full run (2026-11-26 06:57
to 07:25), `week.sh` on the branch with `GUARD_S=1680`, so that its
guard ended it after 28 minutes, in the heaviest part of a run: lane
C's first four checks, lane S's apps-quick and apps-soak-cc, lane L's
fill and first epochs.

* Lane L ran seed 20783, whose order is 20782's shifted by one key (the
  same multiplier, 1,020,787; offset 20783): fresh fill 7,242,961,160
  bytes against 7,244,195,848. Its fill took 83.6 s against 64.9 s
  alone (the other lanes' builds ran then); epochs 1 to 3 ended at
  370.0, 683.6 and 1,119.1 s against 351.2, 735.6 and 1,134.1 s alone:
  from the fill to the end of epoch 3, 1,035 s beside the lanes against
  1,069 s alone. No slowing beyond the run-to-run spread.
* Lane S: apps-quick 263 s, against 238 and 246 s one after another;
  about 7 % slower.
* Load: 10 on average, 27.7 at most (the builds at the start); the three
  lanes' processes used 5.6 cores on average, 8.8 at most, of 10 (L 0.9,
  C 2.9, S 1.8 on average). Resident memory at most: L 8.2 GB, C 2.6 GB
  (the four exports at a batch's start), S 2.8 GB; macOS reported 7 to 8
  GB unused throughout and the swap stayed at 5.3 GB, as before the
  trial.
* The guard fired at 07:25, killed apps-soak-cc, large-reclaim and
  conformance-large with their JVMs and Lean checkers (each a HANG line,
  FAILED), did not run the 9 steps after apps-soak-cc, then `run_finish`
  collected the logs and removed both lane clones (380 kB left in the
  run's directory); no process of the run was left. A large run that the
  guard kills keeps its logs (`logs/large/`), not its data, which goes
  with its clone.

Measured, `java/week.sh short` on the branch (2026-11-26 07:26 to
07:39): WEEK OK in 13 minutes (16 with the steps one after another,
2026-11-19 and 20). Its large-reclaim-quick took 225.5 s beside the
other lanes (apps-quick-cc with CC in 36 JVMs, conformance small), and
188.5 s alone right after (seed 20783 both): 20 % slower, where the full
mode above showed no slowing over its first three epochs. A quick run
holds its database in memory and is bound by CPU and its collector's
threads; the full run reads its 10 GB of kept stream through a 3 GB
cache.

Estimated, the whole run: about 6 hours (5.5 to 6.7), from these
measurements:

* Lane L: 5.5 to 6.6 hours for a seed like 20782: the time alone, and
  at most the quick mode's 20 % over the whole run; 79 minutes to a few
  hours with more local orders.
* Lane C: 4 to 5 hours (as measured, up to 5 % slower).
* Lane S: 4.1 to 5.2 hours (as measured, 7 % slower).
* The run: before-commit, the clones (seconds), the longest lane, the
  logs and news (a minute or two): about 6 hours with seeds like 20782,
  4.5 to 5 with a local order, where lane S or C is the longest. A whole
  full run was not made on 2026-11-26.

Against the aim: about 6 hours is below 10 and below the 12 at most.
The time that is left, about 4 hours, could take more coverage (more
seeds of the large conformance set, a longer fuzz-week); that is a
choice for Frans, not made here.


Files
-----

* `java/week.sh`: the lanes (`step_bg`, `step_wait`), the guard
  (`GUARD_S`, `run_guard`), the trap of INT and TERM (`run_stop`), the
  header's times and steps in the new order.
* `java/stress/runlib.sh`: `clone_commit`, `step_bg`, `step_wait`,
  `run_guard`, `run_stop`, the guard's checks in `step` and
  `run_finish`, and `run_finish` over every clone.
* `java/stress/large.sh`: the header's times (5.5 hours with seed
  20782's order; quick about 3 minutes).
* `java/readme.txt`: the times of `week.sh` and `large.sh`.

Not changed, for the lead: `AGENTS.md` ("about 10 hours" for
`week.sh`) and 013-04 ("about 10 hours"), which state the old time.

Gates: `java/week.sh short` WEEK OK (13 minutes, 2026-11-26 07:39);
the trial of the full run as above (its guard at 28 minutes, as
meant); `DRY=1` of `week.sh`, `week.sh short` and `night.sh`;
`java/before-commit.sh` BEFORE COMMIT OK (61 s; no Java changed).


Log
---

2026-11-26. Registered and taken by an agent of lead-1126, from the aim
that Frans set for `week.sh` on 2026-11-26 (about 10 hours on F53, at
most 12). Done the same day: lanes, guard, trials and texts on the
branch `028-64`.
