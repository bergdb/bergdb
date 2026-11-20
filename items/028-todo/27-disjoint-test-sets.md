028-27. Change: night, week and timing as disjoint sets of tests; Android in week
================================================================================

Status: done. Kind: Change. Frans: decided (2026-11-19).
Created 2026-11-19 by Frans Lundberg.

What: make `java/week.sh` a distinct set of tests that does not run
`java/night.sh`, so that `night.sh`, `week.sh` and `java/timing.sh` are
disjoint sets of tests, and add the Android tests (`java/stress/android.sh`)
to `week.sh`.

Why: Frans decided (2026-11-19): `week.sh` is a distinct set of tests and
does not call `night.sh`; `night.sh`, `week.sh` and `timing.sh` are
disjoint sets of tests, no test step runs in two of them, and each may run
`java/before-commit.sh` first, to fail quickly; the Android tests are part
of `week.sh`. Until then (028-23) `week.sh` ran `night.sh week`: all of
night's steps, then its own, and the Android tests ran only by hand before
a release.

Frans: decided (2026-11-19); nothing more needed.

Done when: `week.sh` stands alone (its own clone, report, news entry and
steps, before-commit first and a stop if it fails, the Android tests last);
the machinery that `night.sh` and `week.sh` share is in one file that both
source; `night.sh` has no `week` and `large` modes and runs its steps as
before; every step of the three scripts is listed below and none runs in
two of them, before-commit.sh excepted; the headers of the three scripts,
`java/readme.txt`, AGENTS.md's "Code" section and a dated note in 028-23
say so; `sh java/week.sh short` ends WEEK OK with the Android SDK set;
`sh java/before-commit.sh` prints BEFORE COMMIT OK.

First step: read 028-23 and the headers of the three scripts.


1. The change
-------------

* `java/stress/runlib.sh` (new): what `night.sh` and `week.sh` share, moved
  from `night.sh` unchanged in behaviour: `run_start` (the clone of HEAD in
  `build/KIND/RUN/repo` with the two `.lake` directories copied in, the
  report's head), `step` (a step's output, its line in the report; now it
  also returns the step's status), `run_finish` (the logs, the clone
  deleted, the last line `NIGHT OK`, `NIGHT FAILED: STEPS`, `WEEK OK` or
  `WEEK FAILED: STEPS`, the `tools/news.sh` entry) and `DAY`, the day's
  number for seeds. Both scripts source it from `java/`. `DRY=1` prints the
  steps in order with their commands and runs nothing: no clone, no
  report, no news entry.
* `java/night.sh`: sources `runlib.sh`; the modes `week` and `large` are
  gone (it refuses them with a usage line that names week.sh), and with
  them the large conformance set and week's steps. Its 17 steps, their
  order and commands, and its report's format are unchanged.
* `java/week.sh`: its own run, no longer `exec sh night.sh week`. The
  report's head has one more line, whether the Android SDK is set. If
  before-commit fails, the run stops there: the report says that the
  other steps were not run, and ends WEEK FAILED. conformance-large (and
  short's conformance-small) builds the jar and the Lean checker (`lake
  build` in `lean/`) itself, since no level step builds it before. The
  android step runs `stress/android.sh`, which takes the SDK from the
  environment (`ANDROID_SDK` or `ANDROID_HOME`, `ANDROID_USER_HOME`);
  without it the step fails with android.sh's message, and week.sh says
  so at its start and in the report's head.
* `java/stress/unlinkfuzz.sh`: a second argument `day` runs only the day's
  block of seeds. Before, week's unlinkfuzz-week ran the fixed block
  (seeds 1, 2, ..., the same every time) as night's unlinkfuzz does: the
  one exact repeat between the two scripts. Now week.sh runs only its own
  day's block.
* `java/timing.sh`: its header only.


2. The steps after the change
-----------------------------

**night.sh** (about 2.5 hours), in order:
before-commit, core-build, transcheck, level1, level2, level3, level4,
count-gates, lean-tests, tree-tests, night-tests, harness-soak (-r 2),
fuzz (12 minutes), unlinkfuzz, kill-restart (1,000 kills),
conformance-medium, contract-medium.

**week.sh** (about 9 hours, an estimate from the steps' times), in order:
before-commit (stops the run if it fails), apps-quick, apps-soak,
apps-kill, kill-restart-week (1,000 kills on each of three seeds),
fuzz-week (60 minutes), unlinkfuzz-week (the day's block only),
harness-soak-week (-r 10), conformance-large (the Lean checker built
first), android.
`week.sh short`: before-commit, apps-quick, kill-restart-week (10 kills on
two seeds), fuzz-week (1 minute), unlinkfuzz-week, harness-soak-week
(-r 1), conformance-small (1 seed), android.

**timing.sh** (about 2 hours, an estimate): core, pauses, perf.


3. Disjointness
---------------

Each step of the three scripts and where else it runs (`DAY` is the day's
number, days since 1970):

* before-commit: night.sh and week.sh, first; the exception that Frans's
  decision allows.
* core-build, transcheck, level1 to level4, count-gates, lean-tests,
  tree-tests, night-tests, conformance-medium, contract-medium: night.sh
  only.
* apps-quick, apps-soak, apps-kill, conformance-large, android: week.sh
  only. (`week.sh short`'s conformance-small, a trial of the script with
  1 seed, is a set that level2.sh in night.sh also runs, with 10 seeds;
  the full week.sh runs the large set, which nothing else runs.)
* core, pauses, perf: timing.sh only; the overlap with level1 below.

The same harness in night.sh and week.sh, a different test run each, kept:

* kill-restart.sh: night.sh 1,000 kills from the seed YYYYMMDD (the date);
  week.sh 1,000 kills on each of the seeds DAY times 10 + 1, + 2 and + 3. The
  harness's self-check and late-exit check run before each seed's kills,
  with that seed: once in night.sh, three times in week.sh.
* fuzz.sh: night.sh 12 minutes, a turn a minute, seeds from DAY times 1000;
  week.sh 60 minutes, seeds from DAY times 1000 + 100.
* unlinkfuzz.sh: night.sh the fixed block (seeds from 1) and the day's
  block from DAY times 1000 (up to 350 rounds a configuration); week.sh only
  a day's block, from DAY times 1000 + 500. Before this entry week.sh also ran
  the fixed block, an exact repeat of night's; now it does not.
* harness-soak.sh: night.sh -r 2 (rounds 0 and 1) from the seed YYYYMMDD
  times 1000; week.sh -r 10 (rounds 0 to 9) from DAY times 1000 + 100. Sizes,
  eviction schedules, the audit and the startup distance cycle with the
  round, so rounds 2 to 9 also run combinations that night's two do not.

timing.sh and the functional scripts: night.sh's level1.sh runs CORE
(`bergdb.dev.props.Core`) once in its Props step and prints the figure as
information, checked against nothing (028-23); timing.sh's core step runs
the same program, ABBA against the last release, and judges the figure.
Nothing else of timing.sh runs in night.sh or week.sh: no step of either
runs the pause probe or performance.sh.


4. Android
----------

`stress/android.sh` needs the Android SDK (006-18-03, section 3, says how
it was installed): `ANDROID_SDK` (or `ANDROID_HOME`) and, if the AVDs are
not in `user/` beside the SDK, `ANDROID_USER_HOME`. week.sh passes the
environment on; its header shows how to start it with the SDK set, with a
placeholder path. The emulator's port is android.sh's `PORT`, 5580 by
default, so two runs of it at once on one machine need different ports.


Log
---

2026-11-19. Registered (Frans's decision of 2026-11-19) and taken by an
agent of coord-1118: in progress; branch `028-27-disjoint-test-sets` in a
scratch clone.

2026-11-19. Done on the branch `028-27-disjoint-test-sets`, by an agent of
coord-1118. Gates on F53, at a load of 13 to 22 (the old form of week.sh
ran from the main tree meanwhile): `stress/android.sh` alone, with the SDK
of 006-18-03 in `ANDROID_SDK` and `ANDROID_USER_HOME`: ANDROID OK (1727
tests, 4 skipped) in 159 s; `week.sh short` on `5989fc22`, with the SDK
set: WEEK OK (13 minutes; before-commit 70 s, apps-quick 243 s,
kill-restart-week 62 s, fuzz-week 60 s, unlinkfuzz-week 141 s with 1,613
rounds, the day's block only, harness-soak-week 15 s, conformance-small
77 s with the Lean checker built by the step, android 133 s), and its
`tools/news.sh` entry; `before-commit.sh`: BEFORE COMMIT OK (95 s);
`DRY=1 sh java/night.sh` lists the 17 steps of before, in their order and
with their commands; `night.sh large` is refused with a usage line;
`sh -n` on every changed script. After the gate only week.sh's header
changed (the short run's time). Not run: a full week.sh (about 9 hours)
and a full night.sh.

2026-11-19. Merged into main by coord-1118 and gated again on the merged
tree: BEFORE COMMIT OK, night.sh's steps listed with DRY=1, and week.sh
short with the Android SDK, WEEK OK (13 minutes; ANDROID OK, 1728 tests,
4 skipped).
