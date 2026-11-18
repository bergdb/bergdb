# 030-12. The writer's contract on the reclaim, medium and large sets

Created 2026-11-17 by Frans Lundberg. Status: done.

More evidence for the tested half of the contract approach (030-04): the
contract check of 030-05 and 030-09 (`lean/contract/check.sh`'s
`contractcheck`: C1 to C5, R1, L1, L2, the completeness checks of 030-09)
on far more of Java's transactions than the level 2 sets: the reclaim,
medium and large sets of `java/stress/treeconf.sh`, with `live=1` where it
fits. Written by an agent of coord-1117 ("I" below), on the branch
`030-12-large`, the night of 17 to 18 November.


# 1. The result

Java met the contract on every trace checked; no failure of any
clause, no trace not whole, no ERROR line.

- **The reclaim set**, `live=1`, 3 seeds: 15 of 15 CONTRACT OK; 8,735
  transactions, 27,209 operations, 34,940 GET, 8,735 SCAN, 21,380,976
  LIVE lines, 18,658 SKIPT. 174 s.
- **The large set**, `live=1`, 1 seed (treeconf.sh's default): 6 of 6
  CONTRACT OK; 17,000 transactions, 55,003 operations, 68,000 GET,
  17,000 SCAN, 202,519,832 LIVE lines, 42,241 SKIPT. Traces of 0.16 to
  4.1 GB; 3.7 hours, three at a time (l-few's check 10,696 s, l-5000's
  6,150 s).
- **The large set**, without `live=1`, 10 seeds: 60 of 60 CONTRACT OK;
  170,000 transactions, 551,124 operations, 680,000 GET, 170,000 SCAN,
  419,440 SKIPT; 2,837 s, three at a time. (Seed 1 alone first: 6 of 6,
  248 s.)
- **The medium set**, without `live=1`, 3 seeds: 27 of 27 CONTRACT OK;
  13,667 transactions, 736,718 operations, 54,668 GET, 13,667 SCAN,
  62,172 SKIPT; 554 s (as 030-09's run).
- **The medium set**, `live=1`, 3 seeds: 27 of 27 CONTRACT OK; 13,667
  transactions, 736,718 operations, 54,668 GET, 13,667 SCAN,
  220,958,484 LIVE lines, 62,172 SKIPT. m-d30's traces (1.2 GB, 17
  million LIVE lines) took 4.4 to 4.5 hours each to check (the checker
  grew to 4 GB), m-d62's (1.7 GB, 16 million) 4.0 to 4.1 hours.
- **The large set's seeds 11 to 30**, without `live=1`, with main's
  two checkers: 120 of 120 CONTRACT OK and BRIDGE OK; 340,000
  transactions, 1,100,217 operations, 1,360,000 GET, 340,000 SCAN,
  843,991 SKIPT; the bridge: 1,426,086 nodes made, 3,735,494 entries;
  3.4 hours, three at a time.
- **In all, with main's checkers**: 222 of 222 traces (reclaim 15,
  medium 27, large 180 over seeds 1 to 30), 532,402 transactions,
  2,415,268 operations, no failure of any clause of either checker.
- **The check's time with LIVE lines is not linear in the trace**:
  l-5000's 4.1 GB (57.7 million LIVE lines) took 1.7 hours, m-d30's
  1.2 GB 4.4 hours. By reading (not measured): each LIVE line is checked
  by a search in the history, `liveOk h' topRoot x t ys` in
  `ContractCheck.lean`, so its cost grows with the history's size, which
  is largest for the many keys and large nodes of m-d30 and m-d62.

# 2. How the sets were run

The old tree checker (`treecheck`) is not run: `treeconf.sh` runs it on
every trace, and it is slow on the large set. Its configurations are taken
as they are from `treeconf.sh`'s set functions by a small script in my
scratch, `/Users/f/fl/bench/2026-11-17/night/s4e/run.sh` (as 030-09's
medium script did): `TraceExport` with `-Dtree=1` (and `-Dlive=1` where
chosen) per configuration and seed, four at a time, then `contractcheck`
on each trace. No script under `java/stress` is changed.


# 3. Decisions

- **No `treecheck`, no change of `treeconf.sh`.** Reason: the brief asks
  for the cheapest way to the traces of format 3 and the contract check
  only; a script in my scratch that reads `treeconf.sh`'s set functions
  needs no change under `java/stress` (so no BEFORE COMMIT gate) and runs
  the same configurations. A flag in `treeconf.sh` would be the lasting
  form; left for a later item, since `check.sh` already takes any set
  whose traces exist.
- **After 030-13 landed (main 6fb4fe9a), the old script stays in my
  scratch.** `treeconf.sh` now has `TREECHECK=none` and
  `java/stress/contractconf.sh` runs both checkers on a set: the lasting
  form the brief asked for exists, so I change no script. My runs began
  before it; I keep them, and recheck their traces with main's checkers.
- **Main's checkers on the same traces, in a second worktree.** Reason:
  main's `contractcheck` has K-LEVEL (030-17) and `bridgecheck` (030-07)
  is new; the m-d62 checks run from my clone's binary, which a `lake
  build` there would replace under them. So main is built in
  `/Users/f/fl/bench/2026-11-17/night/s4e/bw` (a worktree at main) and
  `recheck.sh` in my scratch runs both on the traces without LIVE lines.
- **`live=1` on every set** (the reclaim set too: the exporter writes
  LIVE lines with reclaim on, 0 errors). Reason: the LIVE lines are the
  readers' half of the contract (L1, L2); the traces grow with nodes times
  transactions (r-big 180 MB, m-d8 530 MB), but the checker reads them in
  a few minutes and in less than 100 MB.
- **The large set also without `live=1`**, first, with one seed. Reason:
  its traces are small without LIVE lines and quick to check (248 s for
  all six), so the writer's half is checked on the whole set before the
  long runs with LIVE lines.


# State

2026-11-18, 03:55. Done: the reclaim, medium and large sets checked, with
and without LIVE lines, and with main's checkers (contract with K-LEVEL,
and the bridge) on the traces without LIVE lines, and the large set's
seeds 11 to 30; no failure anywhere.
Branch `030-12-large` in `/Users/f/fl/bench/2026-11-17/night/s4e/clone`,
merged with main 77c876a7. Nothing of Java or the scripts changed.

- The scripts, in `/Users/f/fl/bench/2026-11-17/night/s4e/`: `run.sh SET
  SEEDS LIVE [PAR]` (export and contractcheck of a set), `run2.sh` (the
  same with `ONLY=` a pattern of configurations and `TAG=`), `run3.sh`
  (seeds `S0` to `S1`, main's two checkers from the worktree `bw`),
  `recheck.sh DIR...` (main's checkers on traces already made). Outputs in
  `out/SET-liveL[TAG]/`: `summary.txt`, `times.txt`, per trace its
  `.contract.txt` (and `.new-contract.txt`, `.bridge.txt`).
- The lasting way to run a set is main's `java/stress/contractconf.sh
  SET [seeds]` (030-13); it has no `live=1` switch; a set with LIVE lines
  needs `-Dlive=1` in the configurations, as my scripts add.
- What could follow: the checker's time on LIVE lines (section 1, the
  last point: quadratic by reading, 4 hours for a 1.7 GB trace) if LIVE
  lines are wanted on the medium set in night.sh; main's checkers on the
  traces with LIVE lines (not run: the old checker passed them, and
  by reading, K-LEVEL and the bridge do not use the LIVE lines).


# Log

2026-11-17, 15:58. Read the brief, the common rules, 030-09; built Java and
the checker; started the reclaim set with `live=1`.
2026-11-17, 16:07 to 19:55. The reclaim set (live), the large set (live
and not), most of the medium set (live); the large set with 10 seeds, not
live, started.
2026-11-17, 20:40 to 21:50. The medium set with and without LIVE lines;
pulled main (bridgecheck, K-LEVEL, contractconf.sh); built main's
checkers in a worktree; rechecking the reclaim, medium and large traces
without LIVE lines with both.
2026-11-17, 21:50, to 2026-11-18, 00:30. The recheck: 102 of 102 with
both of main's checkers; the large set's seeds 11 to 30 started, without
LIVE lines, with main's checkers.
GATED a33be2f4: the reclaim set (live=1) 15 of 15 and the large set (live=1) 6 of 6 CONTRACT OK, 25,735 transactions; gate base 6db019b3.
GATED b22c6cce: the medium set not live 27 of 27, live 24 of 27 (m-d62 running), large 10 seeds not live 60 of 60; gate base d7966251.
2026-11-18, 00:30 to 03:55. The medium set with LIVE lines finished (27
of 27); the large set's seeds 11 to 30 with main's checkers, 120 of 120;
pulled main; the item done.
