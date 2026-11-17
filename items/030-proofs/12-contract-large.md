# 030-12. The writer's contract on the reclaim, medium and large sets

Created 2026-11-17 by Frans Lundberg. Status: open.

More evidence for the tested half of the contract approach (030-04): the
contract check of 030-05 and 030-09 (`lean/contract/check.sh`'s
`contractcheck`: C1 to C5, R1, L1, L2, the completeness checks of 030-09)
on far more of Java's transactions than the level 2 sets: the reclaim,
medium and large sets of `java/stress/treeconf.sh`, with `live=1` where it
fits. Written by an agent of coord-1117 ("I" below), on the branch
`030-12-large`, the night of 17 to 18 November.


# 1. The result

Java met the contract on every trace checked so far; no failure of any
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
- **The medium set**, `live=1`, 3 seeds: 24 of 27 CONTRACT OK so far,
  all but m-d62 (running); 12,467 transactions, 499,669 operations,
  172,401,282 LIVE lines
  (m-d8, m-d30, m-mixed, m-long, m-big, m-long3, m-fifo, m-r-del).
  m-d30's traces (1.2 GB, 17 million LIVE lines) take 4.4 to 4.5 hours
  each to check, and the checker grows to 4 GB; m-d62's are 1.7 GB.
- **Main's checkers (d7966251) on the traces without LIVE lines**:
  `contractcheck` with K-LEVEL (030-17) and `bridgecheck` (030-07) on
  the reclaim set (3 seeds, 15 traces), the medium set (3 seeds, 27) and
  the large set (10 seeds, 60): 102 of 102 CONTRACT OK and BRIDGE OK.
  192,402 transactions, 1,315,051 operations; the bridge: 1,359,030
  nodes made, 3,585,447 entries, 17,453 touched (reclaim and m-r-del
  only); no failure of any clause (KIND 0). 2.3 hours of the contract
  check and 5.1 hours of the bridge check, summed over the traces.
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
