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
- **The large set**, without `live=1`, 1 seed: 6 of 6 CONTRACT OK, the
  same 17,000 transactions; 248 s.
- **The medium set**, `live=1`, 3 seeds: running (m-mixed, m-long,
  m-big, m-d8 CONTRACT OK so far; m-d8's 530 MB traces take 53 minutes
  each to check).


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
