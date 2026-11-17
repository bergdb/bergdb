# 030-15. Strict trace parsing, one verdict, and a gate that pins the statements

Created 2026-11-17 by Frans Lundberg. Status: open.

The fixes of an independent review of the contract package (another model,
the night of 17 November; its sections 4 and 5): malformed trace lines
passed both checkers, each checker checked only half of a trace, the
contract checker's exit status was tied to its verdict by reading only, and
the gate did not pin the statements (also 030-06, finding 8). On the
branch `030-15-strict` from `main` 0b677a63 (gate base a25b8b03).


# 1. The result

Work in progress; see the Log.


# 2. Decisions


# 3. State note


Log
===

- 18:30 Started (agent s4i of coord-1117, Opus 5.5). Traces of the level 2
  sets made in the clone (`treeconf.sh small`, `drain`, `reclaim`:
  TREECONF OK, 195 traces).
- 19:05 Work item 1, strict parsing: `lineFault` and `placeLine`
  (Complete.lean), `readLine` strict (Trace.lean); the review's faults in
  `faults.sh` and `bridge-faults.sh`, with `test/small.trace`. FAULTS OK,
  BRIDGE FAULTS OK; `check.sh small drain reclaim` CONTRACT OK (195 traces).
  The gate against a25b8b03 fails only on the coordinator's 006-30 commits
  (items/006-2026-q4/30-day-17-november.md, in main 0b677a63 that this branch
  starts from); against 0b677a63: GATE OK.
