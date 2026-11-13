# 026-11. G4's back-to-empty lag as a gate

Created 2026-11-13 by Frans Lundberg. Status: done; on the branch
`026-11-lag-gate`, to land.

For release 2026.6: the lag of 024-30's G4 (back to empty after a mass
delete) becomes a gate of `count-gates.sh`, and so of `night.sh`'s
step `count-gates`; until now it was printed only (024-30, section 9 and
Q30-3). Made by the agent "lag" of coord-1113 in a clone; the
coordinator lands it.

The decisions:

* 024-30, Q30-3 (decided by the coordinator under Frans's delegation,
  2026-11-12, 12:33): "yes, after the runs at 100,000 and 3M keys, in
  2026.6 (026); printed, not gated, until then".
* 026-05, Q4: "with 026-05 the lag is 1,265 to 1,286 transactions at
  1M, 4M and 10M and every f (section 6), R/4 + about 25 + R; a gate at
  2 R (2,000 transactions at G4's R) is independent of n and has a
  margin of 1.55. Recommended: make it a gate once 026-05 is on `main`".
  Frans, 2026-11-13, 09:41: "Yes to all four." 026-05 (P8) is on `main`
  since `fe5000ec`, so its runs at 1M, 4M and 10M stand in for Q30-3's
  runs at 100,000 and 3M keys.


## 1. The gate, exactly

G4's workload and its twin are 024-30's (section 8), unchanged: R = 1 s
of a test clock that advances dt = 1 ms a transaction, so **R = retain /
dt = 1,000 transactions**; the emptied database fills n = 1M keys in key
order and deletes them all, 100 a transaction; both then run a drive of
40 R, one overwrite of "/a.txt" (1,000 bytes) a transaction.

* **kept**, after each drive transaction: `getStreamLength() -
  getFirstAvailablePos()`.
* **The twin's M1**: the most kept of the twin over the last 1,001
  transactions of its drive (the last R), as for G4's M1 gate.
* **The lag**: the first drive transaction k of the emptied database such
  that after k and after every later transaction of the drive, kept is at
  most twice the twin's M1 (`G4M.lag`, the code that printed it before;
  unchanged). If kept is above twice the twin's M1 after the drive's last
  transaction, there is no lag ("never").
* **The gate**: lag / R at most 2 (the property `g4lag`, 2), that is the
  lag at most 2,000 transactions. "never" fails. The line, after G4's M1
  line:

      G4 lag over R, the drive transactions until kept stays at most twice the twin's M1 (L / 1000) value V limit 2.000 margin M PASS|FAIL

  with V = L / 1,000 and M = 2 / V, as every gate line (024-30, section
  2).

Why 2 R: since 026-05 the iteration that runs when the deletes end ends
with them, so the lag is the two iterations after it, R/4 + about 25 + R
(026-05, section 6; 026-04, section 4.1), independent of n and of the
fraction f. Without 026-05 it is at least that and at most about n/300 +
1,280 (026-04, section 4.1), so a regression shows at 1M with f = 1/4,
G4's setting (4,395 in 024-30, section 9).

The change: `java/stress/CountGates.java` (the gate line after M1's in
`g4()`, its class comment and the property `g4lag`) and
`java/stress/count-gates.sh`'s header. Nothing else; G4's heap gate
(`CountGates.BUFFER`, which 026-10 changes) untouched.


## 2. It fails without 026-05, and passes on main

Two runs of the same `CountGates.java` (fe947c7c), each in a slot.
Logs in /Users/f/fl/bench/2026-11-13/lag/runs/.

| Build | First cut | Lag | Lag / R | Margin | Result |
|---|---|---|---|---|---|
| `main` (c91443d8) with the gate | 1,001 | 1,281 | 1.281 | 1.56 | PASS |
| the same, 026-05 reverted       | 4,117 | 4,395 | 4.395 | 0.46 | FAIL |

* **Without 026-05**: the branch `026-11-nop8` of the clone (worktree
  /Users/f/fl/bench/2026-11-13/lag/nop8, not to land): fe947c7c with
  026-05's two commits reverted (`git revert d9822ebe 94421dd0`; only
  `Reclaim.java` changes, and the item file 024-02 kept as on `main`).
  `count-gates.sh g4`, 10:12, 21 s: the lag gate fails, with 4,395 and
  the first cut at 4,117 as in 024-30, section 9 (the code before
  026-05); every other G4 gate passes; COUNT GATES FAILED, status 1.
  Logs `nop8-g4.txt`, `nop8-g4-full.txt`.
* **On `main`**: `count-gates.sh` (all five gates) on the head
  fe947c7c, 10:13 to 10:15, 152 s: the lag 1,281, as 026-05 measured
  for this workload at 1M and f = 1/4 (026-05, section 6), margin 1.56;
  COUNT GATES OK. The other gates' counts are those of 026-05's run on
  57cbb21e (G4's M1 0.959, G5's kept 0.015), but for the heaps, which
  026-07's buffer changed (026-10). Logs `count-gates.txt`,
  `count-gates-full.txt`.

What the gate does not see: without 026-05 the lag depends on the
phase of reclaim's iteration when the deletes end (026-04, section 4.1),
and at 1M with f = 3/8 or 1/2 it was 1,857 and 1,850, under 2 R. At G4's
setting (1M, f = 1/4) it is 4,395, so the gate catches the regression
there; a run at another n (`count-gates.sh g4 n=...`) uses the same
limit.


## 3. Gates

On the head fe947c7c (`main` c91443d8 and the gate; `main` had not
moved at 10:16), each in a slot; logs in
/Users/f/fl/bench/2026-11-13/lag/runs/ (`gates.sh`, `gates.log`):

* `count-gates.sh` (all): COUNT GATES OK, 152 s, 10:13 to 10:15
  (`count-gates.txt`; section 2).
* `before-commit.sh`: BEFORE COMMIT OK (67 s; unit 1,712, f 89, demos
  14), 10:15 to 10:16 (`before-commit.txt`).

No expected value of an existing test changed; no question for Frans.


## 4. State

2026-11-13, 10:17. Done; ready to land. Clone
/Users/f/fl/bench/2026-11-13/lag/clone, branch `026-11-lag-gate`, from
`main` at c91443d8: fe947c7c (the gate), then this item and its Files
line in 026's readme (the commit after it). Gates of section 3 OK on
fe947c7c; the commit after it changes items only. The branch
`026-11-nop8` (worktree /Users/f/fl/bench/2026-11-13/lag/nop8) is the
check without 026-05, not to land.

To continue: land the branch; `night.sh`'s step `count-gates` then gates
the lag. To change the limit, `g4lag` (a property) or the default in
`CountGates.g4()`, and section 1 together. When 026-10 changes G4's heap
gate, this gate's line (after M1's) is untouched.
