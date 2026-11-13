# 026-09. Reclaim's scan without the values it does not rewrite

Created 2026-11-13 by Frans Lundberg. Status: made on a branch,
measured and gated; to land (Q1).

For release 2026.6: option (b) of 024-34's Q34-1. A reclaim step's scan
does not follow a value pointer whose stream position is at the cut
position pCut or later (the position is known before the follow; a new
option of `GetMany`, for reclaim only), and counts such a KV as its
key's bytes plus 100, its value length unknown. At 1M keys with a 20 MB
cache these loads are 43 % of a step's loads (024-34, section 4).

Made by the agent "kscan" of coord-1113 in a clone, on top of 026-05
(P8, on `main` since `fe5000ec`); the coordinator lands it.


Decided
=======

Frans, 2026-11-13, 09:38, "Yes", to the coordinator's recommendation:
"(b) for 2026.6, after P8 lands. P8 (026-05) changes how a reclaim step
scans, so (b) should be built and measured on top of it. It also
belongs with 2026.6's other changes to the stream's bytes, to be
measured with G3 and the reclaim cost. Until then, (a) stays as is."


What it changes
===============

* The steps' boundaries, so the stream's bytes: new StreamDigest
  digests, a new reference for the C clone; no record format.
* Reclaim's pacing: a step covers more keys when most values are new,
  so an iteration ends sooner in stream growth.
* Measured before and after: G3 (the stream kept, 024-30), ReclaimCost,
  026-04's workloads at 1M and 10M keys, the loads a step.
* Its relation to 026-05: P8's step walks keys it does not rewrite
  (026-05, Risks: "A step still loads the value of every key it walks; a
  keys-only scan would remove those loads"), so this is P8's follow-up.


## 1. The plan

1. Read 024-34 (section 6, Q34-1) and 026-05 (sections 2 and 3): P8's
   scan at the step's time, its end key E, the result with the KVs to
   rewrite only, and fault 13's rule that only KVs stored before pStart
   count toward a step's 16 kB.
2. The change (section 2), on a branch from `main` `c91443d8`: an option
   of `GetMany`, and two lines of `Reclaim.step`.
3. The cut's argument (section 3): what of 026-05, section 3, it
   touches.
4. Unit tests (section 4); the gates (section 5); counts before (`main`)
   and after (the branch), no timing (section 6): 026-04's workloads a
   to d at 1M and 10M keys at f = 1/4 (`FracRuns`), the loads a step,
   the count gates (G3 among them), `ReclaimCost`, StreamDigest.


## 2. The mechanism

### 2.1 `GetMany.valuesBefore`

* **What.** A new field of `GetMany` (java/src/bergdb/dag/GetMany.java),
  `Spos.NULL` by default. With a stream position p in it, a scan gives a
  KV whose value is not stored before p (stored at p or later, or not
  written yet: a vpos) without its value: `Kvt.value` null, `Kvt.spos`
  the value's position, and the pointer to the value is not followed, so
  nothing is loaded for it. A value stored before p is given as without
  the option; the keys, times and positions are the same either way.
* **When, by whom.** In `GetMany.Chain.next()`, after the end key's
  check and before the follow, for a pointer to a value (a segment
  leaf's klong shorter than `Klong.MAX_SIZE`, the test `setup()` uses):
  the value's position is the value's own (`ValueNode.getSpos()`) if the
  pointer holds it in memory, else the pointer's reference, which names
  it (Rule R is for index nodes only). The pair is read under the node's
  monitor, as a follow reads it (C2), so an eviction that unswizzles the
  value meanwhile gives the same position.
* **Who uses it.** `Reclaim.step` only, with p = pCut. The field is
  public, as the Core API's `GetMany` is, and documented as for
  reclaim's scan.

### 2.2 The count of a step

In `Reclaim.step`, `g.valuesBefore = it.pCut`, and a KV counted toward
the step's size adds `key.length * 8 + (rewrite ? value.length : 0) +
100`, where `rewrite` is "stored before pCut". A KV a step walks is in
one of three classes, by its value's position:

| Class | Value stored at | Rewritten | Loaded, before / after | Counted, before / after |
|---|---|---|---|---|
| R | before pCut          | yes | yes / yes | key + value + 100 (same)      |
| M | pCut to pStart       | no  | yes / no  | key + value + 100 / key + 100 |
| N | pStart on, or a vpos | no  | yes / no  | nothing (same)                |

* **R** is what the step rewrites, as on `main`: loaded once by the scan
  (no second read since 026-05), counted with its value.
* **M** values were written in the iteration before (by users or by its
  rewrites): the scan no longer loads them, and counts each as its key's
  bytes plus 100. This is the only change of the steps' boundaries.
* **N** values were written since the iteration began (fault 13's KVs):
  not counted, as since 026-05; now not loaded either.

The count stays a function of the stream: the position of every KV and
the length of every R value are the same whatever is resident, and the
class decides what counts, not whether a value happened to be in memory.
So the steps, and the records, do not depend on the cache (as 024-34,
section 4, found for `main`: eviction changed no byte).

### 2.3 With fault 13's rule (026-05, section 2.3)

Fault 13's rule chooses which KVs count (those stored before pStart:
classes R and M); 026-09 changes only how much an M KV counts. The rule's
argument holds as it is: a counted KV was live at tStart with that value
and the scan moves forward, so each is counted once; each counts at least
100 bytes, so a step that is not split at the reserve covers at most
writeSize / 100 + 1 counted KVs, and an iteration takes at most (the
counted sizes of the KVs live at tStart) / writeSize steps besides the
split ones: no more than before. The keys the user puts ahead of the
scan (class N) still count nothing, so they cannot keep an iteration
going (023-08, fault 13); a step's walk over them is still bounded by
its reserve, and now loads none of their values (026-05, section 7,
"The walk of a step").

What a step holds is bounded as on `main`: its result is class R only,
whose values count in full, so about writeSize bytes and one more KV;
the value limit of 015-50 applies to R as before.

In the first iteration pCut = pStart, so class M is empty and the steps
are those of `main`; only the loads of N go.


## 3. The cut's guarantee

026-05, section 3, holds as it is:

* **REWRITES (3.1).** A value v stored before pCut is class R: the scan
  follows its pointer (its position is before valuesBefore = pCut),
  gives it with its value, and the stop condition puts it in the result
  (ADD or ADD_AND_STOP), as on `main`. The ranges (lastKey, L] of the
  steps still join and reach E: `lastKeyOfStep` is set for every KV
  handled, M and N too, and the value limit's STOP leaves it before the
  KV, as before. The count decides only where a step ends, which the
  argument does not use (026-05, 3.1: "The count (2.3), CONTINUE (2.4)
  and the value limit change where steps end, not that the ranges
  join").
* **LIVEBELOW and COVER (3.2)**: unchanged; the touch marks the paths of
  the step's puts, the KVs of class R at the step's time.
* **INV-RESTART (3.3)**: the count is a function of the stream (2.2):
  the positions, pCut, pStart, the keys and the lengths of R values.
  Nothing of the scan is stored. RestartInvariance with reclaim (level3,
  step 3) checks it.
* **The model and the conformance (3.4)**: the Lean model has no scan;
  C-CUT checks every cut Java decides, in the model's state (level3's
  conformance with reclaim). The traces change (other steps), the checks
  not. Reclaim's FIRST lines (C-L) for the values it no longer loads are
  gone: a value not loaded is not touched.


## 4. Tests

New unit tests:

* `DbTesterGetMany.testValuesBefore`: 100 keys put, then 50 of them and
  100 new keys; a scan with `valuesBefore` the position after the first
  transaction gives the same 200 keys, times and positions as without
  it, the values of the 50 stored before it, and null for the 150
  others; again after a restart, when no value is in memory and the
  position comes from the pointer's reference.
* `Reclaim.Tester.testScanLoadsOnlyValuesToRewrite`: every object
  evicted after every transaction, single puts of 1 to 30 bytes on 200
  random keys until two cuts; the scans load no value at pCut or later
  (`Stats.Iteration.scanValueLoadsAtCut` 0) and at most the values they
  rewrite. Without the option it fails (probe: the line
  `g.valuesBefore = it.pCut` commented out): the first iteration loaded
  69 values and rewrote 15.

Every test of `Reclaim.Tester`, `ReclaimMaintainTester`,
`ReclaimReaderTester`, `ReclaimRetentionTester` and `DbTesterGetMany`
passes unchanged (85 tests, 3.4 s), among them 026-05's
`testStepScansAtItsOwnTime` and `testEndKeyBoundsTheScan` and 023-09's
liveness tests. No expected value of an existing test changed.


## 5. Gates

First on `ab2d4aed` (the branch with `main` `9c9650d6` merged), one
slot each; logs in kscan/runs/gates-ab2d4aed/:

* `java/before-commit.sh`: BEFORE COMMIT OK (65 s; 1,714 unit tests,
  89 f-tests), gate-bc.txt.
* `java/stress/level1.sh`: LEVEL 1 OK (159 s; MEM 129, SS 1.53),
  gate-l1.txt.
* `java/stress/level3.sh` (full): LEVEL 3 OK (498 s); RestartInvariance
  with reclaim, stream identical in its four configurations; the
  conformance with the Lean model, 35 traces, TRACECHECK OK 35, C-CUT 0
  of 794 CUT lines fail; gate-l3.txt.
* `java/stress/count-gates.sh`: COUNT GATES OK (164 s), as in section
  6.3 (G3 4.389, G5's dead klongs 32 against Q2's limit 70), and
  026-11's lag gate: 1,285 drive transactions, the limit 2,000;
  gate-cg.txt.
* `java/stress/level4.sh quick`: LEVEL 4 OK (140 s); the conformance
  with eviction, 18 traces, C-P and C-H 0 of 4,886 transactions fail;
  gate-l4.txt.

`main` then moved (026-10 landed, `e4ac051f`, and the provers' Lean
checkpoints), merged without conflict as `8e0de02b`; the gates again on
it, logs in kscan/runs/gate-*.txt:

* GATES2


## 6. Before and after: counts

Before: `main` `c91443d8` with 026-04-lag's three commits cherry-picked
(branch `026-09-before`, worktree
/Users/f/fl/bench/2026-11-13/kscan/before); after: `9667109b` with the
same three (`026-09-after`, worktree kscan/after); neither is to land.
Counts only, every run deterministic. The runs: kscan/runs/meas.sh and
meas2.sh, one slot each; outputs kscan/runs/{before,after}-*.txt, the
comparison kscan/runs/an.py.

### 6.1 026-04's workloads at 1M keys, f = 1/4

FracRuns (024-29, 026-04), n = 1M, 100-byte values, R = 1,000
transactions, until three cuts; the database's default cache. Loads:
the versions the steps read from the stream (`Reclaim.Stats`); WA_r:
reclaim's extra stream a user byte; K: the stream kept beyond the
user's records within R, in units of the fresh stream (G3's measure);
written: the stream's length at the end.

| Run          | Steps  | Loads     | A step | WA_r  | K peak | K mean | Written, MB |
|---|---|---|---|---|---|---|---|
| a, main      | 60,716 | 3,792,682 | 62.5   | 0.554 | 4.401  | 3.222  | 1,440.6     |
| a, 026-09    | 48,796 | 1,532,948 | 31.4   | 0.531 | 4.389  | 3.221  | 1,440.4     |
| b, main      | 60,638 | 3,971,726 | 65.5   | 0.365 | 6.157  | 4.443  | 1,396.5     |
| b, 026-09    | 48,381 | 1,899,911 | 39.3   | 0.370 | 6.099  | 4.414  | 1,381.4     |
| c, main      | 68,939 | 4,264,760 | 61.9   | 0.362 | 6.461  | 4.747  | 1,864.6     |
| c, 026-09    | 56,213 | 2,332,837 | 41.5   | 0.349 | 6.457  | 4.761  | 1,848.9     |

* **The loads fall by 45 to 60 %, the steps by 18 to 20 %**, and the
  loads a step to 50 to 67 % of `main`'s. As 024-34 found, most loads
  of a step were values at pCut or later.
* **The iterations with nothing to rewrite** (every other one: all
  values at pCut or later, class M) take 44 to 46 % fewer steps (a:
  12,518 to 6,996; b: 13,333 to 7,247; c: 13,326 to 7,245) and load
  almost nothing (a: 876,694 to 8,320). 026-04, section 4.3, noted that
  such iterations are paced by the step's 16 kB of scan.
* **The stream kept and written: no worse.** K peak and mean within 1 %
  (G3's 4.401 to 4.389), WA_r within 0.02, the stream written the same
  or up to 1.1 % less. The iterations that rewrite (class R) take about
  as many steps as before: their R values count in full, as before.

Workload (d), back to empty (G4's: 1M keys put in key order and deleted,
then a drive of 40 R), with `g4its=1`:

* The lag: 1,281 to 1,285 transactions (026-05's 1,265 to 1,286).
* G4's kept, the most in the last R, over the twin's: 0.959 to 0.988.
* **The stream written by the end of the drive: 362.6 to 391.3 MB
  (+7.9 %).** During the fill and the deletes the iterations run faster
  (8 against 6, so the kept stream after the deletes is 176.7 MB
  against 263.9 MB), and they rewrite more values that a later delete
  removes (371,191 against 245,309): 026-05's work ahead of an
  ascending mass delete (026-05, section 6 and Q3), within the internal
  fraction.

### 6.2 026-04's workloads at 10M keys, f = 1/4

As 6.1 with n = 10M. `main`'s runs end at their third cut; the
branch's at the same transaction as `main`'s (`cuts=99 max=...`,
kscan/runs/rest2.sh), so that the window of WA_r and K (from the end
of the first iteration, the same transaction in both, to the last) is
the same. Workload (a) also ended at its own third cut (`a, 3 cuts`;
kscan/runs/after-10m-a-3cuts.txt). Outputs
kscan/runs/{before,after}-10m-*.txt; written in GB.

| Run               | Steps   | Loads      | A step | WA_r  | K peak | K mean | Written |
|---|---|---|---|---|---|---|---|
| a, main           | 568,053 | 43,477,456 | 76.5   | 0.447 | 1.970  | 1.383  | 20.73   |
| a, 026-09         | 491,210 | 21,687,214 | 44.2   | 0.510 | 1.933  | 1.346  | 21.10   |
| a, 026-09, 3 cuts | 453,506 | 19,678,153 | 43.4   | 0.497 | 1.933  | 1.379  | 19.76   |
| b, main           | 582,109 | 39,729,831 | 68.3   | 0.393 | 5.556  | 3.960  | 12.87   |
| b, 026-09         | 477,651 | 19,814,545 | 41.5   | 0.428 | 5.572  | 3.959  | 13.02   |
| c, main           | 682,339 | 45,124,635 | 66.1   | 0.454 | 2.226  | 1.637  | 21.13   |
| c, 026-09         | 572,022 | 25,147,242 | 44.0   | 0.471 | 2.200  | 1.614  | 21.22   |

* **The loads fall by 44 to 55 %, the steps by 14 to 20 %**, as at 1M.
  On `main` the steps load about 4 values or nodes a user put (a:
  43.5M loads in 10.4M puts), with 026-09 about 2.
* **The iterations with nothing to rewrite** take 44 to 46 % fewer
  steps (a: 125,167 to 69,961; b: 133,333 to 72,465; c: 133,251 to
  72,440), load 88 to 92 % less (b: 11,650,249 to 1,283,879), and span
  about half the stream (W/L0, b: 0.279 to 0.151; c: 0.056 to 0.031).
* **K is the same or lower**: within 0.3 % in (b), 1.2 to 1.4 % lower
  in (c), 1.9 to 2.7 % lower in (a).
* **WA_r rises by 4 to 14 %** (c 0.454 to 0.471, b 0.393 to 0.428,
  a 0.447 to 0.510): the stream written in the window grows 1.2 to 4.4 %.
  At 1M the change was -4 to +1 %. The cause is the pacing (2.2): the
  iteration that rewrites starts sooner after the last one that
  rewrote, so fewer of its values were overwritten or deleted meanwhile
  and it rewrites more (b's third iteration: 7,062,743 values against
  6,598,418), and the cuts come a little sooner (so K is lower). On
  `main` an M KV's value counted as if it were to be rewritten, which
  slowed the iterations that rewrite nothing, and so the cuts and the
  rewrites: 026-09 moves reclaim a little along the trade between the
  stream kept and the stream written that f sets (026-04).

Workload (d) at 10M (`g4its=1`), as at 1M:

* The lag: 1,279 to 1,294 transactions; G4's kept over the twin's:
  1.006 to 0.981.
* **The stream written by the end of the drive: 3,278.0 to 3,504.5 MB
  (+6.9 %)**; the kept stream after the deletes 2,615.2 to 1,964.9 MB
  (-25 %); the values rewritten during the fill and the deletes
  3,055,178 to 3,961,273 (+30 %), in 11 iterations against 9.

### 6.3 The count gates (`count-gates.sh`, 1M keys)

| Gate | Quantity                                  | main    | 026-09  | Limit     |
|---|---|---|---|---|
| G1   | largest record without values, bytes      | 112,048 | 102,400 | 1,000,000 |
| G2   | reachable key nodes over the twin's       | 1.295   | 1.295   | 2         |
| G3   | (kept - H_R) / L0, peak                   | 4.401   | 4.389   | 6         |
| G4   | M1 kept over the twin's                   | 0.959   | 0.988   | 2         |
| G4   | M5 dead klongs (twin 18)                  | 18      | 20      | 36        |
| G5   | M1 kept over twice the twin's + 600 kB    | 0.015   | 0.108   | 1         |
| G5   | quiet after call, of 20,000               | 3,015   | 3,007   | 15,000    |
| G5   | M5 dead klongs (twin 0)                   | 22      | 32      | 30        |

**G5's M5 fails with 026-09: 32 dead klongs, the limit 30** (the
twin's plus B = 30, "a leaf's klongs", 023-03's C4). The rest pass with
margins as on `main`. What the 32 are (probe
kscan/probe/bergdb/core/G5Dump.java, output kscan/runs/g5dump-*.txt):
the emptied database's six reachable key nodes are leaves that hold
BergDB's own keys, which `maintain()` overwrites (the reclaim row, the
filler), and each keeps the shadowed versions of its key since its last
compaction: 5, 5, 4, 7, 5, 6 with 026-09; 1, 5, 0, 6, 4, 6 on `main`.
Every node holds at most theta = 7, as 024-23's compaction guarantees
(TP39). How many remain depends on when the last writes came, a phase:
G5's emptied database at other sizes (`CountGates g5 n=...`, output
kscan/runs/g5-dead-scan.txt and above):

| n    | 100k | 200k | 300k | 500k | 700k | 1M | 1.5M |
|---|---|---|---|---|---|---|---|
| main | 23   | 13   | 28   | 23   | 28   | 22 | 15   |
| 026-09 | 20 | 24   | 15   | 29   | 19   | 32 | 22   |

The mean is about the same (21.7 and 23.0); `main` reaches 28 of 30.
The limit B = 30 predates theta: one leaf could reach it, but the
emptied database has six such leaves, up to 42. Q2 (section 8):
the limit the twin's plus 70, theta times a_n = 10 nodes; applied in
its own commit (`c9521d6b`, `CountGates.g5`).

### 6.4 ReclaimCost

`java/stress/ReclaimCost.java` (011-04, "Level 3 cost"): 30 MB of live
data, 4-byte keys, single-put transactions, K = 1, a CutStream in
memory, until 7 cuts. WE: user bytes over stream bytes appended; SE:
user bytes accessible within R over the stream kept; sB: reclaim's
step bytes, MB.

| Work, 100-byte values | WE, main / 026-09 | SE, main / 026-09 | Kept MB      | sB MB        |
|---|---|---|---|---|
| uniform               | 0.1078 / 0.1094   | 0.1150 / 0.1161   | 526.0, 521.4 | 437.4, 421.1 |
| hot                   | 0.2193 / 0.2201   | 0.1355 / 0.1359   | 452.5, 450.8 | 146.8, 143.7 |
| cold                  | 0.2458 / 0.2463   | 0.1411 / 0.1415   | 434.8, 433.5 | 122.2, 120.6 |

| Work, 1,000-byte values | WE, main / 026-09 | SE, main / 026-09 | Kept MB      | sB MB        |
|---|---|---|---|---|
| uniform                 | 0.5324 / 0.5422   | 0.4032 / 0.4104   | 151.2, 148.5 | 569.4, 537.2 |
| hot                     | 0.6016 / 0.6068   | 0.2758 / 0.2778   | 223.4, 221.7 | 444.7, 431.2 |
| cold                    | 0.6429 / 0.6484   | 0.2671 / 0.2680   | 230.9, 230.2 | 385.1, 372.4 |

Slightly better everywhere, at both value sizes: up to 1.8 % more WE,
1.8 % more SE, 3 to 6 % fewer step bytes (outputs
kscan/runs/{before,after}-rc-*.txt and -rc1000-*.txt). Here the
database is small (30 MB live) and the cuts come often, unlike
section 6.2.

### 6.5 StreamDigest

`StreamDigest all` with `main`'s jar and with the branch's (kscan/runs/sd.sh;
outputs sd-before.txt, sd-after.txt, sd-compare.txt): 12 of 48 digests
differ, all four runs (plain, reads, restarts, restarts-once) of three
configurations with reclaim; the four runs of each still agree with one
another, as RestartInvariance requires. The configurations without
reclaim (l2-*) and l3-node14 (50 keys) are the same.

* l3-every1: the stream 1,837,024 to 1,815,920 bytes (-1.1 %).
* l3-node8: 6,945,376 to 6,986,120 (+0.6 %).
* l3-node62: 8,506,808 to 8,074,064 (-5.1 %).

No test pins these digests; they are a reference for later changes
that must not change the records, and for the C clone (022). Q3.


## 7. Risks and limits

* **A step walks more KVs of class M.** Each counts at least 100 bytes,
  so a step covers at most about writeSize / 100 = 164 of them; before,
  writeSize / (key + value + 100): about 75 with 100-byte values, 14
  with 1,000-byte values. Each costs a walk in the index (and the loads
  of index nodes not resident), no value load. The reserve (about 2,759
  index nodes followed) bounds a step as before.
* **The pacing.** An iteration that rewrites nothing ends sooner, so
  the cuts come sooner: at 10M keys reclaim writes 1.2 to 4.4 % more of
  the stream and keeps 0 to 2.7 % less (section 6.2); back to empty
  writes about 7 % more before its drive (6.1, 6.2), within the
  internal fraction.
* **The count is a pacing measure, no longer an estimate of stream
  space** for class M (it was "an approximation of the stream space of
  the KVs stored before pStart"). A step's record is bounded by class
  R, counted in full, as before.
* **Bytes.** Other step boundaries, so other records after the first
  iteration: StreamDigest's digests of the configurations with reclaim
  change (section 6.5); no record format change, no rerun rule. The C
  clone (022) follows releases, so it gets a new reference only if it
  follows 2026.6.


## 8. Questions for Frans

Each is decided here by its recommendation, so that the work goes on;
Frans may overturn it.

* **Q1. Land 026-09?** The numbers (sections 6.1 to 6.4): the steps'
  loads fall by 44 to 60 % and the steps by 14 to 20 %, at 1M and 10M
  keys. At 1M the stream kept and the stream written are the same
  (within 1.1 %). At 10M, over the same window, the stream kept is 0
  to 2.7 % lower and the stream written 1.2 to 4.4 % higher (WA_r +4 to
  +14 %): the pacing of section 2.2. Back to empty writes about 7 %
  more by the end of its drive, its lag the same. ReclaimCost is
  slightly better. Every gate passes, G5 with Q2's limit.
  Recommended: land. The loads it drops are reads from the stream of
  values that the step does not rewrite, about 2 of `main`'s 4 loads a
  user put at 10M (024-04: operations proportional to their work);
  the writes it adds are appends, a few % of the stream, on the trade
  between the stream kept and written that f sets (026-04). Not
  measured: time (no timing slot today); 026-04's timing pass at 10M,
  if run after 026-09 lands, shows the net.
* **Q2. G5's limit on dead klongs** (section 6.3): 026-09 gives 32 at
  1M keys against the limit 30 (the twin's plus B = 30, 023-03's C4),
  a phase of the six leaves of BergDB's own keys, each at most theta
  = 7 (024-23); `main` gives 13 to 28 at other sizes. Recommended: the
  twin's plus 70 (theta in each of a_n = 10 key nodes, as M4 allows
  a_n more nodes than the twin's), in its own commit `c9521d6b`.
  Changes the limit of an existing gate.
* **Q3. The stream's bytes** (section 6.5): the steps after the first
  iteration end elsewhere, so the configurations with reclaim get other
  StreamDigest digests; no test pins a digest. Recommended: accept, as
  026-09's decision foresaw.
* **Q4. `GetMany.valuesBefore` public**: the Core API's `GetMany`
  fields are public and `Reclaim` (bergdb.core) cannot reach a package
  field of bergdb.dag. Recommended: a public field whose Javadoc says it
  is for reclaim's scan (as above); a Core API user who sets it gets KVs
  without values, as documented.


Log
===

2026-11-13. Registered by coord-1113 (Frans, 09:38), from 024-34's Q34-1.


State
=====

2026-11-13, 12:35. The first agent stopped on API errors at about
11:15; the second ("kscan" again) continued. Clone
/Users/f/fl/bench/2026-11-13/kscan/clone, branch `026-09-keys-only-scan`:
`9667109b` (the change and its two tests), `c9521d6b` (G5's limit, Q2),
`53ed98e1` (this item), main merged (`ab2d4aed`, then `8e0de02b`).
Done: the change, the tests, the counts at 1M and 10M, ReclaimCost,
StreamDigest, the gates on `ab2d4aed`, Q1's recommendation. Running,
detached (nohup): kscan/runs/gates.sh bc l1 l3 cg l4 traces on
`8e0de02b`, log kscan/runs/gates.log, outputs kscan/runs/gate-*.txt (and
traces/summary.txt). Not done: section 5's second round (GATES2).
