# 024-14. The thresholds of merges at the delete, measured in Java

Created 2026-11-11 by Frans Lundberg. Status: open.

Step 2 of 024-11's plan (section 7): the thresholds of merges at the
delete (MG) measured in Java at 1M and 10M keys, so that Frans can choose
them before the merge is written into 024-12's Lean tree model. Frans
approved this morning (09:25) merges alone, the bound BU1, BD13 as the
measured gate (BU2), and these measurements before the model is written.
A measuring build, not the implementation: nothing here is landed.

Names are 024-11's: B the node size (30), m the least live klongs of a
node that is not a root, h the most klongs of a last version that a time
split keeps (more: a space split), c the most live klongs that a merge
puts in one node (024-11, section 5.1). Threshold sets are written
"m/h/c".


## 1. Summary

State at 13:50: the 1M grid is complete; at 10M: k = 2 and 024-03's
sparse shape for P5, m8 and dense, churn, and the timed put path for
main, m8 and dense. Not run at 10M: m9, k10-hashed and the other
shapes (section 9).

* **Correctness and thrash, plainly: no threshold set showed a
  correctness problem or a thrash.** UnlinkFuzz strict, 36 runs a set,
  0 failures; CleanupRule with restarts, 16 runs, all exit 0; no 10M or
  1M run failed but by a data-directory clash of my scripts (section 5);
  no split-merge cycle in 560 to 860 constructed trials a set (section
  6). For
  024-21 (Frans, 11:55: P5's thresholds as named constants for now): the
  change to other thresholds is the three constants and h in rule O
  (`handleFullNode`'s `maxNodeSize / 2`), plus `dirtyNodeBound`'s merge
  count, whose sharper form is argued for P5's set only (section 2).
* **Sets measured**: main (no merges), P5 7/15/15, m8 8/17/17, m9
  9/18/19, dense 10/20/20, each on a build checked by UnlinkFuzz strict
  (36 runs a set, 0 failures) and CleanupRule with restarts (section 3).
* **Times the twin, the worst row at 1M** (15 shapes, section 4.2): main
  21.5, P5 1.90, m8 1.49, m9 1.35, dense 1.25. P5's worst is k = 2 in
  every delete order (BD13's 2 with 0.10 to spare); m8 to dense remove
  it (1.00 to 1.11). Their worst is k = 100, descending deletes.
* **BU1 and BU2 hold** in every shape for every set with merges; main
  fails BU2 in 13 of 15 shapes.
* **The put path (databases that never delete)**: P5's is main's to the
  byte. A higher h keeps fuller nodes: key nodes after random overwrites
  13 % (m8) to 28 % (dense) fewer; record bytes a put in a random fill 0
  % (m8) to 2.8 % (dense) more at 1M, **1 % (m8) and 4 % (dense) more at
  10M**, an overwrite's 0 % (m8) and 3 % (dense) more at 10M. **Timed at
  10M, no set puts slower** (fill 53,256 and 54,176 puts/s for m8 and
  dense against main's 50,961 here and 51,971 in 024-03).
* **The delete**: in key order cheaper than main with every set (0.92 to
  0.99); at random up to 1.08 (m8), 1.09 (m9) and **1.17 (dense) times
  main's record bytes, 1.28 in stream bytes: the dense set breaks BU4**.
* **Thrash**: none found in any set (worst 0.20 new nodes an operation,
  time splits); sets with c = h = 2m (dense, and m9) have a split-merge
  cycle on paper, P5 and m8 do not (section 6).
* **Recommendation: m8, 8/17/17** (section 8): P5's worst shape gone
  (1.90 to 1.07, at 10M too), at most 1.49 in every shape, 1 % more
  bytes a put at 10M and no slower, BU4 kept, CB4's separation kept.
  Alternatives: P5 (no put-path change, 0.10 from BD13 at k = 2), dense
  (best ratios, 4 % more bytes a put, over BU4 at random deletes).


## 2. The measuring build

* **Base: P5's merge with fault 12's fix**, the least work that gives a
  correct merge: branch `023-v12-fix` of 023-08's clone, which is P5's
  head `71e386de` (branch `023-p5-merge`, the merge of 023-05 P5 in the
  seven commits `163fed3f` to `71e386de` on P4's head `aeb364ce`) and one
  commit, `92bf4eb5` (023-08, review C, fault 12: `spaceSplitInPlace`
  points the segment leaf's klong of tt in place; UnlinkFuzz's modes
  `order=shuffle` and `dup=P`). It stands on P4's head, before 2026.4's
  last fixes (the sort of a transaction's keys, K4's count): a measuring
  base, as 024-11's probe was.
* **One commit on it**, `bff5e810` on branch `024-14-thresholds`:
  `-Dbergdb.thr=m,h,c` sets the three thresholds for a JVM, given for B =
  30 and scaled to another B as v B / 30 (m at least 2); without it P5's
  formulas, max(2, B / 4), B / 2, B / 2, so the default build is P5's to
  the byte. h replaces `maxNodeSize / 2` in `handleFullNode` (a last
  version of more than h klongs is space split), m and c replace
  `mergeBelow` and `mergeMax`. `Dag.thresholds(B)` refuses a set that
  does not keep V1: a space split's halves (h / 2) and a redistribution's
  halves ((c + 1) / 2) at least m, one merged node 2m - 1 to c, h and c at
  most B - 2. `dirtyNodeBound` keeps P5's sharper merge count for P5's
  set only, and counts one merge a level a delete (P5's safe count) for
  any other; the overflow count uses min(B / 2, B - h, B - c) - 3 for its
  "room after a replacement". Two counters, `Dag.statTimeSplits` and
  `statSpaceSplits`, count rule O's two outcomes. UnlinkFuzz's strict
  check uses the set's m.
* **main for comparison**: branch `024-14-main-counts` (`44fa9b87`):
  `main` at `1fe5f180` with the same two split counters and nothing else.
* **A database is rerun with the thresholds of the JVM that starts it**:
  a run must start its database with the set that wrote it. The probe's
  databases never restart; CleanupRule's restarts below use one set a
  JVM.
* **Not for landing.** The thresholds become rules of format 7 (024-11,
  section 5.1) in step 4, as constants, not properties.

### 2.1 The sets measured

| Set   | m/h/c    | Why                                                          |
|---|---|---|
| main  | -        | 2026.4's put path and delete: no merges                      |
| P5    | 7/15/15  | P5's: B / 4, B / 2, B / 2                                    |
| m8    | 8/17/17  | m = 8 lifts k = 2 above m; h = c = 2m + 1, the least such h  |
| m9    | 9/18/19  | between: the model's best set below the dense one            |
| dense | 10/20/20 | 024-11's dense set (QU4)                                     |

m8 and m9 were chosen in 024-11's model (`sim.py`), 30,000 keys, on
times the twin for k = 2, 3, 10, 100 in the three delete orders:

| m/h/c    | Asc                    | Desc                   | Hashed                 |
|---|---|---|---|
| 7/15/15  | 1.90, 1.16, 1.38, 1.68 | 1.90, 1.50, 1.57, 1.91 | 1.90, 1.51, 1.51, 1.50 |
| 8/16/16  | 1.00, 1.13, 1.34, 1.59 | 1.46, 1.46, 1.57, 1.68 | 1.18, 1.35, 1.30, 1.45 |
| 8/17/17  | 1.01, 1.07, 1.29, 1.50 | 1.37, 1.36, 1.55, 1.68 | 1.12, 1.32, 1.28, 1.27 |
| 9/18/18  | 1.04, 1.02, 1.24, 1.41 | 1.29, 1.38, 1.27, 1.55 | 1.15, 1.24, 1.16, 1.32 |
| 9/18/19  | 1.04, 1.00, 1.16, 1.32 | 1.20, 1.12, 1.27, 1.55 | 1.11, 1.27, 1.21, 1.32 |
| 10/20/20 | 1.00, 1.02, 1.01, 1.32 | 1.02, 1.06, 1.23, 1.36 | 1.10, 1.00, 1.03, 1.18 |
| 10/20/21 | 0.99, 1.02, 0.98, 1.18 | 1.02, 1.03, 1.23, 1.36 | 1.08, 0.94, 1.00, 1.14 |

* **k = 2 is m's alone**: a fill in key order leaves about 12.6 keys a
  leaf, half of them 6.3; with m = 7 a leaf keeps them unmerged, with m =
  8 it merges. So m = 8 is the smallest m that removes P5's worst row.
* **c = 2m + 1 or more** (8/17/17, 9/18/19) keeps a redistribution's
  halves above m, so that the next delete does not merge again.


## 3. Correctness of each set

Run on the frozen build `b1` before any measurement, no lock (one core):

* **UnlinkFuzz strict** (`tools/fuzz.sh`): P5's matrix of 023-05 (shapes
  random, fifo and long, 40 to 70 % deletes, 6 to 30 operations a
  transaction) and one of 400 keys and 60 operations, each sorted and with
  fault 12's modes (`order=shuffle dup=20`), at node sizes 8, 14 and 30:
  V1 with the set's m after every transaction, every get and scan at
  every time against a model: **36 runs a set, 0 failures, for all four
  sets** (`out/fuzz-*.txt`; 09:30 to 10:13). At B = 8 and 14, m8 scales
  to P5's values (2/4/4, 3/7/7); B = 30 is where it differs, and there
  every set merged hundreds of times a run, in both modes.
* **CleanupRule hello** at 100,000 keys, keep = 2 and 10, ascending and
  random deletes, each set (16 runs): lookups against its model after the
  fill, the deletes, the drive and **a restart** (the rerun of the merges
  with the same set): all 16 exit 0 (`out/cr/`).
* Every probe run below checks nothing itself but the counts; its
  scans count every live key (keys = the live keys, in every row).


## 4. 1M keys

### 4.1 Method

The probe `THR` (`14-merge-thresholds/THR.java`), one JVM a run, on
PF1's setup (024-03, section 2): a `FileStream` with the builder's
defaults (startup distance 50 MB, cache indicator 200 MB, eviction on), a
test clock of 1 ms a transaction, retain 1 s; keys `/k/%010d`, values of
100 bytes, 100 operations a transaction, no sync. The random fill is
PF1's order, so main's counts are 024-03's: 88,974 key nodes after a
random fill of 1M (024-03, section 3: 88,974) and 42,075 after "every
30th kept" (section 5: 42,075). The shapes:

* **seq / random fill**: 1M keys in key order or at random.
* **over**: the random fill, then 20,000 transactions of 100 overwrites of
  random keys (the steady state; 024-03's drive).
* **kK-order**: a fill in key order, then every key deleted but each K-th,
  in ascending, descending or hashed order (a fixed random permutation),
  100 a transaction; then the drive, 10,000 transactions of overwrites.
* **k30-rand**: 024-03's "sparse": a random fill, every 30th kept,
  ascending deletes; the drive.
* **mass**: 024-03's mass delete: a random fill, keys 0 to 0.9 n deleted
  in ascending order, the survivors in one run at the end; the drive.
* **churn**: a random fill, then 20,000 transactions of 50 deletes of
  random live keys and 50 puts of random keys of 0 to 2n that are not
  live; the drive.
* **The twin** (023-02, section 3.2), for every shape with deletes: a
  fresh database of the same build with the live keys, in key order after
  a fill in key order, at random after a random fill; then the same
  drive. Its fill is the set's own put path, so the dense set's twin of a
  random fill is denser than P5's.

Counted: the key nodes a full scan follows (CleanupRule's counting
follower), bytes a phase (the user's records, `rec`; and the stream's
growth, `stream`, which includes reclaim's records), rule O's time and
space splits, merges (one node, two nodes) and nodes taken back, all per
operation; "kept" is the stream from the first available position.

**Run**: 09:38 to 10:36, 80 runs one at a time without the lock (one
JVM, about 1.4 cores), two of them (over for P5 and m8) again at 10:37
after a clash of data directories with hold A; under the day's
background load (1-minute load 4 to 13). Counts are exact and repeat;
times here are not timing measurements and are given only for the
scans, as a ratio within a row.

### 4.2 Key nodes against the twin

After the deletes; "x" is the database's key nodes over its twin's,
both of the same set. For main the twin of a fill in key order has
7,899 key nodes at k = 10 (12.66 keys a node).

| Shape       | main  | P5   | m8   | m9   | dense |
|---|---|---|---|---|---|
| k2-asc      | 2.00  | 1.90 | 1.07 | 1.00 | 1.00  |
| k2-desc     | 2.00  | 1.90 | 1.06 | 1.03 | 1.00  |
| k2-hashed   | 2.00  | 1.90 | 1.11 | 1.11 | 1.09  |
| k3-asc      | 3.00  | 1.12 | 1.00 | 1.02 | 1.00  |
| k3-desc     | 3.00  | 1.20 | 1.16 | 1.06 | 1.02  |
| k3-hashed   | 3.00  | 1.49 | 1.32 | 1.26 | 0.96  |
| k10-asc     | 10.00 | 1.41 | 1.29 | 1.00 | 1.10  |
| k10-desc    | 10.00 | 1.29 | 1.12 | 1.27 | 1.15  |
| k10-hashed  | 10.00 | 1.46 | 1.26 | 1.12 | 1.03  |
| k100-asc    | 21.5  | 1.52 | 1.36 | 1.11 | 1.12  |
| k100-desc   | 21.5  | 1.68 | 1.49 | 1.35 | 1.25  |
| k100-hashed | 21.5  | 1.45 | 1.26 | 1.12 | 1.03  |
| k30-rand    | 15.7  | 1.44 | 1.29 | 1.17 | 1.22  |
| mass        | 1.23  | 1.25 | 1.20 | 1.14 | 1.11  |
| churn       | 1.65  | 1.17 | 1.15 | 1.07 | 1.06  |
| worst       | 21.5  | 1.90 | 1.49 | 1.35 | 1.25  |

* **After the drive** (10,000 transactions of overwrites) the ratios
  stay within 0.02 of these but for four rows: k10-desc for m8 1.29 and
  for dense 1.25 (from 1.12 and 1.15); k30-rand 1.05 to 1.10 for every
  set (its twin grows under the drive, 2,685 to 3,666 nodes for P5, as
  024-03's did); churn 1.01 to 1.02 for every set with merges, main 1.36.
  The worst after the drive: P5 1.90, m8 1.48, m9 1.35, dense 1.26.
* **BU2 (BD13's factor 2) holds for every set with merges in every
  row**, P5 with 0.10 to spare (k = 2 in all three orders), the others
  with 0.5 or more. main fails it in 13 of 15 rows.
* **BU1 holds where the probe can see it**: the counting walk counts the
  nodes that are not roots with fewer than 7 and fewer than 10 live
  klongs (`under7`, `under10`). In every run with merges `under7` is 1,
  and for the dense set `under10` is 1 too: one node of the top segment
  tree that holds the internal keys (main's twins have it as well), not a
  node of the user's keys. So P5 and the dense set meet BU1 exactly in
  every shape; for m8 and m9 the probe shows at least 7 (their m is 8
  and 9: UnlinkFuzz strict checks that, section 3). main: up to 72,001
  nodes under 7 (k = 2 and 3).
* **The model was right** (024-11, 3.4, here section 2.1) within about
  0.1 in most rows; it was pessimistic for the dense set's hashed rows
  (0.96 to 1.09 against 1.00 to 1.18).
* **The order still matters**: descending deletes are the worst order for
  every set (P5's sibling rule, M1, takes the left sibling first), up to
  1.68 (P5), 1.49 (m8), 1.35 (m9), 1.25 (dense) at k = 100.

### 4.3 The put path: databases that never delete

| 1M keys                         | main, P5 | m8      | m9      | dense   |
|---|---|---|---|---|
| random fill: key nodes          | 88,974   | 80,025  | 78,209  | 72,109  |
| random fill: record bytes a put | 231.6    | 231.7   | 233.7   | 238.0   |
| random fill: space splits a put | 0.0890   | 0.0800  | 0.0782  | 0.0721  |
| random fill: time splits a put  | 0.0123   | 0.0258  | 0.0309  | 0.0600  |
| seq fill: key nodes             | 78,996   | 78,750  | 78,668  | 78,666  |
| seq fill: record bytes a put    | 168.6    | 168.9   | 168.9   | 169.1   |
| over: key nodes at the end      | 111,399  | 96,738  | 90,725  | 80,554  |
| over: record bytes an overwrite | 402.6    | 400.3   | 399.9   | 404.3   |
| over: stream bytes an overwrite | 447.0    | 444.1   | 443.2   | 446.3   |
| over: time splits an overwrite  | 0.0999   | 0.1163  | 0.1246  | 0.1426  |
| over: space splits an overwrite | 0.0112   | 0.0084  | 0.0063  | 0.0042  |
| over: kept at the end, MB       | 1,122    | 1,118   | 1,120   | 1,135   |
| over: scan of 1M keys, ms       | 2,913    | 2,753   | 2,396   | 2,382   |

* **P5's put path is main's to the byte**: the same key nodes, bytes and
  splits in the random fill and the overwrites (h = 15 in both).
* **A higher h trades space splits for time splits.** A last version of
  16 to h live klongs is now replaced, not split, so nodes stay fuller:
  under random overwrites 13 % (m8) to 28 % (dense) fewer key nodes, as
  the model said (024-11, 3.4: 28 %), and 40 % more time splits for the
  dense set (the model: 41 %).
* **Bytes do not follow the splits**: an overwrite writes 0.4 to 0.7 %
  fewer record bytes with m8 and m9 and 0.4 % more with the dense set; the
  random fill 0.0, 0.9 and 2.8 % more. A replaced node is written whole
  either way; fewer, fuller nodes write as much as more, emptier ones.
* **The fill in key order does not change** (the leaves split full, far
  above any h).

### 4.4 The delete's cost

Record bytes a delete in the delete phase, against main's (BU4: at most
1.2 times 2026.4's); stream bytes (with reclaim's records) in brackets.

| Shape       | main          | P5          | m8          | m9          | dense       |
|---|---|---|---|---|---|
| k2-asc      | 61.0 (99.2)   | 0.99 (0.99) | 0.94 (0.92) | 0.94 (0.91) | 0.94 (0.92) |
| k2-hashed   | 86.1 (179.5)  | 0.99 (0.98) | 1.08 (1.10) | 1.07 (1.14) | 1.14 (1.28) |
| k3-hashed   | 95.4 (201.0)  | 1.02 (1.04) | 1.03 (1.05) | 1.05 (1.10) | 1.15 (1.25) |
| k10-asc     | 57.7 (74.1)   | 0.92 (0.93) | 0.92 (0.93) | 0.92 (0.93) | 0.92 (0.93) |
| k10-hashed  | 100.9 (196.4) | 1.05 (1.05) | 1.04 (1.04) | 1.08 (1.09) | 1.16 (1.20) |
| k100-hashed | 104.2 (190.2) | 1.02 (1.03) | 1.04 (1.06) | 1.09 (1.11) | 1.17 (1.21) |
| k30-rand    | 67.2 (107.9)  | 0.97 (0.97) | 0.99 (0.98) | 0.98 (0.97) | 0.99 (0.96) |
| mass        | 62.9 (101.0)  | 1.03 (1.03) | 1.05 (1.06) | 1.03 (1.05) | 1.05 (1.04) |
| churn       | 299.5 (383.0) | 0.99 (0.99) | 0.99 (0.99) | 1.01 (1.01) | 1.04 (1.03) |

* **Deletes in key order cost less with merges** (0.92 to 0.99): the
  merged nodes are fewer and are written once.
* **Deletes at random cost more with a higher m**: up to 1.09 (m9) and
  1.17 (dense) in record bytes, 1.28 in stream bytes for the dense set
  (k2-hashed): a node of the dense set holds more live klongs, so a
  delete's leaf, and the merged node, are larger records, and a merged
  node is merged again sooner (merges a delete, hashed: P5 0.08 to 0.10,
  dense 0.11 to 0.13). **The dense set breaks BU4's 1.2 in stream bytes**
  for hashed deletes (1.20 to 1.28); P5 and m8 stay at or under 1.10.
* **Merges a delete**: 0.01 (P5, k = 2) to 0.19 (k = 100, ascending);
  CB3's amortized bound holds with room (at most 0.19 merges a delete in
  every run). Taken back (made and left out in one transaction): up to
  0.27 a delete for P5 in key order, 0.002 for the dense set in hashed
  order.
* **After the deletes the drive costs less with merges**: bytes a drive
  transaction over the twin's, k10-hashed: main 1.63, P5 1.13, m8 1.16,
  m9 1.19, dense 1.24; k2-asc: main 1.20, P5 1.17, m8 1.08, m9 1.09,
  dense 1.09. The dense set's leaves are fuller, so they split sooner
  under the drive (more time splits), which costs back part of its gain.

### 4.5 The stream kept and the scans

* **Kept after the drive** (MB, the set over its twin): one sample at the
  end, at whatever phase of the cut it was, so a difference under about
  40 % is the cut's phase, not the set (the twins themselves differ by
  2x between sets, 104 against 204 MB at k100-asc). Rows with a clear
  difference: main against its twin in k10-desc (470 / 234), k3-hashed
  (591 / 326), mass (532 / 227); every set with merges is as far from
  its twin in those rows (k3-hashed 543 to 573 / 327). With 10,000 drive
  transactions (2 to 4 reclaim iterations) reclaim has not settled at
  1M; section 5 has longer drives.
* **Scans** (ms for the live keys, second scan, unlocked): with merges
  2 to 4 times faster than main at k >= 10, about main's at k = 2 and 3
  (where the nodes of a scan are as many and the run is dominated by the
  keys); within 15 % between the four sets.


## 5. 10M keys

The same probe and shapes, n = 10M. Holds (heavy-run lock): **hold A**,
10:29:52 to 11:26:42 (counts, heavy.lock, 3 JVMs at first): k2-asc
for P5 and m8, churn for P5, m8 and the dense set; over for P5 and m8
failed at once (a data directory shared with a 1M run, fixed), over for
the dense set and main were left out (the timing hold measures them);
the dense churn run was stopped at 11:21 after its drive, before its
twin, to end the hold (coordinator). The hold ran 57 minutes, over the
rule's 40: the churn runs at 10M took 50 minutes each (two random fills
of 10M, 30,000 transactions of 100 operations, and five full scans of
10M keys at 8 to 12 µs a key under three JVMs). Later holds: one slot,
two runs (section 7).

### 5.1 The put path at 10M (the random fill)

From the fill phase of the churn runs (three JVMs: the counts are exact,
the rates are not timing measurements).

| 10M keys, random fill        | P5 (= main) | m8      | dense   |
|---|---|---|---|
| key nodes                    | 892,251     | 836,316 | 690,688 |
| keys a key node              | 11.21       | 11.96   | 14.48   |
| record bytes a put           | 581.3       | 586.8   | 604.8   |
| stream bytes a put           | 722.9       | 730.0   | 750.6   |
| against P5: key nodes        | 1           | 0.94    | 0.77    |
| against P5: record bytes     | 1           | 1.009   | 1.040   |
| against P5: stream bytes     | 1           | 1.010   | 1.038   |

* **P5's fill is 024-03's to the node and byte** (892,251 key nodes, 722
  stream bytes a put; 024-03, section 3), as its put path is main's.
* **At 10M the dense put path costs 4 % more bytes a put** (at 1M 2.8 %),
  for 23 % fewer key nodes; m8 1 % more for 6 % fewer. A random fill at
  10M writes each leaf many times (reclaim's iterations, eviction's
  reloads); a fuller leaf is a larger record each time.

### 5.2 Shapes at 10M (counts)

| 10M keys                          | P5        | m8        | dense     |
|---|---|---|---|
| k2-asc: key nodes              | 749,944   | 422,434   | 392,133   |
| k2-asc: its twin                | 394,947   | 393,707   | 393,296   |
| k2-asc: times the twin          | 1.90      | 1.07      | 1.00      |
| k2-asc: rec bytes a delete      | 94.3      | 78.2      | 83.8      |
| k2-asc: drive rec bytes a tx    | 78,658    | 68,013    | 81,196    |
| k2-asc: the twin's drive        | 47,192    | 43,245    | 46,987    |
| k2-asc: dead KEY klongs, drive  | 5,676,419 | 1,676,655 | 2,789,744 |
| k2-asc: the twin's dead klongs  | 1,073,782 | 1,072,648 | 1,070,819 |
| churn: key nodes after the churn  | 1,021,450 | 924,863   | 761,479   |
| churn: the twin (random fill)     | 892,107   | 835,703   | 690,688 * |
| churn: times the twin             | 1.14      | 1.11      | 1.10 *    |
| churn: after the drive            | 1,062,096 | 947,563   | 782,749   |
| churn: twin after the drive       | 974,739   | 900,381   | -         |
| churn: times the twin, drive      | 1.09      | 1.05      | -         |
| churn: rec bytes an operation     | 535.2     | 546.1     | 568.0     |
| churn: drive rec bytes a tx       | 83,248    | 83,591    | 85,495    |
| churn: the twin's drive           | 79,243    | 79,617    | -         |
| churn: kept after the drive, GB   | 9.16      | 9.25      | 9.55      |
| churn: the twin's kept, GB        | 7.73      | 7.81      | -         |

\* the dense set's own random fill of 10M keys, as its churn run's twin
was not run.

* **The 1M ratios hold at 10M** where both were run: k = 2, P5 1.90 and
  m8 1.07 (1M: 1.90, 1.07); churn 1.10 to 1.14 (1M: 1.06 to 1.17).
* **After 5M deletes at 10M every set's drive writes 1.6 to 1.7 times
  its twin's record bytes a transaction** (P5 1.67, m8 1.57, dense 1.73),
  at 1M 1.08 to 1.17. Not the node count: the dense set has the twin's
  key nodes to 0.3 % and the highest ratio. What differs is the dead
  KEY klongs (2.6 to 5.3 times the twin's: the deleted keys' klongs in
  live nodes, 024-11's U5) and the stream to reclaim (3.3 against 1.7
  GB kept). One sample each of 10,000 transactions, one or two reclaim
  iterations, so the reclaim phase is in it; whether it settles with a
  longer drive is not measured. It is no argument between the sets.
* **Churn at 10M**: the dense set writes 6 % more bytes an operation than
  P5 (m8 2 %) and keeps 25 % fewer key nodes; its drive afterwards 2.7 %
  more bytes a transaction.

**024-03's sparse shape at 10M** (k30-rand: a random fill, every 30th
key kept, ascending deletes; 024-03, section 5, main):

| 10M, k30-rand                 | main (024-03) | P5     | m8     | dense  |
|---|---|---|---|---|
| key nodes after the deletes   | 419,680       | 38,518 | 33,997 | 29,819 |
| the twin's                    | 26,746        | 26,874 | 26,447 | 23,937 |
| times the twin                | 15.7          | 1.43   | 1.29   | 1.25   |
| after the drive, times twin   | 11.3 *        | 1.04   | 1.06   | 1.11   |
| drive rec bytes a tx          | 86,651 *      | 26,960 | 26,944 | 26,462 |
| the twin's                    | 26,351 *      | 24,509 | 24,500 | 24,792 |
| rec bytes a delete            | -             | 67.8   | 68.0   | 68.1   |

\* after 024-03's drive of 300,000 transactions; P5's here is 10,000.

* **Each set at 10M is itself at 1M** (P5 1.43 against 1.44, m8 1.29 and
  1.29, dense 1.25 and 1.22): 11 to 14 times fewer key nodes than main
  after the same deletes, and the drive afterwards 1.07 to 1.10 times the
  twin's bytes, where main's was 3.3. The delete's bytes are the same in
  the three sets (68 a delete).

### 5.3 Timed: the put path at 10M (hold T)

Both slots, one JVM at a time, 12:31 to 12:51: a random fill of 10M keys
(PF1's order), then 10,000 transactions of 100 overwrites; `-Xmx8g`, G1.
The 1-minute load: main's run started at 17.6 (two other agents' runs,
a Lean `treetest` and an UnlinkFuzz JVM, were still running after a
6-minute wait for quiet) and ended at 3.9; the dense run 3.9 to 3.3; m8's
3.3 to 3.3. So main's fill is marked disturbed in its first minutes, and
024-03's figure for the same fill on the release jar (load 1.3 to 4.9)
stands beside it.

| 10M keys                       | main      | m8        | dense     |
|---|---|---|---|
| fill, puts/s                   | 50,961 d  | 53,256    | 54,176    |
| fill, puts/s, 024-03 (2026.4)  | 51,971    | -         | -         |
| fill, commit p50 / p99.9, ms   | 1.8 / 18.1 d | 1.8 / 6.5 | 1.8 / 6.1 |
| fill, record bytes a put       | 581.3     | 586.8     | 604.8     |
| fill, key nodes                | 892,251   | 836,316   | 690,688   |
| overwrites, ops/s              | 27,029    | 31,118    | 32,658    |
| overwrites, record bytes an op | 792.8     | 793.1     | 818.4     |
| overwrites, stream bytes an op | 943.1     | 945.2     | 969.7     |
| key nodes after the overwrites | 975,024   | 900,824   | 746,563   |
| kept at the end, GB            | 7.73      | 7.81      | 8.04      |
| scan of 10M keys, µs a key     | 2.74      | 2.72      | 2.63      |

d: disturbed (see above). P5's put path is main's (section 4.3), so
main's row is P5's.

* **No set is slower to put.** The fill's rate is within 4 % in all
  three (m8 and dense slightly faster than main's two figures), commit
  latencies the same; the overwrites 15 to 21 % faster with m8 and dense,
  one run each (main's overwrites ran after its disturbed fill, at a load
  that had fallen to about 4: take the difference as not shown).
* **The dense set writes 3 to 4 % more bytes** a put and an overwrite at
  10M, and keeps 4 % more stream; m8 0 to 1 %. Fewer key nodes (m8 8 %,
  dense 23 % fewer after the overwrites) do not make a scan faster here:
  at 10M a scan of all keys is bound by the 200 MB cache's loads (2.6 to
  2.7 µs a key in all).


Not run: k10-hashed at 10M (hold H3, stopped at 13:47 for the stop
time); the 1M figures of section 4.4 stand for the delete at random.


## 6. Thrash

TU5's question (024-11, section 6; CB4): a workload that makes a node
split and merge in turns, one operation a transaction. Three
constructions in the probe (`THR thrash2`, `thrash3`, `thrash4`), counts
only, seconds a run, no lock; "new nodes an operation" counts a time
split and a merge into one node as one, a space split and a
redistribution as two.

* **thrash3**: 3,000 keys put in key order, one a transaction, which
  leaves every leaf at the half of its last space split; then each key of
  a window of 60 deleted and put in turns, 200 transactions each.
* **thrash2**: a window of 120 keys in 10,000 even keys; 300 bursts, each
  setting the window to a random number of live keys and then putting and
  deleting one random key in turns, 40 transactions.
* **thrash4** (the search): 400 fresh databases of 1,000 even keys, put
  one a transaction in key order; in each, up to 9 odd keys put and up to
  13 even keys deleted within 40 keys of a key y; then y deleted and put
  (or put and deleted) in turns, 200 transactions.

| Set   | thrash3 mean, worst | thrash2 mean, worst | thrash4 mean, worst | cycles |
|---|---|---|---|---|
| main  | 0.109, 0.115        | -                   | -                   | -      |
| P5    | 0.109, 0.115        | 0.121, 0.200        | 0.104, 0.140        | 0      |
| m8    | 0.111, 0.115        | -                   | 0.111, 0.170        | 0      |
| m9    | 0.111, 0.115        | -                   | 0.131, 0.200        | 0      |
| dense | 0.198, 0.210        | 0.144, 0.225        | 0.120, 0.195        | 0      |

* **No set thrashes in what was constructed.** In 400 trials a set, no
  ping-pong made 10 merges and 10 space splits in its 200 operations
  ("cycles"); the most merges in any trial was 2, the worst trial 0.20
  new nodes an operation, nearly all time splits: a leaf that gets two
  klongs a transaction (a time klong and the key's) is replaced every 5
  to 8 transactions in every set, main too (0.11 to 0.115 in thrash3).
* **The dense set costs most at its boundary**: 0.20 new nodes an
  operation in thrash3 against 0.11, as a leaf there holds about 20 live
  klongs of 30 and fills again in 5 transactions, where P5's holds 15
  and takes 8. Bytes an operation are the same in every set, 142 to 145:
  the leaf is written by every transaction anyway.
* **A cycle exists on paper for sets with c = h and m = h / 2** (the
  dense set; m9's 9/18/19 too, for a merged node of 18): a merged node
  of h live klongs gets a key, overflows, and rule O makes a space split
  into halves of m and m + 1; a delete in the half of m merges it again.
  For P5 and m8 the halves are m + 1 each (8 and 8; 9 and 9), so one
  delete cannot merge them: CB4's separation. The search did not reach
  the cycle for the dense set (where the key lands in the larger half,
  or the overflow falls on a delete, the next state is stable); it is
  not proved impossible. 10/21/21 would have P5's separation.
* **The model** (024-11, 3.4: a window held near c live keys a node)
  gives 0.16 new nodes an operation for P5 and the dense set alike.


## 7. The holds

| Hold | When                 | Slot, JVMs       | Ran                                         |
|---|---|---|---|
| A    | 10:29:52 to 11:26:42 | heavy.lock, 3    | 10M: k2-asc P5, m8; churn P5, m8, dense     |
| H1   | 11:57:12 to 12:18:18 | heavy2.lock, 2   | 10M: k2-asc dense; k30-rand P5              |
| T    | 12:23:38 to 12:50:59 | both slots, 1    | timed: over main, dense, m8 (10M)           |
| H2   | 13:35:16 to 13:46:26 | heavy.lock, 2    | 10M: k30-rand dense, m8                     |
| H3   | 13:46:27 to 13:47    | heavy.lock, 2    | stopped at once (stop time), no result      |

1M (section 4), the fuzz and the thrash runs ran without the lock, one
JVM at a time (two at most: the fuzz beside the 1M runs).


## 8. Recommendation

**m8: m = 8, h = 17, c = 17** (for B = 30; other node sizes: QT2). On
the 1M grid and, at 10M, k = 2 and the sparse shape for P5, m8 and
dense, churn, and the timed put path.

* **It removes P5's worst shape**, every second key kept: 1.07 times the
  twin for 1.90, at 1M and at 10M. Its worst row is 1.49 (k = 100,
  descending), a margin of 0.5 to BD13. (The drive's bytes after 5M
  deletes at 10M are 1.6 to 1.7 times the twin's in every set, the dense
  set's too: dead klongs and reclaim, not the thresholds; section 5.2.)
* **It costs the databases that never delete about 1 %**: record bytes a
  put in a random fill +0.0 % at 1M, +0.9 % at 10M; an overwrite -0.6 %
  at 1M, +0.0 % at 10M; key nodes 6 to 13 % fewer; a fill in key order
  unchanged; timed at 10M no slower (53,256 puts/s against main's 50,961
  and 51,971). It is the least change of h (15 to 17) that lifts k = 2
  above m.
* **It keeps the delete within BU4** (at most 1.08 times main's record
  bytes, 1.10 stream bytes, at random) and **CB4's separation**: a split
  of a merged node of c + 1 gives halves of m + 1, so one delete cannot
  merge them again, as with P5.
* **For other node sizes** a formula is still to choose: "m = B / 4 + 1,
  h = c = 2m + 1" gives 8/17/17 at 30 but 3/7/7 at B = 8, where a time
  split would keep 7 of 8 klongs (the build refuses h > B - 2). The
  scaling used here, v B / 30, gives P5's 2/4/4 and 3/7/7 at the test
  sizes 8 and 14 (what UnlinkFuzz ran) and 16/35/35 at 62. QT2 below.

**Alternatives for Frans:**

* **P5, 7/15/15**: no change at all to the put path (main's to the byte),
  the least to prove and the code as prototyped; the price is k = 2: 1.90
  times the twin, 0.10 from BD13's gate, at 1M and at 10M.
* **m9, 9/18/19**: worst 1.35; put path +0.9 % at 1M; delete at random
  up to 1.09 (1.14 stream); no CB4 separation for a merged node of 18
  (a split into 9 and 10). Not measured at 10M.
* **dense, 10/20/20** (024-11's QU4): the best ratios (worst 1.25) and
  23 % fewer key nodes after a random fill at 10M, no slower to put
  (timed), but 4 % more bytes a put there for every database, deletes at random up to 1.17 (1.28
  stream) times main's (over BU4), 0.20 new nodes an operation at its
  boundary for 0.11, and a split-merge cycle on paper. 10/21/21 would
  restore CB4's separation; not measured.


**Questions for Frans** (cite as "024-14, QT1"):

**Decided, QT1: m8, 8/17/17** (Frans, 2026-11-11, 14:34, asked "Shall
the merges use 8/17/17? Named constants for B = 30; how they scale to
other node sizes (QT2) stays open": "1, yes."). QT2 open.

* **QT1. The set**: m8 (8/17/17), P5's 7/15/15, or the dense 10/20/20?
  Recommended: m8 (above). 024-21 builds P5's set as named constants
  (Frans, 11:55); m8 is a change of three constants and of h in rule O.
* **QT2. Other node sizes**: the thresholds for B = 30 only, with the
  test sizes 8 and 14 keeping P5's formulas (as this build scales them),
  or one formula for all B? Recommended: B = 30's numbers as format 7's
  rule, the tests' sizes by v B / 30, so that the fuzz keeps its sizes.


## 9. Not measured

* **Timed runs**: only hold T's three (section 5.3), one run each, main's
  disturbed at its start; every other rate in sections 4 and 5 was taken
  beside other runs. No timed delete, scan after deletes or start.
* **m9 at 10M**; at 10M k = 3, 10 and 100, the descending and hashed
  orders, mass, and main's churn and k = 2 (024-03's figures stand in for
  main's random fill, sparse and mass delete; main's k = 2 is 2.00 by
  its mechanism and at 1M). The delete at random (BU4) only at 1M.
* **Reclaim settled**: drives of 10,000 transactions (2 to 4 iterations
  at 1M, 1 to 3 at 10M), one sample of "kept" at the end, at whatever
  phase of the cut; 024-03's drives were 100,000 to 300,000.
* **Restarts and the rerun's cost** with each set at 1M or 10M (only
  CleanupRule's restarts at 100,000 keys); cold caches; s1.
* **Key shapes**: only `/k/%010d` (two segments); hashed keys, long keys,
  values other than 100 bytes, transactions other than 100 operations.
* **Thrash** of several keys at once at a boundary (only single-key
  ping-pong and random windows); the dense set's cycle was argued, not
  constructed.
* **10/21/21** and other sets with P5's separation at m = 10.

## State

2026-11-11, from 09:26, by the agent "thr" of coord-1111.

* **Clone** `/Users/f/fl/bench/2026-11-11/thr/clone`, branch
  `024-14-thresholds` (head `bff5e810`) on `92bf4eb5`, 023-08's fault 12
  fix on P5's head `71e386de` (branch `023-v12-fix`); branch
  `024-14-main-counts` (`44fa9b87`, worktree `../main-wt`): `main`
  (`1fe5f180`) with split counters only. Builds frozen in `thr/b1` and
  `thr/bmain`; the probe in `thr/probe/THR.java`.
* **Done (13:50), and stopped for the stop time**: the build; UnlinkFuzz
  strict for all four sets (36 runs each, 0 failures); CleanupRule with
  restarts (16 runs); thrash (section 6); the 1M grid, 80 runs (section
  4); at 10M holds A, H1, T (timed) and H2 (section 7). Sections 1 to 9
  written on these; the recommendation is m8 (section 8). No run is
  running and no slot is held (H3 stopped and released at 13:47).
* **Files**: probe, scripts and outputs copied to
  `14-merge-thresholds/` (`THR.java`, `tools/`, `out/`); the working
  directory is `/Users/f/fl/bench/2026-11-11/thr/` (builds `b1`, `bmain`,
  compiled probe in `probe/c-*`); tables by `python3 tools/summ2.py DIR`.
* **To continue**: Frans's answers to QT1 and QT2. More 10M rows, if
  wanted: `tools/hold3.sh tools/jobs-H3.txt H3` (k10-hashed, P5 and
  dense, about 12 minutes in one slot), or new job lines for
  `tools/job.sh OUTDIR SET NAME run args` (SET main, p5, m8, m9, dense).
  Nothing is committed in the main tree; the clone's branches are not
  pushed or landed (a measuring build).
