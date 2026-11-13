# 024-11. Underfill: a design study of the fix

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11), the
design study: the merges made in 024-21 and 024-22 (`67925924`); QU1 to
QU8 not marked answered here (QU4 by 024-14's QT1, QU6 by 024-22's QM1).

A design study, no Java or Lean code: how release 2026.5 removes
underfilled key nodes, the second largest known case against its aim
(024-04, aims 2 and 3; 024-05, OP2 and ST2, with ST4, the dead klongs in
live nodes). The problem made exact, each option as a mechanism, a
recommendation with its algorithm stated exactly enough to be written as
a Lean definition (its state, steps, invariants and cost bound), the
tests, a plan, and the questions for Frans. It builds on 023's
requirements, tests, options, prototypes and reviews.

Decided by Frans today (2026-11-11): a record format change is allowed
in 2026.5 (07:08), and 2026.5 may refuse 2026.4's databases, so there is
one rerun path and a new record format, not merges switched on by the
record's format (07:23, "as recommended"; it replaces 024's readme's
plan and answers 024-06's question 2 and 024-02's Q1). He leans towards
the Lean model before the code: 024-12 writes 2026.4's tree in Lean, and
section 5 here is the change to its delete.

Shapes are U1 to U5, bounds BU1 to BU4, options MG, BW, RB, CW, CT and S1
to S3, invariants V1 to V9, theorems TH1 to TH4, costs CB1 to CB4, tests
TU1 to TU10, questions QU1 to QU8; cite them as "024-11, V1".


## 1. Summary

* **The problem.** 2026.4 removes a key node only when it is empty. After
  scattered deletes the index has 2 to 20 times the key nodes of a fresh
  database with the same keys (the twin); at 10M keys 15.7 times, 11.3
  after 55 reclaim iterations, with 3.3 times the bytes a transaction and
  scans 4.6 times slower (024-03, section 5). Reclaim does not heal it:
  a time split copies an underfull node to an underfull node.
* **The bound proposed (BU1).** After every transaction, with any retain
  duration: every key node that is not a root of a segment tree holds at
  least m = B / 4 live klongs (7 of 30). Then the key nodes are at most
  S + (n + S - 1) / (m - 1), for n live keys in S segment trees: a
  function of the live keys alone. BD13's "twice the twin" stays as the
  measured gate (BU2).
* **The options.** MG, merges at the delete (P5): meets BU1 in every
  shape, with R forever too. BW, borrowing in place: MG's bound, more
  cases. RB, reclaim's rebuild (P3): the shape an iteration or two later,
  nothing with R forever, 2 to 3 times the bytes while deletes run, a
  touch that a start must rerun. CW and CT, compaction by a new node:
  dead klongs only. Three simpler ideas: each fails a shape.
* **Recommended: MG alone.** With R forever only the delete runs, so
  only it can keep scans and gets proportional; its bound is an
  invariant of each transaction, which Lean can prove; it breaks no
  theorem and adds no field to a record; it is prototyped.
* **A probe for this study** (3.3, 35 runs on P5's build): with merges
  1.12 to 1.71 times the twin's key nodes when every k-th key is kept,
  and 1.90 for k = 2; without merges 2.0 to 20.2. A model of the fill
  rules (3.4) agrees, and puts a denser set of thresholds at 1.3 or less.
* **Dead klongs** stay at most B a node, now on nodes in proportion to
  the live keys (1.4 to 2.3 times the twin's KEY klongs). Removing each
  in bounded time needs the touch as a writer; recommended: not (QU3).
* **Format 7**: format 6's layout; a delete's rule includes the merge.
  One rerun path, 2026.4's databases refused (Frans, today).
* **Plan** (section 7): the thresholds measured at 10M on P5's build;
  the merge in 024-12's Lean tree; P5's 545 lines onto `main`; tests,
  gates, digests, the C clone: about two weeks of agent work. **Decide
  first:** QU1 to QU4.


## 2. The problem made exact

### 2.1 Terms

B is the node size, 30 klongs (8, 14, 62 in tests). A **live klong** of a
key node at time t is a KEY klong neither deleted nor shadowed at t
(023-01, section 2.1); a KEY klong that is not live is **dead** here,
whatever f is; cnt(X) is the number of live klongs of X at the latest
time. A **root** is the root of a segment tree: the space root, or a node
that a segment leaf's klong of a full segment names. n is the number of
live keys. S is the number of segment trees: 1, and one for each distinct
prefix of 7, 14, ... bytes of a live key at least that long
(`Keys.toSegments`). The segment leaves hold n + S - 1 live klongs in
all: one a key, one a tree but the first.

### 2.2 The shapes

| ID | Shape                               | What 2026.4 keeps                    |
|---|---|---|
| U1 | scattered deletes, every k-th kept  | every leaf that keeps a live key     |
| U2 | a mass delete with survivors        | a path of one-child nodes a survivor |
| U3 | time splits                         | the underfull node, copied           |
| U4 | a segment tree with one key         | a key node for one klong             |
| U5 | dead klongs in live nodes           | up to B - 2 a node, until its split  |

* **U1.** At 10M keys, k = 30 (024-03, section 5): 419,680 key nodes
  against the twin's 26,746 (15.7 times); after 300,000 transactions and
  55 iterations 420,636 against 37,084 (11.3), 3.3 times the bytes a
  transaction, a scan 4.6 times slower, 2.6 times the stream kept. The
  probe (3.3) gives the law: k times the twin's nodes while no leaf
  empties (2.0 to 9.9 for k = 2 to 10), then 14.9 (k = 30) and 20.
* **U2.** Survivors in one run (024-03, section 4: 1M keys left of 10M):
  1.10 times the twin's key nodes; only the range's edge costs. Far
  apart: each keeps its leaf and the inner nodes above it, each with one
  live child; only a root collapses (RC). Probe, k = 1,000: 303 key
  nodes for 101 keys, the twin 15. Worst case (n + 1) H (023-02, R12).
* **U3.** A time split replaces a node by its last version, with the
  same live klongs. Reclaim's rewrites fill and split every leaf that has
  a live key and change no count: so 55 iterations left 420,636 nodes.
* **U4.** A key whose 7-byte segment no other key shares has a segment
  tree of one leaf with one klong, about 220 bytes of heap (024-05,
  ST1): 54,416 key nodes for the probe's 50,001 hashed keys, 3,952 for
  as many that share their segments. The twin has the same trees: a
  cost of the key's shape, not of deletes; its fix, a one-key tree
  inline in a klong, is a node format change (024-05, QF5).
* **U5.** A node keeps the klongs of its deleted and shadowed keys or
  children, and its bitmaps, until it is full and splits: at most B a
  node, in time unbounded for a node that gets no write (a delete entry
  stayed after 700 cuts; 023-08, section 3). With U1 at 10M: 3,664,200
  KEY klongs against 544,651 (6.7 times).

### 2.3 The twin, exactly

023-02, section 3.2: a fresh database with the same settings and the same
live KVs, put in the order of their last puts, in transactions of the
same sizes, with no deletes; compared after the same drive. "c times the
twin" is a gate, not the bound: **the twin's fill depends on the put
order** (12.6 live keys a key node put in key order, 100 KVs a
transaction, the probe's twin; about 9 put at random, 024-03); **a twin
is a run, not a function**, so no statement of the Lean model; and
**BD13 says "after one or more reclaim iterations"**: nothing with R
forever, the default, where aim 2 still asks scans and gets to cost in
proportion to the live keys.

### 2.4 The bound to meet

* **BU1, the fill (the bound; a theorem to be).** After every
  transaction, at the latest time, with any R: (a) every reachable key
  node that is not a root holds at least m = max(2, B / 4) live klongs;
  (b) an inner root holds at least 2; (c) the leaves of a segment tree
  are at one depth. Then a segment tree with e live klongs in its leaves
  has at most 1 + e / (m - 1) key nodes and, above one node, a height of
  at most 1 + log_m(e / 2). In all:

      key nodes <= S + (n + S - 1) / (m - 1)       (B = 30: m - 1 = 6)

  For 024-03's sparse database (S = 11 for its keys `/k/%010d`): at most
  55,568, where 2026.4 has 420,636 and the twin 26,746 fresh, 37,084
  after its drive. Scans and gets follow: 023-02's R10 wish and R12 (b).
* **BU2, against the twin (the gate; BD13's number).** Key nodes at most
  2 times the twin's, right after the deletes and after the drive, with
  R finite and R forever, for 023-03's T2 rows and TU3's spacings. BU1
  gives about (B / 2) / m = 2 against a twin put in key order, so the
  gate has no margin in the worst shape (k = 2: 1.90).
* **BU3, klongs.** A node holds at most B klongs, so with BU1 the
  reachable klongs are in proportion to the live keys. Gate: KEY klongs
  at most 2.5 times the twin's after the drive (measured 1.4 to 2.3).
* **BU4, a delete's cost (aim 2).** Section 5.5: at most one merge a
  level; amortized under one merge in five deletes; the delete phase's
  bytes at most 1.2 times 2026.4's.


## 3. The options

Common to all: new nodes, never a node's history changed in place, which
would break lemma M and every proof on it (024-06, section 5.2) and give
a reader a wrong answer where today it expires. So readers take no lock
and wait for nothing; a lookup at an earlier time reads the old nodes
through the parents' old klongs; a new node has a new id and handle, and
its pointers are copies that share the pointees' handles (as top nodes
do); a node left out stays resident until CLOCK takes it.

### 3.1 MG, merges at the delete (023-05 P5)

* **What, when, by whom.** A node that is not a root and falls below m
  live klongs is merged with a sibling under the same parent: their live
  klongs make one new node, or two of half each when they are more than
  c = B / 2 (a redistribution: what borrowing becomes when nodes are not
  changed in place). The parent loses a klong and is checked in turn; a
  root left with one child collapses. In the deleting transaction, after
  each delete, by the writer's thread under the write lock, bottom-up on
  the delete's path; the siblings are the only nodes off it (section 5).
* **The stream and a start.** The record has the delete, as today, and
  no field for the merge: format 7 has format 6's layout, and m and c
  follow from B, which the meta block holds. The new nodes and the path
  are dirty and written by a later take, as a split's; a sibling left
  out is written once more only if it was dirty before; a node that the
  transaction made and left out, never. A start reruns the delete by the
  same rule, makes the same nodes with the same ids, and reads the
  siblings as the writer did.
* **Reclaim and the cut**: unchanged. A node left out is to them a
  split's replaced node: reachable only at times before the merge, so
  stored at or after the cut iteration's pStart, or dirty (023-06,
  section 6); `CutOK` at 303 of 303 cuts on P5. Reclaim's transactions
  put and never delete: they merge nothing.
* **The bound and the cost.** U1, U2, U3: yes, at once, with R forever
  too. U4: the twin's. U5: at most B a node, on fewer nodes; not zero. A
  delete's cost as measured: 3.3 (in P5, 2 % of the sibling reads came
  from the stream under eviction); its worst case and `dirtyNodeBound`:
  5.5.
* **Lean.** No theorem breaks: a merge is entries of tt, new nodes
  reachable at tt, and left-out nodes with no entry of tt; P5's runs met
  A2 to A5, TREE, A6' and A-COPY. Two arguments on paper only,
  `PhysStep` and T-SCHEME's "a key range only shrinks" (024-06, section
  4.4), are to be made again for ranges that merge. Its own proof is a
  B-tree's, an invariant kept by each operation (5.4; sizes in 7).
* **P5 showed** that it works: no reachable node but a root below m
  after any transaction (UnlinkFuzz strict, node sizes 8 and 14); every
  gate in full; "sparse" 1.44 and 1.45 times the twin at 100,000 and 1M
  keys, every other T2 row at the twin's 6 nodes.
* **Its faults.** Fixed in P5: the climb gave up after a space split in
  the delete; `dirtyNodeBound` refused transactions of 150,000 deletes;
  P4's take-back left a deleted klong naming a node never written.
  **Fault 12**, found by review C after every gate had passed on P5's
  head: a segment leaf's second klong of tt left the first naming a root
  that was then taken back, and the database could not be opened again
  (023-08, section 4); fixed in 2026.4. The standing gates do not reach
  nodes made and taken back in one transaction; UnlinkFuzz with large
  transactions does, and the model run against Java would.
* **Open in P5.** "Inter" writes 2.1 times the bytes (versions of a hot
  leaf left out while dirty stay dirty by Rule A); thrash is argued, not
  measured; `dirtyNodeBound`'s merge count is an argument; up to 32 %
  more resident objects with `noEvict()`; the rerun's sibling reads are
  not measured; P5 stands on P4's head, before 2026.4's last fixes.

### 3.2 BW, borrowing in place

As MG, in the deleting transaction, by the writer: the underfull node X
takes klongs from a sibling S by entries of tt in the nodes as they are
(a bitmap in S, new klongs in X, the bound between them in the parent
deleted and added again); a merge as MG when S has none to spare. No new
node and none left out, so nothing of fault 12's kind and no Rule A
cost. But S, off the path, gets entries and must be marked; every moved
klong leaves a dead one in S; in an inner node each borrow is a relabel
(LE-b); `dirtyNodeBound` counts a sibling a level. MG's bound, a worse
U5, not prototyped. **Verdict: no;** MG's redistribution is the
borrowing that fits nodes with a history.

### 3.3 The probe: spacings, with and without merges

Run for this study on P5's frozen build `b-head4` (`789b1654`):
`CleanupRule hello n=100000 keep=k`: 100,000 keys put in key order, all
but every k-th deleted, 100 a transaction, in ascending, descending or
random order; 4,000 drive transactions, R = 1 s. Counts only, one run
each; every run's lookups agreed with CleanupRule's model. "None" is the
same build with `-Dbergdb.p5.merge=false`, P4's delete path, as 2026.4's
(ascending). Key nodes reachable at the end, and times the twin's;
ascending k = 30 is P5's own run (P5, 4.1).

| k     | Twin  | None  | x    | Asc   | x    | Desc  | x    | Random | x    |
|---|---|---|---|---|---|---|---|---|---|
| 2     | 3,952 | 7,902 | 2.00 | 7,503 | 1.90 | 7,503 | 1.90 | 7,503  | 1.90 |
| 3     | 2,636 | 7,902 | 3.00 | 2,958 | 1.12 | 3,158 | 1.20 | 3,938  | 1.49 |
| 5     | 1,583 | 7,902 | 4.99 | 1,967 | 1.24 | -     | -    | -      | -    |
| 10    | 795   | 7,902 | 9.94 | 1,122 | 1.41 | 1,335 | 1.68 | 1,174  | 1.48 |
| 30    | 270   | 4,036 | 14.9 | 390   | 1.44 | 426   | 1.58 | 391    | 1.45 |
| 100   | 85    | 1,702 | 20.0 | 125   | 1.47 | 145   | 1.71 | 125    | 1.47 |
| 1,000 | 15    | 303   | 20.2 | 18    | 1.20 | -     | -    | -      | -    |

* **At 1M keys the same ratios** (ascending): 1.90, 1.12, 1.41 for k =
  2, 3, 10 (75,000 against 39,500 for k = 2), and P5's 1.45 for k = 30.
* **k = 2 is the worst spacing for m = B / 4.** The fill left 12.6 keys a
  node; half of them leaves about 7 a leaf, at or above m: 598 merges in
  50,000 deletes. BU1 holds; BU2 with 0.1 to spare. And the sibling rule
  favours ascending deletes: 1.20 to 1.71 for descending ones (5.6).
* **Hashed keys** (3 segments, most trees of one key, U4): 1.01 to 1.02
  times the twin with merges for k = 2, 10, 30 (54,979 against 54,416
  for k = 2), 1.15 to 1.53 without.
* **KEY klongs** against the twin's: 1.9 to 2.3 over a drive of 20,000
  transactions for k = 2; at its end 1.39 for k = 3 and 1.36 for k = 10
  (dead klongs for k = 10: 7,897, without merges 96,852, the twin
  1,826). A leaf of 7 live klongs fills after three rounds of reclaim's
  rewrites, the twin's after two: more dead klongs between its splits.
* **A delete's cost** (ascending): 0.01 merges a delete for k = 2, 0.16
  to 0.19 for the others, with 1 to 1.6 sibling reads a merge; the
  delete phase's bytes 0.77 to 1.10 times those without merges.
* **Made and left out in one transaction:** 73 % of the nodes that
  merges left out (k = 100, ascending: 26,932 of 37,006; in random
  order about 20 %): a merged node is merged again by the transaction's
  next deletes. This is the take-back's exposure (5.6).
* Not run: 10M, a fill in random order of keys that share segments,
  other thresholds (step 2). Output: `/Users/f/fl/bench/2026-11-11/fill/`.

### 3.4 A model of the fill rules

A study tool, not BergDB's code: `sim/sim.py` beside the probe, 300
lines of Python: one segment tree of live klongs with the klongs used in
each node, rule O and section 5's delete. With P5's thresholds its key
nodes are within 10 % of Java's in 15 of the 16 rows of 3.3 that it has
(24 % off for descending, k = 3); after random overwrites it holds 9.0
keys a node, as 024-03's twin. It says nothing of bytes.

| Times the twin, k = 3 to 100 | Asc          | Desc         | Random       | k = 2        |
|---|---|---|---|---|
| P5: m 7, h 15, c 15          | 1.15 to 1.64 | 1.50 to 1.84 | 1.44 to 1.52 | 1.90         |
| c = 22 (3B / 4)              | 0.83 to 1.12 | 1.50 to 2.05 | 1.23 to 1.31 | 1.90         |
| dense: m 10, h 20, c 20      | 1.01 to 1.22 | 1.05 to 1.30 | 0.98 to 1.06 | 1.00 to 1.10 |

* **The invariants and CB3 hold** in its fuzz: V1, V2, V4, V5 and BU1's
  count after each of 3,000 transactions, in 180 runs (B = 8, 14, 30,
  62; at 30 also these sets and three sibling rules).
* **Thresholds.** The larger cap alone helps one direction and hurts the
  other. The dense set (QU4) is at 1.3 or less in every row, and changes the
  put path too: after a fill at random and 200,000 single overwrites,
  8,059 key nodes for P5's 11,125 (12.4 keys a node for 9.0), with 0.145
  splits an overwrite for 0.103.
* **Sibling rules** without a direction ("the one with fewer live
  klongs"; "one that fits, on either side"): 1.4 to 1.8 ascending, 1.15
  to 1.6 descending; neither beats P5's rule in all three orders.
* **Thrash.** Puts and deletes, one a transaction, in a window held near
  c live keys a node: 0.16 new nodes an operation, most of them time
  splits; 0.026 merges and 0.017 space splits an operation.

### 3.5 RB, reclaim's rebuild (023-05 P3)

* **What, when, by whom.** Reclaim's touch, as it leaves a node in
  post-order, replaces it by a new node when its plan changes anything:
  dead klongs dropped, adjacent children merged while they fit in half a
  node, a root with one child collapsed. In each reclaim step's internal
  transaction, by the writer's thread, on every node of the step's key
  range: once an iteration, and only with R finite.
* **The stream, a start, the cut.** The touch is not stored or rerun
  today. RB's nodes are named by later records, so a step's record gets
  a flag and the touch's range (two keys), and a start reruns the touch
  over it before the record's puts. The cut's argument holds again (P3,
  1.3; `CutOK` at 254 of 254).
* **The bound and the cost.** U1, U2, U3 and U5: yes, one or two
  iterations after the writes, with R finite ("sparse" at 100,000: 377
  nodes; P5's twin has 270); with R forever nothing, ever. A delete pays
  nothing more; the delete phase wrote 2.1 times `main`'s bytes at
  100,000 keys and 3.0 at 1M, the steady state 0.9 to 1.0; 1.8 to 2.5
  times the resident objects with `noEvict()` (P3, 4.5). The step's
  reserve, not `dirtyNodeBound`, bounds the nodes a step makes.
* **Its faults.** The decisive one (P3, 5.3): a node replaced while it is
  dirty must still be written, and Rule A keeps it dirty while a child
  is; at 1M, 105,083 of 113,976 rebuilt nodes replaced a node in D. No
  deterministic remedy: the rerun does not know which nodes were dirty.
* **Lean.** The model's touch step changes (`touchOf` marks every node
  the touch reaches, RB unmarks what it replaces: C-S differed in 507
  steps); `T13_markTouch` and T-SCHEME's argument are to be made again;
  the bound, "within K iterations", needs reclaim's scheme in Lean
  (024-06, D1) before it can be stated.
* **Verdict: no.** It fails BU1 with R forever, costs most where MG
  costs least, and its bound is the hardest to prove.

### 3.6 Compaction by a new node: CW and CT (dead klongs, U5)

* **CW, at the write** (023-04's DC). A node counts as full when it has
  no room, or holds theta or more dead klongs; the existing split then
  replaces it by its last version. By the writer, in the transaction
  that adds the dead klong; rerun as the write's rule; no field. About
  theta dead klongs a node at every time, never zero; a second trigger
  beside the fill. Not prototyped.
* **CT, in the touch.** RB's first part alone: the touch replaces a node
  that holds a dead klong. Zero within an iteration, cold nodes too,
  with R finite; at RB's price (the touch's rerun and field, the model's
  touch step, Rule A's rewrites). As reclaim's own rewrites shadow a
  klong in every leaf each round, it replaces every node every
  iteration, unless a rule that the rerun can compute picks the cold
  ones; none is designed here. MG with all of RB is MG with CT.
* **Verdict: neither in 2026.5** (QU3). With MG the klongs are in
  proportion to the live keys (BU3); what stays is 2026.4's named
  allowance, B a node, on nodes that BU1 counts.

### 3.7 Simpler ideas (Frans: KISS)

* **S1. Merge at the split, not at the delete**: when a full node's last
  version has fewer than m live klongs. Nothing new at the delete; but a
  leaf that one transaction empties to one key has room left and fills
  only by reclaim's rewrites: about 14 rounds, never with R forever.
* **S2. A fresh tree an iteration.** Reclaim puts the live keys into a
  new tree and swaps the root: the twin itself, no merge code. But every
  user write goes to both trees during an iteration, a tree not yet
  reachable breaks the model's A3, and nothing happens with R forever.
* **S3. Nothing more than 2026.4** fails U1 and U2. The simplifications
  worth having are inside MG: section 5.6.

U4 is the twin's in every option. Format 7 has format 6's layout in
every option but RB and CT, which add a flag and the touch's range to a
step's record.


## 4. Recommendation

**MG alone: merges at the delete, the thresholds settled by one
measurement (QU4), and no mechanism for dead klongs in 2026.5.**

* **Aim 2 needs it.** With R forever, the default, reclaim never runs:
  what the delete leaves is the shape for ever. Only MG and BW keep scans
  and gets proportional there (the reviews' reason for the unlink at the
  delete; 023-08, section 1).
* **It is one invariant**, checked by one walk and proved operation by
  operation; it breaks no proof and adds no field; and it is the known
  algorithm, the multiversion B-tree's weak version condition (Becker et
  al. 1996; 023-04, section 2.4), Frans's plan of 2012, prototyped.
* **It leaves** U4 (the twin's too), U5 as an allowance in proportion to
  the live keys, "inter"'s bytes (TU6), the thin margin at k = 2 (QU4).


## 5. The algorithm, exactly

The change to 2026.4's delete, which 024-12 models as `deleteUpward`.
Layer B is the nodes with their klongs: what Java has and a trace shows.
Layer A is the tree of live klongs at tt: what the bound's proof needs.
P5's code is the reference for layer B's details (`Dag.merge`,
`mergeParent`, `sibling` on `023-p5-merge`).

### 5.1 State and parameters

* **Parameters**, all from B, by integer division: h = B / 2, the most
  klongs of a last version that a time split keeps (today's); m = max(2,
  B / 4), the least live klongs of a node that is not a root; c = B / 2,
  the most live klongs that a merge puts in one node. For B = 30: 15, 7,
  15; for 8: 4, 2, 4; for 14: 7, 3, 7; for 62: 31, 15, 31.
* **A key node** X: a leaf or inner, with at most B klongs in time order:
  T(t), K(e, p) with compare value e and pointer p, D(bits).
* **live(X, t)**: the map from compare values to pointers of the K klongs
  before the first T later than t, the last of each compare value, less
  those whose index the last bitmap holds. cnt(X) is its size at tt.
  **lv(X, tt)**, the last version: T(tt), then live(X, tt) as K klongs in
  compare order.
* **Layer A**: a segment tree is a leaf (a sorted map from compare values
  to a value or a segment tree) or an inner node (a sorted map from
  lower bounds to children, its first bound the empty key).
* **The writer's state in a transaction** is 024-12's W (the overlay,
  the next id, the nodes made and taken back, `madeFor`, the path).

### 5.2 The step: a delete of a key at tt

1. **Descend** as today: the path X0, the space root, to Xd, the segment
   leaf of the key's last segment s. If s is not live in Xd: a noop.
2. **remove(Xd, s).** remove(X, e): the bits of every K klong of e join
   X's bitmap of tt (one D klong a transaction in a node, before any K
   klong of tt of that compare value). Without room in X: rule O on
   lv(X, tt) with e left out.
3. **fix(Xd).** fix(X), a loop:
   * F1. X an inner root, cnt(X) = 1: root collapse, 2026.4's RC: the
     one child takes X's place (a new top node, or a K klong in the
     segment leaf above); X is left out (M5). Again with the child.
   * F2. X a root and a leaf, cnt(X) = 0, not the space root: its tree
     is gone. With Y the segment leaf above and e its compare value for
     X: X is left out; remove(Y, e); fix(Y).
   * F3. X another root, or cnt(X) >= m: stop.
   * F4. Else X is not a root and cnt(X) = m - 1 (by V1): merge(X) under
     its parent P. Into one node: fix(P). Into two: stop.

**Rule O**, today's `handleFullNode`, unchanged: a node without room is
replaced by its last version with the change applied; of at most h
klongs, one new node (a time split); else two halves, floor and ceiling
(a space split; an inner second half starts with the empty key); the
parent, or a new root, gets the klongs; a node that tt made is changed
in place. After rule O, fix goes on with what replaced the node.

### 5.3 merge(X)

* **M1, the sibling.** In P, a is the live compare value next below X's,
  b the next above; one exists (V1, V2). If a exists, and b does not or
  cnt(child of a) + cnt(X) <= c: L is a's child and R is X. Else L is X
  and R is b's child. The writer reads a sibling through its follower,
  from the stream if needed, and does not mark it.
* **M2, the entries.** E is live(L, tt), then live(R, tt), in compare
  order; in an inner node R's klong of the empty key gets eR, R's
  compare value in P. E has at least 2m - 1 klongs.
* **M3, the new nodes.** If E has at most c klongs: N1 = T(tt), E. Else,
  with k the ceiling of half of them: N1 = T(tt), E's first k; N2 =
  T(tt), the rest; g is the compare value of the rest's first klong,
  which in an inner N2 becomes the empty key. Each klong keeps its
  pointer and reference. Ids in the order N1, N2.
* **M4, the parent**, entries of tt in P: eL names N1. With one node, or
  with g other than eR: eR is removed (remove's bitmap) and N2 gets a K
  klong of g. With g = eR: eR names N2. A K klong of tt is changed where
  it is; an older one is shadowed by a new one. Without room: rule O on
  P's last version with these changes.
* **M5, the nodes left out.** L and R get no entry of tt. One that
  existed loses what tt gave it before (N1 or N2 has it, by lv), serves
  the times before tt, and is written again only if it was dirty before
  tt. One that tt made is taken back: never written, its id used, out of
  D and the node table, and no K klong of any node names it (every K
  klong of tt that did names N1).

### 5.4 Invariants and theorems

After every operation of a transaction, for the nodes current at tt:

| ID | Invariant | Statement                                                           |
|---|---|---|
| V1 | fill      | cnt(X) >= m for every X that is not a root                          |
| V2 | roots     | an inner root has cnt >= 2; a leaf root >= 1, but the space root    |
| V3 | order     | an inner node's live klongs are lower bounds; the first is empty    |
| V4 | balance   | the leaves of a segment tree are at one depth                       |
| V5 | size      | at most B klongs; N1 at most c + 1, a half (B + m) / 2 + 1          |
| V6 | history   | no entry before tt changes; a node left out has none of tt          |
| V7 | new nodes | a node of tt not taken back is current, under one parent            |
| V8 | closed    | no K klong of a written node, live or dead, names a taken-back node |
| V9 | function  | a function of the delete and the state; ids in the order made       |

V3 is 023-06's I1, V8 its I5; V6 is the model's A2, V7 its A3, TREE,
A6' and A-COPY, V9 its A1 with the ids of taken-back nodes counted.

Why V1 holds: a count falls by one at a time (a delete, F2's remove,
M4's removed klong), so X has m - 1 when F4 merges it and its sibling at
least m; one node gets 2m - 1 to c klongs; two get at least (c + 1) / 2
each, which is m or more for every B from 8; a space split's halves get
at least h / 2 = m; a time split keeps the count. F1 keeps V2, so a node
that is not a root always has a sibling.

To state on layer A, as 024-12's stated properties: **TH1, the map:**
after a delete, a get of another key answers as before, the key is
absent, a scan gives the live keys in order, and at times before tt
nothing changes (V6). **TH2, the shape:** put and delete keep V1 to V5.
**TH3, the count:** V1, V2 and V4 give BU1's formulas. **TH4, the
costs:** CB1 and CB3; then `dirtyNodeBound` (024-06, C3).

### 5.5 Costs

* **CB1, one delete.** At most one merge for each level of the path that
  is not a root. A merge reads at most 2 siblings, makes at most 2
  nodes, and gives P at most 4 klongs (T, D, two K).
* **CB2, a transaction** (`dirtyNodeBound`, before the go point).
  2026.4's count, with 4 klongs for a delete in each node of its path (2
  today) and 2 new nodes for each level, two more levels for new roots:
  for a path of 5 nodes about 15 nodes a delete, so transactions of up
  to about 250,000 deletes fit the record limit (my arithmetic, 544
  bytes a node; P5's sharper count, about 2 million, is an argument).
  The simple count follows from CB1 by induction on fix.
* **CB3, amortized** (my derivation; it holds in the model, 3.4). Give
  each node that is not a root max(0, m + 1 - cnt) units. A delete adds
  at most one, a space split at most 2; a merge takes 2 away at X and
  adds at most one, at P (one node) or at a half (two). So over any run
  from the empty database: merges <= deletes + 2 x space splits.
  Measured: at most 0.19 merges a delete (3.3).
* **CB4, thrash.** A merged node has at most c + 1 klongs, so B - c - 1
  = 14 more fit before rule O runs: a merge and a split of the same keys
  are at least 7 one-key transactions apart. Argued (P5, 1.1); 0.16 new
  nodes an operation in the model; to be measured in Java (TU5).

### 5.6 To settle in the model, before Java

* **The unlink inside a tree goes.** With m >= 2 a node that is not a
  root is merged at m - 1, before it is empty: 2026.4's climb inside a
  tree, `emptyKeyNext` and the take-back of an emptied half are reached
  for roots only (the probe's 25 runs with merges: no relabel, no climb
  but F2's; without merges 6,200 climbs and 1,991 relabels at k = 100).
  The model omits them, Java makes them a `Bug` after a fuzz night.
* **The sibling rule.** M1 is P5's, tuned on ascending deletes;
  descending ones get 1.20 to 1.71 for 1.12 to 1.47 (3.3). The model
  finds no rule without a direction that is better in all three orders
  (3.4): M1 stays unless step 2 finds one.
* **Nodes of tt.** P5 always makes new nodes and takes back an L or R of
  tt (73 % of those left out, 3.3). A split changes a node of tt in
  place; a merge could use it as N1 the same way and take back only when
  both are of tt. And the entries of tt could be the net change (no K
  klong of tt shadowed or deleted by tt), so that V8 holds by form and
  A6 for A6'. Either changes the delete's bytes, so it is decided with
  the model, not after (QU6).


## 6. Tests

From 023-03, with new pass lines: **T2 "sparse"** with BU2 for its
strict allowance; **T1** and T2's other rows (the twin's 6 nodes);
**T3** (single scans, R forever); **T4**; **T6** (lookups against a
model, in every test); **T7** (restarts, crashes and readers, here
inside a transaction that merges); **T8**; **T10**; **T11** (format 6
refused, with a message that names 2026.4). New:

| ID   | What it states                                       | Where              |
|---|---|---|
| TU1  | V1, V2, V4 after every transaction                   | UnlinkFuzz strict  |
| TU2  | key nodes <= S + (n + S - 1) / (m - 1)               | every test's end   |
| TU3  | BU2 and BU3 for k = 2, 3, 5, 10, 30, 100, 1,000      | CleanupRule, night |
| TU4  | TU3 with R forever: a scan's key nodes, at once      | CleanupRule        |
| TU5  | thrash: new nodes an operation at a boundary         | a new probe        |
| TU6  | delete phase bytes <= 1.2 x 2026.4's; "inter" named  | CleanupRule        |
| TU7  | V8: every reference written names a written node     | a stream walker    |
| TU8  | `dirtyNodeBound` >= the nodes counted, 1,000 deletes | DagTester          |
| TU9  | a cold start at 50 MB after deletes: loads, time     | PF1, night         |
| TU10 | U1 and U2 at 10M: BU2, bytes a transaction, scans    | PF1, night         |

* TU1 is P5's `strict=1` as a step of `level1.sh`, with the modes that
  found fault 12 (shuffled keys, repeated keys, large transactions).
* TU3 at 100,000 keys in a gate (seconds a row), at 1M and 10M at night;
  deletes in the three orders, the fill in key order and at random.
* TU5: alternating puts and deletes at one boundary, 10,000 operations,
  at most 0.5 new nodes an operation (CB4 allows 4 in 7). TU7 is
  023-03's record walker H2, never built: it catches fault 12's kind.
  TU10 passes with ratios under 2 for 024-03's 11.3, 3.3 and 4.6.


## 7. Plan

| Step | What                                              | Size              |
|---|---|---|
| 1    | Frans: QU1 to QU4                                 | a short dialog    |
| 2    | P5's thresholds and the dense set, in Java, 10M   | a day, lock       |
| 3    | the merge in 024-12's Lean tree; TH2, TH3 proved  | 2 to 4 days       |
| 4    | P5 onto `main`, 5.6's choices, format 7           | 2 to 3 days       |
| 5    | TU1 to TU10 as code, in the scripts               | 1 to 2 days       |
| 6    | gates: the levels in full, a fuzz night, a review | a day and a night |
| 7    | digests, 024-02, the C clone's pin, the docs      | 1 to 2 days       |
| 8    | performance and 10M (T10, TU9, TU10)              | half a day, lock  |

* **Step 2** checks 3.4's model in Java, a build for each variant, no
  new mechanism: P5's thresholds and the dense set, on the rows of 3.3
  at 1M and 10M, a fill at random too, with a put's bytes and a thrash
  probe. It settles m, h and c before they are rerun rules.
* **Step 3** before step 4, as Frans leans: the merge as a definition in
  024-12's `exec`, run by `#guard` on small cases, and against Java when
  step 4's branch exports traces; layer A with TH2 and TH3, a B-tree's
  proof without histories (the proofs' size is a guess). TH1 and layer
  B's assumptions are 024-06's C1 and C2 (a week or two each), later.
* **Step 4.** P5 is 545 lines on P4's head; `main` has since fault 12's
  fix, the sort of a transaction's keys and K4's count. With it in
  format 7, if decided: 024-10's builder rule and any other change of
  what a record means, in one batch of digests.
* **Step 6** is 2026.4's way: one integration head, the fuzz with the
  new modes for a night, a review of the integrated code only.
* **Decided first:** QU1 to QU5, and what else rides on format 7.


## 8. Questions for Frans

* **QU1. The bound.** BU1, the fill after every transaction with its
  count in the live keys, as 2026.5's bound, and BD13's "twice the twin"
  as the gate BU2? **Recommended: yes:** stronger than BD13 (at once,
  with R forever too), and it can be a theorem.
* **QU2. The mechanism.** Merges at the delete alone; no rebuild by
  reclaim? **Recommended: yes** (section 4).
* **QU3. Dead klongs in live nodes.** With merges: at most B a node, on
  nodes in proportion to the live keys; one in a node that nothing
  writes stays. Within aim 3, as a named allowance, or must each go
  within a bounded number of iterations, which makes the touch a writer
  that a start reruns (CT)? **Recommended: the allowance, and CT
  never,** unless step 2 shows KEY klongs over 2.5 times the twin's at
  10M. The format is to be stable after 2026.5: "later" is a refusal.
* **QU4. The thresholds.** m = B / 4 and c = B / 2 give at most about
  twice a twin put in key order (1.90 measured, k = 2). A smaller
  constant needs m near B / 3 (10), and then a time split must keep up
  to 2B / 3 klongs, so that a space split's halves are at least m: the
  put path's fill rule changes for every database. In the model (3.4)
  that set is at most 1.3 times the twin in every row and has 28 % fewer
  key nodes under random overwrites, at 41 % more splits an overwrite;
  what it does to a put's bytes only Java can say. **Recommended: P5's
  values for now; step 2 measures the dense set in Java, and Frans
  decides between them before step 3.**
* **QU5. The model first?** The merge in 024-12's Lean tree, and TH2 and
  TH3 proved, before the Java branch? **Recommended: the definition and
  its `#guard` runs first; the proofs beside step 4.**
* **QU6. Nodes and klongs of tt** (5.6): P5's way (new nodes, take back,
  every klong repointed), or in place and net (fewer take-backs, V8 by
  form)? **Recommended: decide in step 3;** Java follows the model.
* **QU7. `dirtyNodeBound`:** CB2's simple count with its proof (the
  largest delete transaction about 250,000 deletes), or P5's sharper
  one, argued? **Recommended: the simple one.**
* **QU8. U4, one-key segment trees:** outside this change, as the twin
  has them (024-05, QF5)? **Recommended: yes.**


## 9. State

2026-11-11, 07:24 to 08:18, by the agent "fill" of coord-1111. A study:
no Java or Lean written, no clone made, no branch; in the main tree this
file only (677 lines: the probe and the model were not in the brief).

* **Done.** Sections 1 to 8.
* **Read.** 024-03 (4, 5), 024-04 to 024-06, 024's readme, 024-12 (2.1,
  2.2); 023-01 (2 to 4, 7 to 9), 023-02, 023-03 (2.6, 3), 023-04 (2.4 to
  2.7, X3, X4), 023-05's P5 and P3, 023-06 (5, 6, 13.1), 023-07 (5.9,
  9.1), 023-08; the delete, the splits and `dirtyNodeBound` in `Dag` on
  `main`, the merge in `Dag` on `023-p5-merge` (`71e386de`).
* **Run**, in `/Users/f/fl/bench/2026-11-11/fill/`, no lock (seconds
  each, counts, no timing run held it then): the probe of 3.3,
  `shapes.sh` to `shapes4.sh` on P5's frozen build `b-head4`, 35 runs,
  output in `out/`; the model of 3.4, `sim/sim.py` and `randfill.py`,
  written for this study, output in `sim/out-*.txt`.
* **Not done.** Nothing with merges at 10M; thrash and the other
  thresholds only in the model, not in Java; no fill at random in Java
  but the hashed keys. CB2's count is my derivation. BW, CW and CT are
  designs on paper. Not read: 023-09 to 023-11, the three reviews in
  full, `lean/`.
* **To continue.** Frans's answers to QU1 to QU4; then section 7's
  step 2.

2026-11-13. Status set after the release (coord-1113).
