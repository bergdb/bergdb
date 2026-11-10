# 023-06. Architecture review

Created 2026-11-10 by Frans Lundberg. Status: open.

A review of the overall solution of 023 before a mechanism is chosen: the
framing (023-02, 023-03), the options (023-04 and the independent study
in 023-04's folder), the prototypes' first reports (023-05) and the code of
`main`. First pass, written in about an hour; a second pass follows the
prototypes' final reports.


## 1. Summary and recommendation

The two studies agree more than their names show. The independent study's
B1 is 023-04's A (the unlink at the delete), its B2 is 023-04's D (merges
at the delete), its recorded sweep is 023-04's RB, and its A (copy the
whole path on each delete) is not 023-04's A at all. Both say: unlink at
the delete's own time, keep the node histories, and do more later. P1 and
P2 confirm that the unlink alone fixes every observed case at every
available time (6 reachable nodes against 7,902; the queue steady to 1M).

Recommended:

1. **For 2026.4: A+RC with LE-b and X5 (a)**, as 023-04, section 6.1 says.
   LE-b is sound as far as the code shows (section 4) and is the only
   leftmost rule that keeps a delete's whole change on its own path.
2. **For strict: merges at the delete (MG), not reclaim's rebuild (RB).**
   This differs from 023-04's X3. P3 shows RB's price in the code and in
   the numbers: the touch becomes a writer of the tree, the record needs
   the touch's range and the start a new rerun, the model's touch step
   must change (C-S), and a node replaced while dirty is written again and
   again by Rule A (2 to 3 times `main`'s bytes in the delete phase, with
   no deterministic remedy yet, P3's 5.3). MG is a change of the same kind
   as UP: a function of the delete and the state before it (A1), rerun by
   the same rule, checked by the same checkers, strict at every time and
   with R forever too, no new record field. Its price is a sibling read
   per merge, amortized one per m deletes, and more cases in the Dag.
3. **Dead klongs in nodes that keep live keys**: 023-04's X4 (a) with R
   finite; if Frans wants a bound at every time with R forever, DC with a
   threshold (section 5.3), not RB's compaction.
4. **Three things the studies underweight**: reclaim's iteration in
   progress at a mass delete scans every key live at its start, one step a
   user transaction (P1, P2: 1M keys need about 7,500 transactions before
   the cuts resume; a test-spec and a reclaim question, not the unlink's);
   the top nodes that Rule A keeps in D (P2's finding 7, P3's 5.2; not in
   023-02's K1 to K18); and that the touch copies the whole reachable
   index every iteration, which the unlink makes the live index.

Not got to in this pass: section 9.


## 2. Is the problem framed right?

Mostly, yes: 023-02's R1 to R27 and 023-03's tests judge by what a user
pays, against a twin, with counts, at every available time. What is
missing or imprecise:

* **R6's "bounded by the live data".** An iteration that starts before a
  mass delete scans, at its tStart, every key live then, in steps of 10 to
  16 KB, one step a user transaction (`Reclaim.step`, the scan at
  `it.tStart`). With the unlink the steps are cheap (the touch passes no
  emptied node) but not fewer: at N = 1M about 7,500 transactions (P2,
  finding 6; P1, 3.1). The keys were live at tStart, so R6 holds as worded,
  but T1's fixed drive of 4,000 transactions fails at 1M for this reason
  alone. Either the drive is counted from the end of the iteration in
  progress (023-03, Q1), or reclaim's scan runs at each step's own time
  instead of tStart: a value live at tEnd and stored before pCut was live
  at every time of the iteration, so a scan at the step's time finds it
  too, and skips the keys deleted since tStart. That is a change of
  reclaim's rule, deterministic (a function of the stream), for a probe
  in phase 2, not for 2026.4 unless cheap.
* **The top nodes.** TopDs's skip list is never pruned (023-01, 4.4), and
  Rule A keeps a written top node dirty while a node it points to is
  dirty: runs of 10 to 25 top nodes stay in D for thousands of
  transactions (P3, 5.2; P2, finding 7). It is what fails C6 and C9 in P1,
  P2 and P3. Not a leak (it is stable), not in K1 to K18, and not the
  unlink's doing; it needs a line in 023-02 and its own measure, or C6
  and C9 need a tolerance that names it.
* **Bytes written a phase.** 023-03 measures the largest record (M9) and
  the stream kept (M1), not the bytes appended in each phase. That is the
  write amplification R26 asks about, and the measure that separates RB
  (2 to 3 times) from UP (0.16 to 0.9 times `main`); P1 and P3 had to add
  it. Add it as a measure, per phase, against `main` and the twin.
* **R9's form.** With the unlink at the delete, every node reachable at t
  but a root has a live key below it at t, so a scan of n KVs follows at
  most about (n + 2) H key nodes, each single scan, at every time, in both
  directions. 023-02 should state that as the target and keep the
  amortized sum as the minimum; F4 is then answered.
* **T3's times.** T3 scans at the latest time and at one time before the
  deletes. Add scans at times inside a delete phase: at a time t in the
  middle of 1,000 deleting transactions, a scan must return the keys not
  yet deleted at t and follow no node emptied before t. That is the
  per-time invariant that only the unlink at the delete gives.
* **Test gaps for the mechanism.** None of T1 to T12 reaches the cases
  where the prototypes found their faults: a split's half emptied in the
  same transaction (X5), a relabel in a full parent, a root that the
  transaction made and collapses, a merge with a sibling made by this
  transaction, two klongs of one compare value when one is deleted. They
  need unit tests in DagTester and a fuzz with node sizes 8 and 14 where
  leftmost children empty often (P1's UnlinkFuzz, P2's P2Fuzz), as a step
  of `level1.sh`. And `dirtyNodeBound` against counted nodes for
  transactions of many deletes (005-31's record limit).
* **R11's "O(1) amortized new nodes"** needs a unit: per operation for
  fixed key lengths, per segment for long keys (the independent study's
  question 12). UP makes no new node; MG one per m deletes; RB makes new
  nodes per touch, which R11 does not count, so R11 should say whether a
  reclaim step's nodes count against the user's transaction.


## 3. The best overall design

### 3.1 What the two studies got right

* The unlink in the deleting transaction, at its time, upward across
  segment trees (UP). F3 makes it necessary: a lookup at t reads only
  entries of times up to t (sis-model.md, 3.4, A2), so a cleanup made
  later cannot repair a scan at t. The independent study's argument is
  the same, in its section 2.
* Node histories kept, replacement nodes never in place (lemma M).
* The hard cases named: the leftmost child, the empty last segment tree,
  nodes made and emptied in one transaction, the rerun's ids, the sweep's
  replay. P1, P2 and P3 met every one of them.

### 3.2 Alternatives looked at, and why not

* **Per-node live summaries** (a live count or a "has live keys" bit in
  each node): the writer can compute a node's live count from its at most
  62 klongs in the loop `appendDeleteKlong` runs anyway, so nothing need
  be stored. A stored summary would change the node format for no gain.
* **The multiversion B-tree's weak version condition** (Becker et al.;
  020-30-02): a current node holds between m and B live entries; a version
  split when full, a merge when below m. That is exactly UP plus MG with
  separated thresholds. It is the prior art for the shape at every time.
* **Unary collapse at every level**: RC's rule applied to any inner node
  with one live child (its parent's klong re-pointed to the child, as
  time-split-1 does). It would remove the single-child chains of "inter"
  (P1: 14 nodes against 6) without a merge. Not recommended: it makes
  leaves of one segment tree lie at different depths, so a leaf's sibling
  can be an inner node and the balanced merge rule no longer applies; and
  it bounds the node count but not the height. MG with RC covers it.
* **A range delete** (RD): a new Core operation, record content and STM
  rule for what UP already bounds. Not now (023-04, X9).
* **Copy the whole path on each delete** (the independent study's A): 5.5
  times `main`'s writes in its FIFO. Rightly rejected there.
* **Relax the routing rule** (LE-c, P2): section 4.
* **Reclaim alone** (B): fails F3 and R forever (023-04, 3.3; P3's T3).
* **A different division of work**: the deleting transaction unlinks,
  relabels, collapses roots and merges; reclaim rewrites values and cuts,
  as today, and its touch stays a reader of the tree. That is the simplest
  division: the model's touch step, the rerun and the cut's argument are
  unchanged, and every structural change is one kind of thing, an
  operation of `Dag.putKv` that A1 covers.

### 3.3 The recommended design, as mechanisms

In `Dag.setValue`'s delete, for each delete of the transaction, in key
order, at tt:

1. **The leaf.** As today: no live klong of the key, a noop. Else compute
   the union bitmap (Dag.java:955) and the live count after it.
2. **UP.** Live count zero: the leaf is left out (`toPreviousState(tt - 1)`,
   reported replaced, as a split's node); the parent's klong to it is
   the next target, and so on up while the parent would keep no live
   klong. A segment root's parent is a segment leaf: the segment's klong
   is deleted there (`setNode` treats it as absent). The first node that
   keeps a live klong takes the change.
3. **The change in that node.** Its klong to the emptied child is not
   its smallest live one: a bitmap at tt (or in place in the
   transaction's own bitmap), with the bits of every klong of that compare
   value. It is the smallest: **LE-b**, a new klong `EMPTY_KEY` pointing
   to the next live child, and a bitmap for that child's own klong; the
   bitmap before the new klong. A full node goes through `handleFullNode`
   with the new klong as `toInsert` and `lastVersionGivenDel` with the
   bitmap: `replaceKlong` then puts the new pointer into the last version's
   `EMPTY_KEY` entry, timeSplit's existing path.
4. **MG** (strict, later): the node that took the change, if not a root
   and left with fewer than m live klongs, is merged with its right
   sibling under the same parent (the left one if it is the last): one new
   node at tt from both last versions if they fit in B/2, else two; the
   parent gets a klong for each new node and bitmaps for the old ones;
   the old nodes are left out as replaced. Up the path while a parent is
   underfull.
5. **RC.** A root of a segment tree, or the space root, that is an inner
   node with one live klong: its only child becomes the root, through a
   new super root (`TopDs.newSuperRoot`) or a klong of the same compare
   value in the segment leaf above; again while the new root is so. The
   child is followed without being marked (P1's fault 2).
6. **X5 (a).** A node that this transaction made (its first klong is tt's
   TIME klong) and would leave out is taken back: the klong of tt that
   names it is changed in place, behind tt's TIME klong, and the node is
   dropped from D, the record and the node table; its id is consumed, so
   the rerun makes and drops it the same way. P1 re-points the klong to
   the node it replaced and then treats that as an emptied child; P2
   replaces it by a no-op bitmap and deletes the older klong. Either is
   acceptable; P2's form leaves no momentary pointer to a replaced node.
7. **The space root** left with no live klong: an empty segment leaf as
   the new super root (both prototypes). With RC it is rare; it needs a
   unit test, as no run reached it (P1, 5).
8. **`dirtyNodeBound`**: a delete may add a TIME klong, a bitmap and one
   KEY klong to every node of its path (3 klongs a node), a top node for
   RC, and for MG a sibling, up to two new nodes and three klongs a level.
   Everything is on the path or a sibling of it, so the bound stays a
   walk of the path (Dag.java:477).
9. **AP, SE, MT** as 023-04 recommends (X8, X11, 2.11); TE not needed.

With R finite nothing else changes: reclaim's scan and touch are
`getMany`s and pass the live tree; the cut takes the unlinked nodes'
versions as it takes replaced nodes' today.


## 4. The leftmost child: LE-a, LE-b, LE-c, LE-d

### 4.1 What relies on the rule

Checked on `main`: every reader above a segment leaf uses `searchLte`
(`Dag.setValue`, `setNode`, `getEqNodeInSegment`, `dirtyNodeBound`,
`GetMany.Chain.setup` both ways) and relies on a live klong at or below
the key; `checkFound` fails the database if there is none (019-32).
`Chain.next` moves between siblings with `searchGt` and `searchLt`, which
need only the siblings' order. 021-28's end key (a branch) takes a
klong's compare value as a lower bound of its subtree.

### 4.2 LE-b checked in the code

LE-b: every inner node's smallest klong is `EMPTY_KEY` (compare value 0,
Klong.java:79), the roots of space splits have it today (Dag.java:1139,
1256, 1281), and a space split of an inner node gives its second half the
empty key as its first klong while the parent gets the second half's first
compare value, as today (`firstAndSecond`, KeyNode.java:1276; Dag.java:1308
to 1323). An emptied leftmost child is replaced by one new klong
`EMPTY_KEY` in the parent that points to the next live child, and a bitmap
for that child's own klong.

Point by point:

* **The empty key is the smallest compare value.** `createKey(new byte[0])`
  is 0; every other compare value has bytes or a length above 0. A leaf
  may hold a klong of compare value 0, the empty last segment of a key of
  7 or 14 bytes (Keys.java:240), but a leaf is searched by equality, and a
  bound in an inner node comes from the second half's first klong, which
  is above the first half's klongs, so above 0. So in an inner node a klong
  of compare value 0 is always the leftmost bound. Sound.
* **Every inner node has it**, by induction over how inner nodes are made:
  a new root (`EMPTY_KEY` first, today); the first half of a split (the
  node's sorted last version, where 0 comes first); the second half (the
  new rule); a time split's last version (`lastVersionGivenDel` keeps the
  latest klong of each compare value, sorted, KeyNode.java:1091); a merged
  node (the rule must say so, 023-04, 2.4 does); a root collapse (the
  child is inner with the empty key first, or a leaf). The empty key is
  never deleted while the node is current: if its child empties and
  another live klong exists, it is re-pointed, not deleted; if none
  exists, the node itself is left out. Holds for every tree 2026.4 writes
  (F9 (a)).
* **Of two klongs with one compare value the latest wins** in `searchLte`,
  `searchLt` (`>=`), `searchGt`, `searchGte` (`<=`), KeyNode.java:516, 592,
  665, 739: the relabel's new `EMPTY_KEY` klong shadows the old one, as a
  time split's klong in the parent does today. `searchFirst` (763) takes
  the first, the shadowed one; no production code uses it (P2's fault 1).
* **Routing after a relabel.** A key below the old second bound K1 is
  routed to the next child C1 by the new empty klong; in C1, `searchLte`
  finds C1's own empty klong or a larger bound at or below the key, so the
  key goes down C1's left edge, where every bound is 0 or at or below it.
  The order invariant, every key below a child is at or above the child's
  klong and below the next live klong, holds: 0 is below every key, and
  C1's keys were in [K1, K2). Sound; nothing below C1 changes.
* **Splits of inner nodes.** The second half's keys are at or above the
  parent's new bound L_h, and inside the second half a key at or above
  L_h finds the empty klong (child D_h, whose keys are in [L_h, L_h+1)) or
  a larger one. The bound L_h is now only in the parent, not in the child;
  021-28's `isPastEnd` sees 0 for a first child, a weaker check, right,
  and stops one klong later. `replaceKlong` (KeyNode.java:893) matches the
  klong value and time: in a full parent the relabel's `EMPTY_KEY` klong
  at tt replaces the last version's `EMPTY_KEY` entry at tt, timeSplit's
  own path, with no new code.
* **Scan setup.** `kwi.klong == NULL` above a leaf (GetMany.java:262 to
  267) cannot happen in a 2026.4 tree: dead code, harmless. Backward,
  `searchLt` in the parent before the smallest klong finds nothing, which
  is right.
* **The model.** A deleted klong K1 beside a live empty klong to the same
  child: TREE counts current parents by live pointers (C1 has one, P);
  A6' allows a pointer that is not a live child when the node is reachable
  from P through a live pointer (it is); A-COPY: the new pointer is copied
  from P itself, current. The relabel's new klong (compare value 0) and
  its bitmap (compare value K1) differ, so the trap P1 fell into with
  LE-a (a bitmap after a new klong of the same compare value, which the
  trace format reads as deleting the new one too) cannot arise; the rule
  "bitmap first" should still be kept.
* **Cost.** One KEY klong and one bitmap in a node on the delete's path,
  dirty anyway; a time split of that node when full, as any klong causes.
  No node off the path: the delete's dirty set is its path, plus a top
  node for RC. LE-a writes one node a level down the next child's left
  edge, off the path, and P1's version descends from the root for each
  (O(H²) follows).

**Verdict: LE-b is sound everywhere I could check, and the best of the
four.** What P4 must still show: DagTester's split shapes with the rule,
`KeyNode.check()`, `StoredKeyNode` and the trace export with the empty
klong in more nodes, and a fuzz at node sizes 8 and 14 where leftmost
children empty often, with scans both ways at every time.

### 4.3 The others

* **LE-a** (P1): sound, works, but O(H) nodes off the path per emptied
  leftmost child and a larger `dirtyNodeBound` (P1 counts 7 nodes a level
  for a delete); its fault with the trace format shows the extra rule it
  needs. The fallback if P4 finds a problem.
* **LE-c** (P2): sound as built, and P2's numbers are the best so far, but
  the rule moves into every reader (`searchRoute` in five places), into
  the split (`relaxedSplitKlongs`, a relabel at the split after all, with
  three klongs in the parent and a bitmap), into 021-28's end key (an
  exception at first children) and it weakens `checkFound`. For no byte
  saved over LE-b. Not recommended; P2's climb, rule 1, rule 2 and tests
  carry over to LE-b unchanged.
* **LE-d**: fails R3 and blocks RC (023-04, X1).


## 5. Strict: merges at the delete, or a rebuild by reclaim

### 5.1 What strict needs beyond A+RC

Three rests (P1, 5; P2, 6; 023-04, 8.4): underfull leaves ("sparse": 4,031
nodes against the twin's 263, one live key a leaf), single-child chains
below the root ("inter": 14 against 6), and dead klongs in nodes that
keep live keys (M5, C4). Only merges take the first; merges with RC take
the second; the third goes at time splits.

### 5.2 MG against RB against the recorded sweep

The independent study's sweep is RB with a stored cursor: the same thing,
and its section 4.1 says what P3 then built: "A cleanup that creates nodes
cannot be put into that hook without also specifying how the startup
rerun makes the same nodes." P3 answered that correctly (the range in the
record, the rebuild rerun before the step's puts, RestartInvariance and
CrashTest with reclaim pass), so RB is possible. The question is its price:

| Point                        | MG at the delete              | RB in the touch                |
|---|---|---|
| Strict, when                 | at every time, R forever too  | an iteration later, R finite   |
| What a start reruns          | the delete, as UP             | the touch: a field, new code   |
| The model                    | nothing new                   | the touch step changes (C-S)   |
| Rule A on replaced nodes     | as a split's today            | 2 to 3 times the bytes (P3)    |
| Where the sibling comes from | a read in the writer, one     | the walk has it                |
| Step boundaries              | none                          | merges wait for the next pass  |
| Cases in the Dag             | X5-like, siblings, roots      | plan and build, roots          |
| Dead klongs in live nodes    | only in merged nodes          | all, within an iteration       |

P3's 5.3 is the decisive line: a node that the rebuild replaces while it
is dirty must still be written once, and Rule A keeps it dirty while a
child is dirty, so in a busy range it is written again and again; no
deterministic remedy exists yet, and each candidate needs stream-derived
state. With MG a replaced node costs what a split's costs today. RB also
gives nothing with R forever, and its lag adds to K (F6).

So: **MG with separated thresholds** (merge below m = B/4, a merged node of
at most B/2, so a merge is followed by about B/4 operations before the
next split; 023-04, 2.4), on top of A+RC, on its own branch. RB only if
MG's measurements disappoint (T2's "sparse", T10), or if Frans prefers
that the deletes stay as cheap as UP alone and strict waits for reclaim.

MG's risks, to be met in the prototype: a sibling made by this
transaction (merge in place, as the splits do), a sibling in D (written
once, as a split's node), the sibling read in the writer under the write
lock (one node a level, at most H a delete; a put loads its path the same
way), thrash at the thresholds (the gap of B/4 prevents it), and the
pointer copies from the sibling made before it is left out (A-COPY).

### 5.3 The rest for strict

* **"sparse"'s a_n = 10.** With MG the nodes hold m to B/2 live klongs,
  about 2 to 3 times a twin's put in key order; the strict allowance of 10
  nodes came from the hello-world shapes, where UP, LE-b, RC and MG reach
  the twin. For "sparse" the honest target is a constant factor (Y5), or
  a denser merge rule, which trades thrash for density.
* **Dead klongs in live nodes.** With R finite reclaim's rewrites fill and
  time-split every leaf with a live key within about B iterations (023-04,
  X4, probe 8.5), and the relabel's and the climb's klongs go the same
  way. With R forever they stay, at most B a node, which R8 allows. If
  Frans wants a bound at every time: DC, a time split when a node's dead
  klongs exceed its live ones and a threshold of about B/4, which reuses
  `handleFullNode`'s time split and costs a new node per B/4 ended
  versions, amortized. Not RB's compaction.
* **Determinism of a rebuild by reclaim**, if it ever comes: P3's way is
  right (the range stored, the rebuild a function of the tree at ts
  through the writer's follower, rerun before the puts). What it cannot
  fix cheaply is Rule A's rewrites.


## 6. Interactions and risks the studies may underestimate

* **Lookups at earlier times.** Every change is an entry at tt, so the
  state at every time before tt is untouched; the only in-place changes
  are to klongs of tt (the transaction's bitmap, the take-back), behind
  tt's TIME klong, where every reader stops (KeyNode's class comment).
  Readers never swizzle a pointer of tt, as they never follow one.
* **The cut and an unlinked node U.** A lookup at an available time t
  reaches U only if f <= t < tt. Then the cut iteration's tEnd = f < tt, so
  its touch at ts <= tEnd reached U while U still had live keys, and U is
  stored at pStart or later or dirty (Reclaim's class comment). Holds for
  UP, LE-b, RC, MG as for a split today; P3 argued the same for RB.
* **The node table and handles.** An unlinked or replaced node stays
  resident until CLOCK takes it (X6 (a)); a taken-back node must leave the
  node table at once (P2's fault 4, C-H) and the record. After a relabel,
  two pointers of P hold C1's handle; handles are shared by design (top
  nodes do it).
* **The rerun and its id check.** UP, LE-b, RC, MG and X5 are functions
  of the delete and P@(tt - 1), with ids consumed in creation order, the
  taken-back ones included. Risk: any dependence on what is resident (a
  `newInTrans` test uses the object's history, which the rerun rebuilds;
  a merge's sibling has the same content loaded or canonical). A mismatch
  fails the start, loudly (`DbStarter.rerunTransaction`), never silently.
* **Startup, bounded (007).** Delete records are small now (about 60
  bytes), so a startup section holds about ten times as many deletes, and
  the rerun reads each one's path: 6,105 loads against 4 in "long" (P2's
  finding 8). Bounded by the section, a larger constant per byte; measure
  cold at a startup distance of 50 MB before the release.
* **The record limit.** `dirtyNodeBound` must not undercount (005-31):
  P1 and P2 both widened it and one hit DbTester.testRecordsWithinLimit.
  A test of the bound against counted nodes for transactions of 1,000
  deletes at node sizes 8, 14 and 30 is needed.
* **Java's bitmap by index, the model's by compare value.** A delete must
  set the bits of every klong of the compare value (as `appendDeleteKlong`
  does), and a bitmap must come before a new klong of the same compare
  value in the same transaction (P1's fault 1). State it as a rule of the
  Dag; the trace checker catches a breach.
* **Marking.** The model marks the nodes current at tt with a change
  below them; a follow that changes nothing must not mark (P1's fault 2,
  RC). Every new follow in the Dag needs the quiet follower.
* **Reclaim's scan at tStart** after a mass delete (section 2), and the
  touch, which still runs on to the first live key after its range (TE):
  O(H) with UP, fine.
* **Write amplification.** UP writes less than today (0.16 to 0.9); MG
  adds about one node write per m deletes in sparse ranges; the touch
  copies the live index once an iteration, as today. RB: P3's numbers.
* **Top nodes in D** (section 2): bounded, but above the twin's by phase;
  C6 and C9 need a tolerance that names it.
* **The Lean model.** No change for UP, LE-b, RC, MG, X5 (a): entries at
  tt, new nodes reachable at tt, replaced nodes with no entry of tt, A4's
  levels kept (RC and MG point to lower levels), TREE, A6', A-COPY as in
  section 4.2. A2A3Check2 must learn the taken-back node (P1's Q1, P2's
  Q1). RB changes the touch step (C-S).
* **What could go wrong in production.** The one catastrophic failure is
  an unlink or a merge that loses a live key at the latest time; T6,
  DagFuzz, the fuzzers, A2A3Check2 and the trace checker all see it, and
  the climb's plan can be checked before anything changes (P1 does so).
  The others fail loudly (the rerun, `checkFound`, the record limit) or
  cost performance (thrash, startup reads, the FileStream's whole-file
  lag, P3's 4.6).


## 7. The correctness argument, a sketch

For the design of 3.3, at every lookup time t and after every operation.

Invariants:

* **I1, bounds.** In every inner node, every klong live at t is at or
  below every key below it at t and below the next live klong at t; the
  smallest live klong is `EMPTY_KEY`.
* **I2, nothing empty.** Every node reachable at t but the space root has
  a key live at t below it; with RC no root is an inner node with one
  live klong; with MG every reachable node but a root has at least m live
  klongs at t.
* **I3, history.** A node's entries of times at or before t never change
  after t: A2, and in-place changes only to klongs of the running
  transaction.
* **I4, the tree.** TREE, A4, A5, A-COPY.
* **I5, D and the cut.** Every node reachable at times from tEnd on is at
  pStart or later or dirty.
* **I6, determinism.** Every change is a function of the operation and
  P@(tt - 1); ids in creation order.

Each operation: a **put** adds a klong under a live bound (I1) to a leaf
on its path, or splits as today; a split's halves and new root keep I1
by the sorted last version and the empty key, I2 by holding the keys,
I3 by replacing. A **delete with the climb** adds a bitmap at tt to the
first node that keeps a live klong, leaves out the nodes below it (no
entry of tt in them, I3; unreachable at tt, I2; reachable before, I1 as
before); the **relabel** keeps I1 by 4.2; the **take-back** changes only
klongs of tt and drops a node reachable at no time (A3 on the record);
**RC** points a root's parent, or the top, to a child that satisfies I1
on its own (4.2) and had every live key of the root (I2); a **merge**
makes a node of two last versions, sorted, under the left bound, and
deletes the right one (I1, I2, A-COPY from current nodes before they are
left out); **reclaim's step** rewrites values (puts) and touches (a
reader): I5 as today, and the cut's argument of section 6 for left-out
nodes; the **startup rerun** redoes each record's operations by the same
rules on the same state (I6, A1), so the same nodes, ids and D;
**eviction** changes no entry (INV-EVICT). Lookups at t read the tree at
t (I3), which satisfies I1 and I2 at t, so R1 and the single-scan bound
of section 2 follow. A proof is not asked for (023-02, 7.1); the checkers
check A1 to A5, TREE, A6', A-COPY and `CutOK` on every run.


## 8. What to do next, and the test gaps

1. **P4** (LE-b on P1's branch) to the gates, `level2.sh`'s conformance
   included, with the checks of 4.2's verdict; compare P1, P2, P4 by
   023-03's counts and the bytes a phase.
2. **MG on P4's branch**, a design note first (the cases of 5.2), judged
   by T2's "sparse" and "inter" against their twins, T4's hashed queue,
   and the bytes a phase. RB (P3) kept as the measured alternative.
3. **Reclaim's scan at the step's time** as a probe (section 2), or T1's
   drive counted from the end of the iteration in progress.
4. **The top nodes in D**: explain and bound (P3's 5.2), then C6 and C9.
5. **Tests**: the unit tests and fuzz of section 2's last two points; T3's
   scans inside a delete phase; the bytes a phase; `dirtyNodeBound`
   against counted nodes; a startup measure at 50 MB.
6. **The format entry** for Frans's approval (018-01, section 2): format
   6 with UP, LE-b, RC, X5 (a), and MG if it comes; new digests.


## 9. Questions for Frans

Each with a recommendation; the questions of 023-02 (F), 023-03 (Q) and
023-04 (Y) it meets.

* **Z1. LE-b** (Y1; X1). Recommended: yes, LE-a as the fallback, not LE-c.
* **Z2. RC in 2026.4** (Y2). Recommended: yes.
* **Z3. Strict by merges at the delete, not by reclaim's rebuild** (Y3,
  X3; F5, Q2). Recommended: MG, as 5.2; RB kept as the alternative if
  MG's numbers disappoint. This differs from 023-04.
* **Z4. RB in 2026.4** (Y4). Recommended: no; A+RC first, MG next on its
  own branch, into 2026.4 only if it passes the gates when A+RC does.
* **Z5. Dead klongs in live nodes** (F1, F6; X4). Recommended: X4 (a),
  with K about B iterations reported as M5; DC only if a bound at every
  time with R forever is wanted.
* **Z6. maintain()** (F7, Y10). Recommended: yes, bounded a call, as P3
  built it; the tests need it.
* **Z7. T1's drive at large N** (Q1; P1's Q3). Recommended: count the
  drive from the end of the iteration in progress at the deletes, and
  probe the scan at the step's time.
* **Z8. The taken-back node in A2A3Check2** (P1's Q1, P2's Q1).
  Recommended: accept; it is reachable at no time and in no record.
* **Z9. SE and TE** (Y7). Recommended: SE yes, TE not needed.
* **Z10. F4.** Recommended: with UP the single-scan bound is the target;
  the amortized sum stays the minimum.
* **Z11. Top nodes in D** (P2's Q4). Recommended: a measure and a line in
  023-02 now; a todo of its own, not 023's gate.


## 10. State

2026-11-10, 12:15, first pass, written in about an hour at the
coordinator's request for 12:55; from 023-01 to 023-04, the independent
study, P1's, P2's and P3's draft reports (not final), and the code of
`main` (`Dag.putKv` to `spaceSplit`, `KeyNode`'s searches, `lastVersionGivenDel`,
`firstAndSecond`, `replaceKlong`, `toPreviousState`, `GetMany.Chain`,
`TopDs.newSuperRoot`, `Reclaim.step` and its class comment,
`DbStarter.rerunTransaction` and `canonicalNode`, `Db`'s marking and
`touchRange`, `dirtyNodeBound`; sis-model.md 3.4 and 15). No probe run.
Checked after the text was written: `KeyNode.check()` assumes nothing of
the first klong (sizes, time order, pointer positions only), and the
trace checker's `blive` (Check/Trace.lean:56 to 69) folds a node's
entries in order, a `del` naming the compare values before it, which is
what 6's rule "bitmap first, every klong of the compare value" rests on.

Not got to: `StoredKeyNode`, `Audit` and `TraceExport`; `NodeCollection`'s
Rule R maps and position caches (the independent study's audit targets);
`Cache3.evict` and the handles' code; `Reclaim.pretruncateIfPossible`;
the Pub API's `deleteIndex` thread; the C port's estimates; the P4
branch; 020-30-04; levels.md's sections 5 to 7 beyond what 023-01 cites.
For the second pass, with the prototypes' final reports.


## 11. Second pass: the prototypes against the design and each other

Written 2026-11-10 from 13:25, from the final reports of P1 (`13b3692f`),
P2 (`13091f30`), P3 (`7b2cf1ec`) and P4 (`0e66d1c9`), the drafts of P5
(`789b1654`, `level2.sh` full running) and P6 (`c46d607d`, `level4.sh`
full to run), and Frans's answers to Y2, Y6, Y7, Y8 and Y10 (023-04,
section 7). Sections 1 to 10 stay as written; 11.1 says where my view
changed.

### 11.1 Changes of view since the first pass

* **LE-b needs one more rule than 4.2 states.** A space split of an inner
  node that also inserts a klong for the child of the second half's first
  compare value must give that inserted klong the empty key too, so that
  it shadows the copied one (P4, 1.1; found by a mutation test before any
  run). My induction in 4.2 covered the copied klongs, not the inserted
  one. The verdict stands; the rule is in P4's `firstAndSecond`.
* **The take-back must retarget every klong of tt**, deleted ones too
  (P5, section 6): a deleted klong of tt in the parent can still name a
  node that is never written. P4's take-back pointed only the live one.
  P5 fixed it and UnlinkFuzz checks it; P4 should take the change.
* **Memory.** I let X6 (a), CLOCK as today, stand in the first pass.
  Frans chose (b) (Y6, 12:35), and P6 shows that the rule can hold for
  memory at a small, model-free price: the dead hand after each cut and
  the replaced queue. I now recommend both (section 12).
* **The run of dirty top nodes** is not phase, as P1 and I supposed. P6
  found the cause: Rule A with the take's oldest-first lists holds a
  sliding window of consecutive top nodes whose length freezes at what a
  disturbance left (39 inverted pairs at 1M); bounded, but it may ratchet
  up at a later disturbance, and no small fix exists (P6, section 5).
* **Strict by merges at the delete is confirmed** by P5: no reachable node
  but a root below B/4 live klongs after any transaction, at the costs
  section 5.2 predicted, with one anomaly to explain (11.3).
* **Every rule change is a format change** in 018-01's sense, because the
  startup rerun applies the Dag's rules to the section's records: a
  2026.5 that adds merges would rerun 2026.4's sections by other rules and
  fail the start, so it would refuse 2026.4's databases as 2026.4 refuses
  2026.3's, or carry two rerun paths. I had not weighed this in section
  5. It argues for every rule of the delete, merges included, in one
  format 6 (Z12). What is not a rerun rule can come later without a
  refusal: P6's eviction (the records are unchanged), SE (the read path),
  a change of the take (the dirty top nodes' fix (a)), `maintain()`.

### 11.2 The six prototypes

| P  | Mechanism                        | Gates at the head                     | Verdict     |
|---|---|---|---|
| P1 | UP, LE-a, X5 (a), RC             | before-commit, level1 to 4 full OK    | superseded  |
| P2 | UP, LE-c, rule 2, RC apart       | before-commit, level1 to 4 full OK    | not taken   |
| P3 | RB in the touch, MT, format field | level3 and level4 quick: C-S only    | not for 2026.4 |
| P4 | P1 with LE-b, RC take-back       | level1, 2 full OK; 3, 4 quick OK      | the base    |
| P5 | P4 with MG                       | level1 full OK; level2 full running   | strict, if 11.3 |
| P6 | P4 with the dead hand, the queue | before-commit, level1, level4 quick OK | memory, in |

The counts, N = 100,000 "after" unless named, each against its twin:

| Measure                      | main   | P1    | P2    | P3    | P4    | P5    | P6      |
|---|---|---|---|---|---|---|---|
| M4, reachable (twin 6)       | 7,902  | 6     | 6     | 6     | 6     | 6     | 6       |
| "inter" M4 (twin 6)          | 7,901  | 14    | 14    | 6     | 14    | 6     | 14      |
| "sparse" M4 (twin 270)       | 7,902  |       |       | 377   | 4,036 | 390   |         |
| Deletes' bytes, R forever    | 6.78   | 5.04  | 4.74  |       | 4.82  | 5.11  | 4.82    |
| Deletes' bytes, R = 1 s      | 10.9   |       | 6.07  | 22.8  | 6.16  | 6.37  | 6.16    |
| Objects after the deletes    | 9,592  | 10,297 | 9,600 | 19,460 | 9,600 | 12,200 | 9,600 |
| Resident, 1 GB budget, end   | 11,612 |       |       |       | 11,612 |      | 152     |
| Nodes off the path changed   |        | 704   | 0     |       | 0     | 0     | 0       |
| T4 ordered 1M, M4 (117 live) | 111,434 | 117  | 117   |       | 117   | 117   | 117     |

(Bytes in MB; P5's objects are "about 1.27 times P4's"; P3's "sparse" has
no twin run. P6's deletes' bytes are P4's: the records do not change.)

* **P1** proved UP, X5 (a) and RC, and found by the trace checker what no
  other test found: the bitmap must come before a new klong of the same
  compare value; a follow that changes nothing must not mark; a node
  taken back must leave the node table. Its LE-a writes one node off the
  path per ten emptied leftmost children and keeps 7 to 8 % more objects
  than `main`. Superseded by P4, which keeps everything else of it.
* **P2** is the best in bytes (2 % below P4) and the only one whose
  measurements include the full level3 and level4 with its root collapse
  apart. But LE-c moves the rule into five readers and into the split
  (`relaxedSplitKlongs` is a relabel at the split, with a bitmap in the
  parent), weakens `checkFound`, and needs an exception in 021-28's end
  key. 4.3 stands: not taken. P2's rule 2 (the no-op bitmap in place) and
  P2Fuzz carry over.
* **P3** reaches the twin's shape in every row by reclaim alone, and its
  rerun of the touch is sound (RestartInvariance, CrashTest, C-CUT 0 of
  254). What section 5.2 feared is measured: 2.1 to 3.0 times `main`'s
  bytes in the delete phase, 1.8 to 2.5 times the objects, the model's
  touch step to change (C-S in 507 steps), and the structural cause (5.3,
  a node replaced while dirty) has no deterministic remedy without more
  stream state. Its `maintain()` (MT) is separable and good.
* **P4** is the base: no node off the path, 0.71 of `main`'s bytes in
  "after", `main`'s objects, 17 of 18 rows bounded, T4 byte for byte P1's
  stream, and the full level2 with 70 traces. Its RC take-back of a root
  made by the transaction closes "hashed" to the twin's shape.
* **P5** adds merges on P4: "inter" to the twin's 6, "sparse" to 1.44
  times the twin's nodes (1.20 with a 3 B/4 cap, at the price of a
  smaller gap before the next split), T4 unchanged, bytes 0.94 to 1.07 of
  P4's but one row (11.3), one sibling read per merge, 2 % of them from
  the stream under eviction, 27 to 32 % more resident objects until
  eviction (which P6's replaced queue takes). Its strict fuzz is the
  strongest check of the shape so far.
* **P6** gives Frans's Y6 (b): after a cut, every object stored before
  pCut is dead by reclaim's own guarantee, and a bounded round (4,096
  handles, 2 ms a transaction) evicts them whatever the budget; the
  replaced queue evicts a replaced or unlinked node's object once it is
  written, with R forever too. The records are unchanged, so the model
  needs nothing (an eviction schedule), C-P and C-H pass, held readers
  expire as they must. T1 "after" at 100,000 with a 1 GB budget: 152
  resident objects against 11,612 (twin 89); T4 steady at 151 to 185
  against 24,113 and growing.

### 11.3 What the prototypes found that the design must answer

1. **P5's "inter" writes 2.1 times P4's bytes** in T1's deletes with
   reclaim running (1.03 with R forever): unexplained (P5's guess: a
   sibling dirtied by the touch written once as a left-out node and again
   in the merged node, and Rule A). Must be explained before merges ship.
2. **`dirtyNodeBound` overcounts** by 30 to 170 times for transactions of
   many deletes (P5, section 6): P1's count of 4 nodes a level and 2 more
   per delete, kept by P4 and widened by P5, refuses a transaction of more
   than about 150,000 deletes that `main` takes. A regression (R27). The
   count must be by node of the paths, as the walk already is, and checked
   against counted nodes.
3. **Reclaim's scan at tStart** after a mass delete costs every prototype:
   about 7,500 transactions at 1M before the cuts resume (R6, T1's drive),
   and with P6's replaced queue 190,272 loads at 100,000, since the scan
   reads the leaves and values that the deletes unlinked. Section 2's
   proposal, the scan at each step's own time, removes both (Z14).
4. **The dirty top-node window** (11.1): bounded, history-dependent, may
   ratchet. Fix (a) changes the take's records, not the rerun's rules.
5. **Test fixtures pinned to format 5**: `CorruptStreamTester.testFound019_32`
   names byte offsets of streams that every prototype changes; StreamDigest's
   12 digests; `DbTesterJavadoc`'s eviction budget; `PubTester`'s 2,500
   puts (P3 only). New expected values, each with Frans's approval
   (018-01, section 2).
6. **Test races on a loaded machine** (`IndexJobsHarness`, twice in P5's
   `before-commit.sh`, 55 clean runs alone): the checks read memory and
   the stream at different moments while a build runs. Not the code; to
   be understood before the gates are trusted on a busy F53.


## 12. The combination for 2026.4, and what stays out

### 12.1 In

* **P4 as the base**: UP, LE-b with P4's inserted-klong rule, X5 (a) with
  P5's retarget, RC with the take-back of a root made by the transaction,
  the drop of taken-back nodes from the node table, format 6 refusing
  earlier databases with a message that names 2026.3.
* **P5's merges**, m = B/4, a merged node of at most B/2, the left sibling
  first when both fit, into the same format 6, on three conditions: its
  level scripts pass full, 11.3's point 1 is explained, and `dirtyNodeBound`
  is counted by node (point 2). If they do not close before the release's
  gates, 2026.4 ships P4 alone with the bounded allowance, and merges come
  in a release that refuses 2026.4's databases (Z12).
* **P6's dead hand and replaced queue**, on by default in every schedule
  but `noEvict()`; the Cache3 shrink patch later (it changes the node
  table's locking).
* **SE**, 021-28's end key (Y7), and **MT**, `Db.maintain()` and
  `Database.maintain()` as P3 built them without RB (Y10: yes, optional).
* **AP** (023-04, 2.11), a few lines.
* **Tests**: 023-03's T1 to T5 as code, UnlinkFuzz strict and the draining
  configurations in the level scripts, the unit tests of section 15.

### 12.2 Out

* RB (P3's rebuild) and its format field; TU; TE; RD; DC (X4 (a) is
  enough with R finite; a bound at every time with R forever was not
  asked); LE-a and LE-c; the 3 B/4 merge cap (needs a thrash test); the
  dirty top nodes' fix (Z13); the Cache3 shrink; reclaim's scan at the
  step's time unless its probe is clean in time (Z14).


## 13. The correctness argument for the combination

Sharpened from section 7 with the rules the prototypes' faults taught.
At every lookup time t, after every transaction, for the tree 2026.4
writes (F9 (a)).

### 13.1 Invariants

* **I1, bounds.** In every inner node, every klong live at t is at or
  below every key below it at t and below the next live klong at t; its
  smallest live klong is `EMPTY_KEY`, and no delete bitmap ever sets a
  bit of the empty key in an inner node.
* **I2, the shape.** Every node reachable at t but the space root has a
  key live at t below it; no root at the latest time is an inner node
  with one live klong; with merges, every reachable node but a root has
  at least B/4 live klongs at the latest time, and at every time t since
  the transaction that last changed it.
* **I3, history.** A node's entries of times at or before t never change
  after t. In place only: klongs of the running transaction, behind its
  TIME klong; and what a pointer holds (handle, value, reference), under
  the node's monitor, as today.
* **I4, the model's tree.** A1 to A5, TREE, A6', A-COPY (sis-model.md,
  3.4 and 15.2).
* **I5, the record.** No node that a transaction made and took back is
  named by any klong of tt, live or deleted, in any node that is written,
  nor is it in the record or the node table.
* **I6, D and the cut.** Every node reachable at times from tEnd on is at
  pStart or later or dirty; an object stored before pCut is reached by no
  lookup at an available time.
* **I7, the dirty set.** A node is dirty after a transaction exactly if
  it is current at tt and a node below it was made or changed (the
  model's marking), or Rule A keeps it.
* **I8, determinism.** Every change is a function of the operation and
  P@(tt - 1), with ids in creation order, taken-back ones included.

### 13.2 Why each operation keeps them

* **A put.** Adds a klong to a leaf under a live bound (I1) or splits.
  A split's halves hold the keys (I2), start with tt's TIME klong, the
  second half of an inner node with the empty key, the inserted klong of
  the second half's first compare value as the empty key too (I1, P4's
  rule); the replaced node loses only its klongs of tt (I3) and is
  reachable before tt only (A5); pointers are copied from it while it is
  current (A-COPY).
* **A delete, the climb.** The nodes left out get no entry of tt (I3,
  A2) and are unreachable from tt on (I2); the node that keeps a live
  klong gets a bitmap whose bits cover every klong of the compare value,
  and the bitmap precedes any new klong of the same compare value in that
  transaction (so Java's index-based bitmap and the model's compare
  values agree; P1's fault 1). The empty key gets no bit (I1).
* **LE-b.** The new empty klong points to the next live child, a copy of
  a pointer of the same node (A-COPY); 0 is a lower bound of every key;
  the child's own first klong is the empty key or it is a leaf (I1,
  section 4.2). A full node goes through its last version with the empty
  key first (I1).
* **The take-back.** Every klong of tt that names the node, live or
  deleted, is pointed elsewhere (I5, P5's retarget); the node leaves D,
  the record and the table; its id is consumed in order (I8). On the
  record it was never made (A3).
* **Root collapse.** The child satisfies I1 alone and held every live key
  of the root (I2); the child is followed without marking (I7, P1's fault
  2); a root made by the transaction is taken back (I5).
* **A merge.** The new node holds the live klongs of both last versions
  in order under the left bound, the second new node starts with the
  empty key (I1); the right one's compare value is deleted by a bitmap
  that precedes the new klongs; at least B/4 and at most B/2 live klongs,
  or two of more than B/4 (I2); L and R get no entry of tt and are left
  out or taken back (I3, I5); the sibling is read without marking (I7);
  pointers are copied before L and R are left out (A-COPY); the sibling's
  content is the same loaded or canonical (I8).
* **Reclaim's step and cut.** The scan and the touch are readers; the
  rewrites are puts. I6 for a left-out node U: a lookup at an available
  time reaches U only if f <= t < tt, so the cut iteration's touch, at ts
  <= tEnd = f < tt, reached U while it had live keys and it is stored at
  pStart or later or dirty (section 6). So an object stored before pCut
  is dead.
* **The dead hand and the replaced queue.** Evict only detachable,
  written, unpinned objects (I6, I7); a reader that holds one finishes
  with it; one that follows again resolves by id to a version at pCut or
  later, or expires (D1 = A). The records are unchanged, so the model's
  theorems for any eviction schedule apply (T-CACHE, T-READ, T9, T12).
* **The startup rerun.** Each record's deletes rerun by the same rules on
  the same state, the sibling reads included (I8), so the same nodes,
  ids and D; a mismatch fails the start (`DbStarter`), never silently.
* **Lookups.** A lookup at t reads the tree at t (I3), which satisfies I1
  and I2 at t, so R1 holds and a scan of n KVs follows at most about
  (n + 2) H key nodes, each scan, each direction, each available time.

Checked, not proved: A2A3Check2 (with transient nodes counted as not
made), the trace checker (C-A, C-S, C-CUT, C-P, C-H), UnlinkFuzz strict
with gets and scans at every time, P2Fuzz, T6 in every CleanupRule run.


## 14. The risks that remain

* **11.3's points 1 and 2** (P5's "inter" bytes; the bound's overcount):
  blockers for merges in 2026.4.
* **The scan at tStart** (point 3): without a change, T1 at 1M needs a
  drive of 12,000, and P6's queue costs 190,000 loads after a mass delete
  at 100,000. Not wrong, a cost.
* **The dirty top-node window**: bounded, may ratchet; a night run of
  days to watch it.
* **Startup**: the rerun reads the path of each delete (P2's finding 8)
  and now siblings (P5); cold at 50 MB not measured (007).
* **Performance**: no T10 run on any prototype; times on F53 were
  unreliable today. Props MEM 129 to 130 and SS 1.51 on every branch.
* **Not exercised**: the empty space root replaced by a leaf; X5 (c)'s
  fallback (P1, 5); merges of a sibling that is a leaf with klongs to
  segment roots (P5 names it, UnlinkFuzz's long keys reach it).
* **The read path for earlier times** with the replaced queue: lookups
  within R at earlier times reload what the queue evicted; small per
  lookup, not measured.
* **The C port** does not follow until after the release: about 700 lines
  (P4 400, P5 300) plus the eviction schedules; a new pin for `cross.sh`.
* **Test flakiness** on a loaded machine (IndexJobsHarness) can hide or
  fake a failure in the gates.


## 15. What the production work must add

* **Tests for the faults found.** DagTester: LE-b in place, in a full
  parent and across a split (P4's inserted klong); the take-back with a
  deleted klong of tt naming the node (P5's retarget); root collapse of a
  space root and a segment root, made by the transaction or not; a merge
  of a node made by the transaction, as left and as right node; a merge
  whose parent is full; the empty space root replaced by a leaf.
  KeyNodeTester: `firstAndSecond` of an inner node. A test that the
  bitmap precedes the new klong (the trace checker's view, as a unit
  test on the entries' order). UnlinkFuzz strict and its pointer check as
  a `level1.sh` step; the draining A2A3Check2 and trace configurations in
  `level2.sh` and `conformance.sh`; P6's three tests are in.
* **023-03's tests as code**: `CleanupTester` in `before-commit.sh`,
  `cleanup.sh` in `night.sh`, with the measures of section 2 (bytes a
  phase, top nodes in D, scans inside a delete phase) and the allowances
  revised: C6 and C9 with the window named; "sparse" at a constant factor.
* **`dirtyNodeBound`** by node of the paths, checked against counted
  nodes at node sizes 8, 14 and 30 for transactions of 1,000 and 100,000
  deletes; `Db.checkDirtyNodes`'s cheap test with it.
* **Lean alignment** (R24): no change of the model for P4, P5 or P6; the
  Java tier A2A3Check2 counts a transient node as not made (Frans's
  approval); docs/sis-model.md, section 3.4, gets a sentence on transient
  nodes and on the empty key as every inner node's first entry; the 20
  hand-made traces stay; fresh traces from TraceExport in every gate. If
  RB ever comes, the touch step (`touchOf`) changes.
* **The format entry** (018-01, section 2): format 6 = UP, LE-b, X5 (a),
  RC, and MG if in; its refusal message; StreamDigest's new digests;
  `testFound019_32`'s rows found again; `DbTesterJavadoc`'s budget.
* **The C port** (022, after the release): `deleteUpward`, the climb,
  `emptyKeyNext`, the take-back and retarget, `collapseRoot`,
  `firstAndSecond`'s rule, `dropNode`; with merges `merge`, `mergeParent`,
  `sibling`; the dead hand and the replaced queue in C's own memory; then
  `cross.sh full` with a new pin.
* **Docs**: levels.md sections 4 to 7 (the delete's climb, the empty key,
  merges, the dead hand; "an object stays while it is pinned, recently
  used, or the resident bytes are under the budget" changes); README's
  bounds; the release notes: the bounds, the format, the refusal.
* **Clean-up**: the prototypes' static counters and switches
  (`bergdb.p5.*`, `bergdb.p6.*`); `followQuietly` as a follower call; the
  key access path kept through a relabel or merge instead of a descent.


## 16. Open questions for Frans, second pass

Numbered on from section 9.

* **Z12. Merges in 2026.4's format 6, or later?** Later means a format 7
  that refuses 2026.4's databases (11.1) or two rerun paths. Recommended:
  into format 6 if P5's gates pass full and 11.3's points 1 and 2 close
  within days; else 2026.4 with P4 alone and merges in 2026.5 with the
  refusal, as 2026.4 does to 2026.3.
  **Frans, 2026-11-10, 13:42: as recommended.**
* **Z13. The dirty top-node window**: fix (a) in 2026.4 or later? It
  changes what the take writes, not the rerun's rules, so it can come
  later without refusing databases. Recommended: later; now a named
  tolerance in C6 and C9, and a night run to see whether it ratchets.
  **Frans, 13:42: "Z13, solve this now."** The window is fixed in 2026.4.
* **Z14. 023-03's T1 at 1M**: change the drive, or let each reclaim step
  scan at its own time? Recommended: the scan at the step's time, a
  deterministic change of reclaim's rule that also removes P6's loads
  after a mass delete; a probe first (ReclaimStress, RestartInvariance,
  C-CUT); if it is not clean in time, the drive counted from the end of
  the iteration in progress, and the change after the release.
  **Frans, 13:42: yes**: each reclaim step scans at its own time, after a
  probe.
* **Z15. P6's two mechanisms on by default**, `noEvict()` unchanged (P6's
  Q1 to Q3)? Recommended: yes, both; `noEvict()` keeps its contract.
  **Frans, 2026-11-10, 13:57:** (1) the dead hand on by default: agreed;
  (2) the replaced queue on by default only if P8 removes reclaim's reloads
  and a measure of reads at earlier times shows the cost small, else kept
  but off by default: agreed (the coordinator's reading of 13:49, which
  differs from "both on"); (3) `noEvict()`: open; the coordinator looked at
  its use (13:58): a Core-only builder option that sets the budget to
  Long.MAX_VALUE, used by the test setups (`DbBuilder.testSetup`) and the
  benchmark and soak tools (Perf, LoadTest, Soak, ReclaimCost); the Pub API
  has none.
  **Frans, 13:59: agreed** to the coordinator's recommendation: `noEvict()`
  unchanged; its Javadoc says it is for tests and benchmarks, and that
  under it the memory of ended versions is released only at a restart.
* **Z16. P5's sibling rule and cap** (P5's Q1, Q2): the left sibling first
  when both fit in B/2, cap B/2, "sparse" at 1.44 times the twin.
  Recommended: accept the factor for 2026.4; the 3 B/4 cap only after a
  thrash test.
* **Z17. `maintain()`** as P3 built it, without the rebuild (Y10).
  Recommended: yes.
* **Z18. The checker's transient nodes** (P1's Q1, P4's Q3): approve
  A2A3Check2's change.
* **Z19. New expected values** (11.3, point 5): approve each in the
  format entry.
* **Z20. P4's take-back form** (P1's Q2, P4's Q3): the klong of tt pointed
  to the node it replaced, with P5's retarget of every klong of tt.
  Recommended: approve; P2's no-op bitmap is the alternative.


## 17. State of the second pass

2026-11-10, 13:30: sections 11 to 16 added from P1 to P4's final reports,
P5's and P6's drafts (their level2 full and level4 full were running), and
Frans's answers to Y2, Y6, Y7, Y8 and Y10. No code read beyond the first
pass; the prototypes' branches were not opened. When P5's and P6's final
reports come: 11.3's points 1 and 2, P5's gates, and Z12 may change.


## 18. The fix of the dirty top-node window

Written 2026-11-10, 13:50 to 14:00, at Frans's decision to solve Z13 now
(13:42), for prototype P7. From P6's section 5, the code of `TransSeq.take`,
`Db.store`, `DbHelper.handleStillDirtyNodes` and `hasDirtyChild`,
`Handle.serializedRef`, `TopDs.newSuperRoot`, `DbStarter.createMaps` and
`canonicalNode`, sis-model.md 6.1, 6.2 and 8, and `lean/SIS/Algorithm.lean`
with the proofs that name `javaTest`. No code written.

### 18.1 The mechanism, precisely

* **The lists.** At the end of a transaction i, every index node that its
  operations followed, made or changed, and that is not dirty already,
  becomes dirty and goes into the transaction's got-dirty list gd(i)
  (`Db.makeDirtyIfNeeded`, `TransInfo.gotDirtyNodes`); its d(x) is i. D is
  the union of the lists of the startup section, in order
  (`TransSeq`). A record stores its list as (id, position) pairs
  (`StoredTrans.gotDirtyIdsAndSpos`), and a start rebuilds D from them
  (sis-model.md 6.2, step 2; `DbStarter.canonicalNode`).
* **The take** (`TransSeq.take`): whole lists, oldest first, as many as the
  record's share asks and every one before the deadline. The taken nodes'
  pointers are resolved to the latest versions (`resolvePointersOfTakenNodes`),
  the nodes are cleaned, and their versions are written in the record,
  each reference being the pointee's latest written position, or its vpos
  if it has none (`Handle.serializedRef`).
* **Rule A** (`handleStillDirtyNodes`, the model's step 7): a taken node that
  points to a dirty node, through any pointer, is dirty again and is filed
  in the current transaction's list gd(i), the newest; a loop runs this to
  a fixpoint over the record's taken nodes, so a chain of nodes taken in
  one record is cleaned in that record. The test is `javaTest` in the
  model (sis-model.md 6.1, step 7).
* **Top nodes.** A top node holds a root pointer and skip pointers to older
  top nodes (`TopNode.pointers`, by the bits of its ordinal; `newSuperRoot`
  inherits or names the super root). Its content never changes after its
  creation; it is written again only to carry fresh references. Every top
  node but the super root is a replaced node (`topNodeReplaced`), reachable
  only at times before the next root change.
* **The inversion.** T_k is made at transaction i and filed in gd(i). Its
  predecessor T_k-1, filed earlier, is taken at a later transaction j > i
  while T_k-2 is dirty, so Rule A refiles T_k-1 in gd(j): now the newer
  T_k waits in an older list than its predecessor. The take writes T_k
  first, sees T_k-1 dirty, and refiles T_k at the end: a wasted write and a
  wait of a full take cycle (the startup distance's lag). Every top node
  made meanwhile points to its predecessor and is filed in a list older
  than the refiled one: the inversion is passed on at the rate new top
  nodes are made. So the run of dirty top nodes neither grows nor
  shrinks: a window of the length a disturbance left (P6: 157 nodes, 39
  inverted pairs at 1M), and a later disturbance can only lengthen it.
* **The family.** The same holds for any replaced node in D that points to
  current children: nodes a split, an unlink, a merge or a root collapse
  left out (P5's "inter": 248 left-out key nodes kept dirty against P4's
  45, their children being reclaim's internal keys, dirty in most
  transactions). For a *current* node Rule A is right: its version must
  become good for every time up to the startup time, so it must be written
  after its children. For a *replaced* node it is over-strict: the node is
  reachable only at times before its replacement, and a child's version
  written at or after that time serves all of them (lemma M). Rule A asks
  for a clean child where a child written since the replacement suffices.

### 18.2 The fixes

* **(a) Take a written top node's dirty skip targets in the same record**
  (P6's 5.3 (a)). The take removes from D, besides the lists up to s(i),
  every dirty top node that a taken top node points to, recursively, so
  that the fixpoint cleans the chain in one record. It keeps `javaTest`,
  but it changes the model's step 5 (the take), and INV-1 (D is exactly
  the section's lists) no longer holds at a start: a node written ahead of
  its list must be known to be clean, which a start can derive only by a
  new rule (a node of gd(j) with a version in a later record of the
  section and not in that record's list is clean). It covers top nodes
  only, not P5's family, and keeps the first wasted write.
* **(b) Rule A by the replacement time** (P6's 5.3 (b)). The still-dirty
  test, for a replaced node, asks whether a dirty child got dirty before
  the replacement. The test is a different sound test; the model allows
  any sound test (sis-model.md 6.1), and the take, the lists and D are as
  today. It covers the whole family. Its Lean cost is in 18.4.
* **(c) File a re-dirtied node with its child's list.** Rule A files x not
  at d = i but keyed to the dirtiest child's list, d' = max d(y) over the
  dirty children, recorded in gd(i) with the key; the take merges the keys
  into its oldest-first order, so x is written with y and the fixpoint
  cleans them together. This is the generalization sis-model.md, section
  8, suggests ("choices of d with s(i) < d <= i in step 7, recorded in the
  stream; not formalized"). It keeps `javaTest` and the closure the
  physical proofs use, removes the cycle wait and the passing-on of
  inversions, and so dissolves the window; but a replaced node stays
  coupled to its current children for ever (written at every take of a
  child that is dirty then), so it does not cover P5's family, and the
  first wasted write remains.

**Recommended: (b)**, with (c) as the fallback if 18.4's Lean work cannot
be done for 2026.4 and Frans wants the proofs intact (Z21).

**The rule, exactly.** r(x), the replacement time of x: the transaction
time at which x stopped being current, set when x is reported replaced
(`keyNodeReplaced`, a split's node, `toPreviousState`), unlinked or left out
by a merge (P4, P5), collapsed as a root, or superseded as super root
(`topNodeReplaced`); none for a current node. d(y), the time of the list y
is in: set when y is filed (`makeDirtyIfNeeded`, Rule A's refile), the
list's record time after a start. Then, after a taken node x is written in
record i:

    x is dirty again  iff  x points to a node y that is dirty,
                           and (x has no r(x), or d(y) < r(x)).

A taken-back node has no r(x): it is in no list. The loop to a fixpoint
stays as it is. For a current node this is `javaTest`; only replaced nodes
differ.

**Why it is sound** (the test must say dirty whenever the exact test does;
sis-model.md 5.2, 6.1). x's version v, just written, holds every entry of
x (x gets none after r(x)). x is reachable only at times t < r(x). v is
good for such a t iff for each child y of x at t the reference names a
version good for t (5.1). The reference names lv(y), y's latest written
version, or y's vpos if it has none. If y is clean, lv(y) is good for every
t at which y is reachable (INV-2). If y is dirty with d(y) >= r(x), y was
clean just before d(y), so lv(y) is good for every t < d(y) (INV-3), hence
for every t < r(x). If y is dirty with d(y) < r(x), lv(y) may lack y's
entries at times in [d(y), r(x)), or be none (an unwritten y was made before
r(x), so d(y) < r(x)): x must stay dirty, and it does. So every x the exact
test calls dirty, the rule calls dirty.

**Why it dissolves the window.** T_k-1 is replaced at r = tt_k, the next
root change, about 14 overwrites later in T1's drive; its first write comes
a take cycle later, thousands of transactions on. At that write its
predecessor T_k-2 has been written at least once (older list), and if it is
dirty again, by Rule A, its d is the record of that write, far after tt_k:
T_k-1 is clean. The same for its root pointer: the root's refile, if any,
lies after tt_k. So each replaced top node is written once, in list order,
and no inversion is passed on. A top node whose predecessor has never
been written (d < r) stays dirty, rightly: its reference would be a vpos.
In a disturbance where the lag is shorter than a root change's interval,
the rule keeps what it must and nothing more. Expected: D's top nodes at
about the number made in one take's lag of the newest list, for the twin
and the emptied database alike, so T1's C6 and C9 at 1M within the
allowance, and the start's objects with them.

### 18.3 The written references and the cut

* **The invariant.** Every reference in a written version is the position
  of a written version of its pointee, or the pointee's vpos; and no clean
  node names a vpos (an unwritten pointee is in D from its creation,
  INV-4, and keeps its parent dirty: today by Rule A, with the rule because
  d(y) is its creation, before any r(x)). The rule changes nothing about
  what a write names (`serializedRef` is untouched) and writes fewer
  replaced nodes; so the invariant holds as today.
* **Rule R and the startup.** A clean replaced node's latest version may
  now name an older version of a child that is dirty (d(y) >= r(x)). That
  version is good for every time at which the node is reachable (18.2), as
  a clean current node's references are today. Rule R still redirects any
  reference to a version in the section to the newest there (lemma M: a
  newer version serves every time an older one serves), so the lazy start
  reads P at every time from the startup time on as before; L-OUT's
  argument ("got dirty after s") is unchanged, and L-SEC's by level.
* **The cut** (Reclaim's class comment; pEnd, pSafe). The argument needs:
  every node reachable at times from tEnd on is at pStart or later or
  dirty, and after pSafe no such node names a position below pCut for a
  child in the range. With the rule, a replaced node x (touched at ts <=
  tEnd, replaced at r(x) > ts) that is clean after a write names, for each
  child y of the range: lv(y) written after y's touch-dirtying (y clean,
  or dirty again with d(y) >= r(x) > ts, so written after the touch), at
  pStart or later; or x stays dirty (d(y) < r(x)). So pEnd and pSafe keep
  their meaning and need no change; the wait for pSafe covers fewer nodes.
  Top nodes are not touched; P6's 1.1 argument for them does not use Rule
  A and stands.

### 18.4 What the rerun, the id check, Rule R and the Lean model see

* **Record contents, within format 6.** The got-dirty list gains r(x): each
  entry (id, position) becomes (id, position, r), r = 0 for a current node;
  8 bytes an entry, 24 instead of 16 (`store()`'s `fixedBytes`,
  `TransSeq.recordBytes`, `StoredTrans`'s serializer and parser). Needed
  because a node in D can have been replaced before the startup section
  (re-listed by Rule A in the section) and nothing in the section says so.
  No other record change; the rerun's rules are untouched, so the format
  byte stays 6 and no further refusal follows.
* **The startup rerun.** D is rebuilt from the lists as today, each node
  with its d (the list's record) and its r from the entry. The rerun
  reproduces the section's replacements (`keyNodeReplaced` and the others
  during `rerunTransaction`), which set r on the same nodes: where both
  exist they must agree, a check like the node-id check ("startup error"),
  which RestartInvariance exercises after every transaction. The node-id
  check is unchanged: the rule makes no node.
* **Rule R**: unchanged (18.3). `linkD`, rule 4 by position: unchanged.
* **Determinism (P2, INV-RESTART).** The rule's inputs, r(x) and d(y), are
  in the stream (the entry; the list's record), so a run with restarts
  writes the same records: RestartInvariance and StreamDigest's four modes
  check it. The digests change (the entries are longer), as format 6
  changes them anyway.
* **The Lean model.** The algorithm's step 7 is a parameter
  (`Algo.stillDirty`, `stillDirtyOf`, lean/SIS/Algorithm.lean:80, 177) and the
  logical theorems hold for any sound test. But the physical layer's
  theorems, cuts, the lazy start and eviction with handles, take the
  hypothesis `al.stillDirty = javaTest sp` (`lean/SIS/Proof/CutHist.lean`,
  `CutLazyStart.lean`, `EvLogic.lean`, `CutRestart.lean`: `step_dClosed`,
  `step_closed`, `topsD` and their users), that is, they use the closure
  "no clean node points to a dirty node", which the rule gives up for
  replaced nodes. So (b) needs: in `lean/Check`, the new test beside
  `javaTest` (`Steps.lean`'s `java7`), with r derived by the checker from
  reachability or read from the trace, else C-S fails "model only" as it
  did for P3; and in `lean/SIS/Proof`, the physical theorems proved for the
  new test, with the weaker closure "a clean node points to a dirty node
  only if it is replaced and the pointee got dirty at or after its
  replacement", by the argument of 18.2 and 18.3. A proof task of its own,
  effort xhigh, size unknown (those files are long); the checker's change
  is small. Until the proofs are done, R24 holds by the checker and the
  gates, not by the theorems: Frans's call (Z21). (c) would keep
  `javaTest` and touch instead step 7's d, INV-1 and the take's order, the
  model's own suggested generalization, also unproved.
* **The trace format**: unchanged if the checker derives r; one field per
  got-dirty entry if it reads it, which also gives a new check, the
  stored r against the model's reachability.

### 18.5 Coverage: P5's left-out nodes and the rest of the family

Yes. The rule is stated for every replaced node, and P5's case is its
clearest instance: L and R left out by a merge at tt, in D from an earlier
dirtying, pointing to the current children that the merged node now holds;
those children are reclaim's internal keys' nodes, dirty in most
transactions, with d far after tt once each has been written once after
the merge, so L and R are clean after their first write. The same for the
nodes UP leaves out, a split's replaced node, a collapsed root, P3's
replaced nodes if RB ever comes (its 5.3), and every top node but the
super root. P6's replaced queue then evicts them as soon as they are
written, which closes the loop for memory. Not in the family: current
nodes kept dirty by Rule A, rightly, and taken-back nodes, which are in no
list.

### 18.6 How to test it

1. **The failing test** (P7's): T1 at 1M with a drive of 12,000, D in the
   window (M8) and the objects after a restart (M11) against the twin's,
   C6 and C9 with the bounded allowance; and the twin's own D, which the
   rule should bring down too (its 10 to 11 inverted pairs).
2. **A unit test of the rule** in `DbHelper`: a replaced node with a dirty
   child filed at or after r stays clean; filed before r stays dirty; a
   current node with any dirty child stays dirty; a chain cleaned in one
   record by the fixpoint; a top node with a dirty skip target.
3. **A ratchet test**, in `cleanup.sh` or `night.sh`: T4's queue for 1M
   transactions with a mass delete every 200,000, a restart after each,
   and a reclaim iteration spanning each; D's top nodes at every
   checkpoint within the twin's steady value, before and after each
   disturbance.
4. **Determinism and the start**: RestartInvariance (a restart after every
   transaction, the stream byte for byte, the stored r against the
   rerun's), StreamDigest's four modes, CrashTest; the record limit's
   accounting with 24-byte entries (`DbTester.testRecordsWithinLimit`).
5. **The cut and readers**: ReclaimStress, ReclaimReaders, LoadTest
   (`level3.sh`), and EvictionInvariance with the audit (INV-SLOT,
   INV-CAN) under `level4.sh`, with P6's replaced queue on.
6. **The checker**: `level2.sh`, `level3.sh` and `level4.sh`'s conformance
   with the checker's new test; C-S must pass with no "model only" node;
   C-CUT at every cut.
7. **The measures**: bytes written a phase and top nodes written per top
   node made, before and after, in T1 and T4; the twin's D at 100,000 and
   1M (section 2's measure of top nodes in D).

**Z21, for Frans.** (b) changes the still-dirty test that the Lean
physical-layer theorems assume (`javaTest`). Ship (b) in 2026.4 with the
checker aligned and the theorems re-proved as a parallel Lean task, or
take (c), which keeps `javaTest` and fixes the window but not P5's family,
or defer? Recommended: (b), with the Lean task started at once and the
release's R24 stated as "checked by the trace checker; the physical
theorems for the new test in progress" if the proofs are not done in time.
