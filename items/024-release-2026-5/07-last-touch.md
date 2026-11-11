# 024-07. The last touch of a reclaim iteration (CL7, OP1)

Created 2026-11-11. Status: open (the fix is built, gated and merged
into 024-13's integration branch, not yet on `main`; section 13 has the
exact state).

The largest measured fault against aim 2 of release 2026.5 (024-04: no
Core operation costs out of proportion to its work): with keys in time
order, the last step of a reclaim iteration writes one record of 191 to
206 MB at 10M keys and makes a commit of about 21 s (024-03, section 7;
024-05, OP1). This subitem: the mechanism, the bound, the options, the
argument for the cut in the Lean model, the fix built, the numbers before
and after.

Cite the bounds as "024-07, B1", the options as "024-07, option A".


## 1. In short

* **It is a case of aim 1 too (bugs first), not only of aim 2.** At about
  100M keys in time order the index nodes of the last step no longer fit
  in a record (2^31 - 9 bytes). `TransSeq.take` never takes a transaction
  whose nodes do not fit, so the startup pos stops before that step for
  good: no cut is ever made again, the stream, the startup section and
  the pinned nodes grow without end, and nothing throws. Read from the
  code and reproduced with the record limit lowered (section 3; the test
  `testLastStepWithinRecordLimit` fails on `main`). Before that size the
  step pins every index node at once and loads every value (0.67 to
  2.31 GB resident at 10M keys, with a budget of 0.2 GB): with a heap of
  256 MB a queue of 1M keys ends in an `OutOfMemoryError` inside a
  user's commit on `main`, and runs with the fix.
* **The mechanism.** A step scans 16 kB of KVs as they were at tStart,
  but its touch (`Db.touchRange`) walks the same key range as it is now,
  and the last step's touch has no end key. Every key put after the
  scan's last key since the iteration began is in that walk. With keys in
  time order that is the whole tree: 772,454 index nodes made dirty by
  one step at 10M keys (counted, section 2).
* **The touch was for nodes that no longer exist.** It was added on
  2026-10-13 for the nodes that held deleted keys only. Since format 6 a
  delete unlinks the nodes it empties, so every index node has a live key
  below it, and the put of that key makes the node dirty: the user's put,
  or the step's rewrite.
* **Model first: that argument is now two Lean theorems** (section 4).
  T-COVER (`T_cover`): if every data node reachable at the iteration's
  end is at the cut or later, and every index node has a data node below
  it, then every index node is in D or at the cut or later. T-LATEST
  (`T_latest`): then, once the startup pos has reached the iteration's
  end, every node reachable from the end on has its latest version at
  the cut or later. Proved from the model's existing invariants, standard
  axioms only. The model has no keys: the two premises are Java's, and
  section 4.4 says how each is checked. The rest of T-SCHEME (the
  versions that pointers lead to, D's references) stays checked by
  running, as before: now also on runs without any touch.
* **Built, option A: a step makes dirty the index nodes on the paths of
  its own puts only.** `Db.touchPaths` in place of `Db.touchRange`; the
  record format is the same, the bytes written change. A step's cost now
  follows its 16 kB of scan, not the database (bounds B1 to B4, section
  5; the bound is a property in the model and a check in the trace
  checker, `touchPath`).
* **At 10M keys in time order, before and after** (section 8): the last
  step makes 5 to 15 index nodes dirty, not 772,454; the largest record
  is 29 kB, not 206 MB; the slowest commit 78 ms, not 22.3 s; 9.7 % fewer
  bytes a transaction, and the run takes 167 s, not 223 s. Iterations and
  cuts as before.
* **For Frans:** section 11. The main one: the cut's safety now rests on
  the delete's upward unlink (no index node without a live key below it).


## 2. What the last touch does

### 2.1 The code

* **A step** (`Reclaim.step`) scans the KVs at time tStart after the
  iteration's `lastKey`, at most 16 kB of them by the scan's measure
  (`MAX_STEP_SIZE`; a KV counts 8 bytes a key segment, its value and
  100), with maintenance reads; it puts again each live value stored
  before pCut, and its row. On `main` it then sets
  `t.touch = true; t.touchFrom = it.lastKey;`
  `t.touchTo = eod[0] ? null : lastKeyOfStep[0]`.
* **The touch** runs in `Db.putKvs`, before the puts:
  `Db.touchRange(from, to)` is a `GetMany` at the step's own time over
  the keys after `from` up to `to`, with the writer's pointer listener,
  so every index node it follows is marked (`markAtEndOfOp`) and made
  dirty (`endOfOp(true)`, `makeDirtyIfNeeded`), changed or not.
* **Two times.** The scan reads the keys of tStart; the touch walks the
  tree of now. The scan is bounded (16 kB, and the step's reserve, 4 MiB
  of index nodes followed). The touch is not: its range holds the keys
  of tStart that are still live and every key put into the range since.
  In the last step (`eod`) `touchTo` is null: the range is everything
  after E, the scan's last key.
* **What follows from a dirty node.** It is pinned in memory until it is
  written. `TransSeq.take` takes a transaction's dirty nodes whole, when
  the startup pos reaches it, a startup distance later: all in one
  record, written by whatever commit comes then.

### 2.2 Why it grows with the database

With keys in time order every new key is after E. An iteration is long
(a step is allowed while reclaim's charge is below a quarter of the
stream's growth): at 10M keys 133,334 steps in about 133,000
transactions, in which the queue put 13.3M keys. So the last touch
walks the whole current tree, and the tree grows with the keys: 0.077
index nodes and 20.6 bytes of record a live key.

Counted on `main` (release 2026.4's code; the probe T7, 024-03's FIFO:
100 puts at the tail and 100 deletes at the head a transaction, 13-byte
keys, values of 100 bytes). "sd" is the startup distance.

| Live keys  | sd    | Nodes dirty, last step | Largest record | Step's commit  |
|---|---|---|---|---|
| 50,000     | 1 MB  | 3,631                  | 0.99 MB        | -              |
| 100,000    | 1 MB  | 7,559                  | 2.06 MB        | 9 ms           |
| 200,000    | 1 MB  | 15,459                 | 4.17 MB        | 46 to 49 ms    |
| 400,000    | 1 MB  | 31,230                 | 8.36 MB        | 188 to 193 ms  |
| 1,000,000  | 50 MB | 61,693                 | 16.7 MB        | 1.58 to 1.65 s |
| 10,000,000 | 50 MB | 772,454                | 206.1 MB       | 20.6, 22.3 s   |

* **At 100,000 keys with the default 50 MB it does not show**: the whole
  tree is 2 MB and already dirty, so a touch makes 1 or 2 nodes dirty
  (the touches of an iteration still visit 17,200). A small startup
  distance shows it at a small size; so does the unit test of section 7.
* **Four costs of the one step at 10M keys** (the second iteration of
  the run; the first: 716,523 nodes):
  1. its commit: 22.3 s (20.6 s; in the first run, partly disturbed,
     24.4 and 21.7 s), under the write lock: every writer waits. It is
     the walk, a scan through the writer's follower, which loads the
     index nodes that the cache of 200 MB does not hold and follows the
     pointer to every value in the range too (`GetMany.Chain.next`,
     `NodeCollection.followValuePointer`): 10M values;
  2. memory: the 772,454 nodes are pinned until they are written. The
     resident count right after the step was 2.31 GB in one run and 0.67
     GB in the other, with a budget of 0.2 GB: the values that the walk
     loaded can be released, the nodes cannot;
  3. the step's own record: 12.4 MB, its got-dirty list of 16 bytes a
     node;
  4. 83 transactions later (50 MB later) a user commit takes them all:
     the record of 206,065,600 bytes, and that commit takes 2.6 s.
* **All of it for nothing here.** The second iteration scanned
  10,000,003 KVs and found no value to rewrite (`values=0`): every live
  key was put after pCut. `Reclaim.TouchCounter` at 50,000 to 400,000
  keys: of the nodes the touches made dirty, 0 were stored before pCut
  (`old=0`, `minimal=0`).
* **Not only the last step.** Any step's range can hold any number of
  keys put since tStart, for example a prefix that grows between two old
  keys. Not measured here; the mechanism and the fix are the same.

Outputs: `07-last-touch/out/` (`count-main/` for 50,000 keys and the
touch counter; `small-main-sd1m-r2/`, `small-main-r2/`,
`fifo-10000000-main-r2/` and, for the first run, the same names without
`-r2`); the probe and the runners in `07-last-touch/` (section 12).


## 3. At the record limit: a fault today

024-05 (OP1 and section 5) asked what the step does when its nodes reach
the record limit. Read from the code, and reproduced small.

* **Nothing checks a step.** `Db.checkDirtyNodes` refuses a user
  transaction whose index nodes could not be written in one record,
  before it changes anything (005-31). It is not called for internal
  transactions: its Javadoc says a step is "bounded by their own
  reserve". The reserve bounds the nodes the scan follows at tStart. The
  touch has no bound.
* **The take never takes what does not fit.** `TransSeq.take`: "The
  first transaction that does not fit is not taken, also after the
  deadline." The most the taken nodes may add is `recordLimit` less the
  record's own bytes (`Db.store`).
* **So, at the size where the last step's nodes pass 2^31 - 9 bytes:**
  the startup pos stays before that step for good. Then:
  * no iteration gets safe (`markSafePositions` waits for the startup
    pos to pass pEnd), so no cut is ever made again: the stream grows
    without end;
  * the startup section grows without end: every start reruns it;
  * every node made dirty from then on stays pinned: the heap grows;
  * nothing throws. The database answers right until memory or the disk
    ends.
* **The size.** A node of this shape costs 242 bytes and 16 for its
  entry in the got-dirty list; 0.0772 nodes a key; 20.6 bytes a key
  (206,065,600 bytes at 10M). 2^31 / 20.6 is 104M keys in time order,
  for keys of 13 bytes at the default node size. Fewer with longer keys.
* **Reproduced with the limit lowered**, as `StoredTrans`'s own test
  lowers it: record limit 100 kB, a queue of 6,000 keys, node size 8,
  startup distance 2 kB (`Reclaim.Tester.testLastStepWithinRecordLimit`).
  On `main`: 100 transactions after the first iteration ended the
  startup pos is 260,048 bytes behind; after 1,000 it is 2,261,304
  behind, four iterations are done, the stream is 9.2 MB, and nothing
  is cut. With the fix it passes the step within 100 transactions.
* **Before that size, the heap: the database fails.** The step pins its
  nodes at once and loads the range's values: 0.67 to 2.31 GB resident
  at 10M keys (two runs, heap 8 GB), 67 to 231 bytes a live key. Shown
  small (`counts.sh`, 10:13 to 10:15): the queue of 1M keys with a heap
  of 256 MB (startup distance 5 MB, the default cache budget of 200 MB).
  On `main` the first iteration's last step ends in
  `java.lang.OutOfMemoryError: Java heap space`, in `Db.touchRange`
  under `Reclaim.step` under the user's `Db.execute`: inside the go
  point, so the database has failed. The iteration's row is stored, so
  after a restart the same last step runs at the first commit that
  allows a step. With the fix the same run does its 40,000
  transactions, three iterations, the slowest commit 37 ms
  (`out/counts-main/heap-fifo.txt`, `out/counts-fix/heap-fifo.txt`).
  With an 8 GB heap, by the two readings above, that is somewhere
  between 35M and 120M keys in time order: an estimate, not run.

So OP1 is an aim 1 case (bugs first): from some tens of millions of
keys in time order with a heap of 8 GB, sooner with a smaller heap, and
the 21 s commit at 10M is its mild form.


## 4. What the cut needs, and the argument in the model

Frans's order of 2026-11-11 (model first): whether the option keeps the
cut correct is settled against the Lean model's cut conditions before
the fix counts as done.

### 4.1 What `CutOK` asks of the index nodes

`CutOK sp c db k` (lean/SIS/Reclaim.lean), with f the first available
time: (1) c <= f; (2) every version that a read at a time from f on may
follow (`ReadsPhys`) is at c or later; (3) every node of D has its
latest version at c or later, with references below c to latest
versions only; (4) the top is at c or later. For Java, c is the
iteration's pCut and f its tEnd (001-07, section 2.5).

001-07, section 5, argues in ten steps that Java's scheme gives it
(T-SCHEME: checked at every cut, not proved). Only step 3 is about the
touch: "Every index node that is current at the time of the step whose
range meets its key range is in that step's touch". Its conclusion, with
step 5 (a marked node is written once the startup pos passes its mark):
every index node reachable at tEnd is in D at tEnd, or has its latest
version after pStart. The steps after it use only "at pCut or later"
(001-07, "Why not proved": "every node reachable at some time from tEnd
on has its latest version at pCut or later").

So what the cut needs of an iteration's index nodes is **COVER**: every
index node reachable at tEnd is in D then, or has its latest version at
pCut or later. A touch is one way to get it.

### 4.2 T-COVER and T-LATEST, proved

Both are stated in lean/SIS/ReclaimTheorems.lean and proved in
lean/SIS/Proof/CutCover.lean (229 lines; `#print axioms` for both:
propext, Classical.choice, Quot.sound).

**T-COVER**, `T_cover`. In the state after transaction e of a run that
meets the model's assumptions (`RunOK`), for any c:

* **REWRITES**: every data node reachable at e has its version at c or
  later; and
* **LIVEBELOW**: every written index node reachable at e has a data
  node below it at e (in `reachFrom`: through live pointers);

then **COVER**: every written index node reachable at e is in D, or
has its latest version at c or later.

Why it holds, in the model's own terms:

* A node that is not in D is clean: its latest version is good for e
  (`Inv.clean_good`, INV-2).
* A good version's reference for each live child leads to a good
  version of the child (`good`, lean/SIS/Stream.lean), and a reference
  names a record at or before the version's own (`Inv.ref_le_recNo`).
  So a good version leads down, each record at or before the one above,
  to a version of every node below it (`Inv.good_below`).
* A data node has one version (`DataOnce`). So a clean node's latest
  version is at or after the version of every data node below it
  (`Inv.clean_ge_data`). With a data node at c or later below it, the
  node is at c or later.

No touch is in the statement. The marking that Java's puts do is in
`RunOK` and the invariant already: the model need not be told that "a
put marks its path".

**T-LATEST**, `T_latest` (`latest_st` in the same file): with the two
premises at e, c <= e, and a state after T(k), e <= k, whose startup pos
is at e or later (Java's first wait, `startupPos >= row.pEnd`): every
node reachable at a time from e to k has its latest version, if it has
one, at c or later.

* A node made after T(e) has its versions after e.
* A node that existed then was reachable at e (no resurrection,
  `reach_back_st`). A data node is at c or later by REWRITES. An index
  node is at c or later then, and so later too, or it was in D
  (T-COVER), with a got-dirty index at most e; a node of D stays in D
  with that index until it is written (`D_later`), and the indexes of D
  are after the startup pos (`sectionD_mem`): so it was written after e.

This is steps 1, 3 and 5 of 001-07, section 5, proved for the latest
versions: `CutOK`'s part 2 for `ReadsPhys.latest` (and so what part 4
asks of the top), and the first half of its part 3 for the nodes of D
that a read from f on reaches. Not in it: the versions that a pointer
leads to besides the latest ones (`ReadsPhys.child`: Rule R, superseded
versions), the references of D's nodes, and the nodes of D that no read
from f on reaches (steps 6 and 7; the wait for pSafe). Those are
001-07's "why not proved", unchanged by this subitem.

### 4.3 T-SCHEME with COVER, by running

T-SCHEME stays "checked by running, not proved", as before. Its check
in the model (`checkSchemeB`, example 4) had the touch's condition,
`touchCoverB`: the touches cover every index node whose latest version
is at pStart or before. The new check, `checkSchemeC`
(lean/SIS/ReclaimExample.lean), has COVER in its place (`coverB`), which
is weaker, and counts LIVEBELOW (`liveBelowB`). It runs on example 4 and
on example 4 **without any touch** (`spec4n`). `lake exe reclaimtest 20
30` (20 seeds of 30 transactions, four startup pos policies; all checks
pass, 65 s):

| Example 4         | LIVEBELOW | No COVER | COVER, REWRITES | Touch-covered | CutOK fails |
|---|---|---|---|---|---|
| with the touch    | 66        | 0        | 76              | 76            | 0 of 2,356  |
| without any touch | 66        | 0        | 70              | 1 to 6        | 0 of 2,049  |

(Iterations a policy: with LIVEBELOW and REWRITES; of them without
COVER; with COVER and REWRITES, the scheme's conditions; of them with
the touch's condition too. The states are the sum of the four policies.)

* Without any touch, 70 iterations a policy meet the scheme's
  conditions, and `CutOK` holds in every state past the waits, though
  the touch's condition holds for only 1 to 6 of them.
* Every iteration with REWRITES and LIVEBELOW has COVER: T-COVER, seen
  by running.
* **The witness for LIVEBELOW** (`#guard`s): in the fixed run key 3 has
  no value, so its leaf has no data node below it. Without the touch the
  rewrites hold and COVER fails: the leaf keeps its version of R(0),
  below the cut. With a value for every key (`ts4v`) the same run is
  covered without any touch. That leaf is the model's form of the node
  that held deleted keys only, which the touch was made for.

### 4.4 The two premises in Java, and what the model cannot express

The model has no keys, no scan and no delete rule. So it cannot derive
either premise; each is Java's.

* **REWRITES** is 001-07, section 5, step 2, unchanged: a key live at a
  time from tEnd on was put after pStart, or was live at tStart with no
  put since, so the scan at tStart found it and the step put it again
  if its value was stored before pCut (`gd.tpos < it.pCut`). Checked:
  C-CUT at every cut of every trace (part 2 for the data nodes),
  `testIterationRewritesAllOldValues`, every `CutStream` test.
* **LIVEBELOW** is the delete path's invariant I2 (023-07, section 5.1):
  no reachable node without a live key below it. `Dag.deleteUpward`
  keeps it: a delete that empties a leaf unlinks every node it empties,
  up to the first that keeps a live klong, across segment trees, in the
  deleting transaction. Format 6 means it, and a start refuses format 5,
  so every database a start accepts was built under it. Its exceptions:
  * an empty space root (a segment leaf) stays. With reclaim on the
    table and the row are live keys, and the root is on the path of
    every step's row;
  * a node the transaction made, not by a split, and then empties
    (023-04, X5 (c)): since 2026-11-10 a `Bug` is thrown before anything
    changes.
  Checked: UnlinkFuzz checks I2 after every transaction ("every key node
  reachable then has a live klong, but the space root"); it is in no
  gate (024-06, section 4.4, point 3). New here: the trace checker
  checks LIVEBELOW itself at every cut of every reclaim trace, at the
  cut's first available time (C-CUT, `CUT-live`): the premise is no
  longer only argued for the traced runs. And
  `testEmptiedSubtreesAfterCut` (section 7).
* **Top nodes.** In the model they are the root's children, index nodes
  with the tree below them: T-COVER covers them. In Java every step's
  row put follows the super root (`superRootAccessed`), as the touch
  did; step 4 of 001-07, section 5, is unchanged.
* **Key ranges are gone from the argument.** 024-06, section 4.4, point
  2 (its piece A3): step 3 rested on "a key range only shrinks", false
  since 2026.4. T-COVER has no ranges: for the index nodes A3's question
  no longer arises. Steps 1, 2 and 4 to 10 are as they were.

What the tree's model (024-12) can add: I2 as a stated property of the
tree's `exec` (then LIVEBELOW is a theorem about the tree, not a premise),
and the scan, which would make REWRITES one too. For 024-12: the
touch is now the paths of the transaction's keys (`Db.touchPaths`,
`Dag.followPath`), so `touchOf` needs no key range and the trace no
RANGE line.

024-09 (the tie repaired, by "tie"), read at 09:59: its A3, T-SCHEME's
argument written again for 2026.4's code, is not written yet and names
this section as what it will read; nothing there to build on or to
answer. Its A1, done on its branch, is what LIVEBELOW needs in the
gates: a conformance set `drain` (in `level2.sh`, with a `r-drain`
configuration in the reclaim set) and UnlinkFuzz in `night.sh`. With
this branch's `CUT-live` in the checker, those draining traces check
the premise at their cuts.


## 5. The bound

For one reclaim step, whatever the database holds. h is the height of a
segment tree, s the segments of a key.

* **B1, nodes.** A step makes dirty only index nodes that a user
  transaction of the step's puts would reach: the nodes on the paths of
  the values it rewrites and of its row, and the nodes those puts
  create. At most 3 h s + 3 a put (`Db.checkDirtyNodes`'s count), and a
  step puts at most the KVs of its scan and its row: 16 kB of KVs by the
  scan's measure, or one KV if it is larger. In the model:
  `TouchOnPaths` (lean/SIS/ReclaimTheorems.lean): every touched node has
  below it, itself included, a node that the change gives an entry or
  replaces.
* **B2, bytes.** The step's record: its value nodes (within 7/8 of the
  record limit, 015-50), its row, 16 bytes a dirty node. The index bytes
  a later record writes for it: B1's nodes. So a step adds to no record
  more than its own paths, and 024-05's BD1 holds for the record that
  takes it (no record over the larger of 1 MB and 5 times its run's
  mean).
* **B3, time.** The step's commit does the scan's reads and the puts:
  no node outside its keys' paths is followed by the writer.
* **B4, heap.** A step pins B1's nodes, no more.

How each is checked:

* B1 in Java: `Reclaim.Tester.testStepDirtiesItsPathsOnly`, at most 63
  nodes a put at 2,000 and at 8,000 keys; it fails on `main` (991 and
  4,180 nodes for a step with 1 put).
* B1 on traces: the trace checker's C-A has `touchPath` since this
  subitem: for every step of every reclaim trace, every touched node is
  on a path of the step's change. A touch of a key range fails it: on
  one trace of `level3.sh`'s set (`r-del`, seed 1) `main`'s algorithm
  fails it in 18 of its 19 steps, the fix in 0 of 20, with C-S and C-CUT
  (12 cuts) passing (`out/touchpath/`).
* B2 and the record limit: `testLastStepWithinRecordLimit`.
* B2 to B4 at 10M keys: section 8.

On 024-05's BD1 and BD7: BD1 is taken as it is. BD7 ("the nodes it makes
dirty at most a constant times the paths of the KVs it rewrites") is B1
with the constant 3 a node of the path, and the row counted as a put.


## 6. The options

| Option | The touch of a step                          | Meets B1 to B4       |
|---|---|---|
| A      | the paths of its own puts                    | yes                  |
| B      | its key range, the last one ended at E       | no: a range can grow |
| C      | its key range, only nodes stored before pCut | bytes yes, time no   |
| D      | its key range, the tail in further steps     | no: may never end    |

* **A, the rewrite paths** (review A's prototype of 023-08, section 4.2).
  * Mechanism: before its puts the step's transaction follows the path
    of each of its keys with the writer's listener (`Db.touchPaths`,
    `Dag.followPath`), and no key range.
  * The cut: T-COVER, with LIVEBELOW as the premise that the touch made
    unnecessary to assume. C-CUT in `level3.sh` checks every cut.
  * `dirtyNodeBound` and the record limit: a step is now within the
    count that `Db.checkDirtyNodes` makes for a user transaction of the
    same puts, so the Javadoc's "bounded" is true.
  * Startup and the rerun: unchanged. The touch is not stored and not
    rerun; D comes from the stored got-dirty ids.
  * Bytes and format: the bytes change (fewer nodes written); the
    record format does not.
* **B, end the last touch at E.** One line (`touchTo` never null). The
  tail is no longer walked, so 024-03's FIFO is fixed. But a step's own
  range still holds every key put into it since tStart, so B1 is not
  met; and the nodes after E are covered by the same premise as in A
  (their live keys were put after tStart). It takes A's premise and
  keeps the unbounded walk.
* **C, touch only old nodes** (`TouchCounter`'s "minimal" set: nodes
  stored before pCut and their ancestors). The record shrinks to what
  the cut needs, with no new premise. But finding the old nodes means
  visiting every node of the range, and at 10M keys the visit is the 21
  s. A parent's pointer tells where a child was last written, not its
  grandchildren, so no subtree can be skipped.
* **D, walk the tail in bounded steps.** The tail can grow faster than
  the steps walk it (100 keys a transaction against 75 a step in
  024-03's FIFO): the iteration may never end, the fault of P8 (023-08,
  fault 13).

**Recommended and built: A.** It is the smallest, it removes code, and
it is the only one that meets the bound. Its price is the premise
LIVEBELOW: section 11, question 1.

Beside these: 024-11's options RB and CT (a rebuild, or compaction, by
reclaim's touch) make the touch of a key range a writer; its
recommendation, MG, does not. With option A there is no walk to extend.
If RB or CT were chosen, a walk would come back, and its bound would
have to be the keys of the step's scan, not the range as it is at the
step's time: this subitem's mechanism.

Judgement of review A's prototype (`a-evidence/path-mark.diff`, on P8's
tree): right in its idea and its evidence (27 nodes against 81,018; 15
cuts with C-CUT). Two differences here: it used `Dag.getOne`, which
also follows the pointer to each key's value and so reads the value a
second time through the writer's follower; `Dag.followPath` stops at the
segment leaf. And it left "the physical-reference argument" open: that
is section 4.


## 7. What was built

Branch `024-07-last-touch` in the clone
`/Users/f/fl/bench/2026-11-11/touch/clone` (section 13 has the head).

Java:

* `Dag.followPath(time, key, gd)`: follows the index nodes on a key's
  path, as `putKv` and `getOne` do, not the pointer to its value.
* `Db.touchPaths()` in place of `Db.touchRange(from, to)`: for each key
  of the step's transaction, `followPath` at the transaction's time with
  the writer's listener, before the puts. The marks stay as before (a
  touched node that the puts replace stays in D, the model's `touchOf`),
  and the row still stores what the step made dirty.
* `Trans.touchFrom` and `touchTo` are gone; `Reclaim.step` sets
  `t.touch = true` only. The step's scan, rewrites, row, waits and cut
  are untouched.
* Tests in `Reclaim.Tester`: `testStepDirtiesItsPathsOnly` (B1; fails
  on `main`), `testLastStepWithinRecordLimit` (section 3; fails on
  `main`), `testEmptiedSubtreesAfterCut` (LIVEBELOW seen through cuts:
  600 short and 300 long keys, whole subtrees and segment trees emptied,
  three cuts on a `CutStream`, every key and a scan at the first
  available time, between and at the latest, in the running database
  and after a restart; it passes on `main` too).
* Comments in `Reclaim`, `Db`, `Trans`, `DbStarter`.

Lean:

* `SIS/Proof/CutCover.lean` (new) and `T_cover`, `T_latest`,
  `TouchOnPaths` in `SIS/ReclaimTheorems.lean`.
* `SIS/ReclaimExample.lean`: `coverB`, `liveBelowB`, `checkSchemeC`,
  `ts4v`, five `#guard`s; `ReclaimTest.lean` prints and checks them.
* The trace checker: `touchPath` in `Check/Steps.lean`'s
  `touchFailures` (C-A: the bound), and `CUT-live`
  (`liveBelowFailures`, C-CUT: LIVEBELOW at every cut);
  `test-traces/run.sh` expects them for `touch.trace` and `cut.trace`.
* No definition, statement or proof of the model that existed is
  changed (a comment of `T13_markTouch` is; the checker's
  `touchFailures` takes one more argument).

Documents in the branch: docs/levels.md (section 6), docs/sis-model.md
(15.3), docs/trace-format.md (TOUCH), lean/README.md.

Not built, on purpose: no setting, no switch between the two touches,
no change of the record format.


## 8. Numbers before and after

024-03's method (its section 7): a fill of N keys in key order, then the
FIFO, 100 puts after every key so far and 100 deletes of the oldest a
transaction; keys of 13 bytes, values of 100; a `FileStream`, the
builder's defaults (startup distance 50 MB, cache 200 MB), a test clock,
a retain duration of 1 s; G1, 8 GB heap, no -ea. "main" is the clone at
`main`'s head (release 2026.4's code), "fix" the branch. The probe T7
has `Reclaim.Stats` on in both, its touch counter off.

Counts (nodes, bytes, records) are exact and repeat, and they are the
evidence for the bound. Times are one run on a machine that other
agents used: the 1-minute load was 3.0 to 3.6 at the starts of the 10M
runs below and 3.3 to 3.5 at their ends, the fix's and `main`'s,
minutes apart; 4 to 12 at the small ones. `main` was run twice; the
tables have the second run, and its first run agrees in every count.

**10M keys, the FIFO, 200,000 transactions:**

| Measure                               | main                 | fix               |
|---|---|---|
| nodes dirty, last step, 2 iterations  | 716,523 and 772,454  | 15 and 5          |
| index nodes dirty, iteration 2, all   | 808,834, 213.8 MB    | 9,579, 0.63 MB    |
| largest record                        | 206,065,600 bytes    | 29,112 bytes      |
| records over 1 MB                     | 2                    | 0                 |
| largest record of a step              | 12,367,488 bytes     | 18,200 bytes      |
| the last step's commit                | 20.6 and 22.3 s      | 1.1 and 0.9 ms    |
| the commit of the largest record      | 2.6 s                | 0.9 ms            |
| slowest commit                        | 22,306 ms            | 78 ms             |
| commit p50, p99.9                     | 754 µs, 3.0 ms       | 754 µs, 2.9 ms    |
| resident after the last step          | 0.67 GB (2.31 run 1) | 0.20 GB           |
| bytes written a transaction           | 24,865               | 22,454            |
| the 200,000 transactions              | 223 s                | 167 s             |
| stream written                        | 5.12 GB              | 4.63 GB           |
| kept at the end                       | 6.43 GB              | 5.85 GB           |
| iterations, steps of the second       | 2; 133,334           | 2; 133,334        |

**10M keys, the fill in key order, 100,000 transactions:**

| Measure                       | main              | fix             |
|---|---|---|
| nodes dirty, last step        | 111,384; 214,354  | 15; 5           |
| largest record                | 29,724,912 bytes  | 23,328 bytes    |
| largest record of a step      | 57,182,184 bytes  | 17,272 bytes    |
| slowest commit                | 5,875 ms          | 132 ms          |
| the fill                      | 67.6 s            | 51.6 s          |
| stream after the fill         | 2,441,525,064     | 2,266,447,032   |
| stream bytes a put            | 244               | 227             |

**By size, the FIFO** (main, then fix):

| Live keys  | sd    | Nodes dirty, worst step | Largest record     | Last step's commit   |
|---|---|---|---|---|
| 100,000    | 1 MB  | 7,559; 5                | 2.06 MB; 29 kB     | 9 ms; 0.4 ms         |
| 200,000    | 1 MB  | 15,459; 3               | 4.17 MB; 29 kB     | 46 to 49; 0.4 ms     |
| 400,000    | 1 MB  | 31,230; 3               | 8.36 MB; 29 kB     | 188 to 193; 0.7 ms   |
| 1,000,000  | 50 MB | 61,693; 3               | 16.7 MB; 29 kB     | 1.6 s; 0.7 ms        |
| 10,000,000 | 50 MB | 772,454; 15             | 206.1 MB; 29 kB    | 22.3 s; 1.1 ms       |

* **The largest record no longer grows with the keys**: 29 kB at every
  size, a transaction's own 14 kB of values and the take's share. 024-05's
  BD1 holds in these runs with a factor of 1.3 over the mean.
* **A step's nodes no longer grow with the keys**: 3 to 15 for the worst
  step of a run, at 100,000 keys as at 10M (B1).
* **Fewer bytes**: 6 % fewer a transaction at 100,000 to 1M keys, 9.7 %
  at 10M, 7 % in the fill. The nodes that the walk made dirty were all
  written; none had to be.
* **Reclaim does the same work otherwise**: the same number of
  iterations at every size (23, 19, 9, 4, 2), the same steps and KVs
  scanned in each; the first available position moves as before, and
  less is kept at the end.
* **The keys are all there after the cuts**: the queue of 400,000 keys
  with the fix, run again at 09:21 with a full scan at the end: after 9
  iterations, with 895 MB of the stream's 1,235 MB cut and its files
  deleted, the scan gives 400,000 keys (`out/scan-fix/`).
* **Against 024-03**: `main` here writes the same two records to the
  byte (191,137,072 and 206,065,600) with commits of 20.6 and 22.3 s
  (024-03: 20.6 and 22.2 s), so the two sets compare.

**Beside the queue, at 1M keys** (counts; `counts.sh`, the defaults of
the runs above; a fill in random order, then 30,000 transactions of 100
overwrites of random keys; "with a tail": 10 new keys after every key in
each transaction too, keys put beyond the scan's end beside the
overwrites):

| Measure                                  | main             | fix              |
|---|---|---|
| overwrites: bytes a transaction          | 41,043           | 40,540           |
| nodes dirty, iteration with no rewrite   | 44,062, 15.1 MB  | 959, 0.06 MB     |
| nodes dirty, iteration, 145,600 rewrites | 63,735, 20.4 MB  | 52,303, 16.4 MB  |
| nodes dirty, worst step                  | 23               | 25               |
| largest record                           | 88,080 bytes     | 87,104 bytes     |
| with a tail: nodes dirty, last step      | 11,265           | 3                |
| largest record                           | 2,748,560 bytes  | 97,312 bytes     |
| the last step's commit                   | 319 ms           | 1.3 ms           |
| bytes a transaction                      | 44,353           | 43,665           |

* **Random overwrites lose nothing**: 1.2 % fewer bytes, the same three
  iterations with the same 13,334 steps. Where an iteration has values
  to rewrite, a step's paths are most of what its range held (18 % fewer
  nodes). Where it has none, because every value was written since
  pCut, `main` still made 44,062 nodes dirty and the fix 959.
* **A tail beside them is the queue's fault again on `main`**: the last
  step walks the 136,000 keys put after the scan's end, 11,265 nodes and
  a record of 2.7 MB. With the fix: 3 nodes.
* The same at 200,000 keys with a startup distance of 1 MB
  (`out/counts-small/`).

Outputs: `out/fifo-10000000-fix/`, `out/fifo-10000000-main-r2/`,
`out/small-fix-sd1m/`, `out/small-fix/`, `out/small-main-sd1m-r2/`,
`out/small-main-r2/`; each has `env.txt` with the load at the start of
each run. Disturbed, by the coordinator's notes: the first runs on
`main` between 07:21:11 and 07:25:30 (the small ones and the 10M fill;
kept without `-r2`, their counts used, their times not), and the fix's
runs at 100,000 to 400,000 keys between 07:53:40 and 07:54:25 (their
times, 0.4 to 0.7 ms against 9 to 193 ms, are not the evidence; the
counts are). The count runs at 1M keys (`out/counts-main/`,
`out/counts-fix/`, 10:11 to 10:15) ran under the lock; those at 200,000
keys (09:33 to 09:36) beside other agents' gates.


## 9. Gates, and changed tests

On `b33a3daa`, under the heavy lock, 08:47 to 09:02
(`/Users/f/fl/bench/2026-11-11/touch/gates.sh`; the logs are beside it).
The head, `5bbdbf6e`, is one commit later: T-LATEST's premise made
Java's wait exactly (two Lean files and two documents, no Java, no
checker); on it `lake build` of the whole tree is OK (09:26).

| Gate                          | Result                                             |
|---|---|
| `lake build`, the whole tree  | OK, 149 jobs                                       |
| `test-traces/run.sh`          | TRACE TESTS OK                                     |
| `lake exe reclaimtest 20 30`  | all checks pass, 65 s (section 4.3)                |
| `java/stress/level3.sh`, full | LEVEL 3 OK, 8.6 minutes                            |
| `java/stress/level1.sh`, full | LEVEL 1 OK; MEM 130, SS 1.51                       |
| `java/before-commit.sh`       | BEFORE COMMIT OK (259 s), no changed file          |

* **`level3.sh`** in detail: 1,648 unit tests and 89 f-tests;
  ReclaimStress, 200 rounds, each with a cut, 3,528 exhaustive
  verifications, 0 failures; RestartInvariance and CrashTest with
  reclaim; ReclaimReaders, 36 rounds, 0 failures; LoadTest, 6 restarts
  with a full check after a cut; PowerLossTest; conformance with the
  Lean model, **25 traces, TRACECHECK OK 25, C-CUT 0 of 310 cuts**, with
  the two new checks in them (`touchPath` at every step, `CUT-live` at
  every cut); InterruptStress, 60 s.
* **Draining traces**, beside the gates (`07-last-touch/drain.sh`,
  09:11 to 09:17): reclaim traces with 60 and 80 % deletes, and with
  long keys and 60 % deletes, node size 8, 200 to 300 keys, 600 to 800
  transactions, 5 seeds each, so that deletes empty whole subtrees and
  segment trees before the cuts. **15 traces, TRACECHECK OK 15, C-CUT 0
  of 266 cuts**, C-A 0 failures (`out/drain/`). The set that 023-07,
  section 6.2, asked for is still not in `conformance.sh`.
* **Earlier**, on the tree as it was at 07:49 (the fix before its
  comments): `before-commit.sh`, BEFORE COMMIT OK (261 s).
* **Beside the task: `before-commit.sh` takes 4.3 minutes, on `main`
  too.** Of the 259 s, 183 s are `java/doubles.py`, in the main tree as
  it is today as in the clone: `method_regions`'s regular expression
  takes 85 to 95 s for each of the two allowed methods of
  `core/Db.java` (timed 09:05 and 09:20). The cause: `deps.strip` leaves
  the class Javadoc of `Db`, about 300 lines since 2026-11-10, as blank
  lines, and three adjacent parts of the pattern all match spaces, the
  last across lines: 0.5 to 0.8 s for each start position in the
  comment. Its header says "under a second". Not this subitem's, and
  not fixed here; the coordinator has the diagnosis.
* **`level4.sh quick`** on the head, 10:08 to 10:11, beside the gates:
  LEVEL 4 OK; its conformance with eviction, 15 traces, TRACECHECK OK
  15, C-P and C-H 0 of 3,461 transactions.
* **The integration** (024-13, the branch merged with 024-10's, head
  `524732d8`) ran, under its own holds of the lock: `lake build`, the
  checker's test traces, `level1.sh` (LEVEL 1 OK), `level2.sh` (LEVEL 2
  OK, 70 traces), `level3.sh` (conformance 25 traces OK, C-CUT 0 of
  310); read from its logs at 10:06, its own item has the results.
* **Not run here:** `level2.sh` (no touch there; its conformance uses
  the changed checker), `level4.sh` full, `night.sh`.

Changed tests, each its own commit, for Frans's approval:

* The checker's own test, `lean/test-traces/run.sh` (`b33a3daa`): for
  the hand-made `cut.trace` it expected "C-CUT cuts: 1 of 1 CUT lines
  (and PHYSCUT lines) fail (CUT-reach 1, CUT-top 1)"; now "(CUT-reach 1,
  CUT-top 1, CUT-live 1)". The trace has no data node, so its index
  nodes have none below them, which the new check reports beside the two
  failures the trace was made for. (A new expected line for
  `touch.trace`, "touchPath fails for nodes", is in `27093089`.)

* `DbTester.testTouchTransactionReplacedNodes` named a key range for its
  touch (`touchFrom`, `touchTo`), fields that are gone. It now names
  none, and no longer asks for "a node that the puts replaced and the
  touch did not visit": a put replaces only nodes on its key's path that
  existed before the transaction (a node the transaction made is split
  in place), and the touch now visits exactly those paths. The test
  still checks that a touched node that the puts replace stays in D, and
  now asks that there is one. It passes before the fix and after.


## 10. Not done

* **Nothing at 100M keys**, and the heap case of section 3 only at 1M
  keys with a small heap, not at 35M to 120M keys with 8 GB.
* **Keys put ahead of the scan, at scale** (024-05, GM2's second half):
  counted at 1M keys as a tail beside random overwrites (section 8);
  keys put at random between old keys, not at the tail, are not
  measured.
* **T-SCHEME is not proved.** T-COVER and T-LATEST are its steps 1, 3
  and 5 for the latest versions. Steps 6 and 7 (the references after
  pSafe, the nodes of D that no read reaches) and the versions that
  pointers lead to are as 001-07, section 5, left them: checked by
  running and by C-CUT.
* **UnlinkFuzz in a gate** (024-06, A1): LIVEBELOW's direct check, now
  worth more, as the cut rests on it. 024-09 has it on its branch
  (`night.sh`, and a draining conformance set); not on this one.
* **The C clone** (022) and StreamDigest's digests: the bytes of a
  database with reclaim on change.
* **OP8, ST7** (024-05, section 6, step 2, "in the same code"): not
  touched. **TE** (024-01, CL8: the touch ends at its range) falls away:
  there is no range.
* **Four comments in the Lean model's trusted files** still name
  `Db.touchRange` as Java's touch (SIS/Basic.lean, Algorithm.lean,
  Assumptions.lean, Phys.lean). Changing a line of Basic.lean builds
  every proof again; left for the next change of those files.
* **The touch could go altogether.** `Db.touchPaths` marks nodes that
  the puts mark anyway, but for a touched node that the puts replace,
  which stays in D and is written once more. It is kept so that the
  step's row can store what the step made dirty before its puts run
  (`Trans.dirtiedBytes`), and so that Java's D stays the model's
  `touchOf`. A step with no touch at all would be an ordinary
  transaction: one more change of bytes, and the row's count by another
  way.


## 11. Questions for Frans

1. **The cut now rests on the delete path.** With the range touch, a
   node left without a live key below it by a fault in the upward unlink
   was written again anyway. With option A it keeps its version, and a
   cut can remove it: a lookup that passes through it then fails. So I2
   (023-07, section 5.1) becomes a safety premise of reclaim, where it
   was a cleanup property. What guards it now: the `Bug` in
   `Dag.deleteUpward` for the one known way to break it; the trace
   checker's `CUT-live` at every traced cut; `ReclaimStress` and the
   `CutStream` tests, where a read below a cut throws. Recommended:
   accept it, land 024-09's A1 (UnlinkFuzz in `night.sh`, the draining
   conformance set) with this fix, and state I2 in the tree's model
   (024-12), where LIVEBELOW then becomes a theorem.
2. **Approve the two changed tests** (section 9): the unit test that
   named a key range for its touch, and the checker's own expected line
   for `cut.trace`.
3. **The two new checks of the trace checker fail a trace** (`touchPath`
   in C-A, `CUT-live` in C-CUT), in `level3.sh`, `level4.sh` and the
   night's conformance sets. `touchPath` makes the bound B1 a gate: a
   later change that makes a step walk a key range again fails
   conformance. Recommended: keep both as failing checks.
4. **The touch altogether** (section 10, last point). Recommended: not
   now; decide it with the tree's model, where a step would then be a
   plain transaction.
5. **A step's nodes on `main` at 100M keys.** Section 3's two cases
   (the record limit at about 104M keys in time order; the heap before
   it) are reasons to land the fix before any run at that size, and
   they hold for release 2026.4 as shipped. Recommended: a line in
   2026.4's known issues, "a queue of tens of millions of keys with a
   retain duration: fixed in 2026.5 (024-07)".

Landing is decided: Frans approved the integration at 09:25, and 024-13
merges this branch with 024-10's (the coordinator, 09:33).


## 12. Files

* `07-last-touch/probe/T7.java`: the probe (024-03's PF1 with reclaim's
  statistics and each iteration's last step apart).
* `07-last-touch/t7.sh`, `small.sh`, `big.sh`: the runners of section
  8; `t7h.sh` and `counts.sh`: the count runs; `drain.sh`: the draining
  traces.
* `07-last-touch/out/`: every output; `tests-on-main.txt` has the new
  tests failing on `main`'s algorithm, `touchpath/` the checker's new
  check on a trace of `main` and of the fix.


## 13. State

2026-11-11, 10:16: done. The fix is built, measured and gated, and
merged into the integration branch (024-13).

* **Done:**
  * the mechanism, and its count at 10M keys on `main`: 772,454 index
    nodes made dirty by one step (section 2);
  * the record limit, read and reproduced, and the heap, shown at 1M
    keys: an aim 1 case (section 3);
  * the cut's argument in the Lean model: T-COVER and T-LATEST proved,
    the scheme check with the cover run with and without any touch, the
    premise LIVEBELOW checked at every traced cut (section 4);
  * the bound and the options (sections 5 and 6);
  * option A built, with three tests, and committed (section 7);
  * the numbers before and after at 100,000 to 10M keys (section 8): at
    10M the last step makes 5 to 15 nodes dirty, the largest record is
    29 kB (it was 206 MB), the slowest commit 78 ms (22.3 s);
  * the gates (section 9): the Lean build and tests, `level3.sh`,
    `level1.sh`, `before-commit.sh`: all pass, on `b33a3daa`; the head
    is one Lean commit later, built; `level4.sh quick` on the head; 15
    draining traces.
* **The clone:** `/Users/f/fl/bench/2026-11-11/touch/clone`, branch
  `024-07-last-touch`, head `5bbdbf6e`, nine commits on `e7aa50f7`:
  `2d26ead3` the changed test; `98cb7438` the model (T-COVER,
  `checkSchemeC`); `27093089` the fix, its tests, the checker's
  `touchPath`, the documents; `84879877` and `8db50555` comments;
  `e81b8a6d` T-LATEST; `e7b66711` the checker's `CUT-live`; `b33a3daa`
  the checker's changed test; `5bbdbf6e` T-LATEST's premise. The working
  tree is clean. The coordinator merged the branch into `024-13-int`
  (09:33).
* **Nothing is running or queued** from this subitem; it holds no lock.
  The data directories of the runs are deleted; the outputs are in
  `07-last-touch/out/`, the gates' logs in
  `/Users/f/fl/bench/2026-11-11/touch/`.
* **Not done:** section 10. **For Frans:** section 11.
* **To continue:** nothing is needed from this subitem to land the fix.
  What could follow it: 024-09's A1 with it (the draining set and
  UnlinkFuzz in the gates); the C clone's pin and StreamDigest's digests
  after the batch of byte changes; a run at 100M keys in time order,
  now that no step can stop it (024-05, GM7).
