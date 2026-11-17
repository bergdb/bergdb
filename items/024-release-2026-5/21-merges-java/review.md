# 024-21, review rev21: the merges at the delete in Java

Written 2026-11-11, 14:57 to 15:27, by the reviewer "rev21" of coord-1111.
Reviewed: branch `024-21-merges` of `/Users/f/fl/bench/2026-11-11/mgj/clone`,
commits `be6d7f5a` to `ed9d8163` on `main`'s `2105baa7` (17 files, +1,638/-100).
Design read: 024-11 (MG, sections 1, 5, 7; BU1; CB2), 024-14 (8/17/17), 024-21
(the item), 024-22 (sections 2, 3.2, 5, 7), 024-04, 024-16.
Probes in my own clone `/Users/f/fl/bench/2026-11-11/rev21/clone` (its probe
branches are not for landing) and in `/Users/f/fl/bench/2026-11-11/rev21/probe/`.


## 1. Verdict: land with fixes

**I found no defect in the Java code of the merges.** The merge, the fix loop,
the parent's update, the take-back, root collapse after it, the rerun at a
start, the format refusal, the readers' view and the cut's premises agree
with 024-11 section 5 and with 024-22's model as described there, and my
probes found nothing (section 3).

**One finding blocks the landing as the branch stands (R1):** `main` has had
024-12's tree model and level 2's `treeconf` step since `ab1b9e42`. That
model has no merges and h = B / 2, and `TraceExport`'s TREE line on `main`
gives no thresholds. Landed alone, the branch fails `main`'s `level2.sh`. It
lands together with 024-22, with the TREE line that carries m, c and h, and
after a gate of the combined head. R2 is a small documentation fix that
should go in with the landing. R3 to R9 are notes.

The verdict assumes that mgj's 8/17/17 gates (chainD) end OK and that 024-22
finds Java equal to the model at 8/17/17. At 15:25, before-commit,
unlinkfuzz, level1, level2 and level3 had passed on `ed9d8163`, level4 was
running, and mgl's `treeconf` at 8/17/17 was not done.


## 2. Findings

### R1. The landing needs 024-22 and the TREE line with m, c and h (blocks)

* **Where:** on `main`, `java/stress/level2.sh` lines 183-184 (the
  `treeconf.sh` step, 024-12), and `java/stress/TraceExport.java` line 1611
  (`TREE maxNode G H k`, five tokens). `main` has no
  `lean/SIS/Tree/MergeProps.lean`, so 024-22 has not landed.
* **The failure:** suppose `ed9d8163` is merged into `main` without 024-22's
  Lean model, or without J2 and J9's TREE line `TREE M G H k minFill(M)
  mergeCap(M) splitAbove(M)`. Then `treecheck` replays Java's trace with
  2026.4's delete and h = B / 2. C-T1 differs at the first merge (drain and
  small sets). At node sizes 30 and 62 it also differs at the first rule O
  whose last version holds 16 or 17 klongs (h = 17, 35), which can happen in
  a put-only trace. `level2.sh` then prints LEVEL 2 FAILED on `main`, and
  "the Lean model matches the code" (024-04) is broken.
* **What mgj plans (024-21, section 10):** merge `main`, add J2, then
  before-commit. before-commit does not run `treeconf`, so it would pass and
  hide the failure.
* **Fix (the landing's steps):**
  1. Merge `main` into `024-21-merges`. UnlinkFuzz's header and Db's
     comments changed on both sides (024-16), so expect a small conflict.
  2. Write the TREE line with m, c and h (J2 and J9). Change
     `docs/trace-format.md` to match.
  3. Land 024-22 (the checker reads 5 or 8 tokens) before or with it.
  4. Gate the combined head, not only the branch: before-commit and
     `level2.sh` full, whose step runs `treeconf`. Run `level3.sh` and
     `level4.sh` too. The Java of `main` changed after the base (024-16's
     `Db.transformKeys`, 024-10, TraceExport), and the gates of section 7
     ran on the base.

### R2. docs/levels.md: a start's reads and the marks miss the siblings (should fix)

* **Where:** `docs/levels.md` line 299 says "A cold start still reads the
  nodes on the rerun's paths that have no version in the section: about 46 s
  ... (005-57)". Line 305, Marking, says "the index nodes that an operation
  ... follows, creates or changes get dirty".
* **What the code does now:** with format 7, a rerun's delete also reads the
  siblings of its merges through the follower. These reads come from the
  stream at a cold start. M1 reads the left sibling even when it chooses the
  right one (`Dag.merge`, `sibling`), and it reads them without marking
  (`followQuietly`). So:
  * a cold start reads more than "the rerun's paths";
  * the 46 s figure is from before the merges, and 024-11's TU9 (a cold start
    at 50 MB after deletes) was not run;
  * a node an operation follows is not always made dirty.
* **Severity:** documentation only. With CB1 (at most two siblings a level a
  delete) the start's reads stay proportional to its rerun's operations, so
  the form of the bounded-startup claim (007) holds. At 10M keys the merges
  were 0.01 to 0.19 a delete (024-21, 8.1, 8.3).
* **Fix:** add one sentence to each bullet: "and, since format 7, the
  siblings that a delete's merges read (up to two a level)"; "a sibling that
  a merge reads is not marked". Name TU9 as not measured, or measure it later
  (PF1).

### R3. docs/levels.md: the sibling rule is shortened (note)

* **Where:** `docs/levels.md` lines 329 and 332.
* **The difference:** the text says "the left one if both fit in c, ...
  else the right one". The code has a third case: with no right sibling it
  takes the left one, and the merge makes two nodes. The text also says "a
  bitmap ... deletes the right one's" klong. When the second new node starts
  at R's compare value, R's klong is pointed to it instead (M4, `deleteR`
  false).
* **Fix:** "else the right one, or the left one if there is none"; "deletes
  the right one's klong, unless a second new node starts at its compare
  value".

### R4. UnlinkFuzz's header gives P5's m (note)

`java/stress/UnlinkFuzz.java` line 25 says "2 at node size 8, 3 at 14, 7 at
30". Since `55add999` the value at 30 is 8. Change it, or name
`Dag.minFill` without values.

### R5. Reclaim.Tester's 200 kB: purpose kept; the comment's arithmetic off (note)

* **The question:** does `testLastStepWithinRecordLimit` at 200 kB still
  catch 024-07's fault, a last step whose touch walks to the end of the key
  space?
* **Probe:** branch `probe-oldtouch` of my clone. It brings back
  `Db.touchRange` with the step's `touchFrom` and `touchTo` behind
  `-Doldtouch`. With the old touch the test fails at 200 kB: "after 100
  transactions it is 252408 bytes behind". With the head's touch it passes.
  So the raised limit does not weaken the test.
* **The comment:** `java/src/bergdb/core/Reclaim.java` line 2890 says "over
  1,000 nodes, at 192 bytes each more than 200 kB". 1,000 × 192 bytes is
  192 kB, under the limit. Cite the probe's result instead.

### R6. DagTester's bound test runs puts before deletes (note)

* **Where:** `DagTester.BoundCase.run`, `java/src/bergdb/dag/DagTester.java`
  line 981. It applies all of a transaction's puts first and its deletes
  after them.
* **What it misses:** Db applies a transaction's operations in key order. A
  put that comes after a merge into the node that took its range is CB2's
  "extra overflow of a merged node". TU8 never reaches that case.
* **Probe:** `RevBoundProbe`, in key order with puts and deletes mixed.
  * Node sizes 8, 14, 30 and 62; one-segment and long keys; nodes full of
    dead klongs; transactions of 1 to 400 operations.
  * A targeted case: deletes in a node at its least fill, then up to 3B new
    keys in the range of its right sibling.
  * Results: about 128,000 transactions and about 90,000 merges. The nodes
    made dirty never exceeded `dirtyNodeBound`. The tightest case had a ratio
    of 1.0, in a put-only transaction at node size 8 with long keys (2026.4's
    count, unchanged). Scans and gets at the latest time matched the model.
    BU1 held after every transaction, and after every operation in a run of
    2,517 transactions (3,137 merges).
* **Fix:** let BoundCase apply its operations in key order. That is cheap,
  and it makes TU8 cover CB2's case.

### R7. Eviction.testDeadHand restarts less often (note)

* **The change:** the quick test has one restart (at 190) instead of two (at
  120 and 270). The f test has four instead of six.
* **Probe:** branch `probe-deadhand`. With the old restart points the head
  fails the test with "objects the dead hand took: 0", as mgj explains. The
  claims of the test still hold.
* **What it shows:** the test depends on when reclaim's first cut comes
  relative to the restarts.
* **Fix:** later, place the restarts after the first cut is decided, for
  example while `w.s2.getCut() > 0` is false keep going. Then a change of
  the stream's size no longer moves the test's premise.

### R8. CorruptStreamTester's moved copies (note)

* **What the rows assert:** `testFound019_32`'s rows assert only "no
  failure", so a moved row could test nothing.
* **Probe:** `RevCstProbe`. The copy at 27640, offset 708, is a value node
  of 40 bytes. Its outcome is "refused (StreamFormatException)" at the start,
  which is the case its comment names.
* **The other three tests** assert their kind: `testFound021_11` asserts a
  refusal, `testFound021_12` its three exact texts, and
  `testFoundDescentCycle` "node: read failed" and a failing scan.
* **One change of kind:** `testFoundDescentCycle` now sets the prevPos to
  the version of the child that came before the section, where it used to
  xor a byte. The copy is now made by hand, not found by the fuzz. The
  situation it tests is the same. No weakening.

### R9. dirtyNodeBound is still an argument; q is tight at node size 8 (note)

* **The formula:** q = max(2, min(B / 2, B - h, B - c) - 3) gives 2, 4, 10
  and 24 at node sizes 8, 14, 30 and 62.
* **Probes:** the walk was never exceeded (R6). Db's cheap test, 20 nodes a
  level for a delete, was 4.9 times the walk or more on 720 transactions at
  every database node size (`RevCheapProbe`), so the cheap test never
  accepts what the walk would refuse.
* **What it costs:** at node size 30, a transaction of about 120,000
  deletes is refused; 2026.4 took about twice that. 024-17's planned limit of
  1,000 operations is far below it.


## 3. Checked and found sound

* **The merge (`Dag.merge`, `mergeParent`, `mergeAfterDelete`).**
  * M1 picks the latest live klong of x and of each neighbour. `searchLte`
    takes the latest of equal compare values, so x is that klong's child.
  * M2 takes the last versions while both nodes are current.
  * M3: an inner R's empty key becomes R's klong in p, and a second inner
    node starts with the empty key, as a space split's second half does.
  * M4 counts room exactly. Klongs of tt are pointed in place behind p's
    time klong. The transaction's own last bitmap is changed in place. Rule
    O's last version uses the union, `replaceKlong` matches the raw klong,
    and `addSortedKlong` inserts in order.
  * M5 retargets dead klongs of tt to m1 before the take-back. After a rule
    O that replaces p, there is nothing left to retarget.
* **The fix loop.** `fresh` versus a new descent, and the depth moved by new
  roots, are right: every split and new root of a delete is on its key's
  path. The loop ends because a node that is space-split is not underfull.
  It stops at a segment root. Root collapse runs on the right tree in all
  three places. 2026.4's climb is reached only from an emptied root.
* **BU1 at every node size (8, 14, 30, 62).** Each half of a space split
  holds at least h / 2 >= m live klongs, so puts never leave a node under m.
  `MergeTester.testThresholds` checks the conditions.
* **J1's `Bug` cases.** Each fires only on a broken invariant, before
  anything changes (`merge`), or after m1 and m2 are made in rule O's path,
  where a `Bug` fails the database anyway.
* **The restart.**
  * `RevRestartProbe` ran 15,120 transactions with 3,004 restarts and
    76,188 merges. It used long keys of up to five segments, node sizes 8,
    14 and 30, startup distances of 10 B, 3 kB and 10 MB, and eviction on in
    half of the runs. After every restart the tree was the same, node for
    node (ids, klongs and pointers, `DbTesterMerge.tree`), and the values
    were right.
  * Ids come from the creation order, which a rerun repeats.
* **The record format.** Format 7 must equal the record's byte exactly. I
  reran T11 with the release jar of 2026.4 and the head:
  * 2026.5 refuses 2026.4's database with
    `VersioningStreamException: Cannot parse stored transaction of format
    version 6; ... format 6 was written by release 2026.4, which opens it`;
  * 2026.4 refuses the head's database ("format version 7 ... newer");
  * each opens its own.
* **Readers and the cache.**
  * A merge changes p only behind its time klong of tt. L and R lose only
    their klongs of tt, as a split's replaced node does. New nodes are
    reachable only through klongs of tt.
  * Pointers are copied as handles. `Cache3.pointerCreated` matters only for
    values, so `retarget` needs no report.
  * `dropNode` kills only the taken-back node's own handle.
  * Large values are registered for m1 and m2 by `reportNewPointers`.
* **Reclaim and the cut.**
  * Reclaim's steps only put (their row is a value transformation that never
    gives null), so they never merge, and the touch never meets a merge.
  * Nodes left out by a merge are a split's replaced nodes for the cut.
  * m1's children were reachable before tt, so the iteration covers them.
  * CUT-live holds more strongly with V1.
* **Rule A and D.** m1 and m2 are new and dirty, and Rule A keeps them dirty
  while a child is in D. A left-out node leaves D only if it got dirty in
  this transaction (`endOfTrans`). Siblings are not marked.
* **The changed tests.** None weakens its purpose (R5, R7, R8). In
  `DagTester`, the collapse-count tests at node size 6 still fail on B1's
  regression, taking the most of one tree instead of the sum:
  4 × 2 + 8 = 16, under the asserted 20.
* **The new and changed unit tests** (MergeTester, DbTesterMerge,
  CorruptStreamTester's four, StoredTrans, Eviction.testDeadHand,
  DagTester's bound tests): 18 tests, SUCCESS in 3.1 s on the head.
* **`releases/next.md` and `docs/sis-model.md`** match the code. So does
  `docs/levels.md`, apart from R2 and R3.


## 4. Not checked

* The 8/17/17 gates on `ed9d8163` (level4 running at 15:25), and 024-22's
  comparison at 8/17/17.
* Anything on the combined head after a merge of `main` (R1).
* The Lean side: 024-22's statements and proofs, and `treecheck`'s reading
  of the TREE line.
* Timing and performance. No timing runs: the cost of a delete in CPU
  (`liveCount` on every delete), a cold start after deletes (TU9), and the
  numbers of 024-21 section 8.
* Runs at 10M keys and on disk, the C clone (012, unaffected by design), and
  the Pub layer beyond T11.
* The trace branch `024-21-merges-trace`.


## 5. State

Done at 15:27. The probes' sources are in
`/Users/f/fl/bench/2026-11-11/rev21/probe/src/` (`RevBoundProbe`,
`RevRestartProbe`, `RevCheapProbe`, `RevCstProbe`). The probe branches
`probe-oldtouch` and `probe-deadhand` are in
`/Users/f/fl/bench/2026-11-11/rev21/clone`, which is detached at
`ed9d8163`. Nothing in mgj's clone or in the main tree was changed but this
file.
