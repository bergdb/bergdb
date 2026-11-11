# 024-23, review rev23: option 2 of dead klongs, theta 7

Written 2026-11-11, 17:18 to 17:45, by the reviewer "rev23" of coord-1111.
Reviewed: branch `024-23-option2` of `/Users/f/fl/bench/2026-11-11/o2/clone`,
head `1f9fdb64`, the diff `67925924..1f9fdb64` (29 files, +1,442/-154): Lean
`aabafc04`, Java `1838b687`, `6a24e0f0`, the merge of `main` `e633004f`, and
the five test commits of 024-23, section 4.1.
Design read: 024-23 (sections 2 to 6), 024-18 (section 4, section 8's QD1),
024-21, 024-22, and 024-21's review (for the form).
Probes in my own clone `/Users/f/fl/bench/2026-11-11/rev23/clone`, in a
worktree of `67925924` (`rev23/base`, the merges alone), and in class
directories under `/Users/f/fl/bench/2026-11-11/rev23/` (a planted class put
before `build/bergdb.jar` on the class path). Neither branch was changed. No
slot was taken: every probe was a unit test or a run of a few seconds.


## 1. Verdict: land with fixes

**I found no defect in the rule.** Every write path of `Dag` counts the dead
klongs it adds as 024-23, 2.2 says. A compaction is always a time split, and
it fits. The rule reads the node only, so a start's rerun makes the same
nodes. `dirtyNodeBound`'s new term and Db's cheap test stay sound. The
merges, BU1, reclaim and the cut keep their premises. Section 3 lists the
checks. Planted faults show that Java's own unit tests catch an undercount in
three of the four paths that matter. The fourth, LE-b, cannot be reached at
format 7 (R3). They also catch the restart's determinism and the missing
term in `dirtyNodeBound`.

**One test change should be fixed before it lands (R1).** In `c6655215`,
`DbTester.testDecreaseOfStartupDistance`'s "no jump" now passes even when
the jump is planted, on this branch and on the merges alone. So the test no
longer tests what it is named for. A fix of two lines restores it, and I
checked the fix both ways. The other four test changes keep their purpose
(section 3.5).

R2 to R7 are notes. None blocks.

The verdict assumes that o2's remaining gates end OK. At 17:31,
`o2/logs/gates-all.txt` showed: level1 OK, unlinkfuzz OK (3,226 rounds),
and level2 running. 024-23, section 6, gives earlier results: lake build,
no sorry or axiom, test-traces and before-commit OK on `1f9fdb64`. Section
5.2 says treeconf (small, drain, reclaim, medium) found Java equal to the
model.


## 2. Findings

### R1. testDecreaseOfStartupDistance's "no jump" passes with the jump (should fix)

* **Where:** `java/src/bergdb/core/DbTester.java:2068` (commit `c6655215`):
  `assertTrue("no jump", dueLeft(db, db.getStreamLength(), sd))`, with
  `sd = 500 * 1000` at line 2055.
* **What the test is for (007-07):** after a decrease of the startup
  distance, the deadline must not jump to 2 sd at once. If it did,
  setStartupDistance's record would take every transaction older than 2 sd
  from the end. "No jump" means some such transaction is still left after
  the call.
* **The failure:** setStartupDistance writes a record of about 250 kB:
  240 to 265 kB in every run I made, with and without the jump. Counted
  from the stream's end after the call, the 2 sd point moves 250 kB later,
  past transactions that were never due. So the check is true whatever the
  take did. A planted jump shows it. I changed `TransSeq.take`'s
  `hardSp = streamLength - Math.max(2L * startupDistance, span())` to
  `streamLength - 2L * startupDistance` (`rev23/plantJ`, `rev23/plantB`).
  Probe `rev23/probe/.../ProbeDecrease.java`:

  | Build, sd 500 kB  | dueLeft, old end | dueLeft, new end | with the jump: old, new |
  |---|---|---|---|
  | merges (67925924) | true             | true             | false, true             |
  | option 2 (1f9fdb64) | false          | true             | false, true             |

  With the jump planted, the whole of `testDecreaseOfStartupDistance`
  passes on `1f9fdb64`. Also, with option 2 at 500 kB the span is below
  2 sd right after the call (`below` = 0; it was 3 on the merges alone).
  So the test's later part, where the span shrinks commit by commit, no
  longer runs either. The Javadoc's "below twice the setting after 19
  commits" was already out of date.
* **Still covered elsewhere:** TransSeq's unit tests of the deadline after a
  decrease (`TransSeq`, about lines 760 to 835) fail 3 of 18 with the plant.
  So the property is tested, but not at the Db level.
* **Fix (checked):** keep the old form, counted from the end before the
  call, and lower the decrease to 450 kB:

      -        final int sd = 500 * 1000;
      +        final int sd = 450 * 1000;
      ...
      -        assertTrue("no jump", dueLeft(db, db.getStreamLength(), sd));
      +        assertTrue("no jump", dueLeft(db, length, sd));

  On `1f9fdb64` the test then passes, and the shrink phase lasts 7 commits.
  With the jump planted it fails with "no jump, expected true, but was
  false". 400 kB also catches the jump but gives a shrink phase of only 4
  commits, and 500 kB cannot catch it. Change the Javadoc to match: 2 MB
  lowered to 450 kB (until 024-23, 500 kB); the span below 2 sd after a few
  commits; drop "19". This is a changed value in an existing test, so it is
  its own commit and needs Frans's approval, like `c6655215`, which it
  replaces. The test is fragile, because the take's share moves with every
  change of record sizes. A sturdier form would assert that the call's
  record took fewer transactions than a jump would. That is for later.

### R2. Databases written by main since 67925924 rerun differently (note)

* **Where:** 024-23, 2.2 ("No record field, no flag") and QO3;
  `StoredTrans.RECORD_FORMAT` stays 7.
* **Scenario:** a database is written by `main` at `67925924..4c75ebf1`
  (merges, no option 2) and later opened with this code. The rerun of its
  last records compacts nodes that the writer did not compact. The node ids
  and the nodes then differ from those in the stream, so later records may
  link to wrong nodes. Nothing refuses such a database.
* **Who can have one:** only today's internal runs, for example bench
  databases made by agents on `main`'s build since 14:48.
* **Suggested:** land soon. In the landing message (and in news.md if the
  coordinator writes one), say that databases written by `main` between
  `67925924` and the landing must not be reopened. Keep format 7, as QO3
  recommends.

### R3. Java's LE-b compaction is never run (note)

* **Where:** `Dag.java:1666`, `emptyKeyNext`'s `deadFull(node, inPlace ? 1
  : 2)`.
* **What I found:** I planted `if (room)` without the test. All 1,670 unit
  tests still pass (`rev23/plant_leb`). 024-23, 5.2, says no treeconf trace
  reached `leb.*`. At format 7 with B >= 8, a node that is not a root holds
  at least m >= 2 live klongs, so one delete never empties the child of an
  inner node. LE-b is then unreachable. Below 8, theta is 0.
* **Read by hand:** w = 1 for the next child's klong deleted by the bitmap
  (new or the transaction's own), plus 1 for the new empty-key klong unless
  it is pointed in place. This equals the model's `deadCount n2` in
  `Exec.lean`'s `emptyKeyNext`, which treetest runs at node size 4 with
  theta 1 forced. Nothing to do now. If 024-14's QT2 ever turns on merges
  or theta below 8, this branch needs a Java test.

### R4. docs/levels.md says too much about reclaim (note)

* **Where:** `docs/levels.md`, option 2's paragraph: "reclaim's rewrites,
  which are puts, compact the cold leaves they reach". The same paragraph
  is in Dag's section comment, `Dag.java` about line 1855.
* **Why:** a rewrite adds one dead klong. It compacts only a leaf that
  already holds theta, so a cold leaf with fewer dead klongs stays as it
  is.
* **Suggested:** "... and reclaim's rewrites, which are puts, compact the
  cold leaves they take above theta". Also, releases/next.md's figures
  (0.48 to 0.35, 0.83 to 0.30, -3 % to +7 %) come from 024-18's prototype,
  whose rule was "theta or more before a write". The entry should say so
  until section 7's numbers replace them, as 024-23, section 4, plans.

### R5. The cost of the count on every put (note)

* **Where:** `Dag.java:969`. `setValue` computes `isLive` (two passes over
  the node: the scan for the key and `lastBitmap`) before `deadFull`'s
  cheap test `node.size - 1 + dead <= theta`. `deadCount` costs up to
  B^2 / 2 comparisons on a node above theta: about 450 at B = 30 and about
  1,900 at 62.
* **Suggested:** nothing before landing; Frans chose to measure later
  (QD1). If the measurement shows it, test the size first (`node.size <=
  theta` needs no count), or count with one pass per compare value.

### R6. TP40's premise is wider than TP39's conclusion (note)

* **Where:** `lean/SIS/Tree/DeadProps.lean`, `DeadWriteOK`: "every key node
  of P (`keyNodeAt`, any x) holds at most theta". `DeadBoundOK` (TP39)
  speaks of the nodes reachable at the run's time.
* **Why it matters later:** a proof of TP39 from TP40 needs the form over
  all nodes. That form is true: a replaced or unlinked node goes back to
  its state before the transaction (`toPrev`), and it held at most theta
  then. State it, or narrow TP40's premise, when TP39 and TP40 get proofs.
  For now both are unproved statements that the runs check.

### R7. treecheck takes theta from the trace (note)

`parseTreeLine` (`lean/Check/Tree.lean:140`) uses the TREE line's theta as
given. Nothing in the checker compares it with `Params.thetaFor M`, and m,
c and h are not compared either. So treeconf checks Java against the model
at Java's theta, not at the format's theta. The two agree:
`DeadKlongTester.testTheta` checks Java's values, `thetaFor_values` proves
Lean's, and they are the same at 8, 14, 30 and 62. A check in treecheck
(theta = thetaFor M when the line has 9 tokens) would close the gap at one
line's cost. It is optional.


## 3. What I checked and found sound

### 3.1 The rule in every write path (Dag, read line by line)

| Path | Line | w in Java | Agrees |
|---|---|---|---|
| setValue, a put's klong | 969 | 1 if the key is live (isLive) | yes |
| setNode, a new segment's klong | 1035 | 0, not tested | yes: an old klong of cv is dead already |
| appendDeleteKlong, new bitmap | 1138 | 1, after the room test | yes |
| appendDeleteKlong, own bitmap in place | 1124 | 1, compaction | yes |
| appendKlongs (splits, RC, time split's klong) | 2503 | 1 a klong of a live cv | yes |
| emptyKeyNext (LE-b) | 1666 | 2, or 1 in place | yes (R3) |
| mergeParent | 2257 | deleteR + !lInPlace + (m2, !deleteR, !rInPlace) | yes |
| retarget, link in place, repoint, takeBackRoot | - | 0, no klong added | yes |

* Each path tests size first, as before. A compaction is called only when
  the node has room. `handleFullNode`'s `compaction` skips h, so it is
  always a time split (`Dag.java:2583`). It fits: `last` has one time klong
  and one klong for each live compare value, which is no more than the
  node, and the node had room for the write. So the Bug at line 2578 is
  only a guard. After a compaction the new node holds 0 dead klongs:
  `lastVersion` drops them, and `replaceKlong` replaces the write's klong
  of the same compare value instead of shadowing it. The same holds after
  any rule O by size, for the halves and the last version.
* `deadFull`'s cheap test (a node of n klongs has at most n - 1 KEY klongs)
  and `deadCount`'s limit (`theta - dead + 1`) return the same answer as
  the full count.
* Nodes that the transaction made are compacted in place
  (`timeSplitInPlace`), so `pd.replacedBy`, the take-back and `madeFor`
  are as before. A node that existed before is replaced and drops its
  klongs of tt (`toPreviousState`). Unlinked and taken-back nodes go back
  to their state before tt, which held at most theta. `pd.fullNodes++`
  marks the path stale for the merges' loop.
* No key node is written outside Dag: I grepped for `addKlong`,
  `repointKlong`, `setContentFrom` and `klongs[..] =`, and found only
  tests.
* Lean computes the count on the node with the write applied (`deadOver`
  on n'). For each path above, Java's w is `deadCount n' - deadCount n`.

### 3.2 Planted faults (Java's unit tests of dag and DbTesterMerge)

| Plant (rev23/plant_*) | Caught by |
|---|---|
| mergeParent without deleteR's 1 | DeadKlongTester, MergeTester (TP39), DbTesterMerge, 6 tests |
| appendKlongs counts 0 | DeadKlongTester, DbTesterMerge incl. testRestartsRerunTheCompactions |
| own bitmap in place not tested | DeadKlongTester.testOwnBitmapIsAWrite, MergeTester, DbTesterMerge |
| dirtyNodeBound without the term | DeadKlongTester.testCompactionAtTheta |
| reruns do not compact (DbStarter) | testRestartsRerunTheCompactions and the merges' restart tests |
| LE-b without the test | nothing (R3: unreachable at format 7) |

### 3.3 Determinism at a restart

`deadCount`, `isLive` and `theta(maxNodeSize)` read only the node's klongs
and the database's node size. A node read from the stream, a reloaded node
and a rerun node have the same klongs. Db and DbStarter clear the key
access path after each put (`Db.java:3001`, `DbStarter.java:447`).
`testRestartsRerunTheCompactions` compares the tree node for node after
each start, at 10 bytes and at 10 MB. With the plant above it fails, so it
checks what it claims. The existing restart and crash-cut tests (node size
8, theta 1) catch it too.

### 3.4 Bounds, merges, reclaim, the cut

* **dirtyNodeBound** (`Dag.java:732`): the count is max(the size count,
  1) when dead + klongs > theta. A node with room that is compacted gets
  one new node and one klong in its parent. Its replacement has no more
  klongs than the node would have had, so its later size overflows come no
  earlier than the node's. Later compactions are in place. When the size
  count is 0, k <= room, and the replacement never overflows by size. The
  Lean `overflows` is the same function.
* **Db.checkDirtyNodes' cheap test:** for a put, one write per level gives
  at most one rule O: the dirty node plus at most two new nodes, within
  the 3 nodes a level. For a delete, the 20 nodes a level were taken from
  the worst case of a node without room. That case already counts 1 or
  more, so the new term never exceeds it.
* **Merges and BU1:** a compaction keeps every live klong, so live counts
  and therefore V1, BU1 and the merge triggers do not change. A compacted
  node may hold more than h klongs. Nothing assumes a time split's node
  holds h or fewer: q bounds the halves of rule O by size, and the merges
  accept siblings of any size.
* **Reclaim and the cut:** a compaction makes a node at the time of the
  write, past pCut. The node's pointers are those of the replaced node's
  live klongs, so nothing reachable from tEnd on points to anything older
  than before. The cut's argument (Reclaim's header, an index node
  reachable from tEnd on is stored at pCut or later or is dirty) still
  holds. A step's pinned nodes grow by at most one new node per followed
  node, as with splits before.

### 3.5 The five changed tests

* **`1d38e6f4` CorruptStreamTester:** testFound019_32 asserts only "no
  failure", so each row must still hit the same damage. My probe
  (`rev23/probeC`) ran every row, old pins on the merges build and new pins
  on `1f9fdb64`. All ten rows give the same outcome and the same refusal
  text, apart from numbers: "Bad klong type, 2", "Bad key of value node",
  "Bad key count", read failed (rows 4, 5, 8 and 10), "names a node of type
  30", "has no klong at or below the key", and "Bad pointer". testFound021_11
  asserts "refused" for each row. testFound021_12 asserts its three texts.
  testFoundDescentCycle asserts "node: read failed" and its scans. Purpose
  kept.
* **`c6655215` DbTester.testDecreaseOfStartupDistance:** weakened, see R1.
* **`214d4635` Eviction.testLoweredBudgetAfterPinsFell (520):** the test
  asserts its own precondition ("the pins fell", "detachable objects
  resident", budget < bytes <= P0), so it fails when the state is not
  reached. With 500 transactions it failed, which is why it was changed.
  Purpose kept. It is fragile, as its Javadoc says.
* **`7103d741` EvictionReaderTester (40 keys):** it asserts "pointers
  checked >= 3", its own precondition. Purpose kept.
* **`1f9fdb64` DagTester.testPointerCreationListener:** the old test on the
  new code fails with "time-split-1, missing klong in keyAccessPath,
  10186", as the commit says. Without `clearFast` the path grows across
  puts, so the space root's time split took the previous put's node as its
  parent. Db and DbStarter clear the path after each put, so the change
  makes the test do what Db does. Its claims are unchanged.

### 3.6 Lean

* `Params.thetaFor` is `if M < 8 then 0 else max 1 (7 * M / 30)`, and Java
  computes `b < 8 ? 0 : max(1, 7 * b / 30)`. They are equal.
  `KNode.deadCount` has Java's loop: deleted by the last bitmap, or
  shadowed, each klong counted once. `deadOver` is tested in every write
  of `Exec.lean` that Java tests: setValue, appendKlongs, appendDeleteKlong
  (both forms), emptyKeyNext and mergeParent. setNode's klong is not
  tested, as in Java.
* TP39 (`DeadBoundOK`) states what `checkFill` checks: the key nodes
  reachable at the time, each with deadCount at the latest time at most
  theta. TP40 is stated (R6). The proved lemmas are small and true
  (`thetaFor_values` by decide, `deadOver_false`, `thetaFor_pos`). The walk
  reports `DeadOK`, so treetest and treecheck's C-T6 check TP39.
* treecheck reads TREE lines of 5, 7, 8 and 9 tokens. The older forms are
  unchanged and give theta 0. docs/trace-format.md describes the 9-token
  line correctly: "8 numbers, and 7, 4 and 6".

### 3.7 Docs

docs/levels.md, docs/sis-model.md (3.4: a compaction as a time split, A2,
A3 and A5; the format paragraph), docs/trace-format.md, lean/README.md and
releases/next.md agree with the code, except for the wording in R4.


## 4. What I did not check

* I ran no gate, no level script, no treeconf and no treetest myself; I
  relied on o2's logs and 024-23, sections 5 and 6. level2 to level4,
  conformance and the 1M count were still running at 17:31.
* I did not read the Lean proofs line by line beyond the three short
  lemmas. I did not read `TreeTest.lean`'s run set beyond the diff.
* I did not measure stream bytes, MEM or read times. Frans chose to measure
  later (QD1).
* I did not trace `Exec.lean`'s `handleFullWith` with `compact` through
  every branch. I relied on treeconf's equality with Java on 222 traces.
* Node sizes other than 8, 14, 30 and 62 (QO2) were not checked.
