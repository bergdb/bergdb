# 023-08 Review C of 023-07

Written 2026-11-10, 14:49 to 15:47, for Frans Lundberg. Checked against the code of the branches
in section 2 of 023-07, with probes run for this review (section 2.1). No branch was changed;
two fix sketches live only in this review's worktrees.


## 1. Verdict

**Accept the core with changes.** Two faults found and reproduced, both in the core:

1. **P8 can stop the cuts** (K5). With any key after a queue, E does not end the scan: the
   queue's keys come in ahead of it faster than a step's 16 kB. 1,000 live keys, 3,000
   transactions, no cut, 137.5 MB; with the scan at tStart, as on `main`, 15 transactions.
   021-25's failure in a new form. Take P8 out of 2026.4, or give it a quota in proportion.
2. **The take-back misses a klong** (K1). After `Dag.spaceSplitInPlace`, a shadowed klong of tt
   in a segment leaf names a node that tt then takes back. The record names an unwritten node,
   and the next start fails. Reproduced at node size 30 with transformed keys. Fix by rule.
3. The rest holds as far as checked: lemma M, LE-b's readers, the bitmap rule; the dead hand
   does only what the EVERY eviction schedule does.
4. **KISS:** the core without P8 is the smallest design found for R9 with R forever and no
   Lean change. Nothing in the full set is needed for the rule (section 7).
5. Gate the combination with the tests of 5.3 before the tier is decided.


## 2. Soundness, mechanism by mechanism

### 2.1 How I checked

* Code read on each branch with `git show`, at the heads of 023-07, section 2.
* Probes, run in worktrees of this review's clone (not committed):
  * `Reclaim.Tester.testProbeQueueBeforeEndKey`, `testProbeQueueControlNoZ`,
    `testProbeQueueAtTStart`, `testProbeOrderedPutsBeforeEndKey` and `testProbeBackwardLastKey`.
    They run on P8's head, about 4 s; the diff is
    `/Users/f/fl/bench/2026-11-10/rev23/c/scratch-p8/probes.diff`.
  * `DbShadowProbe` and `ShadowProbe`, Db and Dag level. They run on P4 with P5's `retarget`
    ported and with `offPath = 1` (P5's count without merges), in
    `/Users/f/fl/bench/2026-11-10/rev23/c/scratch-p4/probe`.
  * `DbShadowProbe30`, the same at the default node size 30, with 14 keys under one prefix
    and an overwrite history (`/Users/f/fl/bench/2026-11-10/rev23/c/scratch-c`).
  * `BoundProbe2`, and UnlinkFuzz with long keys, 40 rounds.
  * Two fix sketches, switched in the worktrees `wt-p4` and `wt-p8` of
    `/Users/f/fl/bench/2026-11-10/rev23/c`: fault 12's (2.2) and P8's quota (2.6).
* I reran the fault probes myself from 15:30 to 15:41: `DbShadowProbe` 2 failures in 12 cases,
  `DbShadowProbe30` 2 in 1,136, each with -ea and without; the four P8 runs as above.
* Gates and measurements I did not run are marked "report".

### 2.2 K1, the upward unlink and the take-back

| Aspect                          | Result | How checked                                        |
|---|---|---|
| Lookups before tt, held objects | sound | code: in-place changes only behind tt's time klong |
| UP's climb and `stop`           | sound | code; UnlinkFuzz, 40 rounds, 0 failures            |
| The take-back names nothing     | fault | `DbShadowProbe`, reproduced (below)                |
| Fault 6 at P4's head            | fault | `ShadowProbe`: 3 in 73 cases without `retarget`    |
| X5 (c)                          | risk  | reached at the leaf only; the inner branch never   |
| The rerun's choices and ids     | sound | code; ids not compared in a run                    |

* **In-place changes.** `KeyNode.repointKlong` and `copyPointer` assert an index after the time
  klong of tt. `Dag.retarget` stops at that klong and needs `lastTime(p) == tt`.
  `toPreviousState(tt - 1)` runs only on nodes from before tt. `TopDs.newSuperRoot` changes a
  top node in place only when its root time is tt. So lemma M holds: a lookup at t < tt reads
  the same entries as before.
* **Fault 12** (numbered after 023-07, 5.14). In `Dag.spaceSplitInPlace` (P4 and P5), a
  segment root X made by tt is split in place. Its parent is a segment leaf L.
  `appendKlongs(L, klong1 -> newRoot)` calls `KeyNode.addKlong`, so L gets a second klong of
  tt with the same compare value. L's first klong of tt still names X; for the space root,
  `TopDs.newSuperRoot` repoints in place. If tt then empties X, `takeBack` and `retarget`
  repoint klongs in X's parent (newRoot) only, and `takeBackRoot` repoints only the latest
  klong. X is dropped and never written. L's shadowed klong names it, and `Db.store` fails in
  `StoredTrans`' stream pointer check:
  `AssertionError: spos of index node pointer (2261) is vpos, index: 5, node: K/a3 0:3632 L`.
  * Without -ea the record is written, and the next start fails: `StreamFormatException:
    Unexpected stream pointer 2261, index 5 of key node 0 at 3632` (the probe's restart
    phase). The database cannot be opened again.
  * At node size 30: 14 keys under one prefix, put, and 13 of them overwritten; then one
    transaction puts 20 transformed keys that sort after them and deletes the 14. The same
    assertion with -ea, the same failed start without (`DbShadowProbe30`, nb = 14).
  * Reach: `Trans.build` sorts the keys (a TreeMap); `Db` applies a `KeyTransformation` after
    that, so transformed keys can run out of order. The Pub API's key replace does this
    (`/events/${transactionTime}` sorts before `/events/0`): an event log that appends and
    trims the oldest in one transaction. A random Pub probe found no failure in 20 runs, so a
    Pub API reach is plausible but not shown.
  * UnlinkFuzz cannot find it: its transactions are sorted, and the klong is shadowed at every
    time, so its check of pointers reachable at some time does not see it.
  * `main` has no take-back, so there the shadowed klong names a written node.
* **The fix, as a rule.** Every klong of tt that names a node being taken back is repointed,
  in every node, not only in the parent. In the cases found, every node that named it during
  tt lies on the path above it. Two ways: (1) `retarget` in every node of tt on the path above
  the node; or (2) keep `retarget` in the parent, and let `spaceSplitInPlace` repoint L's klong
  of tt in place (`repointKlong`) instead of adding a second one, as `TopDs.newSuperRoot` does
  for the space root. (2) is smaller; (1) needs no search for other such places.
  `StoredTrans`' pointer check (-ea) is the test's oracle. Check: `DbShadowProbe` as a unit
  test; UnlinkFuzz with transformed keys.
* **A sketch of (2)**, about 25 lines in `Dag.spaceSplitInPlace` (diff in
  `/Users/f/fl/bench/2026-11-10/rev23/c/scratch-c/f1-fix-sketch.diff`). With it both probes
  pass (0 of 1,136 cases at node size 30, 0 of 200 at 8), and so do the 1,625 unit tests;
  switched off, the failures come back. A sketch, not a gated fix.
* **X5 (c).** It is reached when a new segment tree is put and deleted in one transaction, and
  then always at the leaf (`stop == depth`). The branch that stops above an inner node of tt
  was never reached: an inner node of tt that is not a split's node has only such nodes below.
  Likely dead code; make it an assertion. The empty space root replaced by a leaf was never
  reached either (P1, 5): it needs a unit test that deletes every key.
* **The rerun.** `DbStarter.rerunTransaction` makes one `PutData` a transaction; the splits
  rebuild `replacedBy` in the same order; `keyNodeCreated` gives the ids in both runs, and a
  taken-back node is dropped at once. Same choices, by reading.

### 2.3 K2, the empty key first

* **Readers: sound** (search of all of `java/src` on P4). `GetMany` (both directions, with start
  keys), Dag's searches, `Audit.currentIds`, `Reclaim.lastKeyAt` and `Db.touchRange` (P8),
  the Pub scans: none takes a lower bound from a node's first klong. `KeyNode.searchFirst` is
  used only in `KeyNodeTester`. No path cache keeps klong bounds.
* **Splits: sound.** `KeyNode.firstAndSecond` is the only space split of an inner node, and its
  inserted klong rule covers the split's insert. The time split (`lastVersionGivenDel`) keeps the
  latest undeleted klong of each compare value in order, so the empty key stays first.
* **The empty key never gets a bit.** `emptyKeyNext` picks j with a compare value other than 0;
  `appendDeleteKlong` on an inner node only for c other than 0. The `Bug` for an inner node
  without the empty key never fired in about 100,000 probe cases.
* `testProbeBackwardLastKey`: after each of 2,400 random transactions, at node size 8, with keys
  of 1 to 4 segments (33,000 unlinks, 1,500 LE-b moves, 206 root collapses), the backward
  read of one KV gave the forward scan's last key every time.

### 2.4 K3, root collapse, and the bitmap rule

* RC lifts the root's only live child. The child's range only grows. `takeBackRoot` has the
  same gap as `takeBack` (fault 12).
* **The bitmap rule: sound** (code). In `emptyKeyNext` the bits of every klong of c_j come
  before the new empty key. `appendDeleteKlong` changes a bitmap in place only if it is the last
  klong. In P5's `mergeParent` the bitmap comes before `link`.

### 2.5 K4, `dirtyNodeBound`

* With P5's count without merges, `BoundProbe2` saw no overrun in about 10,000 random
  transactions at node sizes 8, 14 and 30. The probe's count of dirty nodes is approximate.
* **Risk:** `collapseRoot` loops, and `replaceRoot` adds one klong to the segment leaf above for
  each level collapsed. Those levels can lie off the delete's path, but the count gives 2 klongs
  a delete. Collapses of several levels were rare in the probe. Not proven; it needs a test.

### 2.6 K5, the scan at the step's time with E

| Aspect                | Result | How checked                              |
|---|---|---|
| Values (P8, 2.3)      | sound | code: times and ranges below             |
| Index nodes (P8, 2.4) | sound | argument, for what P8 changes            |
| E correct             | sound | `testProbeBackwardLastKey`, 2,400 checks |
| Determinism, E stored | sound | code: row `endKey=`, `set`, `initFromDb` |
| Liveness (R6)         | fault | four probes, rerun                       |

* **Values.** `Reclaim.transactionCompleted` sets pStart, tStart and E at t; pCut is the previous
  row's pStart. A step scans at the last transaction's time, so every step's scan time lies
  in [tStart, tEnd], tEnd being the last step's time. The ranges join without a gap:
  `IterationInfo.pastEnd` uses "greater than", so a key equal to E is scanned; the value limit's
  break sets lastKey; `Db.touchRange` is from exclusive to inclusive. A value stored before pCut
  and visible at t >= tEnd was live through [tStart, t], so it is at most E and live at its
  step's time. P8's 2.3 holds.
* **Index nodes.** An old node reachable at a time from tEnd on was reachable at tStart. LE-b's
  pointer copy and RC's lift only widen the range of a node already reachable, so the step that
  covers one of its keys touches it, before or after the copy. P8's 2.4 holds for its change.
* **Liveness: fault 13.** A step's scan quota is min(allowed, 16,000) bytes by the scan's measure
  (8 bytes a segment, the value and 100 a KV), at most one step an external transaction. The
  quota does not follow the transaction's size. Before P8 the scan read a fixed set, the KVs
  live at tStart. Now it reads the latest state, so keys put ahead of the cursor and at most E
  join it. E stops the scan only when the keys come in after the last key: with any key after
  the append point (another table, a metadata key), it does not.

| Run (P8's head, unit test)                        | Transactions | Done | Stream      |
|---|---|---|---|
| queue of 1,000, 200 puts and deletes, key "/z"    | 3,000 | no  | 137,547,904 |
| the same, without "/z"                            | 5     | yes | 447,776     |
| the same, with "/z", scanning at tStart as `main` | 15    | yes | 844,488     |
| 200 ordered puts a transaction, key "/z"          | 2,000 | no  | -           |

* In the queue, the deletes at the head overtake the cursor, so each step starts at the head and
  scans about 74 KVs; the tail stays about 900 keys ahead. The iteration scanned 224,925 KVs,
  225 times the live set. No cut comes, so f stays where it was and no deleted KV ever becomes
  dead: R6 and R13 fail, and Frans's rule with them.
* Below the threshold an iteration takes gap / (s - u) steps, for a scan rate s and appends u
  ahead of the cursor. That also grows without a bound as u nears s.
* P8, 2.8 and 7, and 023-07, 5.5, call this a lengthening by random puts. It is no end, and
  with ordered puts.
* **Fixes.** (1) Main's scan at tStart: it already reads each value at the latest state
  (`Reclaim.step`, `db.getOne(Long.MAX_VALUE, ...)`), so a key deleted after tStart is not
  rewritten. (2) A scan quota in proportion to the transaction, at least twice its bytes by the
  same measure. With appends u at most the transaction's bytes, each step then gains at least
  half its quota, and the iteration ends within the data at tStart below E, divided by that
  gain. (2) needs an argument for steps the rewrite budget holds back, and the probes as tests.
* **A sketch of (2)**: the quota min(allowed, max(16 kB, 2 x the transaction's bytes)), about
  10 lines in `Reclaim.transactionCompleted`, behind a switch (diff in
  `/Users/f/fl/bench/2026-11-10/rev23/c/scratch-c/p8-quota-sketch.diff`). With it the queue
  with "/z" ends after 15 transactions (stream 932,496) and the ordered puts after 28; the
  other 1,630 unit tests pass. Not gated, and not argued in full.

### 2.7 K6, the dead hand

* **The main argument: sound** (code). `Cache3.deadStep` evicts an object only if
  `Eviction.detachable` says so, with the same compare-and-set as `Cache3.clockStep`. A value
  is unswizzled only under the condition of today's `unswizzleValues` plus "stored before the
  cut". So the dead hand is one more eviction schedule over detachable objects. The model's
  results for any such schedule (T-CACHE, T-READ, `tc_handles`) and the EVERY gates cover it.
  Its "dead after the cut" (P6, 1.1) is needed to avoid reloads, not for answers.
* **Readers: sound.** `unswizzleValue` runs under x's monitor and checks the pointee again.
  `KeyNode.setPointer` stores the position, then clears the object with release. A reader sees
  the object, or the position with no object: an ordinary stream pointer. A read below the
  first position expires if its time is before f (`Db.expiredIfReadBelowCut`).
* **`detachable` is complete** for what is held across transactions: the super root, the newest
  written top node, D, the record. Reclaim holds no node objects between steps (a new
  `MaintenanceFollower` each step). Main's scan at tStart reads nothing before the cut, since
  tStart > tEnd = f.
* **Cost: not "2 ms".** `deadStep` checks the time only before each part, so one step can take
  all 4,096 handles, each kept key node's pointers, and one copy of a map's handles
  (`Cache3.mapHandles`, one of `Cache3.maps()` shards). The report's maximum, 6.7 ms of CPU on a
  loaded F53, fits that. A round costs the resident table once a cut; nothing grows with history.
* **Risk:** the dead hand evicts right after every cut. A hole in the cut's guarantee that
  residency hides today will then show at once. That is good for the tests, as long as
  level3 and level4 run with it on.

### 2.8 K7, K8, and what crosses the mechanisms

* **SE** (K7): not checked; I took 021-28's review. It changes only the read path.
* **Format 6** (K8): the rerun rules change, so the format must change. The refusal must name
  2026.3 (format 5), as 023-07, 5.8 says.
* **Crash, power loss:** no new durable state beyond the records. The delete's changes are in its
  own record; a taken-back node is never written; the dead hand writes nothing. By argument;
  I ran no crash test.
* **Rule A, D:** an unlinked dirty node stays in D until written. It is needed for lookups
  before tt. P7, 6.3 reports 259 such nodes at 1M, gone within 10,000 drive transactions.
  Rule R and `linkD` with unlinked nodes in the section: not checked beyond the rerun's choices.
* **The model's assumptions:**
  * TREE: at any one time a node is named by one visible klong. LE-b's copy and RC's lift add a
    klong of tt while the old one is deleted or unlinked at tt.
  * A-COPY: `copyPointer` copies a current child's pointer.
  * A2: entries of tt only, behind tt's time klong.
  * A3: no node of tt left unreachable. That is the take-back's reason to exist.
  * Fault 12 breaks none of these. It breaks the record's own rule that every pointer names a
    written node.
  * All by reading. I did not run the trace checker.

### 2.9 The full set

* **F1, merges.** Not reviewed in depth. P5's gates are full (report). Its risks stay: the
  merge count of `mergeBound` is not proven, thrash is not measured, and siblings are read.
* **F2, (a).** Not checked. It changes the model's take and INV-1.
* **F3, (b').** Not checked. A rule of the same kind was unsound this morning (023-06, 18.7).
* **F4, the replaced queue.** Safe by the dead hand's argument: it evicts detachable objects.
  * Cost to readers before the newest time: every transaction that changes the index replaces
    the super root. A reader of a slightly older snapshot then reloads top nodes and split
    leaves that stay resident today. Not measured.
  * It drains at most 4,096 entries a transaction, whatever the transaction's size, and holds
    strong references. A mass delete grows it, and an idle database never drains it.
* **F5, `maintain()`.** Not checked.


## 3. The rule and the bound

| Part                      | Core as proposed             | Core without P8                     |
|---|---|---|
| R9, scans, latest time    | yes (UP; T3)                 | yes                                 |
| R9, earlier times         | yes, by I2 at every time     | yes                                 |
| R2, values of deleted KVs | not with a key after a queue | yes; one iteration later            |
| R2, R3, unlinked nodes    | as values                    | the cut after the next              |
| R3, R7, dead klongs       | bounded: B a node            | the same                            |
| R12 (b), underfill        | bounded, in keys ever put    | the same                            |
| R4, R14, memory           | after each cut (budget)      | the same; `noEvict()`: at a restart |
| R15, startup              | the delete's path, as main   | the same; the window in T1 at 1M    |
| R6, reclaim keeps up      | no (2.6)                     | yes, bounded by the data at tStart  |

* **The scan bound** is met in full at every available time for a database made in format 6.
  At a time t after a delete the emptied subtree is unlinked; before it, its keys were live.
  T3 measured the latest time only.
* **Dead klongs in live nodes** stay, at most B a node, until the node's next time split. The
  touch copies them forward on every iteration. Neither tier releases them; merges do in part.
  So Frans's "zero resources" is met only with a bounded allowance there. His answer to F1 was
  implied (023-02, 7.2), not given.
* **Without P8** the iteration in progress at a mass delete still scans every KV live at its
  tStart. The lag is that data divided by the step quota, in user transactions. In T1 at 1M
  the fixed drive of 4,000 is too short for it; P4 used 12,000 (P4, 3.6). It is bounded and in
  proportion to the data, as on `main`.
* **The window** (D's run of dirty top nodes) is in `main` and in the twin. P8 removes its
  trigger in T1; without P8, T1 at 1M fails C6 and C9 by it (P4, 3.6: D 178 against 94).
  Whether a later disturbance lengthens it is the open question (023-06, 18.6, item 3). If it
  does, D grows without a bound: an R14 and R15 fault that predates this work.


## 4. Simplicity

### 4.1 What is essential, and why

* **UP at the delete.** R9 holds with R forever, where reclaim never runs, so the cleanup
  cannot wait for reclaim. It cannot wait for a later pass either: until then every scan passes
  the trace again, and the sum in R9 is no longer bounded by the deletes. Only the delete can
  do it.
* **The climb, not only the leaf.** Unlinking only the leaf leaves emptied inner nodes linked:
  one in B of the leaves, passed by every scan.
* **LE-b.** UP must handle an emptied leftmost child. LE-b is the B-tree's sentinel key: no
  node off the path changes, and no reader needed a change (2.3). P1's relabel changed nodes
  off the path (023-07, 5.4).
* **The take-back.** Without it, a split's node emptied by tt is either left unreachable in a
  record (A3 broken: a Lean change), or left linked and empty (one per such transaction, for
  ever: R12 (a) and R9 broken).
* **The dead hand.** Y6 (b) asks for memory without the cache's pressure. A sweep by position
  after each cut is the plain way.
* **K4 and format 6.** A fix, and the consequence of new rerun rules.

### 4.2 What can go or wait

* **P8**: out of 2026.4 (2.6). Its gain is a shorter lag after a mass delete, T1's drive at
  1M, and no window in T1; its cost is a new liveness argument and its tests. It is not a
  rerun rule, so it can come later. A row without `endKey=` must then scan at tStart until its
  iteration ends. If it stays, it needs the quota in proportion (2.6) and level3 again.
* **SE**: with UP it is not needed for R9, as no emptied subtree is reachable. It is small,
  independent and decided (Y7). Keep it, or let it slip without a format cost.
* **RC**: not needed for the rule (R10's must is "no worse than today"). It is small and asked
  for (Y2). Keep it.
* **X5 (c)'s inner branch**: an assertion instead (2.2).

### 4.3 The smaller core, as a mechanism

1. **At each delete, by the writer, in the deleting transaction:** UP's climb with LE-b and RC
   as in P4. A split's node of tt that the climb empties is taken back, and every klong of tt
   naming it is repointed, in the parent and in the segment leaf above (2.2, the fix). Checked
   by UnlinkFuzz with transformed, unsorted keys at node sizes 4, 8, 14 and 30, I1 and I2
   after every transaction, the trace checker, and `DbShadowProbe`.
2. **Reclaim, as on `main`:** each step scans at tStart and reads each value at the latest
   state. Checked by level3 (C-CUT), and by a new liveness test: a queue with a key after it,
   which must end within a bounded number of steps. With the scan at tStart it ends in 15
   transactions (P8's branch with the scan switched back).
3. **After each cut, by the writer's thread between transactions:** the dead hand of P6
   (`83e1cb86`, without the CPU probe and the switches). Checked by `Eviction.testDeadHand`, the
   held-reader test, and level4.
4. **Before a transaction changes anything:** `dirtyNodeBound` by the nodes of the paths.
   Checked by a test against counted nodes, with chains of collapses.
5. Format 6 and the refusal naming 2026.3; SE as decided.

It leaves the four bounded rests of section 3: dead klongs, underfill, a lag of one iteration
after a mass delete, and the window. About 1,050 lines of Java.

### 4.4 Simpler designs I looked at and rejected

| Design                                   | Why not                                            |
|---|---|
| Reclaim alone cleans (RB, P3)            | no reclaim with R forever: R9 fails                |
| A live count in each klong; scans skip   | every klong grows; empty nodes stay reachable (R3) |
| No take-back; write the node unreachable | A3 broken: a change of the Lean model              |
| An emptied split node stays linked       | empty nodes pile up, one a transaction             |
| A transaction's deletes before its puts  | still nodes of tt emptied: LE-b's klong splits     |

### 4.5 Is anything in the full set needed for correctness?

No. Merges are for R12 (b), which Frans wants but did not require (F5). (a) and (b') are for
the window, which predates this work; (a) becomes a correctness fix only if the ratchet test
shows growth. The queue is memory before the cut, and `maintain()` is a drive without user
writes. Each is an efficiency or a wish.


## 5. Risk for 2026.4

### 5.1 What could regress

* **Correctness.** Fault 12 needs transformed keys out of order. With -ea it fails the transaction;
  without, the database does not start again. P8's fault shows as a stream that grows with no
  cut, as in U18-1. Neither is in a gate today.
* **Stream size.** With P8, an ascending mass delete at 1M writes 85.0 MB against 68.4, and the
  drive 5.5 against 13.9 (P8, 5.4). In all, 90.5 MB against 82.3: 10 % more.
  Without P8: P4's numbers.
* **Memory.** The dead hand frees after each cut. MEM is not measured on any branch, and Props
  MEM is at 129 to 130 against a limit of 131.
* **Time.** No T10 on any branch. Deletes do the climb, and the rerun does it again. A cold
  start at 50 MB or more after a mass delete has not been measured (R15).
* **The format.** Format 6 is new rerun rules. Every later change of UP's choices (fault 12's fix
  included) must land before the release, or it is another format.
* **The C port.** About 500 lines after the release; `cross.sh full` needs a new pin. Fault 12's fix
  must be in the rules that C copies.
* **Not new, not changed by either tier:** the last step of an iteration touches to the end of
  the key space at its own time (`Reclaim.step`, `touchTo = null`). With keys in time order,
  that is every key put during the iteration, in one transaction. A pause to measure (P1, R11).

### 5.2 What the proposed gates miss

* Keys out of order in one transaction: UnlinkFuzz and DagFuzz sort them.
* Reclaim's liveness with a key after the append point: no test has one. P8's own test,
  `testEndKeyBoundsTheScan`, has the queue as the last range.
* The combination: no gate has run on it (023-07, 7).
* A whole database emptied (the space root replaced by a leaf), and X5 (c).
* RC chains in `dirtyNodeBound`'s test.
* A cold start at 50 MB or more after a mass delete; the ratchet test; T10; C11.

### 5.3 Tests to add

1. `DbShadowProbe` as a unit test, and UnlinkFuzz with a `KeyTransformation` that reorders
   keys, at node sizes 4, 8, 14 and 30.
2. A reclaim liveness test: a queue of bounded size with one key after it, appends ordered and
   random. The iteration must end within 2 x (the data at tStart) / (the step quota) + 10 steps.
3. A unit test that deletes every key, and one that reaches X5 (c) at the leaf.
4. `dirtyNodeBound` against counted nodes with collapses of several levels in one delete.
5. RestartInvariance and StreamDigest's four modes with deletes and the dead hand on.
6. A cold start at sd 50 MB after a mass delete of 1M keys, warm and cold.
7. The ratchet test (023-06, 18.6, item 3), on `main` first: it decides whether (a) is a fix.


## 6. The claims

| Claim in 023-07                                  | Where  | Status                  |
|---|---|---|
| "Reclaim keeps up after a mass delete"           | 1, 5.5 | not in general (2.6)    |
| R6: "the iteration in progress ends"             | 3.2    | not with a key after it |
| R2, R13 met (P8, 5.1)                            | 3.2    | in T1's shapes only     |
| "random puts before E ... lengthen an iteration" | 5.5    | no end; ordered too     |
| a taken-back node is "in no record"              | 5.1    | false (fault 12)        |
| UnlinkFuzz checks pointers to taken-back nodes   | 5.1    | true; cannot see it     |
| a step: "at most 4,096 handles ... and 2 ms"     | 5.6    | 2 ms is not a bound     |
| `retarget` from `4c6bea65`                       | 6.1, 2 | method in `163fed3f`    |
| "P6 430" lines                                   | 6.5    | the dead hand is 169    |
| "about 1,200 lines" for the core                 | 1, 6.5 | supported (about 1,170) |
| P8's bytes "within the internal fraction"        | 5.5    | the total is 10 % more  |
| merges later: a refusal "or two rerun paths"     | 9.1    | true; the second small  |

* **Numbers I found as stated in the reports:** 4,036 and 270 (P5, 4.1); 150,000 (P5, 6); 292,
  263 and 11,612 (P6, 4.1); 712 to 858 and 24,113 (P6, 4.3); 190,272 (P6, 4.3); C-CUT 0 of 303
  and 0 of 163 (P8, 4); 85.0, 68.4, 5.5, 13.9 (P8, 5.4); 178 and 184 (P4, 3.6); 1.44 (P5, 4.1);
  4.82 against 6.78 (P5, 4.3). I did not measure them again.
* **The two rerun paths are small.** The rerun knows each record's format. Merges can run only
  for records of a later format, so putting merges off costs a switch, not a refusal.
* **Not checked:** SE's claims; "P8 alone removes the window's trigger in T1"; the gates of
  023-07, 3.3; the Lean claims of F2 and F3.


## 7. The parts: now, later or never

| Part                               | When  | Condition                                   |
|---|---|---|
| K1 UP, with the take-back          | now   | fault 12 fixed by rule; tests 5.3, 1 and 3  |
| K2 LE-b                            | now   |                                             |
| K3 RC                              | now   | fault 12's fix also in `takeBackRoot`       |
| K4 `dirtyNodeBound` by node        | now   | test 5.3, 4                                 |
| K5 P8, the scan at the step's time | later | or now with the quota in proportion; 5.3, 2 |
| K6 the dead hand                   | now   | without the CPU probe; its real bound named |
| K7 SE                              | now   | as decided; may slip, no format cost        |
| K8 format 6, the refusal           | now   | names 2026.3                                |
| F1 merges                          | later | a switch by record format                   |
| F2 (a)                             | later | sooner if the ratchet test shows growth     |
| F3 (b')                            | never | unless a measure shows a need               |
| F4 the replaced queue              | never | as a default; keep the code off or drop it  |
| F5 `maintain()`                    | later | no format change                            |


## 8. Questions for Frans

1. **P8 in 2026.4?** Your yes to Z14 asked for a probe first. P8 was that probe, and its tests
   had no key after the queue. As built, P8 can stop the cuts (2.6). Recommended: take it out
   of 2026.4 and keep `main`'s scan at tStart; bring it back later with a quota in proportion
   and the liveness test. The cost: a lag of one iteration after a mass delete; T1 at 1M needs
   a drive of 12,000, not 4,000, and shows the window. The other way: keep P8 with the quota
   in proportion (a sketch ends both probes, 2.6), and run level3 again.
2. **The take-back's rule** (D13, Z20). Approve the complete form: every klong of tt that names
   a taken-back node is repointed, wherever it is, and `spaceSplitInPlace` repoints the segment
   leaf's klong of tt in place instead of adding a second one. Recommended: yes, with the tests
   of 5.3, 1. It changes a rerun rule, so it must be in before format 6 is fixed.
3. **The window** (Z13). Without P8, T1 at 1M fails C6 and C9 by a run of dirty top nodes that
   `main` and the twin have too. Recommended: name it in C6 and C9 for 2026.4, run the ratchet
   test on `main` now, and treat (a) as a fix of its own if the run grows.
4. **Dead klongs in live nodes.** Both tiers keep them, at most B a node, until the node's next
   time split. Your answer to 023-02's F1 was implied, not given. Recommended: accept them
   for 2026.4.
5. **Merges** (Z12, D1). Recommended: later, with merges switched on by the record's format, so
   that 2026.4's databases stay readable without a refusal.
6. **The order of work.** Recommended: one integration branch with the smaller core (4.3) and
   the tests of 5.3, gated in full, then T10 and a cold start at 50 MB, before the tier is
   decided. The pieces have never run together.
