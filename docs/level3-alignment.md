# BergDB Level 3: the Java code and the Lean model

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, from 2026-10-16.
Work packages A2, R1 and later of bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md)).
Source commit `a66e4d9` (R1); line numbers below are at that commit, in
`java/src/bergdb/`.

Status, 2026-10-16: R1's version. The scope (section 1), α for reclaim
(section 2), the register (section 3, checked against the code at `75d3c2d`
in A2 and at `a66e4d9` in R1), the arguments for M32 and M38 (section 4)
and the safety argument in the model's terms, every step marked (section
5). To come: R7 the red list (section 6); R9 the outcome.

Level 3 is reclaim: the front of the stream is cut, so that the stream does
not grow forever. How Java does it is in [levels.md](levels.md), "Level 3:
reclaim", and in the class comment of `core/Reclaim.java`. The plan of item
001 aligns it with the model after the model has the cache (stage 2), since
reclaim's safety depends on what a written version names, which Level 4
decides (the plan, "How the levels depend on each other"). This document
says what "aligned" means for reclaim, as
[level2-alignment.md](level2-alignment.md) does for Level 2. The cache is in
[level4-alignment.md](level4-alignment.md).


## 1. Scope

* Reclaim's records: user transactions, reclaim steps and table stores, as
  records of the model; the touch; the first available time; cuts, decided
  and made.
* What makes a cut safe in the model (`CutOK`, the plan, 8.7), and the
  theorems T8, T9, T12 and T-SCHEME (the plan, 1.4, stage 3).
* Reads from the first available time on, and restarts from a cut stream.

Not in the model: when an iteration starts and how much a step rewrites
(the allowance; a policy, like the startup pos policy at Level 2); the
retain duration and the wall clock (the model gets f, not R); bytes,
durability and the order of file deletions
([level3-durability.md](level3-durability.md)); readers that expire while a
cut overtakes them (concurrency; decision D1 = A, levels.md, W1).


## 2. The mapping α for reclaim

Written in A2 as a draft from the plan's 8.1, completed in R1 (2026-10-16).
Times and records as in level2-alignment.md, 2.1: model time i is the time
of record R(i), and a Java lookup at time t is a lookup at the model time
max { i : tt(i) ≤ t }. Line numbers at `a66e4d9` (`core/Reclaim.java` and
`core/Db.java` are unchanged since `75d3c2d`).

### 2.1 Records

Every executed transaction is a record (`Db.executeInner`, 1349: `store()`,
1386, writes one record for each). With reclaim on, three kinds:

* **User transactions** (external): `Trans.isInternal()` false.
* **Reclaim steps**: internal transactions with `Trans.touch` set
  (`Reclaim.step`, 345; lines 431 to 439).
* **Table stores**: internal transactions without a touch that put the
  table (`Reclaim.storeTable`, 648).

Reclaim runs in `Reclaim.transactionCompleted` (262), which
`executeInner` calls at its end (line 1403), inside the write lock, after
the user transaction's record and `transExecuted`. It ignores internal
transactions (line 263), so reclaim does not nest. One call writes, in this
order, at most: a table store when an iteration starts (lines 271 to 280);
one step (282 to 288), followed by a table store if the step ended the
iteration (`step`, 472 to 485); a table store if a row became safe
(`markSafePositions`, 492, line 504); and a table store if a cut is decided
(`pretruncateIfPossible`, 574, line 612). The physical cut (`cutIfDurable`,
309, at line 292) writes no record. So between two user transactions the
model sees zero to five internal records, in that order, each an ordinary
transaction of the model: its own time (`dbClock.transactionBegin`), its own
startup pos and taking of D (`store`, 1407), its own entries.

A step that throws a `RerunException` writes no record (4.2).

### 2.2 T(i) and touch(i)

* **T(i) of a user transaction**: as at Level 2 (level2-alignment.md, 2.7).
* **T(i) of a step**: its value nodes with their keys: the rewrites, one
  `put(key, value)` for each key that the step's scan finds live at tStart
  and whose value at the step's own read time is stored before pCut (line
  393: `value != null && gd.tpos < it.pCut`), with the same bytes; and the
  current row, under `/#i/dreclaim/-current.txt`, a value computed by a
  value transformation during the transaction (lines 416 to 423) from the
  step's progress and the index bytes the step has made dirty
  (`Trans.dirtiedBytes`).
  The value transformation runs inside `putKvs` before that put
  (`kv.transformValue`); for the model it is just the value put. A rewrite
  is a new data node (a data node has one version), so after the step the
  key's value is the same bytes in a node created at the step's record.
* **T(i) of a table store**: one put, the serialized table under
  `/#i/dreclaim/-table.txt` (`storeTable`, 648; M37).
* **touch(i)**, for a step only: the index nodes that `Db.touchRange`
  (1570) visits for the key range (touchFrom, touchTo], touchFrom excluded,
  touchTo included, null for the first or last key (`Trans.touchFrom`,
  `touchTo`, set at lines 438 and 439 from the row's lastKey and the last key
  of the step's scan): every index node that a `GetMany` at the
  transaction's own time follows over the range through the writer's
  pointer follower, and the super root (`superRootAccessed`). `putKvs` runs
  the touch before the puts (1530 to 1538) and makes the visited nodes dirty
  at once (`endOfOp(true)`, 868; `makeDirtyIfNeeded`, 900), whether or not
  anything changes; `endOfTrans` (879) does not remove replaced nodes from
  D for a touch transaction. So touch(i) is computed on P@(i-1) at time i,
  and step 3 of record i marks touch(i) besides the access paths of T(i)
  (M17). The touch makes no entries.

The ranges of an iteration's steps cover every key: the first step starts
at lastKey = null, each next step after the last key of the one before, and
the last step (the scan's end of data) ends at null.

### 2.3 Iterations: positions and times

An iteration is a row of the table (`IterationInfo`): pStart, tStart, pCut,
lastKey, done, tEnd, pEnd, pSafe, cut. Each position is at a record
boundary and maps to the record that starts there; each time maps to a
model time.

* **pStart, tStart**: when an iteration starts, in the call after user
  record R(u): pStart = the stream length after R(u) (`t.nextPos`, line 267),
  so the record that starts there is the table store that follows; tStart =
  tt(u) (lines 275 and 276). The row is stored at once (line 279).
* **pCut**: the pStart of the previous iteration; the first iteration's own
  pStart (line 277). So c(it) is the record that starts at the previous
  iteration's pStart.
* **The scan** of every step is at tStart (line 353): it lists the keys live
  at model time u. The values are read at the latest time (lines 379 to
  384; the step's read time `t.readTime`, line 429).
* **tEnd, pEnd**: the time and the start position of the iteration's last
  step, R(e) (lines 481 and 482). The table store right after R(e) stores
  done, tEnd and pEnd (line 484).
* **pSafe**: in a later call, after user record R(v), when the current
  startup pos has reached pEnd: the stream length after R(v) (lines 492 to
  505). It maps to the record after R(v).
* **cut**: true once a cut is decided at the row (2.5).

The start condition (twice the startup distance of stream growth and a
quarter of the retain duration since the last start, no iteration in
progress, retention finite), the allowance of each step (lines 283 to 287)
and the size of a step are policy: they decide when the records come, not
what they are, and are not in the model (section 1).

### 2.4 fa(i), the first available time

`Reclaim.firstAvailableLookupTime` (141) changes only when a cut is decided
(line 621, after the table store of line 612) and when the database starts
(`initFromDb`, 516, lines 542 to 562): in both cases it is the tEnd of the
newest row marked cut in the table, 0 if none. So, as a function of the
records: **fa(i) is the model time of tEnd of the newest row marked cut in
the table as stored at or before R(i); 0 before the first cut** (Q5). It
never decreases (a cut needs `row.pCut > firstAvailablePos`, line 593, and
the newest cut row has the largest pStart) and is below the time of the
startup pos (2.5, condition 2). `firstAvailablePos` is the cut row's pCut:
c, as a position.

### 2.5 Cuts: decided, then made

A cut is decided in the call after user record R(u), at time tt(u), at the
newest row (largest pStart) that meets all of (lines 586 to 594):

1. done, and tEnd older than the retain duration: tt(u) - R > tEnd;
2. pSafe set and passed: the current startup pos (after the records of the
   call so far) at or after pSafe, so also after pEnd and pCut;
3. the last valid meta block names a transaction at pCut or later (line 591;
   recovery starts there);
4. pCut after the current firstAvailablePos (cuts move forward).

If that row is not yet cut, the rows that started before it are removed,
the row is marked cut, and the table is stored: record R(d), the decision
(lines 605 to 612). Then fa = tEnd and firstAvailablePos = pCut (621, 622).
In the model: **the cut decided at R(d) is at c = the record that starts at
the row's pCut, with f = fa(d) = the model time of tEnd.**

The physical cut comes later: `cutIfDurable` (309) calls `pretruncate(pCut)`
when the stream is durable up to its length right after R(d) (line 626).
`FileStream.pretruncate` deletes whole files below pCut, so the stream's
first position moves to the start of the file that holds pCut, at or below
it; `MemoryStream` keeps whole 1 MB arrays; `CutStream`, a test stream,
refuses every read below the exact position (M35). The model's cut is the
decided c: Java can still read some bytes below c, never bytes the model
keeps that Java lost.

### 2.6 Reads, and what is not in the model

* A read at a time before fa is refused at admission
  (`LookupTimeNotAvailableException`; `Db.getOneInternal`, 1068, lines 1073
  to 1080; `getMany`, 1116, lines 1131 to 1138). The model requires reads
  from f on only (M36).
* A read admitted before a cut can reach bytes the physical cut then
  removes; it expires (`Db.expiredIfReadBelowCut`, 1170) if its actual
  lookup time is now before fa. Concurrency, outside the model (decision
  D1 = A; levels.md, W1); measured by `ReclaimReaders` and the Level 3 soak (WP
  P2).
* Not in the model: the wall clock and the retain duration (condition 1 is
  a policy that chooses f), the meta block condition (3: bytes and
  recovery, [level3-durability.md](level3-durability.md)), durability and
  file deletion, the allowance and the iteration spacing.

### 2.7 For the trace (R2)

What a format-2 trace of a reclaim run needs per record, from the above:
the kind (user, step, table store); for a step, its touched nodes, as ids
(TOUCH lines); the record's fa (FA, only when it changes: at a decision R(d)
and after a restart); for a decision R(d), the cut row's pCut as the record
c that starts there (CUT); and, at the record after which `cutIfDurable`
made it, the physical first position (PHYSCUT). Positions as record
numbers, times as model times.


## 3. The register

Checked against the code at `75d3c2d` in A2, and again at `a66e4d9` in R1,
2026-10-16 (line numbers at `a66e4d9`). Columns as in level2-alignment.md,
section 6. Status: open (o), resolved in a WP (WP name), closed (c). M17 is
reopened from level2-alignment.md.

| | Mismatch or open question | Java | Model | Proposed resolution | Stage, WP, status |
|---|---|---|---|---|---|
| M17 | Reclaim's touch marks nodes without adding entries: every index node the range traversal follows, and the super root, get dirty; the marks stay when the transaction replaces a node | `Db.touchRange` (1570); `endOfOp(true)` (868) in `putKvs` (1521), lines 1530 to 1538; `endOfTrans` (879) skips touch transactions | step 3 (`markOf`) | Model: `Spec.touch`, T13' (α: 2.2) | 3: R3; o |
| M32 | Java keeps the first available time in the reclaim table, a value in the database, and reads it after startup (Codex's review of 09, finding 5): `Db.startInner` calls `DbStarter.start` (through `startDb`) and then `reclaim.initFromDb` (line 511), which reads the table through the reconstructed database | `Reclaim.initFromDb` (516); `Db.startInner` (486), line 511; `Reclaim.pretruncateIfPossible` (574) | — | Model: fa(i) in records, by α (2.4, Q5); argued in 4.1 that Java's startup needs f only after reconstruction, if it reads nothing before c (T8, R4) | 3: R1 (argued), R3, R4; o |
| M33 | After a cut, Java cannot read the id of a slot's target below the cut: a stored key node holds child positions, not ids, so the id is read from the target's header, and `resolvePointers` skips a stream slot below the stream's first position (Codex's review of 09, finding 2) | `NodeCollection.resolvePointers` (317), line 337; `StoredKeyNode.toLongs` (50) | `javaTest` (by id) | Model: version stubs keep positions; CutOK must imply that no such slot of a node in D names a node in D; otherwise a code change (5, step 7) | 3: R3 to R5; o |
| M34 | Java writes every taken node, also nodes that no lookup from f on reaches (F1-008-08's "needed" nodes) | `Db.store` (1407); `TransSeq.take` (83) | step 6 | Model: show that it changes no record after a safe cut (T12), or a needed test in code (5, step 7) | 3: R5; o |
| M35 | A cut is decided (in the table, with the first available time and position) before it is made (when the stream is durable past the table); `FileStream` deletes whole files, `MemoryStream` whole 1 MB arrays; `CutStream` (a test stream) refuses reads below the exact cut | `Reclaim.pretruncateIfPossible` (574), `cutIfDurable` (309); `stream/FileStream.pretruncate` (262); `storage/BufferedStream.pretruncate` (446); `stream/CutStream.read` (60) | `cutStream` | α: the model's cut is the decided position; the physical cut comes later, at the same or a lower position (2.5) | 3: R1 (α); R2 checks it |
| M36 | Reads before f are refused (`LookupTimeNotAvailableException`), and an admitted read may expire when a cut overtakes it (D1 = A): a `ReadBelowFirstPosException` below the cut becomes an expiry if the read's actual time is now before f | `Db.getOneInternal` (1068), lines 1073 to 1080; `Db.getMany` (1116), lines 1131 to 1138; `Db.expiredIfReadBelowCut` (1170) | `view` (every time) | Model: reads required from f on; expiry is concurrency, outside the model (2.6) | 3: R3; o |
| M37 | Reclaim stores its table and the current row as values under internal keys (`/#i/dreclaim/-table.txt`, `/#i/dreclaim/-current.txt`), in internal transactions; the row's value is computed by a value transformation during the step | `Reclaim.storeTable` (648); `Reclaim.step` (345), lines 416 to 423 | T(i) | α: ordinary puts; T(i) is what the record stores (2.2) | 3: R1 (α); R2 checks it |
| M38 | A reclaim step can fail with a `RerunException` (a conflict with its read time) and then writes no record; the step is tried again at a later transaction. A table store cannot fail so (`Bug`) | `Reclaim.step` (345), line 449; `storeTable` (648), line 657; `Db.stmCheckConflicts` (1474), called at line 1362 | — | α: no transaction; nothing to model (argued in 4.2; the exception cannot occur today) | 3: R1 (argued) |
| M41 | After a restart from a cut stream, startup reads D's nodes at their newest section versions or stored positions, and the root chain from topPos | `DbStarter.canonicalNode` (455), `topNodeOfLastTransaction` (293), `findSuperNodeAtStartupTime` (263) | `startup` | CutOK must cover them. For the root chain, review-13-claude, 4.3: a search at a time q loads, besides its answer, only tops created at or after q; so from tEnd on, the tops created after tEnd and the top live at tEnd (5, steps 4 and 6) | 3: R3 to R5; o |

Findings of A2: none beyond the plan's list for Level 3. Noted for R1: the
touch marks the super root of the step's time (through
`superRootAccessed`), which review-13-claude's argument about the root chain
after a cut (M41) uses. Findings of R1: none that needs a new row. Two
notes: the conflict check that M38 is about cannot fail today (4.2); and
`pSafe` is the stream length after the user record of the call that sets it,
which is before that call's own internal records (2.3), so it is a little
earlier than "the stream length when the startup pos passed pEnd" of
levels.md, which the argument in section 5 allows (step 5).


## 4. The arguments

### 4.1 M32: Java's startup needs f only after it has reconstructed the database

The model's startup reads the last record's fa first and reconstructs P
for the times from f on. Java's `Db.startInner` (486) reconstructs first
(`DbStarter.start`, through `startDb`, line 506), and reads f afterwards
from the table (`reclaim.initFromDb`, line 511). The two agree if Java's
reconstruction neither uses f nor reads anything that the cut removed.

1. **Nothing in the reconstruction uses f.** `DbStarter` finds the meta
   blocks and the startup section, reruns the section, and resolves the
   root chain and D; none of it reads `Reclaim` (which has fa = 0 until
   `initFromDb`). After `initFromDb`, f is used only by the admission of
   reads (2.6) and by the next cut decision (condition 4 of 2.5).
2. **What the reconstruction reads.** (a) The meta blocks and the startup
   section, from the startup pos of the last record to the end of the
   stream (`Db.startInner`: `nodeStream.recover`, line 493, and
   `readTransactions`, line 502; `DbStarter.doOrdinaryStartup`, 121). (b) The
   root chain: the top node that the last record names (topPos;
   `topNodeOfLastTransaction`, 293) and the search for the super root at
   the startup time (`findSuperNodeAtStartupTime`, 263). (c) The rerun of
   the section's transactions (`rerunTransactions`, 344), which follows the
   paths of their keys at their own times, all at or after the startup
   time. (d) D's nodes: the canonical object, the newest version in the
   section, or the version at the position stored with the got-dirty id
   (`canonicalNode`, 455). Then (e) `initFromDb` reads the table and the
   current row at the latest time.
3. **None of it is before c, given a safe cut.** (a) is after c: the
   decision needed the startup pos at pSafe or later (2.5, condition 2), and
   the startup pos never decreases. (b), (c) and (e) read versions of nodes
   at times at or after the startup time, which is after f (the record of
   pEnd is before the startup pos): CutOK's parts 2 and 4 (section 5) say
   that these versions are at c or later. (d) is CutOK's part 3.
4. So, with CutOK, Java's startup from the cut stream is the model's
   startup from the cut stream with f supplied after the reconstruction,
   and the order does not matter. That is T8 (WP R4) for Java's startup,
   with M41 (the root chain and D) as its Java-specific part.

Marks: step 1 checked (code, above); step 2 checked (code); step 3 to prove
(R4, R6); it is also tested, since every test with `CutStream` refuses a
read below the cut, and `ReclaimStress`, `RestartInvariance` with reclaim and
`level3.sh` restart after cuts.

One more place reads before `initFromDb` sets f: a read by another thread
while `start()` runs would pass admission with fa = 0. `start()` has not
returned then; the API does not offer reads before it returns.

### 4.2 M38: a step that throws a RerunException is no transaction

`Db.executeInner` checks conflicts (`stmCheckConflicts`, 1474, called at
line 1362) under the write lock and before `dbClock.transactionBegin`
(1365), `putKvs` and `store`: the exception leaves no record, uses no time,
and changes no node. `Reclaim.step` returns at once (line 449) and has not
changed the row (`it.set(next)` is at line 470), so the next call repeats
the step from the same lastKey. The model sees no transaction: nothing to
model.

The check cannot fail today. A step reads its keys (`b.keyRead`) at
`stepLookupTime`, the latest time when its reads begin (lines 379 to 384),
and executes inside the same hold of the write lock that ran the user
transaction (`transactionCompleted` is called at line 1403): no transaction
runs between the reads and the check, so no key was modified after the read
time. A table store reads nothing; `storeTable` treats the exception as a
`Bug` (line 658).

### 4.3 M35 and M37: by α

Both are settled by the mapping (2.5 and 2.2); R2's traces check them
(CUT and PHYSCUT lines; the table and the row as ordinary puts).


## 5. What makes a cut safe

The argument of levels.md ("Level 3: reclaim") in the model's terms, for a
cut decided at R(d) for the iteration `it` (2.5): c is the record at
it.pCut and f the model time of it.tEnd, the last step R(e). Each step is
marked **proved** (with the theorem), **to prove** (with the WP),
**checked** (with the code or test) or **assumed**. "CutOK c f" is the
plan's sketch (8.7), which R3 defines:

1. c ≤ the record of f ≤ s, the startup pos;
2. every node reachable at some time from f on has its latest version at c
   or later, or none;
3. every node in D has its latest version at c or later, or none, and no
   slot of a node in D below c names a node in D (M33);
4. top(k) and the root children that reads from f on need are at c or
   later.

The steps:

1. **Order: c ≤ rec(f) ≤ s.** pCut is the previous iteration's pStart (or
   its own), before the iteration's records; R(e) is a step of the
   iteration; the decision needs the startup pos at pSafe ≥ (the record
   after) pEnd. **Checked** (code: 2.3 and 2.5); R3's `CutOK` states it.
2. **Values live from f on are at c or later.** A key live at a time t ≥ f
   has a data node created at the key's last put before t. If its last user
   put before t came after tStart, that record is after pStart, so after c.
   Otherwise the key was live at tStart with no user put up to t, so the
   step whose range holds it (at a time before tEnd ≤ t) found it in its
   scan, read the same data node, and rewrote it if that node was stored
   before pCut: a new data node at that step, after c. In every case the
   data node live at t is at c or later. **To prove** (R6, T-SCHEME), from the
   coverage of the ranges (2.2) and the rewrite rule (line 393); **checked**
   by `Reclaim.Tester.testIterationRewritesAllOldValues` and
   `testLookupsFromFirstAvailableTime`, and by every `CutStream` test.
3. **Index nodes reachable from f on get an entry or a mark after c.**
   Every index node that is current at the time of the step whose range
   meets its key range is in that step's touch(i) (2.2), and every index
   node created later is new. A key range only shrinks when a node splits,
   so an index node reachable at a time t ≥ f either existed at the step
   time of every range it meets and was touched, or was created after that.
   Deleted-only nodes and the segment subtrees of deleted long keys are
   visited by the range traversal too (bug 3 of levels.md). **To prove**
   (R6, from Spec.touch and TouchOK of R3, with the coverage of the ranges
   and TREE); the B-tree's key ranges are Java's, not the model's: R6 states
   the coverage as an assumption on `Spec.touch` (as F1-008-07, section 8,
   "Reclaim coverage") and R2's traces **check** it (TOUCH lines against the
   nodes reachable at the step's time).
4. **The root chain.** The super root at each step's time is touched
   (`superRootAccessed`); a search at a time q ≥ f loads, besides its
   answer, only tops created at or after q (review-13-claude, 4.3), and its
   answer is the top live at q, which is the super root at some step time,
   or the top live at tEnd, or created after tEnd. **To prove** (R6, with
   M41; part 4 of CutOK).
5. **Every touched or new node is written after its mark.** A node marked
   (dirty) in record j is taken and written once the startup pos passes j
   (the take rule: step 6 of the model; `TransSeq.take`). The decision
   needs the startup pos at pSafe, after pEnd, after every step of the
   iteration; so every node of steps 3 and 4 has a version at c or later,
   and so does every node created after it (CutOK part 2 for index nodes).
   The take rule is the model's step 6 (a definition), and Java's take is
   **checked** against it by the Level 2 conformance (level2-alignment.md,
   section 13); the combination with steps 2 to 4 is **to prove** (R6).
6. **References after pSafe.** A parent written after its touch, before
   a child of D was written, names the child's version before the cut; Rule
   A then keeps the parent in D (it points to a node of D), so it is
   written again after the child. pSafe is the stream length after the user
   record of the call in which the startup pos passed pEnd (2.3): every node
   of D at that moment got dirty before pSafe, so it is written once the
   startup pos passes pSafe, now naming its children's versions after c.
   This gives CutOK part 3's first half for the nodes reachable from f on,
   and part 4 for the root children. **To prove** (R6); no test needs the
   wait for pSafe (levels.md, "Evidence"); it is kept from this argument.
7. **Nodes in D that no read from f on reaches.** Rule A can keep an
   historical node in D (a node no longer current, with a child in D); it
   is not reachable from f on, and steps 3 to 6 say nothing about it. Its
   slots may name versions before c (M33), and Java writes it when it is
   taken (M34). CutOK part 3 asks that no slot of a node in D below c names
   a node in D. **To prove** (R5, T12: such nodes either are written again
   after c, or their writes change no record after a safe cut), or a code
   change (R8). This is the delicate case of the plan's 8.7.
8. **The time condition: tEnd older than R.** A policy that chooses f; the
   model allows any f with CutOK. **Assumed** (outside the model); the
   retention guarantee (lookups in [now - R, now] work) is **checked** by
   `ReclaimRetentionTester`, `ReclaimStress` and the soak.
9. **The meta block condition and durability.** Recovery starts at the
   transaction that the last valid meta block names, so that must be at c
   or later (condition 3 of 2.5), and the cut waits until the table that
   marks it is durable. Bytes and recovery, outside the model. **Checked**
   (f-test `testCutKeepsMetaBlockTransaction`; level3-durability.md).
10. **Reads after the cut, and restarts across cuts.** With CutOK: reads
    from f on through the cut stream give the logical view (T9, **to prove**
    in R4), startup from the cut stream gives the same lookups from f on and
    the same D (T8, R4; 4.1 for Java's order), and a run with restarts and
    cuts writes the same records as the run without them (T12, R5). Java:
    **checked** by `RestartInvariance` with reclaim (the same stream byte
    for byte, with and without restarts), `ReclaimStress`, `CrashTest` with
    reclaim, `level3.sh`, and the soak's checks after cold restarts
    (WP P2).

What is left to prove, in short: steps 2 to 4 and 6 (R6, T-SCHEME: Java's
scheme gives CutOK), step 7 (R5, or a change in R8), and step 10 (R4, R5).
What is assumed: the policies of steps 8 and 9, and that a step's range
traversal visits every node whose key range meets the range (step 3), which
R6 takes as an assumption on the touch and R2 checks.


## 6. Red list

WP R7.
