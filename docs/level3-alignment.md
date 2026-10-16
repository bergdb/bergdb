# BergDB Level 3: the Java code and the Lean model

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, from 2026-10-16.
Work package A2 and later of bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md)).
Source commit `75d3c2d`; line numbers below are at that commit, in
`java/src/bergdb/`.

Status, 2026-10-16: A2's draft. The scope (section 1), a first α for
reclaim (section 2) and the register (section 3), checked against the code.
To come: R1 completes α, writes the arguments for M32 and M38, and the
safety argument in the model's terms; R7 the red list; R9 the outcome.

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


## 2. The mapping α for reclaim (draft)

A draft, from the plan's 8.1. R1 completes it. Times and records as in
level2-alignment.md, 2.1.

* **Records.** Every executed transaction is a record: user transactions,
  reclaim steps and table stores. Reclaim runs in `Reclaim.transactionCompleted`
  (262), which `Db.executeInner` (1349) calls after a user transaction's
  record, under the write lock; its steps (`step`, 345) and table stores
  (`storeTable`, 648) are internal transactions (`Trans.isInternal`),
  executed through `Db.execute` inside the same lock, each with its own
  record. `transactionCompleted` ignores internal transactions, so reclaim
  does not nest. A step that fails with a `RerunException` writes nothing
  (line 449; M38).
* **T(i)** of a step: its stored value nodes with their keys, as at Level 2
  (level2-alignment.md, 2.7): the rewritten values (`b.put(kvt.key, value)`
  for each live value stored before pCut) and the current row, under the
  internal key `/#i/dreclaim/-current.txt`, whose value a value
  transformation computes during the transaction (lines 416 to 423). A table
  store: the table, under `/#i/dreclaim/-table.txt` (M37).
* **touch(i)**: the index nodes that `Db.touchRange` (1570) marks in
  transaction i: every index node that the traversal of the step's key
  range at the transaction time follows, through the writer's follower, and
  the super root (`superRootAccessed`). They get dirty at the end of the
  touch (`endOfOp(true)`, 868), before the puts (`putKvs`, 1521), and keep
  their marks also if the transaction replaces them (`endOfTrans`, 879,
  skips touch transactions) (M17).
* **fa(i)**: the first available time as of R(i): `Reclaim.firstAvailableLookupTime`,
  the tEnd of the newest row marked cut in the table as stored at or before
  R(i), as a model time; 0 before the first cut. Java sets it when it decides
  a cut (`pretruncateIfPossible`, 574) and, after a restart, from the table
  (`initFromDb`, 516) (M32).
* **A cut** decided at R(i): `pretruncateIfPossible` marks the row cut and
  stores the table in R(i); c is the record that starts at the row's pCut,
  and f = fa(i), its tEnd. The physical cut comes later
  (`cutIfDurable`, 309): when the stream is durable up to the length at the
  decision, the stream's first position moves to pCut or, for `FileStream`
  and `MemoryStream`, to a lower position (whole files, whole 1 MB arrays)
  (M35).
* **Iteration positions and times**: pStart, pCut, pEnd and pSafe are
  stream positions at record boundaries; each maps to the record that
  starts there. tStart and tEnd are transaction times; each maps to a model
  time (level2-alignment.md, 2.1).


## 3. The register

Checked against the code at `75d3c2d` in A2, 2026-10-16. Columns as in
level2-alignment.md, section 6. Status: open (o), resolved in a WP (WP
name), closed (c). M17 is reopened from level2-alignment.md.

| | Mismatch or open question | Java | Model | Proposed resolution | Stage, WP, status |
|---|---|---|---|---|---|
| M17 | Reclaim's touch marks nodes without adding entries: every index node the range traversal follows, and the super root, get dirty; the marks stay when the transaction replaces a node | `Db.touchRange` (1570); `endOfOp(true)` (868) in `putKvs` (1521); `endOfTrans` (879) skips touch transactions | step 3 (`markOf`) | Model: `Spec.touch`, T13' | 3: R3; o |
| M32 | Java keeps the first available time in the reclaim table, a value in the database, and reads it after startup (Codex's review of 09, finding 5): `Db.startInner` calls `DbStarter.start` (through `startDb`) and then `reclaim.initFromDb` (line 511), which reads the table through the reconstructed database | `Reclaim.initFromDb` (516); `Db.startInner` (486), line 511; `Reclaim.pretruncateIfPossible` (574) | — | Model: fa(i) in records, by α (Q5); an argument that Java's startup needs f only later (R1) | 3: R1, R3; o |
| M33 | After a cut, Java cannot read the id of a slot's target below the cut: a stored key node holds child positions, not ids, so the id is read from the target's header, and `resolvePointers` skips a stream slot below the stream's first position (Codex's review of 09, finding 2) | `NodeCollection.resolvePointers` (292), line 313; `StoredKeyNode.toLongs` (50) | `javaTest` (by id) | Model: version stubs keep positions; CutOK must imply that no such slot of a node in D names a node in D; otherwise a code change | 3: R3 to R5; o |
| M34 | Java writes every taken node, also nodes that no lookup from f on reaches (F1-008-08's "needed" nodes) | `Db.store` (1407); `TransSeq.take` (83) | step 6 | Model: show that it changes no record after a safe cut (T12), or a needed test in code | 3: R5; o |
| M35 | A cut is decided (in the table, with the first available time and position) before it is made (when the stream is durable past the table); `FileStream` deletes whole files, `MemoryStream` whole 1 MB arrays; `CutStream` (a test stream) refuses reads below the exact cut | `Reclaim.pretruncateIfPossible` (574), `cutIfDurable` (309); `stream/FileStream.pretruncate` (262); `storage/BufferedStream.pretruncate` (446); `stream/CutStream.read` (60) | `cutStream` | α: the model's cut is the decided position; the physical cut comes later, at the same or a lower position | 3: R1; o |
| M36 | Reads before f are refused (`LookupTimeNotAvailableException`), and an admitted read may expire when a cut overtakes it (D1 = A): a `ReadBelowFirstPosException` below the cut becomes an expiry if the read's actual time is now before f | `Db.getOneInternal` (1068), lines 1073 to 1080; `Db.getMany` (1116), lines 1131 to 1138; `Db.expiredIfReadBelowCut` (1170) | `view` (every time) | Model: reads required from f on; expiry is concurrency, outside the model | 3: R3; o |
| M37 | Reclaim stores its table and the current row as values under internal keys (`/#i/dreclaim/-table.txt`, `/#i/dreclaim/-current.txt`), in internal transactions; the row's value is computed by a value transformation during the step | `Reclaim.storeTable` (648); `Reclaim.step` (345), lines 416 to 423 | T(i) | α: ordinary puts; T(i) is what the record stores | 3: R1; o |
| M38 | A reclaim step can fail with a `RerunException` (a conflict with its read time) and then writes no record; the step is tried again at a later transaction. A table store cannot fail so (`Bug`) | `Reclaim.step` (345), line 449; `storeTable` (648), line 657 | — | α: no transaction; nothing to model | 3: R1; o |
| M41 | After a restart from a cut stream, startup reads D's nodes at their newest section versions or stored positions, and the root chain from topPos | `DbStarter.canonicalNode` (451), `topNodeOfLastTransaction` (289), `findSuperNodeAtStartupTime` (263) | `startup` | CutOK must cover them. For the root chain, review-13-claude, 4.3: a search at a time q loads, besides its answer, only tops created at or after q; so from tEnd on, the tops created after tEnd and the top live at tEnd | 3: R3 to R5; o |

Findings of A2: none beyond the plan's list for Level 3. Noted for R1: the
touch marks the super root of the step's time (through
`superRootAccessed`), which review-13-claude's argument about the root chain
after a cut (M41) uses.


## 4. The arguments

WP R1: M32 and M38.


## 5. What makes a cut safe

WP R1: the argument of levels.md, "Level 3: reclaim", in the model's terms
(the plan, 8.7), every step marked as proved (R4 to R6), checked or assumed.


## 6. Red list

WP R7.
