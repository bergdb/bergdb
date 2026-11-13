# 027-11. Startup

Created 2026-11-13 by Frans Lundberg. Status: a draft, for review (027-04,
section 5.2).

Part 7 of 027 (027-04, section 2.3; Levels 1 and 2): from the stream to a
running database. The rule as `main` has it at 03282d8c (2026-11-13),
read from the code. It replaces 027-01's `sis-model.md`, section 6.2, and
`levels.md`, section 4 and the startup points of section 5. The bytes are
027-03's (sections 6, 7, 8 and 14); the take, D, Rule A and the startup
pos policy are part 6's (until it is written, 027-01's `sis-model.md`,
sections 5 and 6.1); a first touch after a start is part 8's; reclaim's
part of a start is 027-13, section 1.9. Each claim carries one status
word of 027-04, section 2.2.


## 1. What it does

A start makes a running database of the end of the stream. It completes
a torn last record as an aborted one, finds the startup pos s in the
last record, reads the startup section, makes the canonical objects of
the section's index nodes, finds the super root at the startup time,
reruns the section's transactions, rebuilds D from the stored got-dirty
ids and links D's pointers (rule 4). Every other node is read at its
first touch. A start appends nothing but a new database's creation and
recovery's fill.

### 1.1. Terms and constants

* **R(i), T(i)**: record i and its transaction; **k**, the last
  committed record. **M** 128, a meta block's size; **MD** 200,000, the
  meta block distance (027-03, section 6).
* **s**, the startup pos: R(k)'s startupPos, a record's position (0 is
  read as 128, the first record). **ts**, the startup time, R(s)'s time.
  **The startup section**: R(s+1), ..., R(k), read with R(s); T(s) is
  not rerun. **sd**: the startup distance of the last valid meta block.
* **topPos**: R(k)'s position of the newest written top node. **gd(j)**:
  R(j)'s got-dirty pairs (id, position). **prevPos**: the position of
  the version before, which a key node version names. A **vpos** (odd)
  is the id of a node not yet written; the nodes that T(j) makes get the
  vpos after R(j)'s position, in the order made.
* **Rule R**: a pointer to a node with a version in R(s), ..., R(k)
  names its newest version there, whatever position it holds. **Rule
  4**: each pointer of a node of D to a node with a canonical object
  holds that object's handle.

### 1.2. The checks before recovery

In this order, under the write lock and `readSync`; from step 2 on, a
refusal has written nothing:

1. **An empty stream** is created: meta block 0 (lastTrans −1, sd, the
   node size, the builder's id or a random one, the time) and the
   primordial record, a super root and an empty key node: 272 bytes
   (`Db.CREATION_LENGTH`, since 024-25). With `created.txt` (the Pub
   API) the creation is synced first (015-01).
2. **An incomplete creation** is refused (`DatabaseNotCreatedException`,
   005-33): a stream not cut and not longer than the creation, whose
   bytes begin as a meta block of this version; its block, if complete,
   valid and naming no record; its record, if begun, cut, or failed.
3. **The last valid meta block**: of the blocks complete in the stream,
   from the last down to the first at or after the first position, the
   first whose last byte is 10. Each block read must have the magic and
   the version 154: else a `StreamFormatException` (SFE) that names the
   causes (020-28), or a `VersioningStreamException` (005-40). None
   valid: an SFE.
4. **Its node size**: 0 is refused (a stream before 2026-10-27, 005-50);
   above 62 is a damaged block; another than the start's (30 but in
   tests, 026-08) is refused.
5. **Its lastTrans**: −1, or from max(128, the first position) to below
   the block (019-34); else an SFE.

### 1.3. Recovery

With L the stream's length, B the last valid block and n(p, z) the
position after a record of z bytes at p, meta blocks skipped:

    if L > 0 and L mod MD < M: append the rest of the block, zero but
        the magic and the version: an invalid block          (005-27)
    the meta block in memory := B, whole, its reserved bytes too
    p := B.lastTrans, or 128 if −1
    loop:
        r := the record bytes from p to the end; if r = 0: done
        if r < 5: complete the size field and byte 4    (027-03, 7)
        z := the size at p; if z < 5: an SFE
        if r < z: append z − r zeros; done          (last byte 0)
        p := n(p, z)

A torn last record becomes an aborted one, which every walk skips. That
is 014-01's contract (section 7; Frans, 2026-11-05): the storage keeps a
prefix of what was appended, a start recovers only a truncated tail, and
other damage is refused as far as the checks see it.

### 1.4. The startup pos and the section

    s := 0;  last := none
    for each committed record R from B.lastTrans (128 if −1) to the end:
        parse R whole (format 7, else refused)
        refuse unless 0 <= R.startupPos <= R's position, a multiple
            of 8, and 0 or at least 128                    (015-75)
        s := R.startupPos;  last := R's position
    the meta block in memory: lastTrans := last;  sd := its sd
    section := every committed record from s (128 if 0) to the end,
        parsed; the record at s must be committed          (005-28)
    the clock's last time := the last record's time

Then the section is validated (005-75), with or without `-ea`: record
positions at least 128 and strictly increasing; times from 0 to 2^56 − 1
and strictly increasing; each node's position valid; each key node valid
at ts (a klong at least, its sizes, its last time index, its times
strictly increasing). A violation is an SFE.

### 1.5. The section's nodes

A section of one record at 128 is a new database: its top node and key
node become canonical, linked. Otherwise:

1. **The maps.** newById: the id of each index node with a version in
   R(s), ..., R(k) to the position of its newest version there, top
   nodes included. posToId: the position of every index node version
   there, and the prevPos each names, to the node's id. posMap: the
   newest version of each index node, but not one made after ts (a top
   node whose root time, a key node whose first time, is after ts), and
   the value nodes of R(s).
2. **Rule R where the id is known without a read**: a pointer of a
   posMap node whose position is a vpos (its id) or in posToId moves to
   newById's position, if that is newer. The others get Rule R at their
   first follow (part 8) or at the writer's resolve.
3. **The cut back**: every key node version of the section loses its
   klongs after ts. Then no stream pointer of a posMap node (of a key
   node, its key klongs) may be −1 or a vpos: else an SFE.
4. **Memory pointers** between posMap nodes, by exact position, each
   pointee of its pointer's type (019-32). The posMap nodes become
   canonical. Rule R (newById, s, ts) goes to the node collection for
   the process's life; until the start ends, a key node version of the
   section read through a pointer is cut back to ts, and one from before
   the section must have no time after ts (021-12).

### 1.6. The super root

    p := R(k).topPos; refuse −1 or a vpos
    id := posToId[p], or the id in the node header at p
    refuse if newById[id] exists and is not p           (015-75)
    x := posMap's node at p, or id's canonical object, or the version
         at p made canonical; refuse it if not a top node
    refuse unless x is the super root at ts that x's skip pointers give

The newest written top node is the super root at ts: a top node is
written only after the startup pos has reached the transaction that made
it (011-11, section 8.3). Until format 5 (2026-10-15) the start looked
for the newest top node in the section, which need not hold one (011-11,
M18). x is the tree's root.

### 1.7. The rerun and D

For each j from s + 1 to k, in order:

1. **The puts.** Each value or delete node of R(j), in stored order (key
   order), is put at T(j)'s time through the writer, which makes each
   node it reaches canonical; deletes and merges are rerun as format 7
   has them (part 4). A node made gets the next vpos as its id; if R(j)
   holds a node with that id, its position (a value its offset, 005-34);
   an index node with a version in the section, newById's position. A
   key node made and taken back is dropped (023-05, P4).
2. **D.** For each pair (id, p) of gd(j): id's canonical object; or the
   version at newById[id], or at p if p is a position, whose id must be
   id (015-75), a key node validated and cut back to ts. It is made
   canonical and dirty and joins T(j)'s got-dirty nodes. None: an SFE.
3. **The take's state.** T(j)'s time, position, startupPos, last
   position and own bytes (its values' bytes and 48; 005-49) join the
   take's queue (part 6).

D is rebuilt from the stored ids, not from the rerun's marks: a reclaim
step's touch is not stored, and a node that Rule A kept dirty got dirty
in the record that wrote it (`DbStarter.canonicalNode`'s Javadoc;
024-07). The node table's resident bytes are then counted again (019-21).

### 1.8. Rule 4, by position

    byPos := the live handle of each canonical object, by its position
    for each node x of D, each pointer i of x to an index node that holds
            no handle and names p (not −1):
        skip if p is a position below the stream's first position (M33)
        id := p if a vpos, else posToId[p], if there
        h := id's live handle if id is known, else byPos[p]
        if no h, no id and x is a top node: h := the live handle of
            the id in the header at p (a read)
        if h holds a canonical object: refuse it if not of the type
            the pointer names (021-11); pointer i := h

Since 005-57 rule 4 reads only those headers (top node versions have no
prevPos, 011-03, G3). Why the maps suffice (005-57's report, section 2):
every write of a node after the version that a node of D names is in the
section, so such a pointer names a vpos, a position in posToId or the
canonical object's own. Argued for Java; proved for the model (section
5). With `-ea` each pointer is also linked by node id, with the read: a
difference is an `AssertionError`, or an SFE where only the id finds the
node (a damaged prevPos; `checkLinkById`, 2026-11-10).

### 1.9. The end of a start

Every value node in memory has a position and every key node passes its
check (`postStartupCheck`, always on); the cut back ends (M22); Rule R
stays. The STM's first time is the last record's (after the validation,
005-75); `created.txt` is written if missing (015-01); the database is
active; reclaim reads its settings and table, and makes a cut that a
crash left pending (027-13, section 1.9); eviction takes in what the
start made resident (015-68, 019-47). The start returns s, sd, ts, the
records read and R(k)'s last position. A start that throws closes the
storage before the exception leaves (005-32).

### 1.10. A start after a cut

Reclaim cuts at pCut only when the record that the last valid meta block
names is at or after pCut and the startup pos at or after pSafe (027-13,
section 1.6). So recovery and the section are after the cut, and blocks
below the first position are not searched. A pointer below the first
position names a version dead for every lookup time from fa on: rule 4
and the writer's resolve leave it (M33); a read that meets it is
027-13's, section 1.8.

### 1.11. Level 1

`levels.md`, section 4, and `level1.sh`: with sd larger than the stream
"the startup pos never moves" and "startup always replays the whole
stream". The take since 005-49 (`TransSeq.take`) takes a share in
proportion to S / sd, S the section's length, so with S below sd a
record takes a transaction with a probability of about S / sd: the
startup pos moves, rarely while the stream is small. Argued; Q2.


## 2. State

* **During a start**: the section's records as parsed, newById, posToId,
  posMap and byPos; garbage when it returns, but Rule R's copy.
* **For the process's life**: Rule R (newById, s, ts), never released;
  the canonical objects of the section, of D and of what the rerun
  reached; the take's queue of T(s+1), ..., T(k) with their got-dirty
  nodes; the meta block in memory, its lastTrans at R(k), so that the
  next block is the one a run without the restart writes; the clock's
  last time and the STM's first time.
* **In the stream**: the meta blocks (027-03, section 6); the frame and
  the fill (section 7); startupPos, topPos and the got-dirty pairs
  (section 8.1); prevPos (section 11); the references (section 14.1).


## 3. Invariants

* **T1, INV-CRASH** (011-01): a start from the stream of any run, or of
  a crash that keeps a prefix of whole records, gives the run's P at
  every time and its D. Proved in the model (section 5). Gated:
  CrashTest, CorruptStreamTester's truncation at every byte,
  `testCrash8InCreation`, PowerLossTest.
* **T2, INV-RESTART**: a run with restarts appends the records of the
  run without them. Proved in the model (`T2_restart`, `T2_lazy`,
  `RunPos_handles`). Gated: RestartInvariance (the stream byte for
  byte), `testLevel2SameStreamWithRestarts`.
* **INV-1** (`sis-model.md`, section 8): each node at most once in D;
  the D rebuilt is the run's: proved (`T1_recovery`).
* **Rule R is safe** (lemma M): a newer version serves every time an
  older one serves. Proved (`LM_newer`, `LM_ruleR`, `LM_cutTo`).
* **Rule 4 by position is rule 4 by node id**: proved for the model
  (`Rule4Pos_handles`; after a safe cut `Rule4PosCut_handles`); tested
  in Java, with `-ea`, at every start of every test (005-57).
* **The newest written top node is the super root at ts**: argued
  (011-11, section 8.3); a stream that breaks it is refused (1.6); gated
  for an older topPos (`testOlderTopPosRefused`).
* **A refused start writes nothing** (R1): gated for the magic, the
  version, the node size and an incomplete creation
  (`testRecoverWithWrongKeyWritesNothing`,
  `testRecoverOtherVersionWritesNothing`, `testOtherNodeSizeRefused`,
  `testIsIncompleteCreation`); not so for another record format, refused
  after recovery's fill (027-03, G18 and Q15).


## 4. Costs and bounds

* **The records read in order**, R(s), ..., R(k): less than R(s) + 2 sd
  + R(k). Proved for the model's take (`T3_take_reads`); Java's take
  gives the model's on 300 cases: checked (TakeCheck). Left out: the
  record limit and the meta blocks (`levels.md`, section 5). Recovery
  and the search for s read the records after the last valid block and
  the one over it, about MD: argued.
* **The transactions rerun**: fewer than 2 sd / 48 + 1, T(k) included,
  as a record has at least 48 bytes. Proved (`T3_take_rerun`).
* **The records at the ends**: each within its transaction and the debt
  before it. Proved, nothing assumed (`T4_ends`). The debt: each node of
  D is on the access path of a change of the last lev(x) + 1 sections;
  proved with the exact still-dirty test and a written root (`T4_debt`),
  open for BergDB's test (part 6). R(s) can be large: after one or two
  transactions of 1.88 GB each start took 27 to 75 s, 0.6 s once 150 MB
  more was written: measured (020-24-13, U13-7).
* **D**: at most the section's got-dirty pairs, 16 bytes each (007-01,
  section 2): argued.
* **A cold start's reads** (007-03, step 6): at most the section's index
  nodes, read in order with the records, and at random the nodes on the
  rerun's writer paths and those of each gd(j), plus 2; the nodes the
  rerun makes count but are not read. Proved for the model's start from
  any stream (`coldReads_lazy`; `coldReads_handles`, both rules 4).
  After a run, with D for the gd(j): proved (`coldReads_run`), the
  writer paths not bounded; with TREE, H + 1 for each node made, given
  an entry, touched or replaced: proved (`coldReads_tree`). For Java:
  argued, but Q4 and Q5.
* **Time, warm** (F53): 7.4 s at 10M keys, 8-byte values and 50 MB, 12.4
  s at 200 MB, 70 to 86 s at 1000 MB with 10M to 50M keys, most of it
  the rerun and the section's nodes: measured (007-05); 6.6 and 12.1 s
  at 50 and 200 MB with rule 4 by position (005-57, its prototype).
  Proposed: at most 0.1 s a MB of sd (024-05, BD6).
* **Time, cold** (s1): 46 and 51 s at 10M keys, 50 and 200 MB, with rule
  4 by position, 34 s of the 46 the rerun's loads; 214 and 210 s before:
  measured (005-57). No bound proposed (BD6). Not measured since format
  7, whose merges read siblings (024-11, TU9).
* **Heap**: the section's records and the maps, outside the cache
  budget: the live heap peaked at 3.3 to 4.9 sd, D included, 0.9 to 2.1
  times the section above the running database's: measured (019-45).
  Proposed: at most 5 sd above it (BD6). Rule R's map stays, one entry
  an index node of the section: argued.


## 5. In the model

* **Definitions** (trusted). lean/SIS/Startup.lean: `newest`, `follow`
  (Rule R), `readFrom`, `topVersion`, `readTops`, `rootVersion`,
  `topsRead`, `startVersion`, `baseStruct` (P up to s), `sectionIdx`,
  `rerun`, `startup`. lean/SIS/Phys.lean: `Version.cutTo`,
  `canonOfVersion`, `sectionNodes`, `Mem.linkCanonical`, `pathOf`,
  `Mem.reachOnPath`, `Mem.canonicalNode`, `lazyStartup` (Java's start,
  step by step), `Mem.sectionPos`, `runLazy`. lean/SIS/Handle.lean:
  `HMem.linkD` (rule 4 by node id), `handleStartup`, `inPosToId`,
  `HMem.byPos`, `HMem.linkDPos`, `handleStartupPos`, `HMem.linkDPosFrom`,
  `handleStartupPosFrom`. lean/SIS/BoundCold.lean: `rerunReach`.
* **Proved** (no `sorry` under lean/SIS):
  * T1 (`T1_recovery`, `T1_nodes`, `T1_crash`), T2 (`T2_restart`): a
    start from the stream of any run, or of a crash's prefix, gives the
    same P and D; restarts change no record (Theorems.lean).
  * T1-L (`T1_lazy`): after Java's lazy start, any reads and writer
    follows read P at every time up to k, and every canonical object
    holds its node's whole history. T2-L (`T2_lazy`): runs with lazy
    restarts append the same records; CC (`CC_canonical`): in them every
    canonical object holds its node's whole history. Lemma M.
  * Rule 4 by position (005-58): `Rule4_positions` (a pointer that rule
    4 links names a version of the section, the version before one, or
    the canonical object's), `Rule4Pos_handles`, `RunPos_handles`; after
    a cut (005-62) `Rule4PosCut_handles`, `RunPosCut_handles` (proofs in
    SIS/Proof/HandleLinkPos.lean and HandleCutPos.lean). T8
    (`T8_recoverCut`): a start from a safely cut stream gives the same
    lookups from fa on and the same D.
  * Costs: `T3_take_reads`, `T3_take_rerun`, `T3_take_restarts`,
    `T4_ends`; `coldReads_lazy`, `coldReads_handles`, `coldReads_run`,
    `coldReads_tree` (BoundColdTheorems.lean, 2026-11-13).
    `coldReads_run` is reduced to a bound on the writer paths, not
    stated, and one on D, which `T4_debt` gives for the exact test only.
* **Assumptions**: `RunOK` (A2 to A5); BergDB's still-dirty test, or the
  exact one with a written root; for T1-L, T2-L and CC `LiveAppend` and
  `TreeRunOK`; with handles `EvictRunOK`; after a cut `ExecRootOK` and
  `VirtLiveOK`. A crash keeps a prefix of whole records. **Stated, not
  proved**: nothing.
* **Left out**: bytes and positions (s is `lastSp`, a record number);
  the meta blocks, recovery and its fill; the walk that finds s; the
  checks, refusals and formats; R(s)'s values linked at the start; top
  node header reads; the end's check; heap and time; concurrency. The
  model applies Rule R to every stream slot it makes (`canonOfVersion`),
  Java to some at once and to the rest at their first follow (Q9).
* **Conformance** (027-02; TraceCheck.lean): C-L, every first touch
  after a restart against the model's rule (`firstFailures`); the trace
  checker on runs with restarts, every transaction a step of the model
  and every restart invisible (`level2.sh`, step 7); rule 4 by position
  against by node id after cuts (`checkHandleCut`, `posCutCounts`,
  SIS/ReclaimExample.lean).


## 6. In Java

* `core/Db`: `start`, `startInner` (the order of 1.2 to 1.9),
  `handleEmptyStream`, `refuseIncompleteCreation`, `refuseOtherNodeSize`,
  `handleStartParams`, `getStartupPosFromLastTransaction`,
  `checkStartupPos`, `readTransactions`, `closeAfterFailedStart`;
  `StartParams`; `StartInfo`.
* `core/DbStarter`: `validateTransactions`, `validateKeyNode`,
  `createMaps`, `updateStreamPointers`,
  `changeKeyNodesToStateAtStartupTime`, `checkStreamPointers`,
  `createMemoryPointers`, `registerSectionNodes`,
  `topNodeOfLastTransaction`, `findSuperNodeAtStartupTime`,
  `rerunTransaction`, `canonicalNode`, `linkD`, `postStartupCheck`,
  `wasCreatedInRerunSection`. `PrevMap` is used only by its tests.
* `core/NodeCollection`: `setStartupSection`, `readVersion`,
  `endReconstruction`, `followStreamPointer`, `resolvePointers`,
  `linkToCanonical`, `checkLinkById`. `core/NodeStream`: `recover`,
  `TransIterator`, `readRecordHeader`. `TransSeq.TransInfo`;
  `KeyNode.toPreviousState`, `validateStreamNode`;
  `TopDs.findSuperRootAtTime`; `Reclaim.initFromDb`.
* `storage/RecoverableStream`: `recover`, `readLastValidMetaBlock`,
  `readMetaBlock`, `checkLastTransSpos`, `fixMetaBlockIfNeeded`,
  `fixLastTransactionIfNeeded`, `transHeaderFixBytes`,
  `isIncompleteCreation`; `storage/MetaBlock`.
* The Pub API: `Database.getStartupInfo()`, the start's duration. The C
  clone (012, 022): `starter.c`, `recover.c`, `meta.c`, `ncoll.c`,
  without the prevPos refusal and the cycle check (027-03, 14.2).


## 7. Tests

* **Gated by `before-commit.sh`**: `DbTesterRestart` (40, unit and f;
  among them `testCorruptRecordTimesRefused`,
  `testCorruptStartupPosRefused`, `testCorruptGotDirtyIdRefused`,
  `testOlderTopPosRefused`, `testMetaBlockLastTransPosRefused`,
  `testOtherNodeSizeRefused`, `testNoNodeSizeRefused`,
  `testLastTransPosAfterRestart`); `DbStarter` (7); `RecoverableStream`
  (37: crashes in a header, a record and a meta block, the fill, an
  incomplete creation, refusals that write nothing); `MetaBlock` (4);
  `NodeCollection`'s `testFollowRuleR` and five `testLinkToCanonical*`;
  `DbTester.testCrash8InCreation`; CorruptStreamTester's sample and its
  six `testFound*` regressions; rule 4's `-ea` check at every start.
* **In the night**: `level2.sh` (RestartStress, RestartInvariance,
  CrashTest, the conformance with C-L); `level3.sh` and `level4.sh`
  (RestartInvariance and CrashTest with reclaim, with eviction;
  PowerLossTest); CorruptStreamTester's full set; `kill-restart.sh`. By
  hand: `performance.sh`'s restarts, warm or cold; 007-05's StartupBench.


## 8. Principles and rules

* **P5**, bounded startup: the section by T3, its ends by T4 (open for
  BergDB's test), a cold start's reads by `coldReads_*`; the time is
  measured, with no constant (section 4). **P2**: a restart changes no
  record (T2); sd is in the stream; the meta block in memory is set as
  the run without the restart has it.
* **P7**: a stream that breaks a check is refused with an SFE; damage
  the checks miss may fail a read later (014-01, section 7, point 3).
  **R1**: a refused start writes nothing, but recovery's fill before a
  refusal of the record format (G18). **R5**: Q11.
* **P10**: sd is the start's one setting, kept in the stream. **P12**: a
  start knows keys and values as bytes. **P1** is about the gets and
  commits of a running database; a start holds both locks until it
  returns, and P5 bounds it.


## 9. Limits and open work

* T4 for BergDB's still-dirty test and virtual root is open (part 6):
  the records at the ends and D have no proved bound for Java. 007-01,
  section 6's "about the last two sections" is refuted by a run
  (SIS/BoundT4Example.lean): lev(x) + 1 sections. A cold start in
  seconds needs the rerun's reads cheaper or fewer (007-05, point 3);
  after it the writer reads a header for each stream pointer of D's
  nodes it writes, 1.48 million in 300 transactions at 50 MB (005-57,
  finding 3; its part 2, not made).
* Refusals that depend on `-ea` (027-03, G14, J3); s not shown to be the
  take's (G12, 015-73); sd not range-checked (G9). Fast restart (006-06)
  is an idea; the start's heap could be halved (019-45, for 017-07).
* **Q1.** 027-03, sections 7, 15 and 18, give the creation as 264 bytes;
  `Db.CREATION_LENGTH` is 272 since 024-25 (bb433188).
* **Q2.** Is Level 1 (1.11) still a mode, with the take writing index
  nodes before the stream reaches sd, or "nearly full replay"?
* **Q3.** A crash inside `setStartupDistance`'s record, after the meta
  block written in it: recovery aborts the record, and the start takes
  the new sd from that block (1.2, 1.4). Intended?
* **Q4.** `coldReads_*` count objects; Java's rule 4 reads the header of
  a top node's pointer that neither map finds, which the model links by
  node id without a read (005-57 found none).
* **Q5.** A format 7 merge reads up to two siblings a level (024-21) and
  may leave one unchanged, on no path of `pathOf`: do `coldReads_*`
  cover Java's rerun of deletes?
* **Q6.** 007-03, step 6, bounds a cold start's reads "with T3 and the
  deadline, without T4"; `coldReads_run` has |D|, which
  BoundColdTheorems.lean says T4 bounds; by its 16-byte pairs D is
  within the section but gd(k), a T4 term. Which is the claim?
* **Q7.** `checkStartupPos` takes a startupPos equal to its own record's
  position, which the take never writes (s(i) < i): a damaged R(k) gives
  a section of R(k) alone, its gd not read. Refuse it?
* **Q8.** 019-45 says the start's maps are garbage when it returns;
  `setStartupSection` keeps a copy of newById for the process's life.
* **Q9.** Rule R in the slots at once (the model) or at the first follow
  (Java, for a pointer whose node needs a read): argued the same (Rule R
  twice gives what it gives once), checked by C-L. A theorem?
* **Q10.** 010-01, P5, "Where BergDB stands": T3 "not yet" proved for
  BergDB's own take; `T3_take` is, since 007-08 (2026-10-28).
* **Q11.** `Db.start(StartParams)` is public and takes a caller's
  startup pos and sd unchecked, and then leaves the meta block's
  lastTrans and sd as read (1.4): another section (R5), another next
  block (P2). Only `StartParams.NULL` is passed in `java/`. Keep it?


## 10. Evidence

001-08 (M22, M33, M44); 005-27, 005-28, 005-32, 005-33, 005-40 (recovery
and the start's refusals); 005-49 (own bytes); 005-50 (node size);
005-57 (rule 4 by position; cold 46 s); 005-58, 005-62 (its theorems);
005-75 (the validation); 007-01, 007-03 (step 6), 007-05 (warm and cold);
007-08 (`T3_take`); 011-03 (G3); 011-11 (8.3, M18); 014-01 (section 7);
015-01; 015-68, 019-47; 015-73, 015-75; 019-21; 019-32, 021-11; 019-34;
019-45 (the heap); 020-24-13 (U13-7); 020-28; 021-12; 024-05 (OP7,
BD6); 024-21, 024-25 (format 7); 026-08; 027-03 (sections 6 to 8, 14).


For the code's comments
=======================

Java comments on `main` (03282d8c) that disagree with the code, for a
028 entry; the code is right in each, and Java was not changed.

1. `RecoverableStream.java`:20, class comment: it "throws
   DBStreamException", a class that does not exist. Read:
   "StreamIoException, or StreamFormatException".
2. `RecoverableStream.java`:65, `MIN_TRANS_SIZE`: "Minimum record size
   accepted by recovery's walk". That walk refuses sizes below 5 only.
   Read: "the least size that recovery's completion of a torn header
   gives; the start's walk refuses 16 and below (readRecordHeader)".
3. `MetaBlock.java`:21: "time, database time". It is the creation's,
   set once (`Db.writePrimordialTransaction`). Read: "the creation's
   time".
4. `MetaBlock.java`:25: "startupDistance in bytes. Typically 20M." Read:
   "the setting in force; 50 MB by default (DbBuilder)".
5. `MetaBlock.java`:66, the constructor: "with startPos = 0". It sets
   lastTrans to −1. Read: "with lastTrans −1: no record yet".
6. `Db.java`:1218, `handleStartParams`: "From meta saves 8 bytes per
   trans". Each record stores its startupPos (027-03, section 8.1).
   Read: "s from the last committed record; sd from the meta block".
7. `Db.java`:1025 and :1060, `start`'s Javadoc: reclaim's read is "the
   last step of the startup"; eviction's admission comes after it.
   Read: "a step after the database is active".
8. `NodeCollection.java`:675, `setStartupSection`: key node versions of
   the section "are cut back ... when read". Read: "when read before
   endReconstruction()".
9. `DbStarter.java`:522 to 524, a lone Javadoc "@throws AssertionError"
   before `linkD`'s, whose :539 says "a difference fails". Read: "a
   difference throws an AssertionError, or a StreamFormatException for a
   damaged prevPos (checkLinkById)"; drop the lone one.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-13. The draft, by an agent of coord-1113, from the code at
03282d8c, the Lean files and the items of section 10 (027-04, section
5.2). For a second agent's review against the code.
