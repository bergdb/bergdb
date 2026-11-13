# 027-04. A proposed outline for 027

Created 2026-11-13 by Frans Lundberg. Status: open (a proposal for
Frans).

A proposed outline for 027, the algorithms of BergDB, for Frans to react
to: the parts in an order that a reader new to BergDB can follow, other
ways to organise them, questions, and how the writing could go on with
him. It is not the document and not a decision. 027 stays a placeholder
until Frans has decided its structure (027's readme; Frans, 2026-11-12,
14:45: "Not a plan for sections with names. I would like to do that
later. [...] Carefully without release stress. I will be part of that
work."). Frans asked for this proposal on 2026-11-13, 10:24, through the
day's coordinator.

Read only: the sources of section 2.1 were read. Nothing in `java/`,
`lean/` or another item was changed.


## 1. In short

* **Recommended: by mechanism, in the levels' order.** 027 would become
  14 parts. Each part covers one mechanism or a small group of them, and
  describes each one under the same ten headings: what it does, its
  state, invariants, costs and bounds, the model, Java, tests,
  principles and rules, limits, evidence (section 2.2). The parts follow
  the levels: Level 0's map first, then bounded startup, memory and
  reclaim. So the levels stay as the reading order and as a map to the
  level scripts (section 2.4), but they are not the structure.
* **The parts** (section 2.3): an overview; the terms; the key tree in
  two parts (structure and reads, then the writer); transactions; the
  self-indexed stream; startup; memory (handles and eviction); reclaim;
  storage and durability; failures; two indexes (costs and bounds, then
  the model and its checks); objects and user indexes. About 3,000 to
  3,500 lines in all, 120 to 350 a part. 027-02 and 027-03 stay as they
  are, beside the parts.
* **Alternatives** (section 3): strictly by level, as 027-01's
  `levels.md`; by data structure, as Frans's `2015-algos.pdf` and the
  Java packages; by operation, as the API and aim 2's bounds. Each one
  suits one kind of reader and fails another. The recommendation takes
  the levels' order and the per-mechanism units.
* **Five questions** (section 4): the levels, the scope, the form, how
  much of the model's mathematics, and which text holds the exact rule.
* **How it could go on** (section 5): Frans decides the outline. Then
  the overview and the terms come first, written with him, and then one
  part as a pilot (reclaim). The rest follow in reading order, one part
  a session: an agent drafts it, a second agent reviews it against the
  code, and Frans reads it.


## 2. The proposed outline

### 2.1. What exists

The algorithms are described in many places today, and each one is
current to a different date:

* **027-01, `levels.md`.** Each level: what it does, how Java does it,
  its checks, its limits and the evidence by item ID. Also failures
  (section 3), durability (8), and objects and indexes (11). It is a
  snapshot of 2026-11-12 and is already stale in places: its section 6
  says that a reclaim step scans at tStart, but since 026-05 (this
  morning) each step scans at its own time.
* **027-01, `sis-model.md`.** The abstract model, T1 and T2, the
  obligations of an implementation (11), and the physical layer with
  eviction and reclaim (15). It is draft 2 of 2026-10-12, updated in
  parts until 2026-11-12. Lean's comments cite its sections.
* **027-01, `sources/`.** Frans's texts of 2012 to 2016:
  * the v5 paper: the problem, and the requirements of a small startup
    distance, a small stream overhead and every state recoverable;
  * `startup.md` and `startup-1604.md`: DB = <P, D, S>, the take and
    the rules of dirtiness;
  * `2015-algos.pdf`: organised by data structure (the Dag,
    transactions, splits, the stream, the trans seq, TopDs, startup).
    It also sets terms: "The terms as they are defined here take
    precedence over conflicting use elsewhere."
* **027-02 and 027-03**: the trace format and the stream format, both
  kept current.
* **`lean/README.md`**: the Lean model file by file, and what is
  proved; kept with `lean/`. The model is organised by mechanism:
  * the abstract model (SIS/Basic.lean to Theorems.lean);
  * T3 (Bound.lean);
  * the physical layer (Phys.lean);
  * handles (Handle.lean);
  * reclaim (Reclaim.lean);
  * the key tree (SIS/Tree/): its definitions run against Java's
    traces, and its properties are stated and partly proved. The
    proofs go on in 024-12 and 024-22;
  * the user indexes (BergDB/Index/): proved.
* **The Java packages** (`package.html`, the class comments). The code
  is organised by layer and by structure (`stream`, `storage`, `dag`,
  `core`, `pubimp`). `core` holds most of the mechanisms (`Db`,
  `DbStarter`, `TransSeq`, `Reclaim`, `Eviction`, `Cache3`,
  `Residents`). Some exact rules exist only in a class comment, such
  as reclaim's in `Reclaim`.
* **The items with designs and evidence**:
  * 001: Levels 3 and 4 in Lean, and their alignments;
  * 007: bounded startup, T3;
  * 009: handles;
  * 023-07: the cleanup's mechanisms;
  * 024-04 and 024-05: the aims and the bounds BD1 to BD14;
  * 024-07: the last touch;
  * 024-11, 024-21 and 024-22: the merges;
  * 024-12: the tree model;
  * 024-23: dead klongs;
  * 024-30 and 026-11: the count gates;
  * 026-05: each reclaim step at its own time;
  * 010-01 and 010-04: the principles and the rules.

So the fields that 027's readme asks for exist for most mechanisms, but
they are scattered. The Lean names are in `lean/README.md`; the bounds
in 024-05 and 024-30; the tests in the level scripts' headers; the
principles in 010-01, with its departures. No single place holds all
of them.

### 2.2. The template of a part

A part describes each of its mechanisms under the same ten headings:
the fields of 027's readme, plus three more (state, limits, evidence).

1. **What it does.** The rule, exact enough to implement in any
   language. It is given in words, and as pseudocode where the rule is a
   computation (the take, the cut's conditions, the delete path). No
   Java names appear here.
2. **State.** What the mechanism keeps in memory and in the stream. For
   the bytes, it points to the right section of 027-03.
3. **Invariants.** Under the names they have today (INV-RECLAIM, BU1,
   LE-b, TP39), each with where it is proved, checked or tested.
4. **Costs and bounds.** Each bound is marked as proved (T3), gated (G1
   to G5, MEM, SEG), proposed (024-05's BD1 to BD14), measured or open.
5. **In the model.** The Lean definitions; the theorems proved; the
   properties stated but not proved; what the model leaves out; and the
   conformance checks (C-A, C-L, C-P, C-H, the tree checker).
6. **In Java.** The classes and methods; later also the C clone's files
   (022).
7. **Tests.** The unit tests and f-tests, the level scripts' steps, and
   the night's tests.
8. **Principles and rules.** The principles of 010-01 and the rules of
   010-04 that it serves, and where it departs from one (010-01 lists
   the departures).
9. **Limits and open work.** As in `levels.md`'s "Limits": what is not
   proved, not built or not measured, with the open items by ID.
10. **Evidence.** The items, by ID, one line each. Measurement tables
    stay in the items.

Each claim's status is one word, the same in every part:

* *proved*: a Lean theorem;
* *stated*: a Lean property without a proof;
* *checked*: checked against the model on traces of Java's runs;
* *gated*: a test with a limit, run by `before-commit.sh`, a level
  script or the night;
* *tested*, *measured* (in an item), *argued* or *open*.

`levels.md` already makes these distinctions, but in words that vary
from place to place.

Sections are numbered within a part, and a number is never reused (as
in `levels.md` and 027-03). Code comments can then cite "bergdb 027-nn,
section m" safely.

### 2.3. The parts

The parts are listed in reading order, one paragraph each: what the part
covers, what it draws on (documents, Lean files, Java classes), and its
size. Each size is an estimate in lines; for scale, `levels.md` has
1,061 lines and `sis-model.md` 928. The level that a part belongs to is
in brackets.

1. **Overview: what BergDB is and what it promises** [all]. What BergDB
   is: an embedded, append-only, multiversion key-value store whose
   index lives in the same stream as its data. What it promises:
   011-01's requirements R1 to R7 and its invariants INV-LOOKUP,
   INV-RESTART, INV-CRASH, INV-RECLAIM and INV-EVICT, as they hold
   today. The layers (stream, storage, Core, Pub; 010-01's P12); a table
   of the principles and the rules, one line each, with the parts that
   serve them; the levels as a map from the parts to the level scripts
   (section 2.4); how to read a part (section 2.2). Draws on
   `README.md`, 011-01, `levels.md` sections 1 and 2, the v5 paper's
   section 1, 010-01 and 010-04. No Lean file. About 150 lines.

2. **Terms** [all]. One list of BergDB's terms, each with its
   definition, and with its Lean name and its Java name where they
   differ: key, value, KV, segment, key node, top node, value node,
   klong, node id; time, lookup time (requested and actual), first
   available time; transaction, record, version, reference; startup
   distance, startup pos, startup section; D, got-dirty, canonical
   object, handle; memory pointer and stream pointer ("pointer i of x";
   "slot" is the Lean model's word only); retain duration, iteration,
   step, cut. It also settles the names that collide today: 011-01's
   requirements R1 to R7 and 010-04's rules R1 to R5; Rule R and the
   retain duration R; the model's T1 to T4 and 023-03's tests T1 to
   T12. Draws on `2015-algos.pdf` (sections 2 to 8, Frans's terms),
   `sis-model.md` sections 2 to 5, SIS/Basic.lean and Stream.lean.
   About 150 lines.

3. **The key tree: structure and reads** [0]. The multiversion map as a
   tree: keys cut into segments of 7 bytes, and segment trees; key nodes
   made of klongs, and the klongs' types; value nodes; the top node and
   its skip pointers; node ids; the searches; a get at a lookup time; a
   scan with its end key and R9's amortized bound; the keys' shape and
   its cost in heap (MEM, SEG; 024-08, 024-15). Draws on
   `2015-algos.pdf` sections 3 and 8 and its appendix A, 024-12 sections
   2 and 6, `levels.md` section 4, `core/doc-files/key-encoding.md`, and
   027-03 sections 10 to 13 for the bytes. Lean: SIS/Tree/Node.lean,
   Read.lean, Top.lean, Inv.lean, Props.lean, Bound.lean, and the proofs
   of the searches and scans (ScanSound.lean, SearchEqProof.lean and
   the files beside them). Java: `Dag`, `KeyNode`, `Klong`, `Keys`,
   `GetMany`, `TopDs`, `TopNode`. About 250 lines.

4. **The key tree: the writer** [0]. What a transaction's operations do
   to the tree, in the order that record format 7 fixes: a put and the
   five splits, with h; a delete's upward unlink, the take-back, LE-b
   and root collapse; the merges of underfull nodes (m and c), with BU1
   and the bound on key nodes by the live keys; at most theta dead
   klongs a node (rule O); `dirtyNodeBound`. The newest design and the
   most open proofs (024-12's TP7, TP10 and TP11; 024-22's TP30 to
   TP33). Draws on `2015-algos.pdf` section 5 (the splits), 023-07
   section 5 (K1 to K4, F1), 023-09, 024-11, 024-14, 024-21, 024-22,
   024-23, 024-12, and `levels.md` section 5's points on deletes, merges
   and dead klongs. Lean: SIS/Tree/Exec.lean, Spec.lean, MergeProps.lean,
   DeadProps.lean, and the Merge, Writer and Split files. Java: `Dag`
   (`deleteUpward`, `mergeAfterDelete`, `minFill`, `mergeCap`,
   `splitAbove`, `theta`, `deadFull`) and `PutData`. About 350 lines.

5. **Transactions** [0]. How a transaction becomes a change and a
   record: the clock and the times (56 bits; the last 1,024 times kept
   for reclaim's internal transactions); the read set and the STM
   check; the key and value transformations; the KVs in key order, one
   a key; the limits L1 to L6 and the check of the dirty nodes; the go
   point (R1: a refused call changes nothing) and the steps after it
   (statistics, eviction, reclaim's work); one writer and readers
   without locks; why a rerun gives the same record (P2, P8). Draws on
   the first half of `levels.md` section 3, `2015-algos.pdf` section 4,
   005-01, 005-17, 005-31, 005-70, 015-55, 023-08 section 7, 024-16,
   024-17 and 024-24. Lean: the model's transaction (`step` in
   SIS/Algorithm.lean, with `changed` and `marked`), `Limits.dirtyNodes`
   and `ReleaseFits`; concurrency is outside the model. Java: `Db`
   (`executeInner`, `checkLimits`), `Trans`, `KeyModSet`, `DbClock`,
   `TransNodes`. About 200 lines.

6. **The self-indexed stream** [2]. BergDB's central idea: the data P,
   the dirty set D and the stream S; versions and references; good and
   dirty; marking (T13) and the still-dirty test (Rule A, BergDB's
   conservative test and what it costs); what a record holds (the
   transaction, the index nodes taken, the got-dirty ids, the startup
   pos, topPos); the virtual root; the take (the share in proportion to
   the stream added, the deadline at twice the startup distance, the
   dither, the integer rule, a decrease of the setting); T1, T2 and T3
   (`T3_take`, `T3_take_decrease`) in plain words, what they leave out
   (the record limit, the meta blocks), and T4, open. Draws on
   `sis-model.md` sections 1 to 9, 11 and 12, `startup.md`,
   `startup-1604.md`, the v5 paper, `levels.md` section 5, 007-01,
   007-03, 007-07, 007-08, 005-49, 005-79 and 024-31. Lean:
   SIS/Basic.lean, Stream.lean, Algorithm.lean, Assumptions.lean,
   Theorems.lean, Bound.lean, BoundTheorems.lean. Java: `TransSeq`
   (`take`, `shareFp`, `ditherFp`), `StartupPos`, `IDirtyNodes`,
   `NodeStream` and the `Stored*` classes. About 350 lines.

7. **Startup** [1, 2]. From the files to a running database: the last
   meta block and record; a torn tail completed as an aborted record
   (014-01's contract); Rule R, the startup section and the super root
   from topPos; the rerun; D rebuilt from the got-dirty ids with rule 4
   by position, also after a cut; the validation of 005-75 and the
   refusal of older formats; the heap a start needs and the time it
   takes, warm and cold. Level 1, restart by full replay, is the case of
   a startup distance larger than the stream: a paragraph. Draws on
   `sis-model.md` section 6.2, `levels.md` sections 4, 5 (startup) and
   8 (the crash contract), 005-57, 005-58, 005-62, 005-75, 007-05,
   014-01, 019-45, and 027-03 sections 7 and 14. Lean: SIS/Startup.lean;
   the lazy startup in Phys.lean; `handleStartupPos`, `HMem.linkDPos`
   and `linkDPosFrom` in Handle.lean; T1-L, CC, T2-L, `rule4Pos_handles`,
   `rule4PosCut_handles`. Java: `DbStarter`, `StartInfo`, and in
   `storage` `RecoverableStream` and `MetaBlock`. About 250 lines.

8. **Memory: handles and eviction** [2, 4]. What a running database
   holds: one canonical object per index node; lazy reading at a
   pointer's first touch, and lemma M; handles, the node table and the
   record rule; the fast path without a lock and its memory-model
   edges, the slow path, the maintenance follower. Then eviction: what
   is counted (`Residents`) and pinned; an eviction; the capacity
   controller (CLOCK, its batches, the writer and the eviction thread);
   a change of the budget; the dead hand after a cut; P1's pause target
   and the collector's part. Draws on `levels.md` section 7 and section
   5's canonical objects, `sis-model.md` section 15, 009-01, 009-02
   sections 3 and 4, 009-05, 001-08, 001-10, 015-13, 015-15, 015-67,
   015-70 and 023-07 section 5.6. Lean: SIS/Phys.lean and
   PhysTheorems.lean (lemma M), Handle.lean and HandleTheorems.lean
   (T-CACHE, T-READ, T2-C, T-PIN). Java: `Handle`, `Pointer`,
   `PointerFollower`, `Cache3`, `Eviction`, `Residents`. About 350
   lines; it could be two parts, handles and eviction, if Frans prefers.

9. **Reclaim** [3]. How the front of the stream is cut: the retain
   duration and its stored settings; an iteration's start and its
   positions (pStart, tStart, pCut); the steps, their allowance by the
   internal fraction, each one scanning at its own time (026-05),
   rewriting live values as puts and touching only the paths of its own
   puts (024-07); the iteration's end; the cut's conditions, the reclaim
   table, the physical cut and the first available time; reads that a
   cut overtakes; `maintain()`. Draws on `levels.md` section 6 (stale
   since 026-05), 001-07, 001-09, 011-06, 011-04 (W1 to W5), 015-87,
   023-07 section 5.5, 024-07, 024-29, 024-31, 024-32, 024-34, 026-05,
   026-11 and 017-04. Lean: SIS/Reclaim.lean, ReclaimTheorems.lean and
   HandleReclaimTheorems.lean (T9 and T12, with handles); T-SCHEME, that
   Java's scheme gives safe cuts, is checked at every cut, not proved.
   Java: `Reclaim`, and `Db`'s `touchPaths` and `maintain`. About 300
   lines.

10. **Storage and durability** [all]. Below the Core: the append-only
    stream's contract; `FileStream`'s files and forces;
    `BufferedStream`'s chunks and group commit; the meta blocks; what
    `sync()`, `stop()` and `close()` promise; the physical cut's
    deletes; the crash contract (a prefix of what was appended);
    per-append forcing turned off; no replication, copies left to the
    OS. Outside the Lean model, which assumes that a crash keeps a prefix
    of complete records. Draws on `levels.md` sections 8 and 9, 011-07,
    014-01, 005-11, 005-13, 005-44, 005-46, 005-48, 005-64, 005-76,
    012-02 (the bytes as C reads them) and 027-03 sections 4 to 7. Java:
    the packages `stream` and `storage`. About 200 lines.

11. **Failures** [all]. The error model: the sound environment that
    BergDB assumes; what fails the database (an I/O error, corrupt data,
    an `Error`, anything after the go point) and what fails only the
    call; a failed database; interrupts; the next start's recovery;
    index jobs. Short, as the design is Frans's and stable (P7, R1, R2).
    Draws on `levels.md` section 3, 005-01, 005-30, 005-46, 015-27,
    015-35, 019-10, and 019-38 to 019-42. No Lean file is needed: the
    stream after a failure is that of a run without the failed
    transaction, or with it (`levels.md`, section 3). Java: `DbState`
    and `Db`'s edges. About 120 lines.

12. **Costs and bounds: the index** [all]. Every bound in one table: its
    statement, its status, its constant, the part that owns it and its
    test; T3, G1 to G5, MEM, SEG, SS, BD1 to BD14 and P1's guide, with
    the aims they serve (024-04: "cost follows value"). The parts state
    their bounds; this part only lists them, so that a release can see
    what is guarded. Draws on 024-04, 024-05 section 4, 024-30, 026-11,
    007, 017-04, and 011-01's R3 to R7. About 150 lines.

13. **The model and its checks: the index** [all]. How an
    implementation is tied to the model: the trusted part of the Lean
    model (the definitions and the statements); the assumptions (A2 to
    A5, TREE, A6, A-COPY, `LiveAppend`); what the proofs leave out
    (concurrency, bytes, torn records, resource bounds); the mapping
    from Java's state to the model's and its registers (011-11, 001-07,
    001-08, 009-05); the checkers and their sets (`conformance.sh`,
    `treeconf.sh`, `TakeCheck`, `A2A3Check2`; 027-02's format); a table
    of every theorem with its part. The guide to the Lean files stays in
    `lean/README.md`. Draws on `sis-model.md` sections 11, 13 and 14,
    `lean/README.md`, 024-06, 024-09, 024-12 section 5 and 027-02. About
    200 lines.

14. **Objects and user indexes** [Pub]. The Pub layer's algorithms,
    built on the Core's four data methods (P12): the key space (`/d`,
    `/-`, `/#`); the stored object and the conversion, by a pointer to
    their specs; the user indexes (the definitions, the generations, the
    build and its activation, the maintenance at every put and delete,
    deletion and cleanup, the scan's check of each entry against its
    value); the primary scan; the index protocol's proofs of safety and
    liveness. Draws on `levels.md` section 11, 020-02, 020-07, 020-09,
    020-10, 020-18, 020-22, 020-26 and 020-29. Lean: BergDB/Index/
    (Model.lean, Theorems.lean, Liveness.lean and the proofs). Java:
    `pubimp`. About 250 lines.

Two subitems stay as they are, beside the parts: 027-02, the trace
format, which part 13 points to, and 027-03, the stream format, which
each part's "State" points to. 027-01 stays a snapshot; when a part is
written, it says which of 027-01's sections it replaces.

### 2.4. The levels in this outline

| Level | What it adds | Parts | Script |
|---|---|---|---|
| 0 | the multiversion map in memory | 3, 4, 5              | `before-commit.sh`, `DagFuzz` |
| 1 | restart by full replay         | 7, a paragraph       | `level1.sh`                   |
| 2 | bounded startup                | 6, 7, 8's first half | `level2.sh`                   |
| 3 | reclaim                        | 9                    | `level3.sh`                   |
| 4 | eviction                       | 8's second half      | `level4.sh`                   |
| - | durability, failures, Pub      | 10, 11, 14           | `before-commit.sh`, the night |

The parts' order departs from the levels' order in one place: memory (8)
comes before reclaim (9). Lazy reading belongs to bounded startup, and
handles serve both the reads and eviction, so after startup the next
question for a reader is what is held in memory.


## 3. Other ways to organise 027

**A. By level**, as `levels.md`: one part for each of Levels 0 to 4, and
then durability, failures and the Pub layer. A variant of A is by
layer, from the bottom up (stream, storage, Core, Pub).

* For: it continues 027-01 and the level scripts, one to one. Each part
  adds one feature to those before it, in the order in which the code
  was made stable (Frans, 2026-11-12, 14:27: "the division of
  functionality into "levels" was very useful to get the old code base
  stability. There were bugs all over and it really helped.").
* Against: the levels are stages of features and of testing, not
  algorithms. Several mechanisms serve more than one level:
  * the delete path is Level 0's, but it exists for Level 3's sake;
  * handles serve Level 2's lazy reading and Level 4's eviction;
  * the take serves Level 2's section and Level 3's cut.

  So such a mechanism is described in pieces, and its invariants, Lean
  theorems and bounds are spread over several parts. Level 1 is no
  longer a mechanism, only a setting. `levels.md`'s framing as "what
  works" is a status, which ages with every release. The by-layer
  variant starts with files and forces, the least particular part of
  BergDB, and leaves the Core as one large layer.

**B. By data structure**, as `2015-algos.pdf` (the Dag, transactions,
splits, the stream, the trans seq, TopDs, startup), with Java's packages
and many of the Lean files. The parts would be: the key tree, the top
node, the transaction sequence, the stream and its records, D, the node
table with its handles, and the reclaim table.

* For: it matches the code and the model's files, so a change usually
  touches one part. Invariants belong to structures. An implementer
  builds structures first. It is Frans's own form of 2016.
* Against: the algorithms that use several structures have no home, or
  are split: startup, the take, reclaim and eviction. Those are the
  mechanisms that the proofs and bounds are about. A reader new to
  BergDB meets the details before the purpose.

**C. By operation**, as the API's lifecycle: open (startup), commit, get
and scan, the work in the background (the take, reclaim, eviction,
`maintain()`), sync, stop and close, and failure.

* For: it matches aim 2's bounds, which are stated per operation (BD1
  to BD9), and P1's pause target, which applies to each call. It is the
  user's view.
* Against: the same structure and invariant appear in many parts. The
  proofs are about runs, not calls. One change of the code touches
  several parts, so the text is the hardest of the four to keep current.

| Organisation | Newcomer | Implementer | Kept current | 027's fields | Levels |
|---|---|---|---|---|---|
| Recommended: mechanisms, levels' order | good | good | good | good | a map         |
| A, by level                            | good | fair | fair | fair | the structure |
| B, by data structure                   | poor | good | good | fair | none          |
| C, by operation                        | fair | fair | poor | poor | none          |

"027's fields" means how well each per-algorithm field of 027's readme
(what it does, invariants, bounds, Lean, Java, tests, principles) gets
one place.

**Recommendation: the outline of section 2.** It is by mechanism, so it
matches what 027's readme asks for: each algorithm with all its fields
in one place. It is the form the Lean model already has. It keeps the
levels' order, which is the right order for a newcomer, without the
levels' seams. It takes one thing from each alternative: from A, the
order and the map to the scripts; from B, a part's "State" field and the
terms; from C, the bounds per operation (BD1 to BD9) in part 12.


## 4. Questions for Frans

**Q1. Should the levels stay as 027's organising idea?** The options
are: (a) yes, parts by level (section 3, A); (b) only as the reading
order and as a map (section 2.4); (c) dropped from 027. *Recommended:
(b).* The levels did their work as stages of stabilisation, and the
level scripts still test them. For a reader they also give the right
order, since each level adds one mechanism to those before it. But a
mechanism such as the delete path, the take or handles serves several
levels, and Level 1 is now a setting rather than a mechanism. The level
scripts do not change under any of the three options.

**Q2. What is the scope: the Core only, or the storage layer and the
Pub layer's objects and user indexes too?** *Recommended: all of them,
in the outline's order, with the Pub layer last* (part 14). The index
protocol is an algorithm with proofs of its own (BergDB/Index). The
stored object's format and the conversion rules stay in 020-07 and
020-09, which are frozen with format 2; 027 cites them and does not
copy them. If they change later, the new text becomes a subitem of 027,
as the stream format became 027-03.

**Q3. Should 027 be one subitem per part, or one document?**
*Recommended: one subitem per part.* All of them would be created at
once, as stubs in reading order (027-05 to 027-18), so that their IDs
follow the reading order and cite well ("027-13, section 4"). 027's
readme would then list them as the table of contents. A single document
of 3,000 lines would be as hard to keep current as `levels.md`, and
027-02 and 027-03 are subitems already.

**Q4. How much of the model's mathematics should go into 027?**
*Recommended: as much as `sis-model.md` has.* That means the definitions
in words and the theorems in plain English with their Lean names, but no
proofs. Parts 6 and 7 would begin as `sis-model.md` brought current,
keeping its order, rather than as a new text: it is the best text there
is, and Lean's comments cite its sections. `lean/README.md` stays the
guide to the files.

**Q5. Which text holds the exact rule: 027 or the code's comments?**
Some exact rules live in class comments today: `levels.md`, section 6,
sends the reader to `Reclaim`'s class comment for reclaim's details.
Once 027 states such a rule too, one of the two must be the reference.
*Recommended: 027,* which is language-neutral and serves every
implementation. The code's comments cite 027's section and keep only
what is particular to Java. The class comments shrink as parts are
written, never in a hurry. Measured numbers stay in the items, and a
part cites them in one line, so a new measurement does not make 027
stale.


**Decided** (Frans, 2026-11-13, 11:09):

* **Q1**: "as recommended": the levels only as the reading order and a
  map (b).
* **Q2**: "Core is really the thing here. Good to have a separate last
  section for the Pub layer." The Core is 027's subject; the Pub layer's
  objects and user indexes are the last part (027-18).
* **Q3**: "as recommended": one subitem per part, created as stubs in
  reading order, 027-05 to 027-18 (made 2026-11-13).
* **Q4**: "as recommended": as much of the model's mathematics as
  `sis-model.md` has, without proofs.
* **Q5**: "027 holds the exact rule as the authority. Together with Lean,
  this is the authority. However, Java comments may duplicate this when
  suitable for readability; or summarize it. Good to have comments that
  makes it possible to understand whether the code really implement what
  is should."


## 5. How the writing could proceed

### 5.1. Order

1. Frans reacts to this proposal: to the outline and to the questions
   of section 4.
2. The overview and the terms (parts 1 and 2) come first, written with
   Frans. They set the words that every other part uses, and the terms
   are his to decide (as with "pointer", not "slot").
3. A pilot: reclaim (part 9). It is one mechanism, and it changed this
   week (026-05), so `levels.md` is already stale on it. It has proofs
   (T9, T12), gates (G3 to G5, and G4's lag since 026-11), principles
   (P3, P4) and an open point (T-SCHEME), so it uses every field of the
   template. Frans reads the pilot and adjusts the template before more
   parts are written.
4. The other parts follow in reading order (3 to 8, 10, 11, 14). The
   two indexes (12, 13) come last, since they list what the parts hold.
5. When parts 1 to 7 exist, `AGENTS.md` and `items/readme.md` point to
   027's overview instead of `levels.md`. That is a small change of its
   own.

There are no dates, and no release is tied to the work. A part is done
when Frans has read it (027's readme: "Carefully without release
stress").

### 5.2. Who does what

* **An agent drafts a part**, in one session. It works from the sources
  at a named commit of `main`, and gives every claim its source: an item
  ID, a Lean name or a class. It reads the code and the Lean files, not
  only the documents. Where the code, the model and the documents
  disagree, it writes a question in the part, not a fix.
* **A second agent reviews the draft** against the code and the Lean
  files, without being given the first agent's conclusions (as 023-07's
  reviews were done).
* **Frans decides:** the outline and the template; the terms; every
  sentence that states a promise (a principle, a rule, the constant of a
  bound); and each part's status. A part is first a draft, then
  reviewed (by the second agent), then current (read by Frans).
* **The coordinator schedules** a part when the machine and Frans have
  room for it, and never in a release's last days.

### 5.3. Keeping it current

* **The same commit.** A change to an algorithm changes its part in the
  same commit, as 027-03 is kept today. The item that makes the change
  names the part's sections that it changed. Nothing outside `items/`
  reads 027, so no gate changes.
* **A reference commit.** Each part names its reference commit and
  lists its Java classes and Lean files (fields 5 and 6 of the
  template). `git log <commit>..main -- <files>` then lists the parts
  that may be stale. The coordinator runs it at each release, as a line
  of the release checklist (as in 024-28), and the release item records
  what it changed. A script can come later, if the list grows long.
* **Citations.** The code's comments cite 027's sections (`bergdb
  027-nn, section m`). Since a section number is never reused, the
  citations stay valid.
* **Measurements in the items** (Q5), so that a new run does not make a
  part stale.
* **Later.** The C clone (022) and a model-first rewrite (025-01) can be
  checked against the parts. That is the test of "language-neutral".


## 6. State

Written on 2026-11-13, 10:25 to 10:40, by an agent of coord-1113, read
only. Nothing else changed but this file's line under Files in 027's
readme. Open: Frans's reaction to sections 2 and 3, and his answers to
the questions of section 4. Next: section 5.1's order, once he has
answered.
