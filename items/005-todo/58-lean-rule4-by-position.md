005-58. Investigate a Lean theorem for rule 4 by position
=========================================================

Status: done (2026-10-27; see Outcome). Kind: investigate. Created 2026-10-27.

Registered at Frans's request, as his answer to question 4 of 005-57's
report ("A Lean theorem for the claim?"), 2026-10-27: "Yes, but in a
separate work item in 005."


The issue
---------

Since 005-57, Java's rule 4 (`DbStarter.linkD`, `NodeCollection.
linkToCanonical`) finds the node that a pointer of D names by the
pointer's position, without reading the stream: by the startup section's
ids (`posToId`: each index node version in the section, and the version
before each key node version there), or among the canonical objects by the
positions of their versions. A pointer whose position is in neither is left
as it is. 005-57's report, section 2, argues that this links every pointer
that rule 4 by node id links: every write of a node after the version that
a node of D names is in the startup section (001-08, 5.4, case 5). The
argument is checked at every startup of the tests, where rule 4 by node id
runs beside it with assertions on, and it found no difference. It is not a
theorem.

The Lean model's rule 4 (`Mem.linkD` in `lean/SIS/Evict.lean`,
`HMem.linkD` in `lean/SIS/Handle.lean`) finds the canonical object by node
id. In the model a slot names its node, so that costs nothing; the
positions that Java has to work with are not in it.


Questions
---------

1. The statement. On every state that the model's startup reaches
   (`handleStartup`, after the rerun), for a pointer that holds no handle,
   of a pinned object, to a node y that has a canonical object o: the
   pointer's record is in the startup section, or is the record of y's
   version just before y's first version in the section, or is the record
   that o's version came from (o's position, `sectionPos`). And the
   converse that makes the two rules equal: a pointer whose record is
   neither names no node with a canonical object.
2. What the model needs for it: "the version before", a node's previous
   version in the stream, as Java's `prevPos` (the model has the records,
   `newest` and `sectionPos`, not a version chain); top nodes, whose
   versions have no `prevPos` in Java (011-03, G3), so the statement
   excludes the root's children or the model gives them none either.
3. Which lemmas it rests on: the record rule (INV-SLOT, `T2_cache`),
   D closed upward and Rule A (TREE, A6'), the take's invariant
   (every node of D has its got-dirty index after s); which of them the
   model has as theorems today, and which are assumptions of `EvictStep`.
4. Then: state Java's rule 4 by position in the model (a `linkDPos` beside
   `HMem.linkD`) and prove that they are equal on reachable states, so that
   the checker's C-H covers the Java code as it is.


Done when
---------

The theorem in `lean/`, with `lake build` clean and no `sorry`; 005-57's
report and `docs/levels.md` cite it; the check under assertions in
`NodeCollection.linkToCanonical` may then stay or go, for Frans to decide.


First step
----------

Read `HMem.linkD` and `handleStartup` with their lemmas
(`lean/SIS/Proof/HandleInit.lean`, `EvictInit.lean`), and write the
statement of question 1 in the model's terms, with what it needs (question
2), before any proof.


Size and order
--------------

M, at a guess. Independent of the code; it can go any time.


The statement
-------------

2026-10-27, by Claude (Opus 5.5, Claude Code), written before the proof,
and brought up to date with the final statements after it and its review
(Outcome): `Stream.lv`'s spelling, and the runs (4). The definitions go
beside `HMem.linkD` in SIS/Handle.lean, the statements beside `T2_handles`
in SIS/HandleTheorems.lean (both trusted), the proof in a new file of
SIS/Proof/, HandleLinkPos.lean.

**Positions in the model.** A Java position names one version. In the
model a reference is a record number, a record holds at most one version
of each node, and a pointer knows its node. So Java's position is the pair
of a pointer's record r and its node y; "the version at r" is y's version
in record r, and Java's `posToId.get(pos)` becomes the question whether
that pair is in the map.

**The state.** Rule 4 runs on the memory that the startup has built just
before it: in `handleStartup sp S`, the memory
`((lazyStartup sp S).sectionPos S).toH`, called m below. S is the stream
after transaction k of a run, s its startup pos (`lastSp S`), D the
startup's D (the run's, by T1). The pinned objects are those that
`HMem.linkD` links: the canonical objects of the nodes of D, and the root's
object.

**1. The positions (question 1).**

    def Rule4_positions (sp : Spec V T) (al : Algo V T) : Prop :=
      ∀ ts : List T, RunOK sp al ts → PhysRunOK sp al ts → EvictRunOK sp al ts →
        al.stillDirty = javaTest sp → al.mark = true →
        ∀ k ≤ ts.length,
          let S := (run sp al (ts.take k)).S
          let s := lastSp S
          let m := ((lazyStartup sp S).sectionPos S).toH
          ∀ a o y p r b, m.obj? a = some o → o.canonical = true →
            (inD (startup sp S).D o.node = true ∨ a = m.root) →
            (y, p) ∈ o.ptrs → p.handle = none → p.ref = some r →
            m.canonicalOf y = some b →
            (s ≤ r ∧ (S.versionAt r y).isSome) ∨
            ((newest S s y).isSome ∧ (Stream.lv (S.take s) y).map (·.recNo) = some r) ∨
            (m.obj? b).bind (·.pos) = some r

In words: take a run of BergDB's algorithm (the still-dirty test
`javaTest`, step 3 by marking) that meets the model's assumptions
(`RunOK`, `PhysRunOK`, `EvictRunOK`, the same as T2-C's), and the startup
from its stream after any transaction k. In the memory just before rule 4,
take a pinned object o, and a pointer of o to node y that holds no handle
and names record r. If y has a canonical object b, then r is one of:

1. a record of the startup section, R(s), ..., R(k), that holds a version
   of y;
2. the record of y's latest version before the section, in R(0), ...,
   R(s - 1), when y has a version in the section: the version just before
   y's first version there, which Java's version names as its `prevPos`;
3. the record of the version that b holds, b's position (`sectionPos`).

Read backwards, it is the converse of question 1: a pointer whose record is
none of the three names no node with a canonical object. A pointer that
names a vpos (`p.ref = none`) is left out: in Java a vpos is its node's id.

**2. Java's rule 4 by position, in the model (question 4).** Four
definitions in SIS/Handle.lean, beside `HMem.linkD` and `handleStartup`:

    def inPosToId (sp : Spec V T) (S : Stream V T) (s : Nat) (y : NodeId) (r : Nat) : Bool :=
      (List.range' s (S.length - s)).any (fun f =>
        match S.versionAt f y with
        | some w => !w.isData && (f == r ||
            (isKeyLevel sp w.isData w.level && (Stream.lv (S.take f) y).map (·.recNo) == some r))
        | none => false)

In words: Java's `posToId` has the position of y's version at r if some
record f of the section, R(s), ..., R(k), holds a version w of y that is
an index node version, and r is f itself, or r is the record of w's
previous version (y's latest version in the records before f) and w is a
key node version. Java writes a `prevPos` only in key node versions; top
node versions have none (011-03, G3).

    def HMem.byPos (m : HMem V) (y : NodeId) (r : Nat) : Option Nat :=
      match m.canonicalOf y with
      | some b => if (m.obj? b).bind (·.pos) == some r then m.tableOf y else none
      | none => none

In words: Java's `byPos`, the live handles of the canonical objects by the
positions of their versions: y's live handle, if y's canonical object is
the version at r.

    def HMem.linkDPos (sp : Spec V T) (S : Stream V T) (m : HMem V) (D : Dirty) : HMem V :=
      { m with objs := m.objs.map (fun p =>
          if !(p.2.canonical && (inD D p.2.node || p.1 == m.root)) then p else
          (p.1, { p.2 with ptrs := p.2.ptrs.map (fun q =>
            let byId : NodeId × HPtr := match m.canonicalOf q.1 with
              | some _ => (q.1, { q.2 with handle := m.tableOf q.1 })
              | none => q
            match q.2.handle, q.2.ref with
            | some _, _ => q
            | none, none => byId
            | none, some r =>
              if inPosToId sp S m.s q.1 r then byId else
              match m.byPos q.1 r with
              | some n => (q.1, { q.2 with handle := some n })
              | none => if isKeyLevel sp p.2.isData p.2.level then q else byId) })) }

    def handleStartupPos (sp : Spec V T) (S : Stream V T) : HMem V :=
      (((lazyStartup sp S).sectionPos S).toH).linkDPos sp S (startup sp S).D

In words: the same objects and pointers as `HMem.linkD`, and for a pointer
that holds no handle, Java's `NodeCollection.linkToCanonical` as committed
in `07b6375`: a vpos is the node's id; a record in `posToId` gives the id;
with the id, the node's live handle if it holds a canonical object, which
is rule 4 by node id (`byId`). Otherwise the handle that `byPos` gives. A
pointer that neither finds stays as it is, except a top node's, which Java
resolves by reading the header at its position: by node id. A top node is
an object that is not on a key level (`isKeyLevel`; with a virtual root, a
root child or the root). Java links pointers to index nodes only; the model
gives values handles (choice 5 of Handle.lean) and `HMem.linkD` links
them, so `linkDPos` does too: a value has one version, its canonical
object's, which `byPos` finds.

**3. The two rules are equal (question 4).**

    def Rule4Pos_handles (sp : Spec V T) (al : Algo V T) : Prop :=
      ∀ ts : List T, RunOK sp al ts → PhysRunOK sp al ts → EvictRunOK sp al ts →
        al.stillDirty = javaTest sp → al.mark = true →
        ∀ k ≤ ts.length,
          handleStartupPos sp (run sp al (ts.take k)).S = handleStartup sp (run sp al (ts.take k)).S

In words: in such a run, the startup with rule 4 by position from the
stream after any transaction gives the same memory as the startup with
rule 4 by node id. Every startup of `runHandles` starts from such a stream
(T2-C: its stream is the run's), so T2-C, T-READ with restarts and T-PIN
hold with rule 4 by position in the model's startup (4). The memory before
rule 4 is the model's startup's, which raises more pointers by Rule R than
Java's can (Outcome, 4a.7).

**4. The runs.** Added with the proof: in SIS/Handle.lean,

    def runHandlesPos (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List HCacheOp)) :
        DB V T × HMem V × Stream V T :=
      ts.foldl (fun (acc : DB V T × HMem V × Stream V T) p =>
        let r := handleTrans sp al acc.2.2 acc.1 acc.2.1 p.1
        if p.2.1 then (startup sp r.1.S, handleStartupPos sp r.1.S, r.1.S) else
        (r.1, p.2.2.foldl (HMem.cacheOp sp acc.2.2 r.1.S r.1.D) r.2, acc.2.2))
        (init sp, handleStartupPos sp (init sp).S, (init sp).S)

`runHandles` with `handleStartupPos` at R(0) and at every restart; and in
SIS/HandleTheorems.lean,

    def RunPos_handles (sp : Spec V T) (al : Algo V T) : Prop :=
      ∀ ts : List (T × Bool × List HCacheOp),
        RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
        EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
        ∀ j ≤ ts.length, runHandlesPos sp al (ts.take j) = runHandles sp al (ts.take j)

In words: in a run as in T2-C, with reads, evictions and restarts, the run
with rule 4 by position at every startup is the model's run after every
transaction: the same state, memory and stream of the last startup.

**What it needs (question 2).** The hypotheses are T2-C's, nothing more:
no new assumption, and no invariant of the run that the model does not
have. "The version before" is y's latest version in the records before a
version (`Stream.lv (S.take f) y`); the model needs no version chain. Top nodes
need no exclusion: statement 1 holds for their pointers too, and for a top
node's pointer that neither map finds, `linkDPos` goes by node id, as Java
reads the header.

**The route (question 3), written before the proof, which follows it.**
Every stream pointer that the startup leaves is (a) a reference of a version
of the section after Rule R, which names a version of the section when its
pointee has one; (b) a reference of a version of the section that the
rerun's walk loads, which names its pointee's latest version at that
version's record (the record rule, `Inv.ref`); (c) a reference of the latest
version of a node without a version in the section, which the rerun's walk
loads at a time K of the section: such a node is current and clean at K, so
its version names the latest versions at K (`EvLogic.clean`: D closed upward
and Rule A); or (d) a copy of one of these, made by a split. In each case no
version of the pointee lies between the version the pointer names and the
section, which is statement 1. Statement 3 follows from it, with A4 (a key
node points to key nodes and values) and a value's one version.


State, 2026-10-27 12:30
-----------------------

(The Outcome below reviews this state and does what it leaves.)

By Claude (Opus 5.5, Claude Code), stopped at the main session's request so
that another agent can take the work over. Nothing is committed; the work is
in the clone `/Users/f/fl/bench/006-09/lean58/` (on `565499f`), uncommitted,
and its patch is
[58-lean-rule4-by-position/rule4-by-position.diff](58-lean-rule4-by-position/rule4-by-position.diff)
(`git diff -- lean/` in the clone, the new file included).

**Proved.** The three statements, with no `sorry`; `lake build` in the clone's
`lean/` passes, 163 jobs, with no warnings; `#print axioms` of
`rule4_positions`, `rule4Pos_handles` and `runPos_handles` prints
`[propext, Classical.choice, Quot.sound]`, as do `tc_handles`, `tr_handles`,
`t2_handles`, `tr_handles_restarts` and `tp_handles` after the change.

* `Rule4_positions` and `Rule4Pos_handles` as in "The statement" above, with
  one change of spelling: `Stream.lv (S.take s) y` for `(S.take s).lv y`
  (`S.take s` is a `List`, so the dot notation does not find `Stream.lv`).
* `RunPos_handles`, added after the statement was written: the run with rule 4
  by position at every startup (`runHandlesPos`, a copy of `runHandles` with
  `handleStartupPos`) is `runHandles` after every transaction, under T2-C's
  hypotheses. It makes "T2-C, T-READ with restarts and T-PIN hold for Java's
  rule 4" a theorem.

**Files changed in the clone's `lean/`.** Trusted: SIS/Handle.lean
(`inPosToId`, `HMem.byPos`, `HMem.linkDPos`, `handleStartupPos`,
`runHandlesPos`; the header's startup bullet), SIS/HandleTheorems.lean (the
three statements; the header). Proofs: SIS/Proof/EvictRerun.lean (`RInv` has
two more fields, `near` and `keys`, proved in `rinv_lazyBase`,
`RInv.reachOnPath` and `RInv.applyChange`; lemmas `NearSec`,
`Inv.nearSec_of_lv`, `Inv.nearSec_of_ref`, `Inv.ref_mem_pointees`,
`Inv.nearSec_of_lvAt`, `clean_ref_lvAt`), SIS/Proof/HandleLinkPos.lean (new,
527 lines), SIS.lean (imports it), README.md (intro, the axioms list, both
tables, a Status entry of 2026-10-27).

**What the model showed.** The route of "The statement" holds: every stream
slot that the lazy startup leaves is a version of the section with Rule R, a
section version's own reference (the record rule, `Inv.ref`), a reference of
the latest version of a node with no version in the section that the rerun's
walk loads at a time K of the section, when the node is current and clean
(not in D: a node of D without a section version got dirty in the section
and has a canonical object by then, `MemInv.coverGd`), so it names the latest
versions at K (`EvLogic.clean`), or a copy of one of these. No new assumption
was needed. The equality needs, besides `RInv.near`: that every slot is for a
pointee of its object's history (`RInv.keys`, new), with A4 (`PtrsOK`) and
CanonOK's level, to show that the first section version of a key node's
pointee is a key node version (Java's `prevPos`); and a data node's one
version (`DataOnce`).

**Left.**

1. The "Outcome" section of this entry (names, files, plain English, what it
   needs, proof size: about 270 lines added to EvictRerun.lean and 527 in
   HandleLinkPos.lean, 140 trusted; axioms as above).
2. A read of the proof file for clarity; the trace tests (`sh
   test-traces/run.sh`) were not run (no checker definition changed, only
   additions).
3. Then the main session copies `lean/` from the clone (or applies the
   patch) and commits; 005-57's report and `docs/levels.md` may cite it.

**Traps met.** `lake env lean` on a file uses the built `.olean`s of its
imports, which may be stale after an edit upstream: build the edited module
first (`lake build SIS.Handle`), and run a full `lake build` at the end. In
`before_canon`, `Mem.toH_canonicalOf` needs `(m := ...)`, or Lean infers the
memory from the `TblND` argument. `(toH m).s` is `lastSp S` only through
`MemInv.sEq`, not by `rfl`. `if_pos` is deprecated (use `simp only [h,
↓reduceIte]`).


Outcome
-------

2026-10-27, by Claude (Opus 5.5, Claude Code), at max effort: a review of
the work above, with the code in front of it, and the rest of the work.
Nothing is in main yet: the work is one commit, `7c1ce2f` (lean/ only, on
main's `78a6723`), in the clone `/Users/f/fl/bench/006-09/lean58/`, and its
patch is
[58-lean-rule4-by-position/rule4-by-position.diff](58-lean-rule4-by-position/rule4-by-position.diff).

**1. The theorems.** Three statements in lean/SIS/HandleTheorems.lean
(trusted), proved in lean/SIS/Proof/HandleLinkPos.lean for every spec `sp`
and algorithm `al`. They use five new definitions in lean/SIS/Handle.lean
(trusted), shown under "The statement": `inPosToId` (Java's `posToId`),
`HMem.byPos` (Java's `byPos`), `HMem.linkDPos` (Java's
`NodeCollection.linkToCanonical`), `handleStartupPos` and `runHandlesPos`
(the startup and the run with it). Below, "a run" is a list of transactions
of BergDB's algorithm with marking (`al.stillDirty = javaTest sp`,
`al.mark = true`) that meets the model's assumptions (`RunOK`, `PhysRunOK`,
`EvictRunOK`), as in T2-C.

1. `Rule4_positions`, proved by `rule4_positions` (question 1). With S the
   stream after any transaction k of a run, s its startup pos and m the
   memory just before rule 4:

       ∀ a o y p r b, m.obj? a = some o → o.canonical = true →
         (inD (startup sp S).D o.node = true ∨ a = m.root) →
         (y, p) ∈ o.ptrs → p.handle = none → p.ref = some r →
         m.canonicalOf y = some b →
         (s ≤ r ∧ (S.versionAt r y).isSome) ∨
         ((newest S s y).isSome ∧ (Stream.lv (S.take s) y).map (·.recNo) = some r) ∨
         (m.obj? b).bind (·.pos) = some r

   In words: take a pinned object o (the canonical object of a node of D, or
   the root's object) and a pointer of o that holds no handle and names
   record r, for a node y that has a canonical object b. Then r is a record
   of the startup section with a version of y; or the record of y's last
   version before the section, when y has a version in the section; or the
   record of b's version.

2. `Rule4Pos_handles`, proved by `rule4Pos_handles` (question 4), for every
   k up to the length of the run:

       handleStartupPos sp (run sp al (ts.take k)).S = handleStartup sp (run sp al (ts.take k)).S

   In words: from the stream after any transaction, the startup with rule 4
   by position gives exactly the memory that the startup with rule 4 by node
   id gives.

3. `RunPos_handles`, proved by `runPos_handles`, for every j, now with
   reads, evictions and restarts between the transactions:

       runHandlesPos sp al (ts.take j) = runHandles sp al (ts.take j)

   In words: a run whose every startup uses rule 4 by position is the
   model's run (`runHandles`): the same state, memory and stream. So T2-C,
   T-READ with restarts and T-PIN over handles hold for it as they are.
   `runHandlesPos_of_startup` checks that `runHandlesPos` differs from
   `runHandles` only in its startups: with the same startup it would be the
   same run.

**2. What it needs (questions 2 and 3).** The hypotheses are T2-C's: no new
assumption. "The version before" is `Stream.lv (S.take f) y`, y's latest
version in the records before f; the model needs no version chain. Top
nodes need no exclusion: statement 1 holds for their pointers too, and
`linkDPos` takes a top node's pointer that neither map finds by node id, as
Java reads its header. The proof follows the route of "The statement" and
rests on theorems of the model: the record rule (`Inv.ref`); a node that the
rerun's walk loads without a version in the section is current and clean
then, so its version names the latest versions (`EvLogic.clean`: D closed
upward and Rule A); a node of D without a version in the section has a
canonical object from the transaction it got dirty in (`MemInv.coverGd`:
the take's invariant); A4 (`PtrsOK`: a key node points to key nodes and
data nodes); a data node's one version (`DataOnce`); and T2-C for the runs
(`t2_handles`). TREE, A6' and A-COPY (`EvictRunOK`) enter through those
theorems. New: two more facts of E5's rerun invariant in
lean/SIS/Proof/EvictRerun.lean, `RInv.near` (no version of a stream slot's
pointee lies between the slot's record and the section) and `RInv.keys`
(every slot is for a pointee of its object's history).

**3. Size, axioms, gates.** Trusted: 81 lines added to SIS/Handle.lean and
71 to SIS/HandleTheorems.lean, mostly comments: five definitions in 34
lines, three statements in 24. Proofs: SIS/Proof/HandleLinkPos.lean, new,
537 lines; 261 lines added to SIS/Proof/EvictRerun.lean. Examples: 65 lines
in SIS/HandleExample.lean. `#print axioms` prints `[propext,
Classical.choice, Quot.sound]` for the three theorems, for `tc_handles`,
`tr_handles`, `t2_handles`, `tr_handles_restarts` and `tp_handles`, and for
every theorem of lean/README.md's lists (`LM_cutTo`, `T3_section`,
`T3_restarts` and `Fast.step_eq_fast` without `Classical.choice`). No
`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`,
`extern` or `partial` anywhere in lean/. `lake build`: 163 jobs, no
warnings, also from scratch on the commit (40 s); `sh test-traces/run.sh`:
TRACE TESTS OK.

**4. The review.**

a. *The definitions against Java* (`DbStarter.createMaps` and `linkD`,
   `NodeCollection.linkToCanonical`, at `07b6375`). They match line by line,
   but for these differences; none changes the claim.

   1. `prevPos`. The model has no such field: `inPosToId` takes the record
      of the node's latest version before the record. Java writes the
      canonical object's position just before the write
      (`StoredTrans.prepareToSerialize`), which is that version: in the
      model a canonical object is at its node's latest record (`HCanOK`). A
      new node's `prevPos` is NULL in Java, none here. The trace checker
      does not see `prevPos`.
   2. Positions. A Java position names one version; the model uses the pair
      of a record and the pointer's node. The id that `posToId` gives is
      always the pointer's node (a version's `prevPos` is its own node's
      earlier version), and so is the object that `byPos` gives. Same.
   3. The order. A vpos or `posToId` gives the id, and then only the node's
      live handle counts, never `byPos`; else `byPos`; else, for a top
      node's pointer, the header. Same as Java's `live == null && id == null
      && top`.
   4. Top nodes. Java tests the object that holds the pointer
      (`TYPE_TOP_NODE`); the model, that it is not on a key level: a root
      child or the root with a virtual root (none without one, which is not
      Java's case). Java does not run rule 4 on the root (TopDs holds its
      super root); the model's root object stands for TopDs, and
      `HMem.linkD` and `linkDPos` both link it by node id. Same result.
   5. Values. Java's rule 4 skips pointers to value nodes; the model gives
      values handles and `HMem.linkD` links them (Handle.lean's choice 5),
      so `linkDPos` does too, by `byPos`. A model addition, which the
      theorem covers.
   6. Java skips a pointer below the stream's first position, cut by
      reclaim, in both rules; the model with handles has no cuts, so this is
      not covered. Java's null pointers have no counterpart in the model.
   7. The memory before rule 4, outside the new definitions. The model's
      startup applies Rule R by node id to every slot of the canonical
      objects it makes from versions (`canonOfVersion`: the section's
      objects, the root, and the objects of `canonicalNode` for D) and links
      them by position (`Mem.linkCanonical`). Java can apply Rule R only
      where `posToId` gives the node (`updateStreamPointers`), and not at
      all to the nodes that `canonicalNode` reads. For key nodes the two
      leave rule 4 the same pointers: a key node's pointer to an index node
      with a version in the section names a version that `posToId` knows
      (the record rule and A4), and in the example runs below no object
      that `canonicalNode` read had a reference that Rule R changes. A top
      node's pointer to a top node's version before the section is
      different: Java's rule 4 meets it and reads its header; the model has
      raised and linked it before. In the 20 example runs below the model
      raised 10 references that `posToId` does not know (counted at each
      startup), all of a top node's pointer to a top node.

b. *The statements* say what questions 1 and 4 ask, for the startup that the
   model uses (`handleStartup`), from the stream after every transaction of
   a run, R(0) included; and `RunPos_handles` for `runHandles` itself, with
   restarts. The hypotheses can hold together: examples 3 and 5 meet them
   (their `Bool` twins `runOKB`, `physRunOKB` and `evictRunOKB`, on 20 runs:
   seeds 1 to 12 of example 5 with 60 transactions, 1 to 8 of example 3 with
   40). The conclusion says something there: rule 4 links 434 pointers in
   the 1,060 startups of those runs (none in six runs of example 2, with a
   written root). No quantifier makes them weaker than they read: every
   pointer of every pinned object, every k, every j.

   One limit, found by running: all 434 pointers are of the third kind, at
   their canonical object's position, which `byPos` finds. None names a
   version of the section or the version before one, and no top node's
   pointer needs its header (SIS/HandleExample.lean, `rule4Counts`, checks
   two of the runs at every build). So in these runs the model never takes
   `linkDPos`'s `posToId` branch or its header read: the theorem covers
   them, but no state has such a pointer. That leaves no gap where the
   claim needs a proof. What Java links by `posToId`, by `byPos` or by the
   header is what rule 4 by node id links, by construction (a position
   names one version). The one case where the two rules could differ is a
   pointer that rule 4 by position leaves: a key node's pointer in neither
   map. For key nodes the model leaves rule 4 the pointers that Java leaves
   (a.7's argument), and the theorem says that such a pointer names no node
   with a canonical object. That holds as far as the model's startup is
   aligned with Java's. (By the same reasoning Java's rule 4 may never need
   `posToId` for a key node's pointer; not measured.)

c. *Soundness*: as in 3. The trusted files differ from `565499f` by
   additions and two changed comment lines; no definition or statement that
   was there changed. E5's `RInv` has two more fields; it is a proof-side
   invariant, so earlier proofs changed, not their statements.

d. *The trusted part.* Each of the five definitions and three statements is
   needed. `inPosToId` follows `createMaps`' loop literally, which makes it
   easy to check against Java. `runHandlesPos` is a copy of `runHandles`
   with `handleStartupPos` in its two startups; kept, and
   `runHandlesPos_of_startup` now checks that this is the only difference.
   Neither alternative is clearly better: `runHandles` with the startup as a
   parameter changes or copies `runHandles` too; a statement about
   `runHandles`'s own startups (`handleStartupPos` of the stream of its last
   startup is `handleStartup` of it) needs no definition, but leaves the
   step from there to the run to an argument.

Changed in the review: the comments of `Rule4_positions` (how `linkDPos`
finds each kind, the vpos, top nodes), `Rule4Pos_handles` (the memory is
the model's startup's, a.7, in place of "hold for Java's rule 4 as it is"),
`HMem.linkDPos` (reclaim, the root) and `runHandlesPos`;
`runHandlesPos_of_startup`, new; `rule4Counts` and its checks in
SIS/HandleExample.lean; lean/README.md. The commit is rebased on `78a6723`;
main's lean/ had not changed since `565499f`.

**5. Questions for Frans.**

1. The trusted additions: `inPosToId`, `HMem.byPos`, `HMem.linkDPos`,
   `handleStartupPos` and `runHandlesPos` in SIS/Handle.lean, and
   `Rule4_positions`, `Rule4Pos_handles` and `RunPos_handles` in
   SIS/HandleTheorems.lean. Recommended: take them as they are (4d).
2. The check under assertions in `NodeCollection.linkToCanonical` (rule 4 by
   node id beside rule 4 by position, with a header read for each pointer,
   at every startup of the tests). Recommended: keep it. It costs nothing
   when assertions are off. The theorem is about the model's startup, which
   differs from Java's in where Rule R is applied (4a.7) and has no reclaim
   cuts; the check compares the two rules on Java's own states, `posToId`'s
   branch included, which the model's runs never take. If you prefer it
   gone, the risk is small: the case that needs a proof, a key node's
   pointer in neither map, is covered.

Then the main session applies the patch (or copies lean/ from the clone)
and commits it, and 005-57's report and docs/levels.md cite it.
