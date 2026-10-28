/-
Self-indexed streams in Lean: the statements of the physical layer with handles
(bergdb item 009, phase 2, step 2c). Trusted part: what is to be proved, stated
as definitions of type `Prop`, not as theorems, so that nothing here is
assumed or left unproved. All are proved for every `sp` and `al`:
`TC_handles` (`tc_handles`, SIS/Proof/HandleRecords.lean; step 2d),
`TR_handles` (`tr_handles`, SIS/Proof/HandleReadT.lean), `T2_handles` and
`TR_handles_restarts` (`t2_handles`, `tr_handles_restarts`,
SIS/Proof/HandleRestart.lean), and `TP_handles` (`tp_handles`,
SIS/Proof/HandlePin.lean); the last four in phase 4a. And rule 4 by position
(bergdb 005-58): `Rule4_positions`, `Rule4Pos_handles` and `RunPos_handles`
(`rule4_positions`, `rule4Pos_handles`, `runPos_handles`,
SIS/Proof/HandleLinkPos.lean).

They are stage 2's T-CACHE, T-READ, T-PIN and T2-C (bergdb item 001, WPs E3
to E6; bergdb 001-08, sections 5.11 to 5.14), and the forms with restarts, where
Rule R on the fast path matters, over the memory with handles of SIS/Handle.lean
(stated over Evict.lean's memory before handles, as PhysTheorems.lean's
`TC_records`, `TR_view`, `TP_pins`, `T2_cache` and `TR_view_restarts`, until
bergdb 005-62). The assumptions: BergDB's bookkeeping (`javaTest`, marking), the
Level 2 assumptions (`RunOK`), those of the physical layer (`PhysRunOK`) and
those of stage 2 (`EvictRunOK`: TREE, A6' and A-COPY; SIS/Phys.lean).
SIS/HandleExample.lean checks each of them by running, with the `Bool` twins
of the invariants below.
-/
import SIS.Handle
import SIS.Assumptions

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariants (02, 4.10, the audit) -/

/-- The table and the handles (02, 4.1, 4.3 and 4.10). Every entry of the table
names a live handle of its node that holds an object in memory, of that node;
the table has one entry per node; every live handle is its node's entry in the
table (so a node has at most one live handle); a dead handle holds no object
(and, by the first part, is not in the table); every object in memory is held
by its node's live handle (so a node has at most one object in memory); and
every handle that a pointer holds exists and is of the pointer's pointee. -/
def HTableOK (m : HMem V) : Prop :=
  (∀ y n, m.tableOf y = some n → ∃ hd a o, m.handle? n = some hd ∧ hd.dead = false ∧
    hd.node = y ∧ hd.obj = some a ∧ m.obj? a = some o ∧ o.node = y) ∧
  (m.table.map (·.1)).Nodup ∧
  (∀ n hd, m.handle? n = some hd → hd.dead = false → m.tableOf hd.node = some n) ∧
  (∀ n hd, m.handle? n = some hd → hd.dead = true → hd.obj = none) ∧
  (∀ a o, m.obj? a = some o → ∃ n, m.tableOf o.node = some n ∧ m.objOf n = some a) ∧
  (∀ a o y p n, m.obj? a = some o → o.ptr? y = some p → p.handle = some n →
    ∃ hd, m.handle? n = some hd ∧ hd.node = y)

/-- INV-CAN with handles, in state db (part of T-CACHE): a
canonical object is its node's canonical object (the object of its live
handle), holds its node's whole history, level and kind, and its position is its
node's latest record; every node of D has a canonical object. -/
def HCanOK (db : DB V T) (m : HMem V) : Prop :=
  (∀ a o, m.obj? a = some o → o.canonical = true →
    m.canonicalOf o.node = some a ∧
    (∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData) ∧
    o.pos = (db.S.lv o.node).map (·.recNo)) ∧
  (∀ y, inD db.D y = true → (m.canonicalOf y).isSome)

/-- INV-SNAP with handles: every object that is not canonical is exactly the
version of the stream at its position. -/
def HSnapOK (db : DB V T) (m : HMem V) : Prop :=
  ∀ a o, m.obj? a = some o → o.canonical = false → ∃ r w, o.pos = some r ∧
    db.S.versionAt r o.node = some w ∧ o.hist = w.hist ∧ o.level = w.level ∧ o.isData = w.isData

/-- INV-SLOT with handles, the obligation of the record rule (02, 4.6; 004-01,
4.4), at time k after a startup from S0: a canonical object of a written node
that is current at k or in D has a pointer for each pointee of its history, live
or dead; writing it now would give each pointee its latest version
(`HMem.refOf`: a pointee of D by node id, any other by the record rule); and its
pointer for a pointee y in D holds y's live handle with y's canonical object, or
belongs to a node of D that got dirty no later than y (so it is written no
later than y). -/
def HSlotOK (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (k : Nat) (m : HMem V) : Prop :=
  ∀ a o, m.obj? a = some o → o.canonical = true → written sp o.node = true →
    (reachable sp db.P k o.node = true ∨ inD db.D o.node = true) →
    ∀ y ∈ pointees sp o.hist, (o.ptr? y).isSome ∧
      m.refOf S0 db.D o y = (db.S.lv y).map (·.recNo) ∧
      (inD db.D y = true →
        (∃ p n, o.ptr? y = some p ∧ p.handle = some n ∧ m.tableOf y = some n ∧
          (m.canonicalOf y).isSome) ∨
        (inD db.D o.node = true ∧ ∃ a b, (o.node, a) ∈ db.D ∧ (y, b) ∈ db.D ∧ a ≤ b))

/-- Rule R and the snapshots, after a startup from S0 (open points 1 and 2 of
02, section 7): every snapshot that a handle holds is at least as new as its
node's newest version in the startup section, R(s), ..., R(k) of S0. A snapshot
is only ever loaded by the slow path, which applies Rule R, and the startup
makes canonical objects only. With `HLiveWrittenOK`, the fast path's test with a
pointer's own reference (`HMem.followR`) then gives the slow path's answer
whenever the reference is not a vpos (`HFastOK`); and a stale read of a
reference that the writer, or the slow path, is changing to its reference after
Rule R (`HMem.writeNode`, `HMem.followR`) gives the same answer as the new
reference. -/
def HRuleROK (S0 : Stream V T) (m : HMem V) : Prop :=
  ∀ n hd b o w, m.handle? n = some hd → hd.obj = some b → m.obj? b = some o →
    o.canonical = false → newest S0 m.s hd.node = some w → ∃ p, o.pos = some p ∧ w.recNo ≤ p

/-- Live handles have no written position: only an eviction sets one, from a
canonical object's position, and it kills the handle (choice 1 of Handle.lean,
as Java's `Cache3.evict`). So the record rule for a pointer that holds a live
handle is its canonical object's position, or the pointer's own reference after
Rule R. -/
def HLiveWrittenOK (m : HMem V) : Prop :=
  ∀ n hd, m.handle? n = some hd → hd.dead = false → hd.written = none

/-- What `HRuleROK` and `HLiveWrittenOK` are for (open point 1): for every
pointer of an object in memory whose reference is a position (not a vpos) and
whose handle holds an object, the fast path's test with the pointer's own
reference gives what the slow path's test gives, with the pointer's reference
after Rule R raised to the handle's written position. So the fast path needs
neither Rule R nor a written position. It follows from `HTableOK`, `HRuleROK`
and `HLiveWrittenOK` (`hFastOK_of` in SIS/Proof/HandleMem.lean). -/
def HFastOK (S0 : Stream V T) (m : HMem V) : Prop :=
  ∀ a o y p n hd b ob r, m.obj? a = some o → o.ptr? y = some p → p.handle = some n →
    m.handle? n = some hd → hd.obj = some b → m.obj? b = some ob → p.ref = some r →
    ob.usable p.ref = ob.usable (maxRef (ruleRRef S0 m.s y p.ref) hd.written)

/-- References and written positions name versions: a handle's written
position, and a pointer's reference, is a record of the stream that holds a
version of the node. -/
def HWrittenOK (db : DB V T) (m : HMem V) : Prop :=
  (∀ n hd w, m.handle? n = some hd → hd.written = some w → (db.S.versionAt w hd.node).isSome) ∧
  (∀ a o y p r, m.obj? a = some o → o.ptr? y = some p → p.ref = some r →
    (db.S.versionAt r y).isSome)

/-! ## The theorems to prove -/

/-- T-CACHE with handles (bergdb item 009, 2c; bergdb 001-08, 5.11). For a
run of BergDB's algorithm (`javaTest`, with marking) that meets the assumptions,
those of the physical layer and those of stage 2, from the startup with handles
from R(0) (`handleStartup`), with any reads and evictions after each transaction
(`HCacheOp`, `runHandles`) and no restart: after every transaction and its
operations, the physical writer with handles (`handleTrans`) has appended
exactly the model's records and left the model's D (the state is the model's),
and the memory meets the invariants above: the table and the handles, INV-CAN,
INV-SNAP, INV-SLOT for the record rule, the snapshots against Rule R, live
handles without written positions, and references that name versions. The
operations being any, this holds whatever reads and evictions run between
transactions, in any order. Proved: `tc_handles`, and the first part, that the
records are the model's, alone: `TC_handles_records` (SIS/Proof/HandleRecords.lean). -/
def TC_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List (T × Bool × List HCacheOp),
    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
    EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    (∀ p ∈ ts, p.2.1 = false) →
    ∀ j ≤ ts.length,
      let db := run sp al ((ts.take j).map (·.1))
      let m := (runHandles sp al (ts.take j)).2.1
      (runHandles sp al (ts.take j)).1 = db ∧ HTableOK m ∧ HCanOK db m ∧ HSnapOK db m ∧
        HSlotOK sp (init sp).S db j m ∧ HRuleROK (init sp).S m ∧ HLiveWrittenOK m ∧
        HWrittenOK db m

/-- T2-C with handles (bergdb 001-08, 5.13): T-CACHE with restarts. In a
run as in `TC_handles`, now with restarts after any transactions (after a
transaction marked true: the logical startup for ⟨P, D, S⟩ and the startup with
handles, `handleStartup`, for the memory), after every transaction and its
operations or its restart, the state is the run's without restarts: the same
records (so restarts change no record) and D, and P with the same nodes; and
the memory meets the invariants of `TC_handles` for the startup it last made,
from the run's stream after some earlier transaction k1 (Rule R from that
stream's section). Without restarts `HRuleROK` says nothing (every position is
at least the version in R(0)); after a restart it is what open point 1 needs.
Proved: `t2_handles` (SIS/Proof/HandleRestart.lean). -/
def T2_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List (T × Bool × List HCacheOp),
    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
    EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    ∀ j ≤ ts.length,
      let db := run sp al ((ts.take j).map (·.1))
      let r := runHandles sp al (ts.take j)
      let m := r.2.1
      r.1.S = db.S ∧ r.1.D = db.D ∧ (∀ x, r.1.P.get? x = db.P.get? x) ∧
      ∃ k1, k1 ≤ j ∧ r.2.2 = (run sp al ((ts.take k1).map (·.1))).S ∧
        HTableOK m ∧ HCanOK db m ∧ HSnapOK db m ∧ HSlotOK sp r.2.2 db j m ∧
        HRuleROK r.2.2 m ∧ HLiveWrittenOK m ∧ HWrittenOK db m

/-- T-READ with handles (bergdb 001-08, 5.12). In a run as in `TC_handles`
(BergDB's algorithm with marking, the assumptions, the startup with handles from
R(0), any reads and evictions, no restart), after any transaction and its
operations, a read through the handles (`HMem.read`: the fast path, or resolve
and load) at any time t up to the last record gives P at t: it reaches exactly
the nodes reachable at t, each with its node at t (level, kind and history at
t). The operations being any, this holds for every read between transactions,
and for the writer's own read at the last time. Proved: `tr_handles`
(SIS/Proof/HandleReadT.lean). -/
def TR_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List (T × Bool × List HCacheOp),
    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
    EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    (∀ p ∈ ts, p.2.1 = false) →
    ∀ j ≤ ts.length, ∀ t ≤ j,
      let db := run sp al ((ts.take j).map (·.1))
      let m := (runHandles sp al (ts.take j)).2.1
      (m.read sp (init sp).S db.S t).2.map (·.1) = reachList sp db.P t ∧
        ∀ p ∈ (m.read sp (init sp).S db.S t).2, view sp db.P t p.1 = some p.2

/-- T-READ with handles and restarts (bergdb 001-08, 5.13). In a
run as in `T2_handles` (with restarts after any transactions), after any
transaction and its operations or its restart, a read through the handles (with
Rule R from the stream of the last startup) at any time t up to the last record
gives P at t. This is where open point 1 of 02 (Rule R on the fast path) matters
for reads: without a restart, Rule R changes nothing. Proved:
`tr_handles_restarts` (SIS/Proof/HandleRestart.lean). -/
def TR_handles_restarts (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List (T × Bool × List HCacheOp),
    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
    EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    ∀ j ≤ ts.length, ∀ t ≤ j,
      let db := run sp al ((ts.take j).map (·.1))
      let r := runHandles sp al (ts.take j)
      let m := r.2.1
      (m.read sp r.2.2 db.S t).2.map (·.1) = reachList sp db.P t ∧
        ∀ p ∈ (m.read sp r.2.2 db.S t).2, view sp db.P t p.1 = some p.2

/-- T-PIN with handles (bergdb 001-08, 5.14; 02, 2c: "every LIVE handle whose
object is not pinned and is written may be evicted, in one step"). In a run as
in `TC_handles`, now with restarts after any transactions too,
after any transaction and its operations or its restart: every live handle whose
object is not pinned (`HMem.pinned`: the canonical objects of the nodes of D,
and the root's object) may be evicted (`HMem.evictable`: its object has been
written), and one eviction (`HCacheOp.evict`) removes the object from memory and
kills the handle. The second part is by the definition of `HMem.evict`; the
first, that every object outside the pinned set has been written, is what needs
a proof (`HEInv.evictable_of_unpinned`). With `TC_handles` and `TR_handles`,
which hold for any operations,
the pinned set is all that must stay: no walk, and nothing about the pointers
that hold a handle. Proved: `tp_handles` (SIS/Proof/HandlePin.lean). -/
def TP_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List (T × Bool × List HCacheOp),
    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
    EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    ∀ j ≤ ts.length,
      let r := runHandles sp al (ts.take j)
      let m := r.2.1
      ∀ n hd a, m.handle? n = some hd → hd.dead = false → hd.obj = some a →
        m.pinned r.1.D a = false →
        m.evictable r.1.D n = true ∧
        (m.cacheOp sp r.2.2 r.1.S r.1.D (.evict n)).obj? a = none ∧
        ((m.cacheOp sp r.2.2 r.1.S r.1.D (.evict n)).handle? n).map (·.dead) = some true

/-! ## Rule 4 by position (bergdb 005-58) -/

/-- The positions of rule 4 (bergdb 005-58, question 1; the argument of 005-57's
report, section 2). In a run of BergDB's algorithm with marking that meets the
assumptions, as in `T2_handles`, take the startup with handles from the stream S
after any transaction k, just before rule 4: m, the memory that `handleStartup`
gives `HMem.linkD`, with s the startup pos. Every pointer of a pinned object (the
canonical object of a node of D, or the root's object) that holds no handle and
names a record r, to a node y that has a canonical object b, names (1) a version
of y in the startup section, R(s), ..., R(k); or (2) y's latest version before
it, in R(0), ..., R(s - 1), when y has a version in the section: the version just
before y's first version there (Java's `prevPos`); or (3) the version of b, b's
position. A pointer that names a vpos (`p.ref = none`) is left out: Java takes a
vpos as its node's id. So Java's rule 4 by position (`HMem.linkDPos`) finds the
pointer's node (`Rule4Pos_handles`): by `posToId` in (1), and in (2) when y is a
key node, whose versions name their `prevPos`; by `byPos` in (3) and for a data
node. In (2) for a top node y, the pointer is a top node's or the root's, which
`HMem.linkDPos` takes by node id, as Java reads the header for a top node's.
Proved: `rule4_positions` (SIS/Proof/HandleLinkPos.lean). -/
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

/-- Rule 4 by position is rule 4 by node id (bergdb 005-58, question 4). In a
run as in `Rule4_positions`, the startup with handles and rule 4 by position
(`handleStartupPos`, Java's since bergdb 005-57) from the stream after any
transaction k gives the same memory as the startup with rule 4 by node id
(`handleStartup`). Every startup of `runHandles` is from such a stream (T2-C:
its stream is the run's), so the theorems over handles with restarts hold with
rule 4 by position too (`RunPos_handles`). The memory before rule 4 is the
model's startup's, which applies Rule R by node id to the slots of the canonical
objects it makes from versions, of the section and for the nodes of D
(`canonOfVersion`); Java's startup can apply it only where `posToId` gives the
pointer's node. So a pointer that reaches Java's rule 4 with no handle may be
raised by Rule R or linked here before it: a top node's pointer to a top node's
version before the section, whose header Java reads (bergdb 005-58, Outcome).
Proved: `rule4Pos_handles` (SIS/Proof/HandleLinkPos.lean). -/
def Rule4Pos_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List T, RunOK sp al ts → PhysRunOK sp al ts → EvictRunOK sp al ts →
    al.stillDirty = javaTest sp → al.mark = true →
    ∀ k ≤ ts.length,
      handleStartupPos sp (run sp al (ts.take k)).S = handleStartup sp (run sp al (ts.take k)).S

/-- Runs with rule 4 by position are runs with rule 4 by node id (bergdb 005-58).
In a run as in `T2_handles`, the run with handles and rule 4 by position at every
startup (`runHandlesPos`) is the same as the run with rule 4 by node id
(`runHandles`) after every transaction and its operations or its restart: the
same state, memory and stream of the last startup. So `T2_handles`,
`TR_handles_restarts` and `TP_handles` hold for it as they are. Proved:
`runPos_handles` (SIS/Proof/HandleLinkPos.lean). -/
def RunPos_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List (T × Bool × List HCacheOp),
    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
    EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    ∀ j ≤ ts.length, runHandlesPos sp al (ts.take j) = runHandles sp al (ts.take j)

end SIS
