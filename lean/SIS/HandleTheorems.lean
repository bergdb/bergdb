/-
Self-indexed streams in Lean: the statements of the physical layer with handles
(bergdb item 009, phase 2, step 2c). Trusted part: what is to be proved, stated
as definitions of type `Prop`, not as theorems, so that nothing here is
assumed or left unproved. A proof of `TC_handles sp al` for every `sp` and
`al` is step 2d (its first part, the records) and phase 4a; so are the others.

They mirror PhysTheorems.lean's `TC_records` (T-CACHE), `TR_view` (T-READ),
`TP_pins` (T-PIN), and `T2_cache` (T2-C) and `TR_view_restarts`, the forms
with restarts, where Rule R on the fast path matters; over the memory with
handles of SIS/Handle.lean, with the same assumptions: BergDB's bookkeeping
(`javaTest`, marking), the Level 2 assumptions (`RunOK`), those of the physical
layer (`PhysRunOK`) and those of stage 2 (`EvictRunOK`: TREE, A6' and A-COPY).
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

/-- INV-CAN with handles, in state db (TC_records' second and third parts): a
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
makes canonical objects only. With `HSnapWrittenOK`, the fast path's test with a
pointer's own reference (`HMem.followR`) then gives the slow path's answer
whenever the reference is not a vpos (`HFastOK`); and a stale read of a
reference that the writer is changing to its reference after Rule R
(`HMem.writeNode`) gives the same answer as the new reference. -/
def HRuleROK (S0 : Stream V T) (m : HMem V) : Prop :=
  ∀ n hd b o w, m.handle? n = some hd → hd.obj = some b → m.obj? b = some o →
    o.canonical = false → newest S0 m.s hd.node = some w → ∃ p, o.pos = some p ∧ w.recNo ≤ p

/-- The snapshots and the written positions: every snapshot that a handle
holds is at least as new as the handle's written position. A load installs a
version at least as new as it (`HMem.load`); a re-resolve that raises it
(choice 1 of Handle.lean) is followed at once by a load that compares with it
(choice 7). -/
def HSnapWrittenOK (m : HMem V) : Prop :=
  ∀ n hd b o w, m.handle? n = some hd → hd.obj = some b → m.obj? b = some o →
    o.canonical = false → hd.written = some w → ∃ p, o.pos = some p ∧ w ≤ p

/-- What `HRuleROK` and `HSnapWrittenOK` are for (open point 1): for every
pointer of an object in memory whose reference is a position (not a vpos) and
whose handle holds an object, the fast path's test with the pointer's own
reference gives what the slow path's test gives, with the larger of the
reference after Rule R and the handle's written position. So the fast path
needs neither Rule R nor the written position. It follows from `HTableOK`,
`HRuleROK` and `HSnapWrittenOK` (`hFastOK_of` in
SIS/Proof/HandleRecords.lean). -/
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

/-- T-CACHE with handles (bergdb item 009, 2c; `TC_records` over handles). For a
run of BergDB's algorithm (`javaTest`, with marking) that meets the assumptions,
those of the physical layer and those of stage 2, from the startup with handles
from R(0) (`handleStartup`), with any reads and evictions after each transaction
(`HCacheOp`, `runHandles`) and no restart: after every transaction and its
operations, the physical writer with handles (`handleTrans`) has appended
exactly the model's records and left the model's D (the state is the model's),
and the memory meets the invariants above: the table and the handles, INV-CAN,
INV-SNAP, INV-SLOT for the record rule, the snapshots against Rule R and
against the written positions, and references that name versions. The
operations being any, this holds whatever reads and evictions run between
transactions, in any order. The first part, that the records are the model's,
is step 2d. -/
def TC_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List (T × Bool × List HCacheOp),
    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
    EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    (∀ p ∈ ts, p.2.1 = false) →
    ∀ j ≤ ts.length,
      let db := run sp al ((ts.take j).map (·.1))
      let m := (runHandles sp al (ts.take j)).2.1
      (runHandles sp al (ts.take j)).1 = db ∧ HTableOK m ∧ HCanOK db m ∧ HSnapOK db m ∧
        HSlotOK sp (init sp).S db j m ∧ HRuleROK (init sp).S m ∧ HSnapWrittenOK m ∧
        HWrittenOK db m

/-- T2-C with handles (`T2_cache` over handles): T-CACHE with restarts. In a
run as in `TC_handles`, now with restarts after any transactions (after a
transaction marked true: the logical startup for ⟨P, D, S⟩ and the startup with
handles, `handleStartup`, for the memory), after every transaction and its
operations or its restart, the state is the run's without restarts: the same
records (so restarts change no record) and D, and P with the same nodes; and
the memory meets the invariants of `TC_handles` for the startup it last made,
from the run's stream after some earlier transaction k1 (Rule R from that
stream's section). Without restarts `HRuleROK` says nothing (every position is
at least the version in R(0)); after a restart it is what open point 1 needs. -/
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
        HRuleROK r.2.2 m ∧ HSnapWrittenOK m ∧ HWrittenOK db m

/-- T-READ with handles (`TR_view` over handles). In a run as in `TC_handles`
(BergDB's algorithm with marking, the assumptions, the startup with handles from
R(0), any reads and evictions, no restart), after any transaction and its
operations, a read through the handles (`HMem.read`: the fast path, or resolve
and load) at any time t up to the last record gives P at t: it reaches exactly
the nodes reachable at t, each with its node at t (level, kind and history at
t). The operations being any, this holds for every read between transactions,
and for the writer's own read at the last time. -/
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

/-- T-READ with handles and restarts (`TR_view_restarts` over handles). In a
run as in `T2_handles` (with restarts after any transactions), after any
transaction and its operations or its restart, a read through the handles (with
Rule R from the stream of the last startup) at any time t up to the last record
gives P at t. This is where open point 1 of 02 (Rule R on the fast path) matters
for reads: without a restart, Rule R changes nothing. -/
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

/-- T-PIN with handles (`TP_pins` over handles; 02, 2c: "every LIVE handle whose
object is not pinned and is written may be evicted, in one step"). In a run as
in `TC_handles`, now with restarts after any transactions too (as `TP_pins`),
after any transaction and its operations or its restart: every live handle whose
object is not pinned (`HMem.pinned`: the canonical objects of the nodes of D,
and the root's object) may be evicted (`HMem.evictable`: its object has been
written), and one eviction (`HCacheOp.evict`) removes the object from memory and
kills the handle. The second part is by the definition of `HMem.evict`; the
first, that every object outside the pinned set has been written, is what needs
a proof (as `EInv.detachable_of_unpinned` for Evict.lean). With `TC_handles` and
`TR_handles`, which hold for any operations, the pinned set is all that must
stay: no walk, and nothing about the pointers that hold a handle. -/
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

end SIS
