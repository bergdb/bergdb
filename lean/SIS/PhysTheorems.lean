/-
Self-indexed streams in Lean: the theorems of the physical layer (bergdb item
001, stages 1 and 2). Trusted part: the statements. The proofs are in
SIS/Proof/; the proofs here only connect them.
-/
import SIS.Theorems
import SIS.Proof.Newer
import SIS.Proof.PhysT2
import SIS.Proof.EvictInit
import SIS.Proof.EvictReadT
import SIS.Proof.EvictRestart

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Lemma M (bergdb item 001, WP L2; docs/level2-alignment.md, M8). In every
run, after every transaction: if version v of node x is good for time t (5.1),
so is every version w of x written at or after v. Java relies on it when it
reads a node on its first touch after a restart: it takes the newer of the
version that the pointer names and the node's version in the startup section,
or the object it already holds. -/
theorem LM_newer (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (j : Nat) (hj : j ≤ ts.length) (x : NodeId) (r r' : Nat) (v w : Version V) (t : Time)
    (hv : (run sp al (ts.take j)).S.versionAt r x = some v)
    (hw : (run sp al (ts.take j)).S.versionAt r' x = some w) (hrr : r ≤ r')
    (hg : good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t v = true) :
    good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t w = true := by
  have hinv := inv_st sp al ts hok (algOK_of sp al hst) j hj
  exact hinv.newer hok.1.liveSub (v.level + 1) r r' x v w (by omega) hv hw hrr t hg

/-- Lemma M with Rule R (WP L2): if a version of y is good for time t, so is
the newest version of y in R(s), ..., R(k), which Rule R follows instead of
the version a pointer names. For every startup pos s. -/
theorem LM_ruleR (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (j : Nat) (hj : j ≤ ts.length) (y : NodeId) (r s : Nat) (u w : Version V) (t : Time)
    (hu : (run sp al (ts.take j)).S.versionAt r y = some u)
    (hw : newest (run sp al (ts.take j)).S s y = some w)
    (hg : good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t u = true) :
    good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t w = true := by
  have hinv := inv_st sp al ts hok (algOK_of sp al hst) j hj
  obtain ⟨r', -, hw', hrr⟩ := newest_ge hw hu
  exact hinv.newer hok.1.liveSub (u.level + 1) r r' y u w (by omega) hu hw' hrr t hg

/-- Lemma M, cut back (WP L2): a version cut back to time s (`Version.cutTo`;
Java cuts back a version of the startup section to the startup time) is good
for a time t ≤ s exactly when the whole version is. -/
theorem LM_cutTo (sp : Spec V T) (S : Stream V T) (P : Struct V) (w : Version V)
    {s t : Time} (ht : t ≤ s) : good sp S P t (w.cutTo s) = good sp S P t w :=
  good_cutTo sp S P w ht

/-- T1-L, lazy startup (bergdb item 001, WP L3). After a run of BergDB's
algorithm (`javaTest`) that meets the assumptions of the physical layer
(`PhysRunOK`), Java's lazy startup (`lazyStartup`) from the stream after T(k)
(the whole stream, or a prefix of it, which a crash leaves), followed by any
reads and writer follows (`Op`; admissible: `OpsOK`): a read at any time t up
to k, through `Phys.lean`'s first-touch rule, gives P at t: it reaches
exactly the nodes reachable at t, each with its node at t (level, kind and
history at t). Every object in memory is canonical,
with its node's whole history, or holds a version of its node from the
stream, all of it or cut back to s; a memory slot that a canonical object's
node uses at a time t (it is reachable at t, the pointee a live child at t)
leads to a canonical object, or to one that holds a version good for t if it
holds all of it. -/
theorem T1_lazy (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (k : Nat) (hk : k ≤ ts.length)
    (ops : List Op)
    (hops : OpsOK sp ((run sp al ts).S.take (k + 1)) (run sp al (ts.take k)).P k
      (lazyStartup sp ((run sp al ts).S.take (k + 1))) ops) :
    let S : Stream V T := (run sp al ts).S.take (k + 1)
    let P := (run sp al (ts.take k)).P
    let m := ops.foldl (Mem.step sp S) (lazyStartup sp S)
    (∀ t ≤ k, (m.read sp S t).2.map (·.1) = reachList sp P t ∧
      ∀ p ∈ (m.read sp S t).2, view sp P t p.1 = some p.2) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → (P.get? o.node).map (·.hist) = some o.hist) ∧
    (∀ h o, m.obj? h = some o → o.canonical = false → ∃ r w, o.pos = some r ∧
      S.versionAt r o.node = some w ∧ (o.hist = w.hist ∨ o.hist = w.hist.upTo (lastSp S))) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → ∀ t ≤ k, reachable sp P t o.node = true →
      ∀ y ∈ sp.live (o.hist.upTo t), ∀ h', o.slot? y = some (Slot.mem h') →
        ∃ o', m.obj? h' = some o' ∧ o'.node = y ∧ (o'.canonical = true ∨
          ∃ r w, o'.pos = some r ∧ S.versionAt r y = some w ∧
            (o'.hist = w.hist → good sp S P t w = true))) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hpre := st_S_prefix sp al ts (j := k) (j' := ts.length) hk (Nat.le_refl _)
  have hlen := st_len sp al ts hok hst hk
  rw [st_length] at hpre
  have htake : (run sp al ts).S.take (k + 1) = (st sp al ts k).S := by
    rw [← hlen]; exact (List.prefix_iff_eq_take.mp hpre).symm
  intro S P m
  have hS : S = (st sp al ts k).S := htake
  have hP : P = (st sp al ts k).P := rfl
  rw [htake] at hops
  obtain ⟨hm, hctx, hkk⟩ := T1_lazy_strong hok hph hj hk ops hops
  have := hm.t1_facts hctx hkk
  simp only [m, hS, hP]
  exact this

/-- `step` is `stepWith` with the change of step 1, T(i)'s change on P@(i - 1)
(bergdb item 001, WP L4). -/
theorem step_eq_stepWith (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    step sp al db tr =
      stepWith sp al db tr (sp.exec tr db.S.length (view sp db.P (db.S.length - 1))) := rfl

/-- T2-L, restarts with a lazy startup (bergdb item 001, WP L4). A run of
BergDB's algorithm (`javaTest`) that meets the assumptions, also those of the
physical layer (`PhysRunOK`), with restarts after any transactions, each a lazy
startup (`lazyStartup`), and whose writer reads its view of P and reaches the
nodes of its paths through the physical layer (`lazyTrans`, `runLazy`),
appends exactly the same records as the run without restarts. -/
theorem T2_lazy (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) :
    (runLazy sp al ts).1.S = (run sp al (ts.map (·.1))).S := by
  have h := (T2_lazy_strong hok hph hj (j := ts.length) (Nat.le_refl _)).1.1
  rw [List.take_length] at h
  have hl : (ts.map (·.1)).length = ts.length := List.length_map _
  rw [← hl, st_length] at h
  exact h

/-- CC, canonical objects (bergdb item 001, WP L4). In a run with lazy restarts,
after any of its transactions, every canonical object in memory, whether the
startup made it or the writer's follows did, holds its node's whole history:
that of the node in P of the run without restarts. -/
theorem CC_canonical (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (j : Nat) (hjt : j ≤ ts.length) :
    ∀ h o, (runLazy sp al (ts.take j)).2.1.obj? h = some o → o.canonical = true →
      ((run sp al ((ts.take j).map (·.1))).P.get? o.node).map (·.hist) = some o.hist := by
  have h := (T2_lazy_strong hok hph hj hjt).2
  rw [List.map_take]
  exact h

/-- D closed upward (F1-008-08's T15; bergdb item 001, WP E3). In a run of
BergDB's algorithm (`javaTest`, with marking) that meets the assumptions and
those of stage 2 (`EvictRunOK`), after every transaction: a written node
current at the last time with a node of D below it is in D; and a current
written node not in D has no pointee in D, and its latest version names the
latest version of each of its pointees, live or dead. -/
theorem T15_closed (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hev : EvictRunOK sp al ts)
    (j : Nat) (hjt : j ≤ ts.length) :
    let db := run sp al (ts.take j)
    (∀ x n y, written sp x = true → reachable sp db.P j x = true → db.P.get? x = some n →
      inD db.D y = true → y ∈ reachFrom sp db.P j x n → inD db.D x = true) ∧
    (∀ x n, written sp x = true → reachable sp db.P j x = true → db.P.get? x = some n →
      inD db.D x = false → ∀ y ∈ pointees sp n.hist,
        inD db.D y = false ∧ ∃ v, db.S.lv x = some v ∧ v.ref? y = (db.S.lv y).map (·.recNo)) := by
  intro db
  have h := evLogic_st sp al ts hok hj hmk hev j hjt
  exact ⟨h.closed, h.clean⟩

/-- T-CACHE (bergdb item 001, WP E3; docs/level4-alignment.md, 5.3, 5.4 and
5.6). A run of BergDB's algorithm (`javaTest`, with marking) that meets the
assumptions, those of the physical layer (`PhysRunOK`) and those of stage 2
(`EvictRunOK`: TREE, A6' and A-COPY), from the Level 4 startup from R(0)
(`evictStartup`), with any cache schedule (after each transaction any reads,
unswizzles and releases, `CacheOp`; `runEvict`) and no restart. After every
transaction and its cache operations, the physical writer (`evictTrans`) has
appended exactly the model's records and left the model's D (the state is the
model's), and the memory meets the invariants. INV-CAN: a canonical object is
the node table's for its node (so a node has at most one), holds its node's
whole history, level and kind, and its position is its node's latest record;
every node of D has one. INV-SNAP: every other object is exactly the version
at its position. No memory slot dangles. INV-SLOT: a canonical object of a
written node that is current or in D has a slot for each pointee of its
history, live or dead; writing it now would give each pointee its latest
version (`Mem.refOf`); and its slot for a pointee in D that is not a memory
slot to the pointee's canonical object belongs to a node of D that got dirty
no later. The schedule being any, this holds after every operation. -/
theorem TC_records (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp))
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hev : EvictRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hnr : ∀ p ∈ ts, p.2.1 = false) (j : Nat) (hjt : j ≤ ts.length) :
    let db := run sp al ((ts.take j).map (·.1))
    let m := (runEvict sp al (ts.take j)).2.1
    (runEvict sp al (ts.take j)).1 = db ∧
    (∀ h o, m.obj? h = some o → o.canonical = true →
      m.canonicalOf o.node = some h ∧
      (∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData) ∧
      o.pos = (db.S.lv o.node).map (·.recNo)) ∧
    (∀ y, inD db.D y = true → (m.canonicalOf y).isSome) ∧
    (∀ h o, m.obj? h = some o → o.canonical = false → ∃ r w, o.pos = some r ∧
      db.S.versionAt r o.node = some w ∧ o.hist = w.hist ∧ o.level = w.level ∧ o.isData = w.isData) ∧
    (∀ h o y h', m.obj? h = some o → o.slot? y = some (Slot.mem h') →
      ∃ o', m.obj? h' = some o' ∧ o'.node = y) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → written sp o.node = true →
      (reachable sp db.P j o.node = true ∨ inD db.D o.node = true) →
      ∀ y ∈ pointees sp o.hist, (o.slot? y).isSome ∧
        m.refOf (init sp).S db.D o y = (db.S.lv y).map (·.recNo) ∧
        (inD db.D y = true → (∃ h', o.slot? y = some (Slot.mem h') ∧ m.canonicalOf y = some h') ∨
          (inD db.D o.node = true ∧ ∃ a b, (o.node, a) ∈ db.D ∧ (y, b) ∈ db.D ∧ a ≤ b))) := by
  intro db m
  obtain ⟨e1, -, e3⟩ := TC_run_init hok hph hev hj hmk hnr j hjt
  have hst : st sp al (ts.map (·.1)) j = db := by
    show run sp al ((ts.map (·.1)).take j) = run sp al ((ts.take j).map (·.1))
    rw [List.map_take]
  rw [hst] at e1 e3
  exact ⟨e1, e3.tc_facts⟩

/-- T-READ (bergdb item 001, WP E4; docs/level4-alignment.md, 5.6). In a run as
in `TC_records` (BergDB's algorithm with marking, the assumptions, those of the
physical layer and of stage 2, the Level 4 startup from R(0), any cache
schedule, no restart), after any transaction and its cache operations, a read
through the Level 4 loader (`Mem.read4`) at any time t up to the last record
gives P at t: it reaches exactly the nodes reachable at t, each with its node
at t (level, kind and history at t). The schedule being any, this holds for
every read of a schedule too, the writer's own read at the last time
included. -/
theorem TR_view (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp))
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hev : EvictRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hnr : ∀ p ∈ ts, p.2.1 = false) (j : Nat) (hjt : j ≤ ts.length)
    (t : Time) (ht : t ≤ j) :
    let db := run sp al ((ts.take j).map (·.1))
    let m := (runEvict sp al (ts.take j)).2.1
    (m.read4 sp (init sp).S db.S t).2.map (·.1) = reachList sp db.P t ∧
      ∀ p ∈ (m.read4 sp (init sp).S db.S t).2, view sp db.P t p.1 = some p.2 := by
  intro db m
  have hst : st sp al (ts.map (·.1)) j = db := by
    show run sp al ((ts.map (·.1)).take j) = run sp al ((ts.take j).map (·.1))
    rw [List.map_take]
  obtain ⟨-, -, e3⟩ := TC_run_init hok hph hev hj hmk hnr j hjt
  have hh := HInv.run hok hph hev hj hmk hnr j hjt
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j (by rw [List.length_map]; exact hjt)
  rw [hst] at e3 hh hinv
  exact read_list_view (e3.read4T_ok hinv hok.1.liveSub hh ht).2.2

/-- T2-C, restarts with eviction (bergdb item 001, WP E5; docs/level4-alignment.md,
5.13). A run as in `TC_records` (BergDB's algorithm with marking, the
assumptions, those of the physical layer and of stage 2, the Level 4 startup
from R(0), any cache schedule), now with restarts after any transactions
(`runEvict`: after a transaction marked true, the logical startup for
⟨P, D, S⟩ and the Level 4 startup, `evictStartup`, for the memory, from the
stream). After every transaction and its cache operations or its restart, the
state is the run's without restarts: the same records (so restarts change no
record) and D, and P with the same nodes. The memory meets the invariants of
`TC_records` for the startup it last made, from the run's stream after some
earlier transaction k1 (Rule R from that stream's section): INV-CAN, INV-SNAP,
no dangling slot, INV-SLOT. Right after a restart (k1 = j) they are the
invariants of the startup's memory. -/
theorem T2_cache (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp))
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hev : EvictRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (j : Nat) (hjt : j ≤ ts.length) :
    let db := run sp al ((ts.take j).map (·.1))
    let r := runEvict sp al (ts.take j)
    let m := r.2.1
    r.1.S = db.S ∧ r.1.D = db.D ∧ (∀ x, r.1.P.get? x = db.P.get? x) ∧
    ∃ k1, k1 ≤ j ∧ r.2.2 = (run sp al ((ts.take k1).map (·.1))).S ∧
    (∀ h o, m.obj? h = some o → o.canonical = true →
      m.canonicalOf o.node = some h ∧
      (∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData) ∧
      o.pos = (db.S.lv o.node).map (·.recNo)) ∧
    (∀ y, inD db.D y = true → (m.canonicalOf y).isSome) ∧
    (∀ h o, m.obj? h = some o → o.canonical = false → ∃ r w, o.pos = some r ∧
      db.S.versionAt r o.node = some w ∧ o.hist = w.hist ∧ o.level = w.level ∧ o.isData = w.isData) ∧
    (∀ h o y h', m.obj? h = some o → o.slot? y = some (Slot.mem h') →
      ∃ o', m.obj? h' = some o' ∧ o'.node = y) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → written sp o.node = true →
      (reachable sp db.P j o.node = true ∨ inD db.D o.node = true) →
      ∀ y ∈ pointees sp o.hist, (o.slot? y).isSome ∧
        m.refOf r.2.2 db.D o y = (db.S.lv y).map (·.recNo) ∧
        (inD db.D y = true → (∃ h', o.slot? y = some (Slot.mem h') ∧ m.canonicalOf y = some h') ∨
          (inD db.D o.node = true ∧ ∃ a b, (o.node, a) ∈ db.D ∧ (y, b) ∈ db.D ∧ a ≤ b))) := by
  intro db r m
  obtain ⟨k1, hk1, hS0, hrel, hm, -⟩ := evictInvR_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = db := by
    show run sp al ((ts.map (·.1)).take j) = run sp al ((ts.take j).map (·.1))
    rw [List.map_take]
  have hst1 : st sp al (ts.map (·.1)) k1 = run sp al ((ts.take k1).map (·.1)) := by
    show run sp al ((ts.map (·.1)).take k1) = run sp al ((ts.take k1).map (·.1))
    rw [List.map_take]
  rw [hst] at hrel hm
  rw [hst1] at hS0 hm
  rw [← hS0] at hm
  obtain ⟨e1, e2, e3⟩ := hrel
  exact ⟨e1, e2, e3, k1, hk1, hS0, hm.tc_facts⟩

/-- T-READ with restarts (bergdb item 001, WP E5; docs/level4-alignment.md,
5.13). In a run as in `T2_cache` (with restarts after any transactions), after
any transaction and its cache operations or its restart, a read through the
Level 4 loader (`Mem.read4`, with Rule R from the stream of the last startup)
at any time t up to the last record gives P at t: it reaches exactly the nodes
reachable at t, each with its node at t. With `TR_view`, which is the case
without restarts, this is T-READ for every state a run with eviction can
reach. -/
theorem TR_view_restarts (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp))
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hev : EvictRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (j : Nat) (hjt : j ≤ ts.length) (t : Time) (ht : t ≤ j) :
    let db := run sp al ((ts.take j).map (·.1))
    let r := runEvict sp al (ts.take j)
    let m := r.2.1
    (m.read4 sp r.2.2 db.S t).2.map (·.1) = reachList sp db.P t ∧
      ∀ p ∈ (m.read4 sp r.2.2 db.S t).2, view sp db.P t p.1 = some p.2 := by
  intro db r m
  obtain ⟨k1, -, hS0, -, hm, hh⟩ := evictInvR_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = db := by
    show run sp al ((ts.map (·.1)).take j) = run sp al ((ts.take j).map (·.1))
    rw [List.map_take]
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j (by rw [List.length_map]; exact hjt)
  rw [hst] at hm hh hinv
  rw [← hS0] at hm hh
  exact read_list_view (hm.read4T_ok hinv hok.1.liveSub hh ht).2.2

end SIS
