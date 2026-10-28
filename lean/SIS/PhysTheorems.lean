/-
Self-indexed streams in Lean: the theorems of the physical layer (bergdb item
001, stages 1 and 2). Trusted part: the statements. The proofs are in
SIS/Proof/; the proofs here only connect them.
-/
import SIS.Proof.EvLogic
import SIS.Theorems
import SIS.Proof.Newer
import SIS.Proof.PhysT2

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Lemma M (bergdb item 001, WP L2; bergdb 011-11, M8). In every
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

end SIS
