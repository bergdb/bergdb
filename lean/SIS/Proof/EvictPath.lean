/-
Proofs for stage 2 (bergdb item 001, WP E3), part 6: the writer reaches the nodes
of its paths (`Mem.reachOnPath4`), highest level first. Every node of the paths
then has a canonical object, named by the slot of its parent's canonical object
on the path, and the invariant is kept.
-/
import SIS.Proof.EvictPromote

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Path

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- Node a of the path is reached in m: it has a canonical object, and (but the
root) the canonical object of a node of the path that has a as a live child at
k names it by a memory slot. -/
def PathDone (sp : Spec V T) (P : Struct V) (k : Nat) (path : List NodeId) (m : Mem V) (a : NodeId) :
    Prop :=
  (m.canonicalOf a).isSome ∧
    (a ≠ root → ∃ p ∈ path, ∃ np hp op ha, P.get? p = some np ∧ a ∈ sp.live (np.hist.upTo k) ∧
      m.canonicalOf p = some hp ∧ m.obj? hp = some op ∧ op.slot? a = some (Slot.mem ha) ∧
      m.canonicalOf a = some ha)

/-- The writer reaches one node x of a path. -/
theorem EInv.reachOnPath4_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : EInv sp db S0 k m) {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (x : NodeId) :
    EInv sp db S0 k (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x) ∧
      (∀ z h, m.canonicalOf z = some h →
        (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x).canonicalOf z = some h) ∧
      (∀ h o, m.obj? h = some o → ∃ o', (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x).obj? h = some o' ∧
        ∀ z, z ≠ x → o'.slot? z = o.slot? z) ∧
      ((∃ p ∈ path, ∃ np, db.P.get? p = some np ∧ m.canonicalOf p ≠ none ∧
          x ∈ sp.live (np.hist.upTo k)) →
        ∃ p ∈ path, ∃ np hp op hx, db.P.get? p = some np ∧ x ∈ sp.live (np.hist.upTo k) ∧
          (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x).canonicalOf p = some hp ∧
          (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x).obj? hp = some op ∧
          op.slot? x = some (Slot.mem hx) ∧
          (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x).canonicalOf x = some hx) := by
  unfold Mem.reachOnPath4
  have hK1 : k + 1 - 1 = k := by omega
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (k + 1 - 1))).contains x
      | _, _ => false) with
  | none =>
    simp only
    refine ⟨hm, fun _ _ h => h, fun h o ho => ⟨o, ho, fun _ _ => rfl⟩, ?_⟩
    rintro ⟨p, hp, np, hnp, hcp, hxl⟩
    exfalso
    rw [List.find?_eq_none] at hf
    apply hf p hp
    rw [hnp]
    cases hc : m.canonicalOf p with
    | none => exact absurd hc hcp
    | some _ => simp only [hK1]; exact List.contains_iff_mem.mpr hxl
  | some p =>
    simp only
    have hpp := List.find?_some hf
    have hpm := List.mem_of_find?_eq_some hf
    cases hnp : db.P.get? p with
    | none => rw [hnp] at hpp; simp at hpp
    | some np =>
      cases hcp : m.canonicalOf p with
      | none => rw [hnp, hcp] at hpp; simp at hpp
      | some hp =>
        simp only
        rw [hnp, hcp] at hpp
        simp only [hK1, List.contains_iff_mem] at hpp
        obtain ⟨op, hop, hco, hnode⟩ := hm.obj_of_canonicalOf hcp
        obtain ⟨nf, hnf, hh, -, -⟩ := hm.cc hp op hop hco
        rw [hnode, hnp, Option.some.injEq] at hnf
        subst hnf
        have hxop : x ∈ sp.live op.hist := by
          rw [hh, ← upTo_of_forall _ _ (hinv.times p np hnp)]; exact hpp
        obtain ⟨hm', h', -, hwf⟩ :=
          hm.follow4_writer hinv hls hev hop hco (by rw [hnode]; exact hpath p hpm) hxop
        refine ⟨hm', hwf.mono, fun h o ho => ?_, fun _ => ?_⟩
        · obtain ⟨o', ho', -, -, -, -, -, -, hs⟩ := hwf.frame h o ho
          exact ⟨o', ho', fun z hz => hs z (Or.inr hz)⟩
        · obtain ⟨op', hop', hsl'⟩ := hwf.slot
          exact ⟨p, hpm, np, hp, op', h', hnp, hpp, hwf.mono p hp hcp, hop', hsl', hwf.can⟩

/-- The writer reaches every node of the paths, highest level first. -/
theorem EInv.reachPath4_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (hparent : ∀ x ∈ path, x ≠ SIS.root → ∃ p ∈ path, ∃ np nx, db.P.get? p = some np ∧
      db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k)) :
    ∀ (L A : List NodeId) (m : Mem V), EInv sp db S0 k m → (∀ a ∈ A, PathDone sp db.P k path m a) →
      (∀ x, x ∈ A ++ L ↔ x ∈ path) → (A ++ L).Nodup →
      (A ++ L).Pairwise (fun a b => lev db.P b ≤ lev db.P a) →
      EInv sp db S0 k (L.foldl (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) path) m) ∧
        ∀ x ∈ path, PathDone sp db.P k path (L.foldl (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) path) m) x := by
  intro L
  induction L with
  | nil =>
    intro A m hm hA hmem _ _
    refine ⟨hm, fun x hx => hA x ?_⟩
    have := (hmem x).mpr hx
    simpa using this
  | cons x L ih =>
    intro A m hm hA hmem hnd hsort
    simp only [List.foldl_cons]
    obtain ⟨hm1, hmono, hframe, hc1⟩ := hm.reachOnPath4_ok hinv hls hev hpath x
    -- x is reached now.
    have hx1 : PathDone sp db.P k path (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x) x := by
      by_cases hxr : x = SIS.root
      · subst hxr
        obtain ⟨o, ho, hco, hn⟩ := hm1.root
        refine ⟨?_, fun h => absurd rfl h⟩
        have := hm1.canonicalOf_of ho hco
        rw [hn] at this
        rw [this]; rfl
      · obtain ⟨p, hp, np, nx, hnp, hnx, hlt, hxl⟩ := hparent x ((hmem x).mp (by simp)) hxr
        -- p is before x in the sorted list: in A, so reached
        have hpA : p ∈ A := by
          have hpAL := (hmem p).mpr hp
          rcases List.mem_append.mp hpAL with h | h
          · exact h
          · exfalso
            rcases List.mem_cons.mp h with h | h
            · subst h; rw [hnp, Option.some.injEq] at hnx; subst hnx; omega
            · have hs := List.pairwise_append.mp hsort
              have := List.pairwise_cons.mp hs.2.1
              have := this.1 p h
              simp [lev, hnp, hnx] at this
              omega
        obtain ⟨hpc, -⟩ := hA p hpA
        have hpc' : m.canonicalOf p ≠ none := by
          intro h; rw [h] at hpc; cases hpc
        obtain ⟨q, hq, nq, hq', op, hx, hnq, hxq, hcq, hop, hsl, hcx⟩ :=
          hc1 ⟨p, hp, np, hnp, hpc', hxl⟩
        exact ⟨by rw [hcx]; rfl, fun _ => ⟨q, hq, nq, hq', op, hx, hnq, hxq, hcq, hop, hsl, hcx⟩⟩
    -- The nodes reached before stay reached.
    have hA1 : ∀ a ∈ A ++ [x], PathDone sp db.P k path (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x) a := by
      intro a ha
      rcases List.mem_append.mp ha with haA | haA
      · have hax : a ≠ x := by
          intro he; subst he
          have := List.nodup_append.mp hnd
          exact this.2.2 a haA a (by simp) rfl
        obtain ⟨hac, hap⟩ := hA a haA
        unfold PathDone
        refine ⟨?_, fun hr => ?_⟩
        · obtain ⟨h0, h0e⟩ := Option.isSome_iff_exists.mp hac
          rw [hmono a h0 h0e]; rfl
        · obtain ⟨p, hp, np, hpc, op, ha', hnp, hal, hcp, hop, hsl, hca⟩ := hap hr
          obtain ⟨op', hop', hs⟩ := hframe hpc op hop
          exact ⟨p, hp, np, hpc, op', ha', hnp, hal, hmono p hpc hcp, hop', by rw [hs a hax]; exact hsl,
            hmono a ha' hca⟩
      · rw [List.mem_singleton] at haA; subst haA; exact hx1
    exact ih (A ++ [x]) _ hm1 hA1 (by intro y; rw [← hmem y]; simp) (by simpa using hnd)
      (by simpa using hsort)

end Path

end SIS
