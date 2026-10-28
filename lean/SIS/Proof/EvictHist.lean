/-
Proofs for stage 2 (bergdb item 001, WP E4), part 1: the invariant for reads at
earlier times (`HInv`). For every canonical object, every time t at which its
node is reachable, and every live child at t: a memory slot to an object that a
read at t may use (canonical, or the snapshot of a version good for t); or a
stream slot that names, after Rule R, a version good for t, or a node of D, the
object's node being in D and no later (INV-SLOT's second half). The cache
operations keep it.
-/
import SIS.Proof.EvictInit

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- INV-SLOT's second half: y and x are in D, x got dirty no later. -/
def DLater (D : Dirty) (x y : NodeId) : Prop :=
  inD D y = true ∧ inD D x = true ∧ ∃ a b, dOf D x = some a ∧ dOf D y = some b ∧ a ≤ b

/-! ## Memories that keep what reads need -/

section Keep

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' m'' : Mem V}

end Keep

/-! ## Good versions -/

section Good

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- A written node not in D, reachable at t ≤ k, has a latest version, good for
t: it is clean (INV-2). -/
theorem Inv.clean_good (hinv : Inv sp db k) (hls : LiveSub sp) {y : NodeId} (hyD : inD db.D y = false)
    (hyw : written sp y = true) {t : Time} (ht : t ≤ k) (hr : reachable sp db.P t y = true) :
    ∃ v, db.S.lv y = some v ∧ good sp db.S db.P t v = true := by
  obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  cases hd : ny.isData with
  | true =>
    obtain ⟨v, hv, -⟩ := hinv.dataV y ny hny hd
    exact ⟨v, hv, hinv.good_data hls hny hd hv t⟩
  | false =>
    have hidx : isIndex db.P y = true := by simp [isIndex, hny, hd]
    have hcl : dirty sp db.S db.P k y = false := by
      cases hdy : dirty sp db.S db.P k y with
      | false => rfl
      | true => have := hinv.inv2 y hidx hyw hdy; rw [hyD] at this; cases this
    unfold dirty at hcl
    cases hl : db.S.lv y with
    | none => rw [hl] at hcl; cases hcl
    | some v =>
      rw [hl] at hcl
      simp only [List.any_eq_false, List.mem_range] at hcl
      refine ⟨v, rfl, ?_⟩
      have := hcl t (by omega)
      simp only [hr, Bool.true_and, Bool.not_eq_true'] at this
      cases hg : good sp db.S db.P t v
      · rw [hg] at this; exact absurd rfl this
      · rfl

theorem ruleRRef_some_some (S0 : Stream V T) (s : Nat) (y : NodeId) (r : Nat) :
    ∃ r', ruleRRef S0 s y (some r) = some r' := by
  unfold ruleRRef
  cases newest S0 s y with
  | none => exact ⟨r, rfl⟩
  | some w =>
    simp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- A live child at t of a node reachable at t is reachable at t, below it, and
not the root. -/
theorem Inv.reach_child (hinv : Inv sp db k) (hls : LiveSub sp) {x : NodeId} {n : Node V}
    (hn : db.P.get? x = some n) {t : Time} (hr : reachable sp db.P t x = true) {y : NodeId}
    (hy : y ∈ sp.live (n.hist.upTo t)) :
    reachable sp db.P t y = true ∧ y ≠ root ∧ ∃ ny, db.P.get? y = some ny ∧ ny.level < n.level := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  obtain ⟨ny, hny, hlt⟩ := hinv.ptrs x n hn e (mem_upTo.mp he).1 y hye
  refine ⟨?_, hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye, ny, hny, hlt⟩
  rw [reachable_iff] at hr ⊢
  exact Reach.child hr hn hy hny hlt

end Good

/-! ## The cache operations -/

section Cache

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Cache

end SIS
