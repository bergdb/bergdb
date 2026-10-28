/-
Proofs about reclaim, part 14 (bergdb item 001, WP R4, T9): one transaction of
the physical writer keeps T9's invariant (`CInv`). The change gives a new
pointer the canonical object of its pointee, or a copy of a slot that names the
pointee's latest version; the writes make the slots of a taken node for the
pointees of D memory slots to their canonical objects, and give the taken node a
version that names its pointees' latest versions; Rule A's order keeps a node
of D written no later than a pointee of D that a stale slot names.
-/
import SIS.Proof.CutPhys

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The change -/

section Change

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

end Change


/-! ## Root children -/

section Root

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- With a virtual root, a pointee of the root is a root child. -/
theorem VInv.top_of_pointee (hvi : VInv sp db k) {n : Node V} (hn : db.P.get? root = some n)
    {y : NodeId} (hy : y ∈ pointees sp n.hist) : ∃ m c, TopAt sp db.P y m c := by
  obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hy
  obtain ⟨z, m, htop, hval⟩ := hvi.rootEntry n hn e he
  rw [hval, hvi.rootPtrs, List.mem_singleton] at hye
  subst hye
  exact ⟨m, e.time, htop⟩

/-- With a virtual root, a node reachable at k with a root child as a live child
at k is the root: a node above a root child is one too, and a root child that a
root child points to is not reachable (`VInv.deadTops`). -/
theorem Inv.parent_of_top (hinv : Inv sp db k) (hls : LiveSub sp) (hv : sp.virt = true) {p y : NodeId}
    {np : Node V} (hrp : reachable sp db.P k p = true) (hnp : db.P.get? p = some np)
    (hy : y ∈ sp.live (np.hist.upTo k)) (hty : isTop sp db.P y = true) : p = root := by
  rcases Classical.em (p = root) with h | hne
  · exact h
  · exfalso
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    have he' := (mem_upTo.mp he).1
    obtain ⟨my, hmy, hlt⟩ := hinv.ptrs p np hnp e he' y hye
    have hyp : y ∈ pointees sp np.hist := (mem_pointees sp _ _).mpr ⟨e, he', hye⟩
    have htp : isTop sp db.P p = true := by
      unfold isTop at hty ⊢
      rw [hmy] at hty
      rw [hnp]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hty ⊢
      exact ⟨hne, by omega⟩
    have hdead := (hinv.vr hv).deadTops p np hnp htp y hyp hty
    have hry : reachable sp db.P k y = true := by
      rw [reachable_iff] at hrp ⊢
      exact Reach.child hrp hnp hy hmy hlt
    rw [hry] at hdead; cases hdead

/-- A version's references are for its pointees. -/
theorem Inv.ref_pointees (hinv : Inv sp db k) {x : NodeId} {v : Version V} (hv : db.S.lv x = some v)
    {y : NodeId} {r : Nat} (hr : v.ref? y = some r) : y ∈ pointees sp v.hist := by
  obtain ⟨r0, hr0⟩ := lv_versionAt hv
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hr0
  obtain ⟨pre, -, href⟩ := hinv.ref r0 R hR v hvR
  rw [href y] at hr
  split at hr
  · assumption
  · cases hr

end Root


/-! ## The next state -/

section Next

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}


end Next

end SIS
