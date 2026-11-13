import SIS.Tree.WriterKinds

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem Params.keyLevel_pos (p : Params) (g h : Nat) : 0 < p.keyLevel g h := by
  unfold Params.keyLevel
  omega

/-- The bounded height is recovered exactly from the stored key level. -/
theorem Params.heightOf_keyLevel (p : Params) (g h : Nat) (hh : h ≤ p.H) :
    p.heightOf (p.keyLevel g h) = h := by
  have he : p.keyLevel g h - 1 = (p.G - g) * (p.H + 1) + h := by
    unfold Params.keyLevel; omega
  simp only [Params.heightOf]
  rw [he]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : h < p.H + 1)]

theorem Params.segOf_keyLevel (p : Params) (g h : Nat)
    (hg : g ≤ p.G) (hh : h ≤ p.H) : p.segOf (p.keyLevel g h) = g := by
  have he : p.keyLevel g h - 1 = (p.G - g) * (p.H + 1) + h := by
    unfold Params.keyLevel; omega
  have hd : ((p.G - g) * (p.H + 1) + h) / (p.H + 1) = p.G - g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt (by omega : h < p.H + 1)]
  simp only [Params.segOf, he, hd]
  omega

theorem Params.keyLevel_injective (p : Params) (g h g' h' : Nat)
    (hg : g ≤ p.G) (hh : h ≤ p.H) (hg' : g' ≤ p.G) (hh' : h' ≤ p.H)
    (he : p.keyLevel g h = p.keyLevel g' h') : g = g' ∧ h = h' := by
  constructor
  · have hs := congrArg p.segOf he
    simpa only [p.segOf_keyLevel g h hg hh, p.segOf_keyLevel g' h' hg' hh'] using hs
  · have hs := congrArg p.heightOf he
    simpa only [p.heightOf_keyLevel g h hh, p.heightOf_keyLevel g' h' hh'] using hs

/-- Reading a nonzero key level and allocating a replacement from its
decoded tags reproduces the old level exactly. -/
theorem Params.keyLevel_decode (p : Params) (level : Nat)
    (hpos : 1 ≤ level) (hmax : level ≤ p.keyMax) :
    p.keyLevel (p.segOf level) (p.heightOf level) = level := by
  have hq : (level - 1) / (p.H + 1) ≤ p.G := by
    apply Nat.le_of_not_gt
    intro hn
    have hh : p.G + 1 ≤ (level - 1) / (p.H + 1) := by omega
    have hm := Nat.mul_le_mul_right (p.H + 1) hh
    have hd := Nat.div_mul_le_self (level - 1) (p.H + 1)
    rw [Nat.add_mul] at hm
    unfold Params.keyMax at hmax
    simp only [Nat.one_mul] at hm
    omega
  have hs : p.G - (p.G - (level - 1) / (p.H + 1)) = (level - 1) / (p.H + 1) := by
    exact Nat.sub_sub_self hq
  unfold Params.keyLevel Params.segOf Params.heightOf
  rw [hs]
  have hd := Nat.mod_add_div (level - 1) (p.H + 1)
  rw [Nat.mul_comm (p.H + 1)] at hd
  omega

theorem Params.keyLevel_inner_child_lt (p : Params) (g h : Nat) :
    p.keyLevel g h < p.keyLevel g (h + 1) := by
  unfold Params.keyLevel
  omega

/-- Every allowed height in the next segment is below the preceding
segment leaf, the level decrease for a long-segment edge. -/
theorem Params.keyLevel_next_segment_lt (p : Params) (g h : Nat)
    (hg : g < p.G) (hh : h ≤ p.H) :
    p.keyLevel (g + 1) h < p.keyLevel g 0 := by
  have hs : p.G - g = (p.G - (g + 1)) + 1 := by omega
  have hm : (p.G - g) * (p.H + 1) =
      (p.G - (g + 1)) * (p.H + 1) + (p.H + 1) := by
    rw [hs, Nat.add_mul, Nat.one_mul]
  unfold Params.keyLevel
  rw [hm]
  omega

/-- A bounded actual allocation records exactly the level that decodes to
its segment, height and supplied leaf flag, and does not mark an overflow.
This is a local metadata rule; it assumes the caller's leaf/height agreement. -/
theorem writerWP_newKey_level (g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (hg : g ≤ c.p.G) (hh : h ≤ c.p.H) (hleaf : leaf = (h == 0)) :
    WriterWP (newKey g h leaf ks) c w (fun x v =>
      x = w.next ∧ v.made = w.made ++ [⟨x, c.p.keyLevel g h, false⟩] ∧
      v.outside = w.outside ∧ c.p.segOf (c.p.keyLevel g h) = g ∧
      c.p.heightOf (c.p.keyLevel g h) = h ∧
      leaf = (c.p.heightOf (c.p.keyLevel g h) == 0)) := by
  have hnot : (decide (c.p.G < g) || decide (c.p.H < h)) = false := by
    simp [Nat.not_lt_of_ge hg, Nat.not_lt_of_ge hh]
  unfold newKey fresh
  wpSimplify
  simp only [hnot, Bool.false_eq_true, ↓reduceIte]
  wpSimplify
  exact ⟨trivial, trivial, trivial, c.p.segOf_keyLevel g h hg hh, c.p.heightOf_keyLevel g h hh,
    by rwa [c.p.heightOf_keyLevel g h hh]⟩

end SIS.Tree
