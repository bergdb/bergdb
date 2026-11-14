import SIS.Tree.WriterKinds

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

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

end SIS.Tree
