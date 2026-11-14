import SIS.Tree.GetCascadeIP

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The reader's fuel (bergdb 024-12, TP10): `getFromR` gives each segment's
descent the same fuel (`Params.fuel`, from G and H). Once every descent fits in
it, more fuel gives the same answer (`getFromR_fuel_mono`): the fuel is then no
restriction of the model. A split that makes a new root grows a segment's tree
by a level; its reading needs one level of room (`SegDepthLe` below the fuel). -/

/-- The segment tree of x has depth at most d: a node at depth 0 is a segment
leaf, an inner node's live children have depth at most d - 1. -/
def SegDepthLe (N : NodeId → Option KNode) (t : Time) : Nat → NodeId → Prop
  | 0, x => ∀ n, N x = some n → n.leaf = true
  | d + 1, x => ∀ n, N x = some n → n.leaf = false → ∀ c y, (c, y) ∈ n.liveAt t → SegDepthLe N t d y

theorem SegDepthLe.mono (N : NodeId → Option KNode) (t : Time) :
    ∀ d x, SegDepthLe N t d x → ∀ d', d ≤ d' → SegDepthLe N t d' x := by
  intro d
  induction d with
  | zero =>
    intro x h d' _
    cases d' with
    | zero => exact h
    | succ d' => intro n hn hl; rw [h n hn] at hl; cases hl
  | succ d ih =>
    intro x h d' hd
    cases d' with
    | zero => omega
    | succ d' =>
      intro n hn hl c y hy
      exact ih y (h n hn hl c y hy) d' (by omega)

/-- Once the descent fits, the fuel does not change what it finds. -/
theorem getEqR_fuel_mono (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ d x, SegDepthLe N t d x → ∀ f f', d < f → d < f' →
      getEqR N t cv f x = getEqR N t cv f' x := by
  intro d
  induction d with
  | zero =>
    intro x h f f' hf hf'
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [getEqR]
    cases hn : N x with
    | none => rfl
    | some n => simp only [h n hn, ↓reduceIte]
  | succ d ih =>
    intro x h f f' hf hf'
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [getEqR]
    cases hn : N x with
    | none => rfl
    | some n =>
      simp only
      cases hl : n.leaf with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hs : n.searchLte t cv with
        | none => rfl
        | some fd =>
          simp only
          exact ih fd.y (h n hn hl fd.c fd.y (KNode.searchLte_mem n t cv fd hs)) f f' (by omega)
            (by omega)

/-- Every segment tree reached from r has depth at most d. -/
def SegFits (N : NodeId → Option KNode) (t : Time) (d : Nat) (r : NodeId) : Prop :=
  ∀ x, ReachS N t r x → SegDepthLe N t d x

/-- With more fuel `getFromR` gives the same answer once every descent fits. -/
theorem getFromR_fuel_mono (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (d : Nat) (r0 : NodeId) (hwf : ∀ x xn, ReachS N t r0 x → N x = some xn → klongsWf xn.ks = true)
    (hfit : SegFits N t d r0) (f f' : Nat) (hf : d < f) (hf' : d < f') :
    ∀ key r, ReachS N t r0 r → getFromR N V t f key r = getFromR N V t f' key r := by
  intro key
  induction key with
  | nil => intro r _; rfl
  | cons c rest ih =>
    intro r hr
    have he := getEqR_fuel_mono N t c d r (hfit r hr) f f' hf hf'
    cases rest with
    | nil => simp only [getFromR]; rw [he]
    | cons e rest' =>
      simp only [getFromR]
      rw [← he]
      cases hg : getEqR N t c f r with
      | none => rfl
      | some y =>
        simp only
        split
        · exact ih y (getEqR_reach N t r0 c hwf f r y hr hg)
        · rfl

/-! ## The per-segment fuel premise

`SegFits N t (fuel - 1) r`: every path inside one segment tree reached from r,
from a node through inner nodes, is shorter than the fuel. It is the premise of
the readings over a new root (a space split grows one segment's tree by a
level). The fuel is per segment (`getEqR`), so this per-segment form, not the
whole path from the space root (`PathsFit`), is what the writer's states inside
a transaction can meet; that they all do is an open premise (`boundsOK` checks
the bounds at the transaction's end). -/

/-- What N reaches from r, N' reaches, when they agree on N's reached nodes. -/
theorem ReachS.of_agree (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : ∀ y, ReachS N t r y → N' y = N y) : ∀ x, ReachS N t r x → ReachS N' t r x := by
  intro x hx
  induction hx with
  | root => exact ReachS.root
  | step x n c z hx hn hz ih =>
    exact ReachS.step x n c z ih (by rw [h x hx]; exact hn) hz

/-- The depth below x is N''s when N and N' agree on the nodes N reaches from x. -/
theorem SegDepthLe.of_agree (N N' : NodeId → Option KNode) (t : Time) :
    ∀ d x, (∀ y, ReachS N t x y → N' y = N y) → SegDepthLe N' t d x → SegDepthLe N t d x := by
  intro d
  induction d with
  | zero =>
    intro x h hd n hn
    exact hd n (by rw [h x ReachS.root]; exact hn)
  | succ d ih =>
    intro x h hd n hn hl c y hy
    have hy' : ReachS N t x y := ReachS.step x n c y ReachS.root hn hy
    exact ih y (fun z hz => h z (reachS_trans N t x y hy' z hz))
      (hd n (by rw [h x ReachS.root]; exact hn) hl c y hy)

/-- `SegFits` of N' gives N's when they agree on the nodes N reaches. -/
theorem SegFits.of_agree (N N' : NodeId → Option KNode) (t : Time) (d : Nat) (r : NodeId)
    (h : ∀ x, TReach N t r x → N' x = N x) (hf : SegFits N' t d r) : SegFits N t d r := by
  have h' : ∀ y, ReachS N t r y → N' y = N y := fun y hy => h y (reachS_tReach _ _ _ _ hy)
  intro x hx
  exact SegDepthLe.of_agree N N' t d x (fun y hy => h' y (reachS_trans N t r x hx y hy))
    (hf x (ReachS.of_agree N N' t r h' x hx))

/-- The depth below x in N' is at most N's when every node N' reaches from x is
N's or a leaf. -/
theorem SegDepthLe.of_sub (N N' : NodeId → Option KNode) (t : Time) :
    ∀ d x, (∀ y n', ReachS N' t x y → N' y = some n' → n'.leaf = true ∨ N y = some n') →
      SegDepthLe N t d x → SegDepthLe N' t d x := by
  intro d
  induction d with
  | zero =>
    intro x hmap hd n hn
    rcases hmap x n ReachS.root hn with h | h
    · exact h
    · exact hd n h
  | succ d ih =>
    intro x hmap hd n hn hl c y hy
    rcases hmap x n ReachS.root hn with h | h
    · rw [h] at hl; cases hl
    · have hy' : ReachS N' t x y := ReachS.step x n c y ReachS.root hn hy
      exact ih y (fun z n' hz hzn => hmap z n' (reachS_trans N' t x y hy' z hz) hzn) (hd n h hl c y hy)

/-- `SegFits` of N gives N''s when N reaches what N' reaches from r and every
node N' reaches is N's or a leaf. -/
theorem SegFits.of_sub (N N' : NodeId → Option KNode) (t : Time) (d : Nat) (r : NodeId)
    (hreach : ∀ x, ReachS N' t r x → ReachS N t r x)
    (hmap : ∀ y n', ReachS N' t r y → N' y = some n' → n'.leaf = true ∨ N y = some n')
    (hf : SegFits N t d r) : SegFits N' t d r :=
  fun x hx => SegDepthLe.of_sub N N' t d x
    (fun y n' hy hyn => hmap y n' (reachS_trans N' t r x hx y hy) hyn) (hf x (hreach x hx))

end SIS.Tree
