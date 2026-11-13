import SIS.Tree.GetInPlaceCascade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Splits of any depth (bergdb 024-12, TP10): the steps of an induction over
the writer's `appendKlongs` along the access path. At each level the reading of
the writer's state after the split, with the klongs to the new nodes put in the
parent, equals the reading of the state with the klongs put in the split node
(the virtual map), given that the virtual map is a tree (cost's `TreeOK`):
`getFromR_timeLevel` for a time split; and a node no longer reached may change
without changing the reading (`getFromR_updN_unreach`). -/

/-- A node that is not reached changes no reading. -/
theorem getFromR_updN_unreach (M : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r x : NodeId) (m : KNode)
    (hwf : ∀ z zn, ReachS M t r z → M z = some zn → klongsWf zn.ks = true)
    (hx : ¬ ReachS M t r x) :
    ∀ key, getFromR (fun z => if z = x then some m else M z) V t fuel key r =
      getFromR M V t fuel key r := by
  intro key
  have hrx : r ≠ x := fun h => hx (h ▸ ReachS.root)
  exact getFromR_avoid M _ V t fuel r (· = x) hwf
    (fun z _ hz => by simp only [hz, ↓reduceIte])
    (fun z zn c y hz hzn hy hyx => hx (hyx ▸ ReachS.step z zn c y hz hzn hy))
    key r ReachS.root hrx

/-- The reading through a time split at one level: in the virtual map V the
node x holds `xv` (its klongs with those put); in A the new node Y holds a node
of the same live klongs, x's parent q names Y by its klong K, and x is anything.
If V is a tree from r, the readings from r agree. -/
theorem getFromR_timeLevel (V A : NodeId → Option KNode) (Val : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r q x Y : NodeId) (qn xv l : KNode) (K : Nat)
    (hT : TreeOK V t r) (hwfV : ∀ z zn, ReachS V t r z → V z = some zn → klongsWf zn.ks = true)
    (hVq : V q = some qn) (hrq : ReachS V t r q) (hql : qn.leaf = false)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hKx : (K, x) ∈ qn.liveAt t) (hqx : q ≠ x)
    (hVx : V x = some xv) (hxwf : klongsWf xv.ks = true) (hxt : ∀ s, Klong.time s ∈ xv.ks → s ≤ t)
    (hVY : V Y = none) (hnoY : ∀ u c, ReachS V t r u → ¬ TLink V t u c Y)
    (hAY : A Y = some l) (hll : l.leaf = xv.leaf) (hlwf : klongsWf l.ks = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ t) (hllook : ∀ c, l.live.lookup c = xv.live.lookup c)
    (hAq : A q = some (qn.add t (.key K Y)))
    (hA : ∀ z, z ≠ x → z ≠ q → z ≠ Y → A z = V z)
    (hVal : Val x = Val Y) (hrY : r ≠ Y) (hrx : r ≠ x) :
    ∀ key, getFromR A Val t fuel key r = getFromR V Val t fuel key r := by
  have hYx : Y ≠ x := fun h => by rw [h, hVx] at hVY; cases hVY
  have hYq : Y ≠ q := fun h => by rw [h, hVq] at hVY; cases hVY
  have hk1 : (K, x) ∈ qn.live := by rw [← KNode.liveAt_of_times qn t hqt]; exact hKx
  have hrqT := reachS_tReach V t r q hrq
  have honly : ∀ c z, (c, z) ∈ qn.liveAt t → z = x → c = K := by
    intro c z hz hzx
    subst hzx
    exact (hT.oneLink q c q K z hrqT hrqT ⟨qn, hVq, hz⟩ ⟨qn, hVq, hKx⟩).2
  have hnotL : ∀ z zn, ReachS V t r z → z ≠ q → V z = some zn → ∀ c y, (c, y) ∈ zn.liveAt t →
      y ≠ x := by
    intro z zn hz hzq hzn c y hy hyx
    subst hyx
    exact hzq (hT.oneLink z c q K y (reachS_tReach V t r z hz) hrqT ⟨zn, hzn, hy⟩ ⟨qn, hVq, hKx⟩).1
  have hnoty : ∀ z zn, ReachS V t r z → V z = some zn → ∀ c y, (c, y) ∈ zn.liveAt t → y ≠ Y := by
    intro z zn hz hzn c y hy hyY
    subst hyY
    exact hnoY z c hz ⟨zn, hzn, hy⟩
  have hS := renSim_timeSplitGen V A t r x q Y qn xv l K hqx hYx hYq hVx hVq hql hqwf hqt hk1 honly
    hAY hll hxwf hlwf hxt hlt hllook hAq (fun z h1 h2 h3 => hA z h1 h2 h3) hwfV hnotL hnoty
  intro key
  have := getFromR_ren V A Val Val t fuel _ x Y hS (fun a => by
    by_cases ha : a = x
    · subst ha; simp [hVal]
    · simp [ha]) key r ⟨hrY, ReachS.root⟩
  rw [this]
  simp [hrx]

end SIS.Tree
