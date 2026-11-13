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

/-- The parent's search after a space split of its child x into F and S at the
divider sc, routed by compare value, from the virtual map's tree. -/
theorem splitParent_search_tree (V : NodeId → Option KNode) (t : Time) (r q x F S : NodeId)
    (qn : KNode) (K sc : Nat) (hT : TreeOK V t r) (hVq : V q = some qn) (hrq : ReachS V t r q)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hKx : (K, x) ∈ qn.liveAt t) (hKsc : K ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ qn.live → c' ≤ K ∨ sc < c') :
    ∀ c : Nat, (((qn.add t (.key K F)).add t (.key sc S)).searchLte t c).map (·.y) =
      (qn.searchLte t c).map (fun fd => if fd.y = x then (if c < sc then F else S) else fd.y) := by
  intro c
  have hk1 : (K, x) ∈ qn.live := by rw [← KNode.liveAt_of_times qn t hqt]; exact hKx
  have hrqT := reachS_tReach V t r q hrq
  have hA := KNode.splitParent_searchLte qn t K sc x F S hqwf hqt hk1 hKsc hgap c
  rw [hA]
  cases hs : qn.searchLte t c with
  | none => rfl
  | some fd =>
    simp only [Option.map_some, Option.some.injEq]
    have hmemfd := KNode.searchLte_mem qn t c fd hs
    have hyx : fd.y = x ↔ fd.c = K := by
      constructor
      · intro hy
        rw [hy] at hmemfd
        exact (hT.oneLink q fd.c q K x hrqT hrqT ⟨qn, hVq, hmemfd⟩ ⟨qn, hVq, hKx⟩).2
      · intro hc
        rw [KNode.liveAt_of_times qn t hqt, hc] at hmemfd
        exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup qn) hmemfd).symm.trans
          (lookup_some_of_mem (KNode.live_keys_nodup qn) hk1))
    by_cases hc : fd.c = K
    · simp only [hc, ↓reduceIte, hyx.mpr hc, Int.ofNat_lt]
    · have hy : ¬ fd.y = x := fun h => hc (hyx.mp h)
      simp only [hc, ↓reduceIte, hy]

/-- The reading through a space split at one level: in the virtual map V the
node x holds `xv`; in A the halves f and s are at F and S, x's parent q names
F by its klong K and S by a new klong sc, and x is anything. The halves search
as `xv` below sc and from sc on. If V is a tree from r, the readings agree. -/
theorem getFromR_spaceLevel (V A : NodeId → Option KNode) (Val : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r q x F S : NodeId) (qn xv f s : KNode) (K sc : Nat)
    (hT : TreeOK V t r) (hwfV : ∀ z zn, ReachS V t r z → V z = some zn → klongsWf zn.ks = true)
    (hVq : V q = some qn) (hrq : ReachS V t r q) (hql : qn.leaf = false)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hKx : (K, x) ∈ qn.liveAt t) (hqx : q ≠ x) (hKsc : K ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ qn.live → c' ≤ K ∨ sc < c')
    (hVx : V x = some xv)
    (hVF : V F = none) (hVS : V S = none)
    (hnoFS : ∀ u c z, ReachS V t r u → TLink V t u c z → z ≠ F ∧ z ≠ S)
    (hAF : A F = some f) (hAS : A S = some s) (hfl : f.leaf = xv.leaf) (hsl : s.leaf = xv.leaf)
    (hleafF : xv.leaf = true → ∀ c, c < sc → (f.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y))
    (hleafS : xv.leaf = true → ∀ c, sc ≤ c → (s.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y))
    (hinF : xv.leaf = false → ∀ c : Nat, c < sc →
      (f.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y))
    (hinS : xv.leaf = false → ∀ c : Nat, sc ≤ c →
      (s.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y))
    (hAq : A q = some ((qn.add t (.key K F)).add t (.key sc S)))
    (hA : ∀ z, z ≠ x → z ≠ q → z ≠ F → z ≠ S → A z = V z)
    (hrx : r ≠ x) (hrF : r ≠ F) (hrS : r ≠ S) :
    ∀ key, getFromR A Val t fuel key r = getFromR V Val t fuel key r := by
  have hFx : F ≠ x := fun h => by rw [h, hVx] at hVF; cases hVF
  have hSx : S ≠ x := fun h => by rw [h, hVx] at hVS; cases hVS
  have hrqT := reachS_tReach V t r q hrq
  have hrx' : ReachS V t r x := ReachS.step q qn K x hrq hVq hKx
  have hnotL : ∀ z zn c y, ReachS V t r z → z ≠ q → V z = some zn → (c, y) ∈ zn.liveAt t →
      y ≠ x := by
    intro z zn c y hz hzq hzn hy hyx
    subst hyx
    exact hzq (hT.oneLink z c q K y (reachS_tReach V t r z hz) hrqT ⟨zn, hzn, hy⟩ ⟨qn, hVq, hKx⟩).1
  have hnotFS : ∀ z zn c y, ReachS V t r z → V z = some zn → (c, y) ∈ zn.liveAt t →
      y ≠ F ∧ y ≠ S := fun z zn c y hz hzn hy => hnoFS z c y hz ⟨zn, hzn, hy⟩
  have hq2l : ((qn.add t (.key K F)).add t (.key sc S)).leaf = false := by
    rw [KNode.add_leaf, KNode.add_leaf]; exact hql
  have hqsearch := splitParent_search_tree V t r q x F S qn K sc hT hVq hrq hqwf hqt hKx hKsc hgap
  have hsame : ∀ z, z ≠ x → z ≠ q → z ≠ F → z ≠ S → A z = V z := hA
  have hget : ∀ c (z : NodeId), ReachS V t r z → z ≠ x → z ≠ F → z ≠ S →
      getEqR A t c fuel z = getEqR V t c fuel z := by
    intro c z hz hzx hzF hzS
    cases hxl : xv.leaf with
    | true =>
      exact getEqR_split V A t r x q F S qn _ xv f s sc hVq hql hAq hq2l hqsearch hVx hxl hAF
        (by rw [hfl, hxl]) hAS (by rw [hsl, hxl]) (hleafF hxl) (hleafS hxl) hsame hnotL
        (fun z zn c y hz hzn hy => ⟨fun _ => (hnotFS z zn c y hz hzn hy).1,
          (hnotFS z zn c y hz hzn hy).2⟩) c fuel z hz hzx hzF hzS
    | false =>
      exact (getEqR_split_inner V A t r x q F S qn _ xv f s sc hVq hql hAq hq2l hqsearch hVx hxl
        hrx' hAF (by rw [hfl, hxl]) hAS (by rw [hsl, hxl]) (hinF hxl) (hinS hxl) hsame hnotL
        hnotFS (fun h => hqx h.symm) c fuel).1 z hz hzx hzF hzS
  intro key
  exact getFromR_split V A Val t fuel r x q F S hwfV hget hsame (by rw [hAq, hVq]; rfl) hnotL
    (fun xn c z hxn _ hxl => by rw [hVq] at hxn; cases hxn; rw [hql] at hxl; cases hxl)
    (fun z zn c y hz hzn hy => ⟨fun _ => (hnotFS z zn c y hz hzn hy).1,
      (hnotFS z zn c y hz hzn hy).2⟩) key r ReachS.root hrx hrF hrS

end SIS.Tree
