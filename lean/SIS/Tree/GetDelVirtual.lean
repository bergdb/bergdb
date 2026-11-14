import SIS.Tree.GetCascadeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The reading after a delete's split of its leaf (bergdb 024-12, TP10), through
the leaf with its last version in place (`getFromR_delVirtual`): the key reads
as no value, every other key as before; then the split as a step of the tree
(`getFromR_timeLevel`, `getFromR_segTimeLevel`), below a parent that is inner or
a segment leaf (`getFromR_timeSplit_delAny`). -/

/-- The reading of N with the leaf L's contents m, n's live klongs but cv's:
the delete's key reads as no value, every other key as before. -/
theorem getFromR_delVirtual (N : NodeId → Option KNode) (Val : NodeId → Option Nat) (i : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (r L rk : NodeId) (pre : List Nat) (cv : Nat) (n m : KNode)
    (hNL : N L = some n) (hnl : n.leaf = true) (hml : m.leaf = true)
    (hs : ∀ c', (m.searchEq i c').map (·.y) = if c' == cv then none else (n.searchEq i c').map (·.y))
    (hrk : segRootR N i fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' r →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv]) :
    ∀ key', keyWf key' = true → getFromR (updN N L m) Val i fuel key' r =
      if pre ++ [cv] == key' then none else getFromR N Val i fuel key' r := by
  have hA := getFromR_leaf_change_seg N (updN N L m) Val Val i fuel hfuel L pre cv r rk n m
    (fun x hx => (updN_ne _ _ _ _ hx).symm) hNL (updN_self _ _ _) hnl hml
    (fun c' hc' => by
      rw [hs c']
      have : (c' == cv) = false := by simpa using hc'
      rw [this]; rfl)
    hrk hcv hvisL huniq (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  intro key' hkey'
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, hs cv]
    simp
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)


/-- N with the leaf L's contents m, n's live klongs but cv's, in place: a tree
from r whose nodes reached N reaches, and whose reading is the delete's. -/
theorem del_virtual (N : NodeId → Option KNode) (Val : NodeId → Option Nat) (i : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (r L rk : NodeId) (pre : List Nat) (cv : Nat) (n m : KNode)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hml : m.leaf = true) (hmwf : klongsWf m.ks = true) (hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i)
    (hlook : ∀ c, m.live.lookup c = if c == cv then none else n.live.lookup c)
    (hT : TreeOK N i r)
    (hrk : segRootR N i fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' r →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv]) :
    TreeOK (updN N L m) i r ∧ (∀ z, ReachS (updN N L m) i r z → ReachS N i r z) ∧
    (∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i) ∧
    ∀ key', keyWf key' = true → getFromR (updN N L m) Val i fuel key' r =
      if pre ++ [cv] == key' then none else getFromR N Val i fuel key' r := by
  have hL1 := KNode.liveAt_of_times n i hnt
  have hLm := KNode.liveAt_of_times m i hmt
  have hsub : ∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i := by
    intro c z hz
    rw [hLm] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup m) hz
    rw [hlook] at this
    by_cases hc : c = cv
    · subst hc; simp at this
    · have hc' : (c == cv) = false := by simpa using hc
      rw [hc'] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [hL1]; exact lookup_some_mem this
  have hWx : updN N L n = N := by
    funext z
    by_cases hz : z = L
    · rw [hz, updN_self, hNL]
    · exact updN_ne _ _ _ _ hz
  obtain ⟨hV, hRV⟩ := treeOK_updN_sub N i r L n m (by rw [hWx]; exact hT) hsub
  rw [hWx] at hRV
  have hs : ∀ c', (m.searchEq i c').map (·.y) = if c' == cv then none else (n.searchEq i c').map (·.y) := by
    intro c'; rw [KNode.searchEq_live m i hmwf hmt, hlook, KNode.searchEq_live n i hnwf hnt]
  exact ⟨hV, fun z hz => tReach_reachS _ _ _ _ (hRV z (reachS_tReach _ _ _ _ hz)), hsub,
    getFromR_delVirtual N Val i fuel hfuel r L rk pre cv n m hNL hnl hml hs hrk hcv hvisL huniq⟩

/-- After a time split of the delete's leaf L into the new node y with L's live
klongs but cv's, its parent q, inner or a segment leaf, naming y by its klong
k1: the key reads as no value, every other key as before. -/
theorem getFromR_timeSplit_delAny (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q y : NodeId) (n qn m : KNode)
    (k1 : Nat) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (hT : TreeOK N i root) (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.liveAt i)
    (hrqV : ReachS (updN N L m) i root q)
    (hml : m.leaf = true) (hmwf : klongsWf m.ks = true) (hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i)
    (hmlook : ∀ c, m.live.lookup c = if c == cv then none else n.live.lookup c)
    (hN2y : N2 y = some m) (hN2q : N2 q = some (qn.add i (.key k1 y)))
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ y → N2 x = N x)
    (hVL : V L = none) (hVy : V y = none)
    (hqL : q ≠ L) (hyL : y ≠ L) (hNy : N y = none)
    (hnoy : ∀ u c, ReachS N i root u → ¬ TLink N i u c y)
    (hrootL : root ≠ L) (hrooty : root ≠ y)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv]) :
    ∀ key', keyWf key' = true → getFromR N2 V i fuel key' root =
      if pre ++ [cv] == key' then none else getFromR N V i fuel key' root := by
  obtain ⟨hTV, hRV, hsub, hread⟩ := del_virtual N V i fuel hfuel root L rk pre cv n m hNL hnl hnwf hnt
    hml hmwf hmt hmlook hT hrk hcv hvisL huniq
  have hwfV : ∀ z zn, ReachS (updN N L m) i root z → updN N L m z = some zn → klongsWf zn.ks = true := by
    intro z zn hz hzn
    by_cases hzL : z = L
    · subst hzL; rw [updN_self] at hzn; cases hzn; exact hmwf
    · rw [updN_ne _ _ _ _ hzL] at hzn
      exact hwf z zn (hRV z hz) hzn
  have hVq : updN N L m q = some qn := by rw [updN_ne _ _ _ _ hqL]; exact hNq
  have hVy' : updN N L m y = none := by rw [updN_ne _ _ _ _ hyL]; exact hNy
  have hnoY : ∀ u c, ReachS (updN N L m) i root u → ¬ TLink (updN N L m) i u c y := by
    intro u c hu hl
    obtain ⟨mm, hm, hc⟩ := hl
    have hu' := hRV u hu
    by_cases huL : u = L
    · subst huL
      rw [updN_self] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      exact hnoy u c hu' ⟨n, hNL, hsub c y hc⟩
    · rw [updN_ne _ _ _ _ huL] at hm
      exact hnoy u c hu' ⟨mm, hm, hc⟩
  have hA : ∀ z, z ≠ L → z ≠ q → z ≠ y → N2 z = updN N L m z := by
    intro z h1 h2 h3
    rw [hN2 z h1 h2 h3, updN_ne _ _ _ _ h1]
  have hlev : ∀ key, getFromR N2 V i fuel key root = getFromR (updN N L m) V i fuel key root := by
    cases hql : qn.leaf with
    | true =>
      exact getFromR_segTimeLevel (updN N L m) N2 V i fuel root q L y qn m m k1 hTV hwfV hVq hrqV hql
        hqwf hqt hk1 hqL (updN_self _ _ _) hmwf hmt hVy' hnoY hN2y rfl hmwf hmt (fun _ => rfl) hN2q hA
        (by rw [hVL, hVy]) hrooty hrootL
    | false =>
      exact getFromR_timeLevel (updN N L m) N2 V i fuel root q L y qn m m k1 hTV hwfV hVq hrqV hql
        hqwf hqt hk1 hqL (updN_self _ _ _) hmwf hmt hVy' hnoY hN2y rfl hmwf hmt (fun _ => rfl) hN2q hA
        (by rw [hVL, hVy]) hrooty hrootL
  intro key' hkey'
  rw [hlev key', hread key' hkey']

end SIS.Tree
