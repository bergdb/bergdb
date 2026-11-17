/-
R1 through two changed levels for the delete's leaf (bergdb 030-01, R4's open part, l4b's
`DelFullTimeHole2M`): `holeAtW_copyG` with the redirect one level higher. The key's leaf L,
full, split in time, its copy y the hole; its parent q (inner) split too, q's copy or half
q' (a new inner node) named by q's parent q0 (inner, its node changed in place: a klong
added, or a time split in place). The merges' descent at (g, 0) finds y, by l4e's
`lteP_redirect2` at q0.
-/
import SIS.Tree.LiveDelHoleMade
import SIS.Tree.LiveRedirect2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `(rk :: E)[i]` as an index of `A ++ E` when A ends at rk. -/
theorem getElem?_cons_of_getLast (A E : List NodeId) (rk : NodeId) (hA : A.getLast? = some rk)
    (i : Nat) : (rk :: E)[i]? = (A ++ E)[A.length - 1 + i]? := by
  obtain ⟨A', rfl⟩ := List.getLast?_eq_some_iff.mp hA
  have h1 : A' ++ [rk] ++ E = A' ++ (rk :: E) := by simp
  rw [h1, List.getElem?_append_right (by simp)]
  congr 1
  simp

set_option maxHeartbeats 3200000 in
/-- R1 at the copy y of the key's leaf L when L's parent q (inner) split too: q's parent
q0 (inner) now names q's new node q' (inner, its copy or the half with L's klong) by its
search of the key's last compare value, and q' names y; the reads alike but at q0, q, L,
q' and y. The merges' descent at y's cached segment and height 0 finds y. -/
theorem holeAtW_copyG2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w w3 v : W)
    (pre : List Nat) (cv : Nat) (rk L : NodeId) (n : KNode) (P : List (Option Nat × NodeId))
    (y : NodeId) (g : Nat) (ny : KNode)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hun : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hwfw : ∀ x m, wNode c.p base w x = some m → klongsWf m.ks = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hr03 : ReadsAs c.p base w w3) (hp3' : w3.path = (none, w.top.rootKey) :: P)
    (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hXD : nodeAt w.top.rootKey P P.length = L)
    (hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n))
    (hkey : keyWf (pre ++ [cv]) = true) (hP2 : 2 ≤ P.length)
    (hq0in : ((wNode c.p base w (nodeAt w.top.rootKey P (P.length - 2))).getD n).leaf = false)
    (hqin : ((wNode c.p base w (nodeAt w.top.rootKey P (P.length - 1))).getD n).leaf = false)
    (q' : NodeId) (q0n' qn' : KNode)
    (hvq0 : v.nodes.lookup (nodeAt w.top.rootKey P (P.length - 2)) = some q0n')
    (hq0l' : q0n'.leaf = false)
    (hs0 : ∃ fd0, q0n'.searchLte c.i cv = some fd0 ∧ fd0.y = q')
    (hvq' : v.nodes.lookup q' = some qn') (hq'l : qn'.leaf = false)
    (hs' : ∃ fd', qn'.searchLte c.i cv = some fd' ∧ fd'.y = y)
    (hvy : v.nodes.lookup y = some ny) (hnyl : ny.leaf = true) (hy3 : w3.nodes.lookup y = none)
    (hq'3 : w3.nodes.lookup q' = none)
    (hvn : ∀ z, z ≠ nodeAt w.top.rootKey P (P.length - 2) → z ≠ nodeAt w.top.rootKey P (P.length - 1) →
      z ≠ L → z ≠ q' → z ≠ y → v.nodes.lookup z = w3.nodes.lookup z)
    (hvtop : v.top = w3.top)
    (hs : SegRd (rdN c v) (rdG c v)) (hgy : rdG c v y = some (g, 0)) :
    HoleAtW (pre ++ [cv]) g 0 c v y := by
  -- notation
  generalize hroot : w.top.rootKey = root at *
  have hw3root : w3.top.rootKey = root := by rw [hr03.2.1, hroot]
  have hvroot : v.top.rootKey = root := by rw [hvtop, hw3root]
  -- the path's nodes: reached, distinct, at the path's places
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hdist : ∀ i i', i ≤ P.length → i' ≤ P.length → nodeAt root P i = nodeAt root P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt root P i) := by
    intro i hi
    have hl : i < (root :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  -- the reads at w3 agree with the tree at the key's reading
  have hag3 : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) root,
      ∃ m, wNode c.p base w q.1 = some m ∧ rdN c w3 q.1 = some m := by
    intro q hq
    obtain ⟨k, hk⟩ := fromVisits_reach_leaf _ _ _ cv L n hn hnl hwfw pre _ rk hrk hL q hq
    have hR : TReach (wNode c.p base w) c.i root q.1 :=
      reachS_tReach _ _ _ _ (fromVisits_reach _ _ _ _ (fun x xn _ hx => hwfw x xn hx) _ _ q.1 q.2
        ReachS.root hq)
    obtain ⟨hkj, hqj⟩ := nodeAt_of_reach _ _ _ hT P hlinkP q.1 L k hk hR P.length (Nat.le_refl _) hXD.symm
    have hm : ∃ m, wNode c.p base w q.1 = some m := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [hqj, h0, Nat.sub_zero, hXD]; exact ⟨n, hn⟩
      · obtain ⟨_, m, _, hm0, _⟩ := LinkedFrom.get _ _ _ P hlinkP (P.length - k) (by omega)
        exact ⟨m, by rw [hqj]; exact hm0⟩
    obtain ⟨m, hm⟩ := hm
    have hl3 : w3.nodes.lookup q.1 = some ((wNode c.p base w q.1).getD n) := by
      have := hlkX (P.length - k) (by omega)
      rw [← hqj] at this
      exact this
    rw [hm] at hl3
    exact ⟨m, hm, rdN_of_lookup _ w3 _ m hl3⟩
  -- the key's descent at w3: through pre to rk, then to L
  obtain ⟨P0, hP0⟩ := dsrFold_of_segRootR (wNode c.p base w) (rdN c w3) c.i c.p.fuel cv pre root
    [(none, root)] rk (fun q hq _ => by obtain ⟨m, h1, h2⟩ := hag3 q hq; exact Or.inl (by rw [h1, h2]))
    (keyWf_last_notin pre cv hkey) hrk
  have hRL3 : rdN c w3 L = some n := by
    have := hlkX P.length (Nat.le_refl _)
    rw [hXD, hn] at this
    exact rdN_of_lookup _ w3 _ n this
  obtain ⟨ext, hext⟩ := lteP_of_eqVisits (wNode c.p base w) (rdN c w3) c.i cv L ⟨n, hRL3, hnl⟩ c.p.fuel rk hL
    (fun q hq m hm _ => by
      obtain ⟨m', h1, h2⟩ := hag3 q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
      rw [hm] at h1; cases h1; exact h2)
  -- it is linked in the tree, so it is the walk's path
  have hsub3 : ∀ y m, TReach (wNode c.p base w) c.i root y → rdN c w3 y = some m →
      wNode c.p base w y = some m := by
    intro y m hy h
    rw [← hr03.1]
    exact rdN_sub_wNode c base hvc w3 y m (by rw [hr03.2.2.1]; exact hun y hy) h
  obtain ⟨sfx, hsfx, hlsfx, hesfx⟩ := dsrFold_linked (rdN c w3) (wNode c.p base w) c.i root c.p.fuel hsub3
    hwfw pre root [(none, root)] rk P0 hP0 TReach.root
  have hrkR : TReach (wNode c.p base w) c.i root rk := by
    rw [← hesfx, ← nodeAt_last]
    exact (LinkedFrom.pathLen _ _ _ sfx hlsfx sfx.length (Nat.le_refl _)).reach
  obtain ⟨hlext, heext⟩ := lteP_linked (rdN c w3) (wNode c.p base w) c.i root cv hsub3 c.p.fuel rk L ext
    hext hrkR
  have hPeq : P = sfx ++ ext := by
    refine linkedFrom_unique _ _ _ hT P (sfx ++ ext) hlinkP
      (LinkedFrom.append _ _ root sfx ext hlsfx (by rw [hesfx]; exact hlext)) ?_
    rw [hXD, nodeAt_last, pathEnd_append_gen, hesfx, heext]
  have hw3p : w3.path = P0 ++ ext := by rw [hp3', hPeq, hsfx]; simp
  -- the path's nodes at w3 read as the tree's
  have hR3i : ∀ i, i ≤ P.length → rdN c w3 (nodeAt root P i) =
      some ((wNode c.p base w (nodeAt root P i)).getD n) :=
    fun i hi => rdN_of_lookup _ w3 _ _ (hlkX i hi)
  -- a path node is no y and no q'
  have hpy : ∀ i, i ≤ P.length → nodeAt root P i ≠ y := by
    intro i hi he
    have := hlkX i hi
    rw [he, hy3] at this
    cases this
  have hpq' : ∀ i, i ≤ P.length → nodeAt root P i ≠ q' := by
    intro i hi he
    have := hlkX i hi
    rw [he, hq'3] at this
    cases this
  -- the path's nodes before q0 read alike at v
  have hag : ∀ i, i + 2 < P.length → rdN c v (nodeAt root P i) = rdN c w3 (nodeAt root P i) := by
    intro i hi
    apply rdN_congr_lookup
    apply hvn
    · intro he; have := hdist _ _ (by omega) (by omega) he; omega
    · intro he; have := hdist _ _ (by omega) (by omega) he; omega
    · intro he; rw [← hXD] at he; have := hdist _ _ (by omega) (Nat.le_refl _) he; omega
    · exact hpq' i (by omega)
    · exact hpy i (by omega)
  have hlenW : w3.path.length = P.length + 1 := by rw [hp3']; simp
  have hinW : ∀ (Q R : List (Option Nat × NodeId)), w3.path = Q ++ R → ∀ z ∈ Q.map (·.2),
      ∃ i, i < Q.length ∧ i ≤ P.length ∧ z = nodeAt root P i := by
    intro Q R hQR z hz
    obtain ⟨i, hi, hiz⟩ := mem_prefix_index Q R w3.path hQR z hz
    have h1 : (Q ++ R).length = P.length + 1 := by rw [← hQR]; exact hlenW
    rw [List.length_append] at h1
    have h2 := hpX i (by omega)
    rw [hiz] at h2
    exact ⟨i, hi, by omega, Option.some.inj h2⟩
  have hP0last := (dsrFold_shape (rdN c w3) c.i c.p.fuel pre root [(none, root)] _ P0 hP0 (by simp))
  have hlen0 : P0.length + ext.length = P.length + 1 := by
    have : (P0 ++ ext).length = P.length + 1 := by rw [← hw3p, hlenW]
    simpa using this
  have hP0pos : 1 ≤ P0.length := by
    have := hP0last.1
    cases P0 with
    | nil => simp at this
    | cons _ _ => simp
  -- the index of the segment's tree's descent in the path
  have hidx : ∀ i z, (rk :: ext.map (·.2))[i]? = some z → P0.length - 1 + i ≤ P.length ∧
      z = nodeAt root P (P0.length - 1 + i) := by
    intro i z hz
    have hz' := hz
    rw [getElem?_cons_of_getLast (P0.map (·.2)) (ext.map (·.2)) rk hP0last.1 i] at hz'
    simp only [List.length_map] at hz'
    have hle : P0.length - 1 + i ≤ P.length := by
      rcases Nat.lt_or_ge i (ext.length + 1) with h | h
      · omega
      · rw [List.getElem?_eq_none (by simp; omega)] at hz; cases hz
    refine ⟨hle, ?_⟩
    have h2 := hpX _ hle
    rw [hw3p, ← List.getElem?_map, List.map_append, hz'] at h2
    exact Option.some.inj h2
  -- the segment's tree holds q0 and q: else q0 or q would be a segment leaf
  have hpre_leaf : pre ≠ [] → ∃ yl, (P0.map (·.2)).dropLast.getLast? = some yl ∧
      ∃ nl, rdN c w3 yl = some nl ∧ nl.leaf = true := by
    intro hne
    obtain ⟨yl, nl, h1, h2, h3⟩ := hP0last.2 hne
    exact ⟨yl, h1, nl, h2, h3⟩
  have hP0two : pre ≠ [] → 2 ≤ P0.length := by
    intro hne
    obtain ⟨sfx0, hsfx0, hne0⟩ := dsrFold_prefix _ c.i c.p.fuel pre root _ rk P0 hP0
    rw [hsfx0]
    cases sfx0 with
    | nil => exact absurd rfl (hne0 hne)
    | cons _ _ => simp
  have hsecond : pre ≠ [] → ∃ nl, rdN c w3 (nodeAt root P (P0.length - 2)) = some nl ∧ nl.leaf = true := by
    intro hne
    obtain ⟨yl, hyl, nl, h2, h3⟩ := hpre_leaf hne
    have h2' := hP0two hne
    refine ⟨nl, ?_, h3⟩
    have hy : nodeAt root P (P0.length - 2) = yl := by
      have hh := hpX (P0.length - 2) (by omega)
      rw [hw3p, List.getElem?_append_left (by omega)] at hh
      rw [List.getLast?_eq_getElem?, List.getElem?_dropLast] at hyl
      have hl1 : (P0.map (·.2)).dropLast.length - 1 < (P0.map (·.2)).length - 1 := by simp; omega
      simp only [hl1, ↓reduceIte] at hyl
      have : (P0.map (·.2)).dropLast.length - 1 = P0.length - 2 := by simp; omega
      rw [this, List.getElem?_map] at hyl
      rw [hyl] at hh
      exact (Option.some.inj hh).symm
    rw [hy]; exact h2
  have hext2 : 2 ≤ ext.length := by
    rcases Nat.lt_or_ge ext.length 2 with h | h
    · exfalso
      by_cases hpre0 : pre = []
      · rw [hpre0] at hP0
        simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at hP0
        rw [← hP0.2] at hlen0
        simp at hlen0
        omega
      · obtain ⟨nl, hnl1, hnl2⟩ := hsecond hpre0
        rcases Nat.lt_or_ge ext.length 1 with h0 | h1
        · -- L is the segment root, q the segment leaf above it
          have : P0.length - 2 = P.length - 1 := by omega
          rw [this, hR3i _ (by omega)] at hnl1
          cases hnl1
          rw [hqin] at hnl2; cases hnl2
        · -- q is the segment root, q0 the segment leaf above it
          have : P0.length - 2 = P.length - 2 := by omega
          rw [this, hR3i _ (by omega)] at hnl1
          cases hnl1
          rw [hq0in] at hnl2; cases hnl2
    · exact h
  -- q0's place in the segment's tree's descent
  have hq0in' : nodeAt root P (P.length - 2) ∈ rk :: ext.map (·.2) := by
    have hz : (rk :: ext.map (·.2))[P.length - 2 - (P0.length - 1)]? =
        some (nodeAt root P (P.length - 2)) := by
      rw [getElem?_cons_of_getLast (P0.map (·.2)) (ext.map (·.2)) rk hP0last.1, ← List.map_append,
        ← hw3p, List.getElem?_map, List.length_map]
      have : P0.length - 1 + (P.length - 2 - (P0.length - 1)) = P.length - 2 := by omega
      rw [this]
      exact hpX _ (by omega)
    exact List.mem_of_getElem? hz
  have hq0L : nodeAt root P (P.length - 2) ≠ L := by
    intro he; rw [← hXD] at he; have := hdist _ _ (by omega) (Nat.le_refl _) he; omega
  -- the descent through pre is the walk's
  have hfv : pre.foldl (dsrStep (rdN c v) c.i c.p.fuel) (some (root, [(none, root)])) = some (rk, P0) := by
    refine dsrFold_congr (rdN c w3) (rdN c v) c.i c.p.fuel pre root _ rk P0 hP0 ?_ ?_
    · intro hpre
      have h2 := hP0two hpre
      have h0 := hag 0 (by omega)
      simpa [nodeAt] using h0
    · intro z hz
      have hne : P0 ≠ [] := by intro h0; rw [h0] at hP0pos; simp at hP0pos
      obtain ⟨i, hi, hiP, rfl⟩ := hinW P0.dropLast ([P0.getLast hne] ++ ext) (by
        rw [hw3p]
        conv => lhs; rw [← List.dropLast_concat_getLast hne]
        simp) z hz
      rw [List.length_dropLast] at hi
      exact hag i (by omega)
  -- the redirect at q0
  obtain ⟨qm0, hqm0⟩ : ∃ m, rdN c w3 (nodeAt root P (P.length - 2)) = some m :=
    ⟨_, hR3i _ (by omega)⟩
  have hqm0l : qm0.leaf = false := by
    rw [hR3i _ (by omega)] at hqm0; cases hqm0; exact hq0in
  have hq0R : TReach (wNode c.p base w) c.i root (nodeAt root P (P.length - 2)) := (hPL _ (by omega)).reach
  obtain ⟨ext', hlv⟩ := lteP_redirect2 (rdN c w3) (rdN c v) c.i cv (nodeAt root P (P.length - 2)) q' y L
    qm0 q0n' qn' hqm0 (rdN_of_lookup _ v _ _ hvq0) hq0l' (by
      intro fd hfd f' ext'' _
      refine ⟨?_, hs0⟩
      intro hfL
      -- q0's child is at depth P.length - 1, L at P.length
      obtain ⟨_, qm, _, hqm, _⟩ := LinkedFrom.get _ _ _ P hlinkP (P.length - 2) (by omega)
      have hqq : qm0 = qm := by
        rw [hR3i _ (by omega), hqm] at hqm0
        exact (Option.some.inj hqm0).symm
      subst hqq
      have hmem := KNode.searchLte_mem qm0 c.i _ fd hfd
      have hd2 : PathLen (wNode c.p base w) c.i root fd.y (P.length - 2 + 1) :=
        PathLen.link (hPL (P.length - 2) (by omega)) ⟨qm0, hqm, hmem⟩
      rw [hfL] at hd2
      have hd1 := hPL P.length (Nat.le_refl _)
      rw [hXD] at hd1
      have := PathLen.depth_unique hT _ _ _ hd1 hd2
      omega)
      (rdN_of_lookup _ v _ _ hvq') hq'l hs' ⟨ny, rdN_of_lookup _ v _ ny hvy, hnyl⟩
      c.p.fuel rk ext hext hq0in' hq0L (by
        intro z i hz hzq0 hfirst
        obtain ⟨hle, rfl⟩ := hidx i z hz
        have hq0i : (rk :: ext.map (·.2))[P.length - 2 - (P0.length - 1)]? =
            some (nodeAt root P (P.length - 2)) := by
          rw [getElem?_cons_of_getLast (P0.map (·.2)) (ext.map (·.2)) rk hP0last.1,
            ← List.map_append, ← hw3p, List.getElem?_map, List.length_map]
          have : P0.length - 1 + (P.length - 2 - (P0.length - 1)) = P.length - 2 := by omega
          rw [this]
          exact hpX _ (by omega)
        have hij := hfirst _ hq0i
        have hne : P0.length - 1 + i ≠ P.length - 2 := fun he => hzq0 (by rw [he])
        exact hag _ (by omega))
  exact holeAtW_leaf c v pre cv rk y g 0 hs (keyWf_init_long pre cv hkey) ⟨P0, by rw [hvroot]; exact hfv⟩
    ⟨ext', hlv⟩ hgy

end SIS.Tree
