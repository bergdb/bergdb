/-
R1 through two changed levels at the upward delete's stop node (bergdb 030-01, R4's open
part, l4e's `UpCascSplitRest7OK`): `holeAtW_stopCopy` with the redirect one level higher.
The stop node X stop, a segment leaf, split in time, its copy y the hole; its parent q
(inner) split too, q's copy or half q' (a new inner node) named by q's parent q0 (inner,
its node changed in place). The merges' descent at (g, 0) finds y, by l4e's
`lteP_redirect2` at q0 and the cut at y (`holeAtW_cut`).
-/
import SIS.Tree.LiveUpCascCopy
import SIS.Tree.LiveDelHole2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 3200000 in
/-- R1 at the copy y of the upward delete's stop node X stop when its parent q (inner)
split too: q's parent q0 (inner) now names q's new node q' (inner) by its search of the
chain's compare value, and q' names y; the reads alike above q0 and off the walk's path
below the stop node but at q0, q, X stop, q' and y. -/
theorem holeAtW_stopCopy2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w w3 v : W)
    (pre : List Nat) (cv : Nat) (rk L : NodeId) (n : KNode) (P : List (Option Nat × NodeId))
    (stop gs : Nat) (y q' : NodeId) (nyc q0n' qn' : KNode)
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
    (hkey : keyWf (pre ++ [cv]) = true)
    (hsD : stop < P.length) (hs0 : 1 < stop)
    (hsl : ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf = true)
    (hql : ((wNode c.p base w (nodeAt w.top.rootKey P (stop - 1))).getD n).leaf = false)
    (hq0l : ((wNode c.p base w (nodeAt w.top.rootKey P (stop - 2))).getD n).leaf = false)
    (hvn : ∀ z, z ≠ nodeAt w.top.rootKey P (stop - 2) → z ≠ nodeAt w.top.rootKey P (stop - 1) →
      z ≠ nodeAt w.top.rootKey P stop → z ≠ q' → z ≠ y →
      (∀ k, stop < k → k ≤ P.length → z ≠ nodeAt w.top.rootKey P k) →
      v.nodes.lookup z = w3.nodes.lookup z)
    (hy3 : w3.nodes.lookup y = none)
    (hvtop : v.top = w3.top)
    (hvq0 : v.nodes.lookup (nodeAt w.top.rootKey P (stop - 2)) = some q0n') (hq0l' : q0n'.leaf = false)
    (hs0' : ∃ fd0, q0n'.searchLte c.i (((P[stop]?).bind (·.1)).getD 0) = some fd0 ∧ fd0.y = q')
    (hvq' : v.nodes.lookup q' = some qn') (hq'l : qn'.leaf = false)
    (hs1' : ∃ fd1, qn'.searchLte c.i (((P[stop]?).bind (·.1)).getD 0) = some fd1 ∧ fd1.y = y)
    (hq'3 : w3.nodes.lookup q' = none)
    (hvy : v.nodes.lookup y = some nyc) (hnyl : nyc.leaf = true)
    (hcutK : ∀ z, (((P[stop]?).bind (·.1)).getD 0, z) ∉ nyc.live)
    (hsw : klongsWf nyc.ks = true) (hst : ∀ s, Klong.time s ∈ nyc.ks → s ≤ c.i)
    (hs : SegRd (rdN c v) (rdG c v))
    (hgL : rdG c v y = some (gs, 0)) :
    HoleAtW (pre ++ [cv]) gs 0 c v y := by
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
  -- the stop node on the descent: one segment's leaf
  have hXsl : rdN c w3 (nodeAt root P stop) = some ((wNode c.p base w (nodeAt root P stop)).getD n) :=
    rdN_of_lookup _ w3 _ _ (hlkX stop (by omega))
  have hXsL : nodeAt root P stop ≠ L := by
    intro he
    rw [← hXD] at he
    have := hdist _ _ (by omega) (Nat.le_refl _) he
    omega
  -- its place in P0: not in ext but at its end L, and not rk unless rk = L
  obtain ⟨j, c', rj, Pj, extj, ny, fd, hc', hfj, hlj, hny, hfd, sfx', hP0'⟩ :
      ∃ j c' rj Pj extj ny fd, pre[j]? = some c' ∧
        (pre.take j).foldl (dsrStep (rdN c w3) c.i c.p.fuel) (some (root, [(none, root)])) = some (rj, Pj) ∧
        lteP (rdN c w3) c.i c' c.p.fuel rj = some (nodeAt root P stop, extj) ∧
        rdN c w3 (nodeAt root P stop) = some ny ∧ ny.searchEq c.i c' = some fd ∧
        ∃ sfx', P0 = Pj ++ extj ++ (some fd.c, fd.y) :: sfx' := by
    -- the stop node is a node of the walk's path at stop; it is on P0
    have hXP0 : nodeAt root P stop ∈ P0.map (·.2) ∧ nodeAt root P stop ≠ rk := by
      have hin : (w3.path[stop]?).map (·.2) = some (nodeAt root P stop) := hpX stop (by omega)
      rw [hw3p] at hin
      by_cases hlt : stop < P0.length
      · rw [List.getElem?_append_left hlt] at hin
        refine ⟨?_, ?_⟩
        · obtain ⟨e, he⟩ : ∃ e, P0[stop]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
          rw [he] at hin
          simp only [Option.map_some, Option.some.injEq] at hin
          rw [← hin]
          exact List.mem_map.mpr ⟨e, List.mem_of_getElem? he, rfl⟩
        · intro hrkE
          -- rk a leaf: its descent is empty, so rk = L
          have hlrk := lteP_leaf _ c.i cv c.p.fuel rk L ext hext
          cases fuel_eq : c.p.fuel with
          | zero => rw [fuel_eq] at hext; simp [lteP] at hext
          | succ f =>
            rw [fuel_eq] at hext
            obtain ⟨m0, hRm0, ⟨_, hLe, _⟩ | ⟨hml, _⟩⟩ := lteP_succ_some _ c.i cv f rk L ext hext
            · exact hXsL (hrkE.trans hLe.symm)
            · rw [← hrkE, hXsl] at hRm0
              cases hRm0
              rw [hsl] at hml
              cases hml
      · exfalso
        rw [List.getElem?_append_right (by omega)] at hin
        -- a node of ext's part: inner, but the stop node is a leaf
        have hmem : nodeAt root P stop ∈ rk :: ext.map (·.2) := by
          obtain ⟨e, he⟩ : ∃ e, ext[stop - P0.length]? = some e := by
            cases h' : ext[stop - P0.length]? with
            | none => rw [h'] at hin; cases hin
            | some e => exact ⟨e, rfl⟩
          rw [he] at hin
          simp only [Option.map_some, Option.some.injEq] at hin
          rw [← hin]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, List.mem_of_getElem? he, rfl⟩)
        obtain ⟨m, hm, hml⟩ := lteP_mid_inner _ c.i cv c.p.fuel rk L ext hext _ hmem hXsL
        rw [hXsl] at hm
        cases hm
        rw [hsl] at hml
        cases hml
    by_cases hs0 : stop = 0
    · -- the stop node is the space root, a leaf: the first segment's search
      have hroot0 : nodeAt root P stop = root := by rw [hs0]; simp [nodeAt]
      cases pre with
      | nil =>
        exfalso
        simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at hP0
        exact hXP0.2 (by rw [hroot0, hP0.1])
      | cons c0 pre' =>
        simp only [List.foldl] at hP0
        cases hst : dsrStep (rdN c w3) c.i c.p.fuel (some (root, [(none, root)])) c0 with
        | none => rw [hst, dsrFold_none] at hP0; cases hP0
        | some acc =>
          rw [hst] at hP0
          obtain ⟨leaf0, ext0, n0, fd0, hl0, hRl0, hfd0, rfl⟩ := dsrStep_some _ c.i c.p.fuel root _ c0 acc hst
          have hle0 : lteP (rdN c w3) c.i c0 c.p.fuel root = some (root, []) := by
            cases fuel_eq : c.p.fuel with
            | zero => rw [fuel_eq] at hl0; simp [lteP] at hl0
            | succ f =>
              rw [← hroot0]
              simp [lteP, hXsl, hsl]
          rw [hle0] at hl0
          simp only [Option.some.injEq, Prod.mk.injEq] at hl0
          obtain ⟨rfl, rfl⟩ := hl0
          obtain ⟨sfx0, hsfx0, _⟩ := dsrFold_prefix _ c.i c.p.fuel pre' fd0.y _ rk P0 hP0
          refine ⟨0, c0, root, [(none, root)], [], n0, fd0, rfl, rfl, by rw [hroot0]; exact hle0,
            by rw [hroot0]; exact hRl0, hfd0, sfx0, by rw [hsfx0]; simp⟩
    · obtain ⟨j, c', rj, Pj, extj, ny, fd, hc', hfj, hlj, hny, hfd, sfx', hP0'⟩ :=
        dsrFold_leaf_mid (rdN c w3) c.i c.p.fuel pre root [(none, root)] rk P0 hP0 (nodeAt root P stop)
          (by
            have hin : (w3.path[stop]?).map (·.2) = some (nodeAt root P stop) := hpX stop (by omega)
            rw [hw3p] at hin
            have hlt : stop < P0.length := by
              apply Classical.byContradiction
              intro hge
              exact absurd hXP0.1 (by
                intro hm
                obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hm
                simp only [List.length_map] at hi
                -- a node of P0 at index i < P0.length is at index i on the path
                have hpi := hpX i (by
                  have : P0.length ≤ w3.path.length := by rw [hw3p]; simp
                  rw [hp3'] at this; simp at this; omega)
                rw [hw3p, List.getElem?_append_left hi, List.getElem?_eq_getElem hi] at hpi
                simp only [Option.map_some, Option.some.injEq] at hpi
                rw [List.getElem_map] at hie
                rw [hie] at hpi
                have := hdist _ _ (by
                  have : P0.length ≤ w3.path.length := by rw [hw3p]; simp
                  rw [hp3'] at this; simp at this; omega) (by omega) hpi.symm
                omega)
            rw [List.getElem?_append_left hlt] at hin
            have hdrop : P0 = [(none, root)] ++ P0.drop 1 := by rw [hsfx]; simp
            rw [hdrop, List.getElem?_append_right (by simp; omega)] at hin
            simp only [List.length_singleton] at hin
            obtain ⟨e, he⟩ : ∃ e, (P0.drop 1)[stop - 1]? = some e := by
              cases h' : (P0.drop 1)[stop - 1]? with
              | none => rw [h'] at hin; cases hin
              | some e => exact ⟨e, rfl⟩
            rw [he] at hin
            simp only [Option.map_some, Option.some.injEq] at hin
            rw [← hin]
            simp only [List.length_singleton]
            exact List.mem_map.mpr ⟨e, List.mem_of_getElem? he, rfl⟩)
          ⟨_, hXsl, hsl⟩ hXP0.2
      exact ⟨j, c', rj, Pj, extj, ny, fd, hc', hfj, hlj, hny, hfd, sfx', hP0'⟩
  -- the stop node's index in the descent's path: the segment step after it is the chain's
  have hPj0 := (dsrFold_shape (rdN c w3) c.i c.p.fuel (pre.take j) root [(none, root)] rj Pj hfj
    (by simp)).1
  obtain ⟨⟨_, _, _⟩, hlastj⟩ := lteP_leaf _ c.i c' c.p.fuel rj _ extj hlj
  have hA := getLast_map_append Pj extj rj _ hPj0 hlastj
  have hw3p' : w3.path = (Pj ++ extj) ++ (some fd.c, fd.y) :: (sfx' ++ ext) := by
    rw [hw3p, hP0']; simp
  have hlenA : 0 < (Pj ++ extj).length := by
    cases h' : Pj ++ extj with
    | nil => rw [h'] at hA; simp at hA
    | cons _ _ => simp
  have hlenW : w3.path.length = P.length + 1 := by rw [hp3']; simp
  have hAlt : (Pj ++ extj).length < w3.path.length := by rw [hw3p']; simp
  have hAidx : (w3.path[(Pj ++ extj).length - 1]?).map (·.2) = some (nodeAt root P stop) := by
    rw [hw3p', List.getElem?_append_left (by omega)]
    exact path_last_map _ _ hA
  have hAstop : (Pj ++ extj).length - 1 = stop := by
    have h1 := hpX ((Pj ++ extj).length - 1) (by omega)
    rw [hAidx] at h1
    exact hdist _ _ (by omega) (by omega) (Option.some.inj h1).symm
  have hKc : ((P[stop]?).bind (·.1)).getD 0 = c' := by
    have h1 : w3.path[stop + 1]? = some (some fd.c, fd.y) := by
      rw [hw3p', List.getElem?_append_right (by omega), show stop + 1 - (Pj ++ extj).length = 0 by omega]
      rfl
    rw [hp3', List.getElem?_cons_succ] at h1
    rw [h1]
    simp only [Option.bind_some, Option.getD_some]
    exact KNode.searchEq_c ny c.i c' fd hfd
  rw [hKc] at hs0' hs1'
  have hqR3 : rdN c w3 (nodeAt root P (stop - 1)) =
      some ((wNode c.p base w (nodeAt root P (stop - 1))).getD n) :=
    rdN_of_lookup _ w3 _ _ (hlkX (stop - 1) (by omega))
  have hq0R3 : rdN c w3 (nodeAt root P (stop - 2)) =
      some ((wNode c.p base w (nodeAt root P (stop - 2))).getD n) :=
    rdN_of_lookup _ w3 _ _ (hlkX (stop - 2) (by omega))
  have hyRv : rdN c v y = some nyc := rdN_of_lookup _ v _ nyc hvy
  have hq0S : nodeAt root P (stop - 2) ≠ nodeAt root P stop := by
    intro he; have := hdist _ _ (by omega) (by omega) he; omega
  have hAl : Pj.length + extj.length = stop + 1 := by
    have := hAstop; rw [List.length_append] at this hlenA; omega
  -- the stop node's segment's descent has two steps or more: q and q0 are inner
  have hext2 : 2 ≤ extj.length := by
    rcases Nat.lt_or_ge extj.length 2 with h | h
    · exfalso
      by_cases hpj : pre.take j = []
      · rw [hpj] at hfj
        simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at hfj
        rw [← hfj.2] at hAl
        simp at hAl
        omega
      · obtain ⟨y0, n0, hy0, hRy0, hn0l⟩ := (dsrFold_shape (rdN c w3) c.i c.p.fuel (pre.take j) root
          [(none, root)] rj Pj hfj (by simp)).2 hpj
        have hidx := dropLast_getLast_idx _ _ hy0
        rw [List.length_map, List.getElem?_map] at hidx
        have hPjl : 2 ≤ Pj.length := by
          obtain ⟨sfxj, hsfxj, hne'⟩ := dsrFold_prefix _ c.i c.p.fuel (pre.take j) root _ rj Pj hfj
          rw [hsfxj]
          cases sfxj with
          | nil => exact absurd rfl (hne' hpj)
          | cons _ _ => simp
        have h2 := hpX (Pj.length - 2) (by omega)
        rw [hw3p', List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega),
          hidx] at h2
        have hy0' : y0 = nodeAt root P (Pj.length - 2) := Option.some.inj h2
        rcases Nat.lt_or_ge extj.length 1 with h0 | h1
        · have : Pj.length - 2 = stop - 1 := by omega
          rw [hy0', this, hqR3] at hRy0
          cases hRy0
          rw [hql] at hn0l
          cases hn0l
        · have : Pj.length - 2 = stop - 2 := by omega
          rw [hy0', this, hq0R3] at hRy0
          cases hRy0
          rw [hq0l] at hn0l
          cases hn0l
    · exact h
  -- the path's nodes above q0 read alike at v
  have habove : ∀ i, i + 2 < stop → rdN c v (nodeAt root P i) = rdN c w3 (nodeAt root P i) := by
    intro i hi
    apply rdN_congr_lookup
    apply hvn
    · intro he; have := hdist _ _ (by omega) (by omega) he; omega
    · intro he; have := hdist _ _ (by omega) (by omega) he; omega
    · intro he; have := hdist _ _ (by omega) (by omega) he; omega
    · intro he
      have := hlkX i (by omega)
      rw [he, hq'3] at this
      cases this
    · intro he
      have := hlkX i (by omega)
      rw [he, hy3] at this
      cases this
    · intro k h1 h2 he; have := hdist _ _ (by omega) h2 he; omega
  -- the descent at v through the stop node's segments
  have hfv : (pre.take j).foldl (dsrStep (rdN c v) c.i c.p.fuel) (some (root, [(none, root)])) =
      some (rj, Pj) := by
    refine dsrFold_congr (rdN c w3) (rdN c v) c.i c.p.fuel (pre.take j) root _ rj Pj hfj ?_ ?_
    · intro hne
      obtain ⟨sfxj, hsfxj, hne'⟩ := dsrFold_prefix _ c.i c.p.fuel (pre.take j) root _ rj Pj hfj
      have h2 : 2 ≤ Pj.length := by
        rw [hsfxj]
        cases sfxj with
        | nil => exact absurd rfl (hne' hne)
        | cons _ _ => simp
      have hroot0 : root = nodeAt root P 0 := by simp [nodeAt]
      rw [hroot0]
      exact habove 0 (by omega)
    · intro y hy
      have hPjne : Pj ≠ [] := by
        intro h0; rw [h0] at hPj0; simp at hPj0
      have hsplit : w3.path = Pj.dropLast ++ ((Pj.getLast hPjne) :: (extj ++
          (some fd.c, fd.y) :: (sfx' ++ ext))) := by
        rw [hw3p']
        conv => lhs; rw [← List.dropLast_concat_getLast hPjne]
        simp
      obtain ⟨i', hi', hiy'⟩ := mem_prefix_index Pj.dropLast _ w3.path hsplit _ hy
      rw [List.length_dropLast] at hi'
      have h2 := hpX i' (by omega)
      rw [hiy'] at h2
      rw [Option.some.inj h2]
      exact habove i' (by omega)
  have hPjpos : 1 ≤ Pj.length := by
    cases Pj with
    | nil => simp at hPj0
    | cons _ _ => simp
  -- the index of the segment's descent in the path
  have hidxS : ∀ i z, (rj :: extj.map (·.2))[i]? = some z → Pj.length - 1 + i ≤ stop ∧
      z = nodeAt root P (Pj.length - 1 + i) := by
    intro i z hz
    have hz' := hz
    rw [getElem?_cons_of_getLast (Pj.map (·.2)) (extj.map (·.2)) rj hPj0 i] at hz'
    simp only [List.length_map] at hz'
    have hle : Pj.length - 1 + i ≤ stop := by
      rcases Nat.lt_or_ge i (extj.length + 1) with h | h
      · omega
      · rw [List.getElem?_eq_none (by simp; omega)] at hz; cases hz
    refine ⟨hle, ?_⟩
    have h2 := hpX (Pj.length - 1 + i) (by omega)
    rw [hw3p', List.getElem?_append_left (by simp; omega), ← List.getElem?_map, List.map_append,
      hz'] at h2
    exact Option.some.inj h2
  have hq0i : (rj :: extj.map (·.2))[stop - 2 - (Pj.length - 1)]? = some (nodeAt root P (stop - 2)) := by
    rw [getElem?_cons_of_getLast (Pj.map (·.2)) (extj.map (·.2)) rj hPj0, ← List.map_append,
      List.getElem?_map, List.length_map]
    have : Pj.length - 1 + (stop - 2 - (Pj.length - 1)) = stop - 2 := by omega
    rw [this]
    have h2 := hpX (stop - 2) (by omega)
    rw [hw3p', List.getElem?_append_left (by simp; omega)] at h2
    exact h2
  have hq0in : nodeAt root P (stop - 2) ∈ rj :: extj.map (·.2) := List.mem_of_getElem? hq0i
  obtain ⟨_, qm, _, hqm, _⟩ := LinkedFrom.get _ _ _ P hlinkP (stop - 2) (by omega)
  have hq0R3' : rdN c w3 (nodeAt root P (stop - 2)) = some qm := by rw [hq0R3, hqm]; rfl
  have hqml : qm.leaf = false := by
    have := hq0l; rw [hqm] at this; exact this
  obtain ⟨ext', hlv⟩ := lteP_redirect2 (rdN c w3) (rdN c v) c.i c' (nodeAt root P (stop - 2)) q' y
    (nodeAt root P stop) qm q0n' qn' hq0R3' (rdN_of_lookup _ v _ _ hvq0) hq0l' (by
      intro fd hfd f' ext'' _
      refine ⟨?_, hs0'⟩
      intro hfL
      have hmem := KNode.searchLte_mem qm c.i _ fd hfd
      have hd2 : PathLen (wNode c.p base w) c.i root fd.y (stop - 2 + 1) :=
        PathLen.link (hPL (stop - 2) (by omega)) ⟨qm, hqm, hmem⟩
      rw [hfL] at hd2
      have hd1 := hPL stop (by omega)
      have := PathLen.depth_unique hT _ _ _ hd1 hd2
      omega)
    (rdN_of_lookup _ v _ _ hvq') hq'l hs1' ⟨nyc, hyRv, hnyl⟩ c.p.fuel rj extj hlj hq0in hq0S (by
      intro z i hz hzq0 hfirst
      obtain ⟨hle, rfl⟩ := hidxS i z hz
      have hij := hfirst _ hq0i
      have hne : Pj.length - 1 + i ≠ stop - 2 := fun he => hzq0 (by rw [he])
      exact habove _ (by omega))
  -- the cut: the copy has no live klong of the chain's compare value
  have hcut : nyc.searchEq c.i c' = none := by
    have h1 := KNode.searchEq_live nyc c.i hsw hst c'
    cases h2 : nyc.searchEq c.i c' with
    | none => rfl
    | some f =>
      exfalso
      rw [h2] at h1
      simp only [Option.map_some] at h1
      have := bk_mem_of_lookup _ _ _ h1.symm
      rw [← hKc] at this
      exact hcutK _ this
  have hkeyEq : pre.take j ++ c' :: (pre.drop (j + 1) ++ [cv]) = pre ++ [cv] := by
    have hjl : j < pre.length := (List.getElem?_eq_some_iff.mp hc').1
    have e := (List.getElem?_eq_some_iff.mp hc').2
    have hpre : pre.take j ++ c' :: pre.drop (j + 1) = pre := by
      rw [← e, ← List.drop_eq_getElem_cons hjl, List.take_append_drop]
    calc pre.take j ++ c' :: (pre.drop (j + 1) ++ [cv])
        = (pre.take j ++ c' :: pre.drop (j + 1)) ++ [cv] := by simp
      _ = pre ++ [cv] := by rw [hpre]
  rw [← hkeyEq]
  exact holeAtW_cut c v (pre.take j) c' (pre.drop (j + 1) ++ [cv]) rj y gs 0 hs
    (fun x hx => keyWf_init_long pre cv hkey x (List.mem_of_mem_take hx)) ⟨Pj, by rw [hvroot]; exact hfv⟩
    ⟨ext', hlv⟩ (Or.inr ⟨nyc, hyRv, hcut⟩) hgL


end SIS.Tree
