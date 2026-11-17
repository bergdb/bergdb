/-
R4 narrowed further (bergdb 030-01, step 5): the leaf split in time below a parent
that the transaction made, full, whose own split is in time, in place.
-/
import SIS.Tree.LiveAssembly2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `KNode.add_key_searchLte` for any node m whose live klongs are n's but k1's
naming y. -/
theorem KNode.searchLte_redirect (n m : KNode) (t : Time) (k1 : Nat) (y : NodeId)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (ht2 : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (hk1 : ∃ z, (k1, z) ∈ n.live)
    (hlk : ∀ c', m.live.lookup c' = if k1 == c' then some y else n.live.lookup c') (c : Int) :
    (m.searchLte t c).map (fun f => (f.c, f.y)) =
      (n.searchLte t c).map (fun f => (f.c, if f.c = k1 then y else f.y)) := by
  have hL1 := KNode.liveAt_of_times n t ht
  have hL2 := KNode.liveAt_of_times _ t ht2
  have hnd1 := KNode.live_keys_nodup n
  have hnd2 := KNode.live_keys_nodup m
  have hmem2 : ∀ c' z, (c', z) ∈ m.live ↔
      if k1 = c' then z = y else (c', z) ∈ n.live := by
    intro c' z
    rw [mem_iff_lookup _ hnd2, hlk]
    by_cases h : k1 = c'
    · subst h; simp [eq_comm]
    · have : (k1 == c') = false := by simpa using h
      simp only [this, Bool.false_eq_true, ↓reduceIte, h]
      rw [mem_iff_lookup _ hnd1]
  -- the same compare values
  have hkeys : ∀ c', (∃ z, (c', z) ∈ m.live) ↔ ∃ z, (c', z) ∈ n.live := by
    intro c'
    by_cases h : k1 = c'
    · subst h
      constructor
      · intro _; exact hk1
      · intro _; exact ⟨y, (hmem2 k1 y).mpr (by simp)⟩
    · simp only [hmem2, h, ↓reduceIte]
  have hs1 := n.searchLte_spec t c
  have hs2 := m.searchLte_spec t c
  unfold NodeSearchSpec at hs1 hs2
  rw [hL1] at hs1
  rw [hL2] at hs2
  cases h1 : n.searchLte t c with
  | none =>
    have hall := hs1.2.mp h1
    have : m.searchLte t c = none := by
      apply hs2.2.mpr
      intro q hq
      obtain ⟨z, hz⟩ := (hkeys q.1).mp ⟨q.2, hq⟩
      exact hall (q.1, z) hz
    rw [this]; rfl
  | some f =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs1.1 f h1
    cases h2 : m.searchLte t c with
    | none =>
      have hall := hs2.2.mp h2
      obtain ⟨z, hz⟩ := (hkeys f.c).mpr ⟨f.y, hfm⟩
      have := hall (f.c, z) hz
      rw [hfa] at this; cases this
    | some f' =>
      obtain ⟨hfm', hfa', hfmax'⟩ := hs2.1 f' h2
      obtain ⟨z, hz⟩ := (hkeys f.c).mpr ⟨f.y, hfm⟩
      have hle1 := hfmax' (f.c, z) hz hfa
      obtain ⟨z', hz'⟩ := (hkeys f'.c).mp ⟨f'.y, hfm'⟩
      have hle2 := hfmax (f'.c, z') hz' hfa'
      simp only [decide_eq_true_eq] at hle1 hle2
      have hc : f'.c = f.c := by omega
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨hc, ?_⟩
      have hy := (hmem2 f'.c f'.y).mp hfm'
      rw [hc] at hy
      by_cases hk : f.c = k1
      · subst hk; simp only [↓reduceIte] at hy ⊢; exact hy
      · have hk' : ¬ k1 = f.c := fun h => hk h.symm
        simp only [hk', ↓reduceIte] at hy
        simp only [hk, ↓reduceIte]
        exact Option.some.inj ((lookup_some_of_mem hnd1 hy).symm.trans (lookup_some_of_mem hnd1 hfm))

/-! ## A descent with its access path -/
set_option maxHeartbeats 3200000 in
/-- `holeAtW_copy` for any new node qn' of the parent q whose searches are q's but
its klong of L naming the copy y (q's time split in place, or its klong added). -/
theorem holeAtW_copyG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w w3 v : W)
    (pre : List Nat) (cv : Nat) (rk L : NodeId) (n : KNode) (P : List (Option Nat × NodeId))
    (y : NodeId) (g : Nat) (ny : KNode)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hun : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hwfw : ∀ x m, wNode c.p base w x = some m → klongsWf m.ks = true)
    (htmw : ∀ x m, wNode c.p base w x = some m → ∀ s, Klong.time s ∈ m.ks → s ≤ c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hr03 : ReadsAs c.p base w w3) (hp3' : w3.path = (none, w.top.rootKey) :: P)
    (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hXD : nodeAt w.top.rootKey P P.length = L)
    (hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n))
    (hkey : keyWf (pre ++ [cv]) = true) (hPpos : 0 < P.length)
    (qn' : KNode)
    (hvq : v.nodes.lookup (nodeAt w.top.rootKey P (P.length - 1)) = some qn')
    (hqlf' : qn'.leaf = ((wNode c.p base w (nodeAt w.top.rootKey P (P.length - 1))).getD n).leaf)
    (hsLte : ∀ cc : Int, (qn'.searchLte c.i cc).map (fun f => (f.c, f.y)) =
      (((wNode c.p base w (nodeAt w.top.rootKey P (P.length - 1))).getD n).searchLte c.i cc).map
        (fun f => (f.c, if f.c = ((P[P.length - 1]?).bind (·.1)).getD 0 then y else f.y)))
    (hsEq : ∀ cc : Nat, (qn'.searchEq c.i cc).map (·.y) =
      if ((P[P.length - 1]?).bind (·.1)).getD 0 == cc then some y else
        (((wNode c.p base w (nodeAt w.top.rootKey P (P.length - 1))).getD n).searchEq c.i cc).map (·.y))
    (hvy : v.nodes.lookup y = some ny) (hnyl : ny.leaf = true) (hy3 : w3.nodes.lookup y = none)
    (hvn : ∀ z, z ≠ nodeAt w.top.rootKey P (P.length - 1) → z ≠ L → z ≠ y →
      v.nodes.lookup z = w3.nodes.lookup z)
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
  -- the parent q and its klong to L
  have hqidx : P.length - 1 + 1 = P.length := by omega
  obtain ⟨kq, qm, hPq, hqm, hkq⟩ := LinkedFrom.get _ _ _ P hlinkP (P.length - 1) (by omega)
  rw [hqidx, hXD] at hPq hkq
  have hK : ((P[P.length - 1]?).bind (·.1)).getD 0 = kq := by rw [hPq]; rfl
  rw [hK] at hsLte hsEq
  have hqmg : (wNode c.p base w (nodeAt root P (P.length - 1))).getD n = qm := by rw [hqm]; rfl
  rw [hqmg] at hsLte hsEq hqlf'
  have hqwf := hwfw _ _ hqm
  have hqtm := htmw _ _ hqm
  have hqR3 : rdN c w3 (nodeAt root P (P.length - 1)) = some qm := by
    have := hlkX (P.length - 1) (by omega)
    rw [hqmg] at this
    exact rdN_of_lookup _ w3 _ qm this
  have hqRv : rdN c v (nodeAt root P (P.length - 1)) = some qn' :=
    rdN_of_lookup _ v _ _ hvq
  have hyRv : rdN c v y = some ny := rdN_of_lookup _ v _ ny hvy
  have hqL : nodeAt root P (P.length - 1) ≠ L := by
    intro he; rw [← hXD] at he; have := hdist _ _ (by omega) (Nat.le_refl _) he; omega
  -- a path node is no y
  have hpy : ∀ i, i ≤ P.length → nodeAt root P i ≠ y := by
    intro i hi he
    have := hlkX i hi
    rw [he, hy3] at this
    cases this
  -- the path's nodes other than q and L read alike at v
  have hag : ∀ i, i ≤ P.length → i ≠ P.length - 1 → i ≠ P.length →
      rdN c v (nodeAt root P i) = rdN c w3 (nodeAt root P i) := by
    intro i hi h1 h2
    apply rdN_congr_lookup
    apply hvn
    · intro he; have := hdist _ _ hi (by omega) he; omega
    · intro he; rw [← hXD] at he; have := hdist _ _ hi (Nat.le_refl _) he; omega
    · exact hpy i hi
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
  cases hextc : ext with
  | cons e0 erest =>
    -- L below rk: q in the last segment's tree; the descent through pre is the walk's
    have hfv : pre.foldl (dsrStep (rdN c v) c.i c.p.fuel) (some (root, [(none, root)])) = some (rk, P0) := by
      refine dsrFold_congr (rdN c w3) (rdN c v) c.i c.p.fuel pre root _ rk P0 hP0 ?_ ?_
      · intro hpre
        obtain ⟨sfx0, hsfx0, hne0⟩ := dsrFold_prefix _ c.i c.p.fuel pre root _ rk P0 hP0
        have hsfxe : sfx0 = sfx := by rw [hsfx] at hsfx0; simpa using hsfx0.symm
        have hsl : 1 ≤ sfx.length := by
          rw [← hsfxe]
          cases h' : sfx0 with
          | nil => exact absurd h' (hne0 hpre)
          | cons _ _ => simp
        have hPl : P.length = sfx.length + ext.length := by rw [hPeq]; simp
        rw [hextc] at hPl
        simp only [List.length_cons] at hPl
        have h0 := hag 0 (by omega) (by omega) (by omega)
        simpa [nodeAt] using h0
      · intro z hz
        have hne : P0 ≠ [] := by rw [hsfx]; simp
        obtain ⟨i, hi, hiP, rfl⟩ := hinW P0.dropLast ([P0.getLast hne] ++ ext) (by
          rw [hw3p]
          conv => lhs; rw [← List.dropLast_concat_getLast hne]
          simp) z hz
        have hPl : P0.length + ext.length = P.length + 1 := by
          have : (P0 ++ ext).length = P.length + 1 := by rw [← hw3p, hlenW]
          simpa using this
        have hP0pos := List.length_pos_iff.mpr hne
        rw [List.length_dropLast] at hi
        rw [hextc] at hPl
        simp only [List.length_cons] at hPl
        exact hag i hiP (by omega) (by omega)
    -- q is inner, on the walk's last segment's path, its search going to L
    have hqin : nodeAt root P (P.length - 1) ∈ rk :: ext.map (·.2) := by
      have hPl : P.length = sfx.length + ext.length := by rw [hPeq]; simp
      rw [hextc] at hPl
      simp only [List.length_cons] at hPl
      have := nodeAt_append_mem root sfx ext (P.length - 1) (by omega)
        (by rw [List.length_append, hextc]; simp only [List.length_cons]; omega)
      rw [← hPeq, hesfx] at this
      exact this
    obtain ⟨qm0, hqm0, hqml⟩ := lteP_mid_inner _ c.i cv c.p.fuel rk L ext hext _ hqin hqL
    rw [hqR3] at hqm0
    cases hqm0
    have hqlive : ∃ z, (kq, z) ∈ qm.live := ⟨L, by rw [← KNode.liveAt_of_times qm c.i hqtm]; exact hkq⟩
    have hqRw : TReach (wNode c.p base w) c.i root (nodeAt root P (P.length - 1)) :=
      (hPL _ (by omega)).reach
    obtain ⟨ext', hlv⟩ := lteP_redirect (rdN c w3) (rdN c v) c.i cv (nodeAt root P (P.length - 1)) y L qm
      qn' hqR3 hqRv (by rw [hqlf']; exact hqml) (by
        intro fd hfd f' ext'' hr'
        -- the run's step at q goes to L: q is L's parent
        have hmem := KNode.searchLte_mem qm c.i _ fd hfd
        have hfdR : TReach (wNode c.p base w) c.i root fd.y := TReach.link hqRw ⟨qm, hqm, hmem⟩
        obtain ⟨hlf, hle⟩ := lteP_linked (rdN c w3) (wNode c.p base w) c.i root cv hsub3 f' fd.y L ext'' hr' hfdR
        have hPF : PathFromLen (wNode c.p base w) c.i fd.y L ext''.length := by
          rw [← hle, ← nodeAt_last]
          exact (LinkedFrom.pathLen _ _ _ ext'' hlf ext''.length (Nat.le_refl _)).toFrom
        obtain ⟨hkl, hfdq⟩ := nodeAt_of_reach _ _ _ hT P hlinkP fd.y L ext''.length hPF hfdR P.length
          (Nat.le_refl _) hXD.symm
        have hd1 := hPL (P.length - ext''.length) (by omega)
        rw [← hfdq] at hd1
        have hd2 : PathLen (wNode c.p base w) c.i root fd.y (P.length - 1 + 1) :=
          PathLen.link (hPL (P.length - 1) (by omega)) ⟨qm, hqm, hmem⟩
        have := PathLen.depth_unique hT _ _ _ hd1 hd2
        have hk0 : ext''.length = 0 := by omega
        have hfyL : fd.y = L := by
          rw [hfdq, hk0, Nat.sub_zero, hXD]
        have hfc : fd.c = kq := (hT.oneLink _ _ _ _ L hqRw hqRw ⟨qm, hqm, by rw [← hfyL]; exact hmem⟩
          ⟨qm, hqm, hkq⟩).2
        have h1 := hsLte cv
        rw [hfd] at h1
        simp only [Option.map_some, hfc, ↓reduceIte] at h1
        obtain ⟨fd', hfd', hfy'⟩ := Option.map_eq_some_iff.mp h1
        exact ⟨fd', hfd', (Prod.mk.inj hfy').2⟩) ⟨ny, hyRv, hnyl⟩ c.p.fuel rk ext hext hqin hqL (by
        intro z hz hzq hzL
        have hzw : z ∈ w3.path.map (·.2) := by
          rw [hw3p, List.map_append]
          rcases List.mem_cons.mp hz with rfl | hz
          · apply List.mem_append_left
            have := (dsrFold_shape (rdN c w3) c.i c.p.fuel pre root [(none, root)] _ P0 hP0 (by simp)).1
            exact List.mem_of_getLast? this
          · exact List.mem_append_right _ hz
        obtain ⟨i, _, hiP, rfl⟩ := hinW w3.path [] (by simp) _ hzw
        refine hag i hiP (fun he => hzq (by rw [he])) (fun he => hzL (by rw [he, hXD])))
    exact holeAtW_leaf c v pre cv rk y g 0 hs (keyWf_init_long pre cv hkey) ⟨P0, by rw [hvroot]; exact hfv⟩
      ⟨ext', hlv⟩ hgy
  | nil =>
    -- L = rk, a segment root, q the segment leaf above it: the last segment step goes to the copy
    have hPs : P = sfx := by rw [hPeq, hextc]; simp
    have hw3p0 : w3.path = P0 := by rw [hw3p, hextc]; simp
    have hlen0 : P0.length = P.length + 1 := by rw [← hw3p0, hlenW]
    have hfuel : 0 < c.p.fuel := by
      cases hf : c.p.fuel with
      | zero => rw [hf] at hext; simp [lteP] at hext
      | succ _ => omega
    obtain ⟨pre', k', hpre⟩ : ∃ pre' k', pre = pre' ++ [k'] := by
      rcases List.eq_nil_or_concat pre with h0 | ⟨pre', k', h'⟩
      · exfalso
        rw [h0] at hP0
        simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at hP0
        have h1 : ([(none, root)] : List (Option Nat × NodeId)).length = P.length + 1 := by
          rw [hP0.2]; exact hlen0
        simp only [List.length_singleton] at h1
        omega
      · exact ⟨pre', k', by rw [h', List.concat_eq_append]⟩
    rw [hpre, List.foldl_append] at hP0
    simp only [List.foldl_cons, List.foldl_nil] at hP0
    cases hf' : pre'.foldl (dsrStep (rdN c w3) c.i c.p.fuel) (some (root, [(none, root)])) with
    | none => rw [hf'] at hP0; simp [dsrStep] at hP0
    | some acc =>
      rw [hf'] at hP0
      obtain ⟨r', P'⟩ := acc
      obtain ⟨leaf', ext', n', fd, hl', hRl', hfd, hacc⟩ := dsrStep_some _ c.i c.p.fuel r' P' k' _ hP0
      simp only [Prod.mk.injEq] at hacc
      obtain ⟨hrkfd, hP0eq⟩ := hacc
      -- leaf' is q, fd's klong is kq
      have hP'0 := (dsrFold_shape (rdN c w3) c.i c.p.fuel pre' root [(none, root)] r' P' hf' (by simp)).1
      obtain ⟨⟨_, hRl0, hl0⟩, hlast'⟩ := lteP_leaf _ c.i k' c.p.fuel r' leaf' ext' hl'
      have hA := getLast_map_append P' ext' r' leaf' hP'0 hlast'
      have hlenA : (P' ++ ext').length = P.length := by
        rw [hP0eq] at hlen0; simp at hlen0 ⊢; omega
      have hqleaf' : nodeAt root P (P.length - 1) = leaf' := by
        have h1 := hpX (P.length - 1) (by omega)
        rw [hw3p0, hP0eq, List.getElem?_append_left (by rw [hlenA]; omega)] at h1
        have h2 := path_last_map _ _ hA
        rw [hlenA] at h2
        rw [h1] at h2
        exact Option.some.inj h2
      have hfdc : fd.c = kq := by
        have h1 : w3.path[P.length]? = some (some fd.c, fd.y) := by
          rw [hw3p0, hP0eq, List.getElem?_append_right (by omega)]
          simp [hlenA]
        rw [hp3'] at h1
        have h2 : (P[P.length - 1]?) = some (some fd.c, fd.y) := by
          rw [show P.length = P.length - 1 + 1 by omega, List.getElem?_cons_succ] at h1
          exact h1
        rw [hPq] at h2
        exact (Option.some.inj (Prod.mk.inj (Option.some.inj h2)).1).symm
      have hk' : k' = kq := by rw [← hfdc, KNode.searchEq_c n' c.i k' fd hfd]
      subst hk'
      rw [← hqleaf'] at hRl'
      rw [hqR3] at hRl'
      cases hRl'
      have hqml : qm.leaf = true := by
        rw [← hqleaf', hqR3] at hRl0
        cases hRl0
        exact hl0
      -- the descent at v
      have hagi : ∀ z ∈ (P' ++ ext').map (·.2), z ≠ nodeAt root P (P.length - 1) →
          rdN c v z = rdN c w3 z := by
        intro z hz hzq
        obtain ⟨i, hi, hiP, rfl⟩ := hinW (P' ++ ext') [(some fd.c, fd.y)] (by
          rw [hw3p0, hP0eq]) z hz
        exact hag i hiP (fun he => hzq (by rw [he])) (by omega)
      have hfv' : pre'.foldl (dsrStep (rdN c v) c.i c.p.fuel) (some (root, [(none, root)])) = some (r', P') := by
        refine dsrFold_congr (rdN c w3) (rdN c v) c.i c.p.fuel pre' root _ r' P' hf' ?_ ?_
        · intro hne
          obtain ⟨sfx', hsfx', hne'⟩ := dsrFold_prefix _ c.i c.p.fuel pre' root _ r' P' hf'
          have h2 : 2 ≤ P'.length := by
            rw [hsfx']
            cases sfx' with
            | nil => exact absurd rfl (hne' hne)
            | cons _ _ => simp
          have h0 := hag 0 (by omega) (by simp at hlenA; omega) (by omega)
          simpa [nodeAt] using h0
        · intro z hz
          have hPne : P' ≠ [] := by intro h0; rw [h0] at hP'0; simp at hP'0
          obtain ⟨i', hi', hiz'⟩ := mem_prefix_index P'.dropLast ([P'.getLast hPne] ++ ext' ++ [(some fd.c, fd.y)])
            w3.path (by
              rw [hw3p0, hP0eq]
              conv => lhs; rw [← List.dropLast_concat_getLast hPne]
              simp) _ hz
          rw [List.length_dropLast] at hi'
          have hle : P'.length ≤ P.length := by rw [← hlenA]; simp
          have h2 := hpX i' (by omega)
          rw [hiz'] at h2
          rw [Option.some.inj h2]
          exact hag i' (by omega) (by omega) (by omega)
      have hlv' : lteP (rdN c v) c.i k' c.p.fuel r' = some (nodeAt root P (P.length - 1), ext') := by
        rw [hqleaf']
        refine lteP_congr_end (rdN c w3) (rdN c v) c.i k' c.p.fuel r' leaf' ext' hl' ?_
          ⟨_, by rw [← hqleaf']; exact hqRv, by rw [hqlf']; exact hqml⟩
        intro z hz hzl
        apply hagi z _ (by rw [hqleaf']; exact hzl)
        rcases List.mem_cons.mp hz with rfl | hz
        · rw [List.map_append]
          exact List.mem_append_left _ (List.mem_of_getLast? hP'0)
        · rw [List.map_append]; exact List.mem_append_right _ hz
      have hse := hsEq k'
      simp only [beq_self_eq_true, ↓reduceIte] at hse
      obtain ⟨fd'', hfd'', hfy''⟩ := Option.map_eq_some_iff.mp hse
      have hfv : (pre' ++ [k']).foldl (dsrStep (rdN c v) c.i c.p.fuel) (some (root, [(none, root)])) =
          some (y, P' ++ ext' ++ [(some fd''.c, fd''.y)]) := by
        rw [List.foldl_append, hfv']
        simp only [List.foldl_cons, List.foldl_nil, dsrStep, hlv', hqRv, hfd'', hfy'']
      have hlte : lteP (rdN c v) c.i cv c.p.fuel y = some (y, []) := by
        obtain ⟨f, hf⟩ : ∃ f, c.p.fuel = f + 1 := ⟨c.p.fuel - 1, by omega⟩
        rw [hf]
        simp [lteP, hyRv, hnyl]
      rw [hpre]
      exact holeAtW_leaf c v (pre' ++ [k']) cv y y g 0 hs
        (fun x hx => keyWf_init_long _ cv (by rw [← hpre]; exact hkey) x hx)
        ⟨_, by rw [hvroot]; exact hfv⟩ ⟨[], hlte⟩ hgy

/-- `writerWP_handleFullWith_timeInPlace_term` with the heights' cache kept. -/
theorem writerWP_handleFullWith_timeInPlace_termGh (up : NodeId → List (Nat × NodeId) → M Unit)
    (d' : Nat) (x q : NodeId) (n qn : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hpq : (w.path[d']?).map (·.2) = some q) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up (d' + 1) x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        w'.path = w.path ∧ w'.nodes = upsert w.nodes x ⟨n.leaf, l.ks⟩ ∧ w'.gh = w.gh) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases compact with
    | true =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst hw3
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    | false =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst hw3
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial


/-- A node with a key klong k1 of n redirected to y (its live klongs n's but k1's
naming y): `liveAt` of it, and its count. -/
theorem liveAt_redirect_facts (n m : KNode) (t : Time) (k1 : Nat) (y : NodeId)
    (htn : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (htm : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (hlk : ∀ c', m.live.lookup c' = if k1 == c' then some y else n.live.lookup c') :
    (∀ c z, (c, z) ∈ m.liveAt t → (c = k1 ∧ z = y) ∨ ((c, z) ∈ n.liveAt t ∧ c ≠ k1)) ∧
      (n.liveAt t).length ≤ (m.liveAt t).length := by
  rw [KNode.liveAt_of_times n t htn]
  rw [KNode.liveAt_of_times m t htm]
  refine ⟨fun c z h => ?_, ?_⟩
  · have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup m) c z h
    rw [hlk c] at hl
    by_cases hc : k1 = c
    · subst hc; simp at hl; exact Or.inl ⟨rfl, hl.symm⟩
    · have hb : (k1 == c) = false := by simpa using hc
      rw [hb] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      exact Or.inr ⟨bk_mem_of_lookup _ c z hl, Ne.symm hc⟩
  · have h1 := liveAt_length_le n m t
    rw [KNode.liveAt_of_times n t htn, KNode.liveAt_of_times m t htm] at h1
    apply h1
    intro c z hz
    by_cases hc : k1 = c
    · subst hc
      refine ⟨y, bk_mem_of_lookup _ _ _ ?_⟩
      rw [hlk]; simp
    · have hb : (k1 == c) = false := by simpa using hc
      refine ⟨z, bk_mem_of_lookup _ _ _ ?_⟩
      rw [hlk, hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z hz

set_option maxHeartbeats 8000000 in
/-- The leaf x not made by the transaction, full, split in time below a parent q
that the transaction made, full or compacting with the copy's klong, whose own
split is in time, in place (q's last version within a split's bound): q's node
becomes its last version with its klong of x naming the copy y. From the live
counts but at x in the tree with x's node its last version, they hold but at y;
q's new node redirects k1 to y and holds nothing else new. -/
theorem writerWP_handleFull_timeMadeParent_liveGh (d'' : Nat) (x q q0 : NodeId) (n qn qq : KNode)
    (k1 : Nat) (last : KNode) (compact : Bool) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup x = some n)
    (hlq : w.nodes.lookup q = some qn) (hqt : w.taken.contains q = false) (hqx : q ≠ x)
    (hxn : x < w.next) (hqn : q < w.next)
    (hlq0 : w.nodes.lookup q0 = some qq) (hq0n : q0 < w.next)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq0 : (w.path[d'']?).map (·.2) = some q0)
    (hpq : (w.path[d'' + 1]?).map (·.2) = some q) (hpk : w.path[d'' + 1 + 1]? = some (some k1, x))
    (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqmade : qn.firstTime = some c.i) (hqsz : (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hfullq : ¬ (qn.size + 2 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hk : (k1, x) ∈ qn.liveAt c.i)
    (hT : TreeOK (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey)
    (hqR : TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey q)
    (hnx : wNode c.p base w w.next = none) (hnl : w.nodes.lookup w.next = none)
    (hnt : w.taken.contains w.next = false)
    (hfreshT : ∀ u c', TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey u →
      ¬ TLink (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i u c' w.next)
    (hV : LiveEdgesH c.p (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey
      (fun z => z = x)) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) x [] last
      compact) c w
      (fun _ w' => LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun z => z = w.next) ∧
        (∀ z, z ≠ q → z ≠ x → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) ∧
        w'.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧
        (∃ l : KNode, klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
          (∀ c', l.live.lookup c' = if k1 == c' then some w.next else qn.live.lookup c') ∧
          w'.nodes.lookup q = some ⟨qn.leaf, l.ks⟩) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.gh.lookup w.next = w.gh.lookup x) := by
  have hqy : q ≠ w.next := by omega
  have hxy : x ≠ w.next := by omega
  have hq0y : q0 ≠ w.next := by omega
  refine writerWP_handleFullWith_time_up_last_gh (d'' + 1) x q n qn k1 last compact c w hlk hlq hfirst hcs
    hpq hpk _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1path h1next
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hqy]; exact hlq
  have hlq01 : w1.nodes.lookup q0 = some qq := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hq0y]; exact hlq0
  have hpq01 : (w1.path[d'']?).map (·.2) = some q0 := by rw [h1path]; exact hpq0
  -- q's split: in time, in place, either flag
  have hqsplit : ∀ compact' : Bool, WriterWP (handleFullWith (fun q more => appendKlongs d'' q more)
      (d'' + 1) q [(k1, w.next)] (qn.lastVersion c.i) compact') c w1 (fun _ w2 =>
      WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 =>
        LiveEdgesH c.p (wNode c.p base w3) c.i w3.top.rootKey (fun z => z = w.next) ∧
        (∀ z, z ≠ q → z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z) ∧
        w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧
        (∃ l : KNode, klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
          (∀ c', l.live.lookup c' = if k1 == c' then some w.next else qn.live.lookup c') ∧
          w3.nodes.lookup q = some ⟨qn.leaf, l.ks⟩) ∧
        w3.taken = w.taken ∧ w3.top = w.top ∧ w3.gh.lookup w.next = w.gh.lookup x)) := by
    intro compact'
    have hcs' : (!compact' && decide ((qn.lastVersion c.i).size > c.p.splitAbove)) = false := by
      have : ¬ ((qn.lastVersion c.i).size > c.p.splitAbove) := by omega
      simp [this]
    refine writerWP_mono (writerWP_handleFullWith_timeInPlace_termGh _ d'' q q0 qn qq [(k1, w.next)] compact' c
      w1 hlq1 hlq01 hpq01 hqmade hcs') ?_
    rintro _ w2 ⟨l, hl_leaf, hl_wf, hl_times, hl_look, h2t, h2top, _, _, _, h2n, h2gh⟩
    have hlx2 : w2.nodes.lookup x = some n := by
      rw [h2n, lookup_upsert, if_neg (Ne.symm hqx), h1n, lookup_append_single_ne _ _ _ _ hxy]; exact hlk
    rw [writerWP_bind, writerWP_getNode_known x n c w2 hlx2]
    simp only [putNode, writerWP_modify]
    have hlk' : ∀ c', l.live.lookup c' = if k1 == c' then some w.next else qn.live.lookup c' := by
      intro c'
      rw [hl_look c']
      simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]
    have key : ∀ w3 : W, w3.nodes = upsert w2.nodes x (n.toPrev (c.i - 1)) → w3.taken = w2.taken →
        w3.top = w2.top → w3.gh = w2.gh →
        LiveEdgesH c.p (wNode c.p base w3) c.i w3.top.rootKey (fun z => z = w.next) ∧
        (∀ z, z ≠ q → z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z) ∧
        w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧
        (∃ l : KNode, klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
          (∀ c', l.live.lookup c' = if k1 == c' then some w.next else qn.live.lookup c') ∧
          w3.nodes.lookup q = some ⟨qn.leaf, l.ks⟩) ∧
        w3.taken = w.taken ∧ w3.top = w.top ∧ w3.gh.lookup w.next = w.gh.lookup x := by
      intro w3 h3n h3t0 h3top0 h3gh
      have h3t : w3.taken = w.taken := by rw [h3t0, h2t, h1t]
      have h3top : w3.top = w.top := by rw [h3top0, h2top, h1top]
      have hlook : ∀ z, z ≠ q → z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z := by
        intro z hzq hzx hzy
        rw [h3n, lookup_upsert, if_neg hzx, h2n, lookup_upsert, if_neg hzq, h1n,
          lookup_append_single_ne _ _ _ _ hzy]
      have hly : w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ := by
        rw [h3n, lookup_upsert, if_neg (Ne.symm hxy), h2n, lookup_upsert, if_neg (Ne.symm hqy), h1n,
          lookup_append_single_self]
        exact hnl
      have hlq3 : w3.nodes.lookup q = some ⟨qn.leaf, l.ks⟩ := by
        rw [h3n, lookup_upsert, if_neg hqx, h2n, lookup_upsert]; simp
      have hVq : updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩ q = some qn := by
        rw [updN_ne _ _ _ _ hqx]; simp only [wNode, hqt, Bool.false_eq_true, ↓reduceIte, hlq]
      have hq3t : w3.taken.contains q = false := by rw [h3t]; exact hqt
      have hy3t : w3.taken.contains w.next = false := by rw [h3t]; exact hnt
      have hN'y : wNode c.p base w3 w.next = some ⟨n.leaf, last.ks⟩ := by
        simp only [wNode, hy3t, Bool.false_eq_true, ↓reduceIte, hly]
      have hN'q : wNode c.p base w3 q = some ⟨qn.leaf, l.ks⟩ := by
        simp only [wNode, hq3t, Bool.false_eq_true, ↓reduceIte, hlq3]
      have hN' : ∀ z, z ≠ q → z ≠ x → z ≠ w.next →
          wNode c.p base w3 z = updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩ z := by
        intro z hzq hzx hzy
        rw [updN_ne _ _ _ _ hzx]
        simp only [wNode, h3t, hlook z hzq hzx hzy]
      have hlkm : ∀ c', (⟨qn.leaf, l.ks⟩ : KNode).live.lookup c' =
          if k1 == c' then some w.next else qn.live.lookup c' := by
        intro c'; rw [upf_live_ks (⟨qn.leaf, l.ks⟩ : KNode) l rfl]; exact hlk' c'
      obtain ⟨hq', hq'len⟩ := liveAt_redirect_facts qn ⟨qn.leaf, l.ks⟩ c.i k1 w.next hqtm hl_times hlkm
      have hgh3 : w3.gh = (w.next, gh.1, gh.2) :: w.gh := by
        rw [h3gh]
        rw [h2gh, h1gh]
      refine ⟨?_, hlook, hly, ⟨l, hl_wf, hl_times, hlk', hlq3⟩, h3t, h3top, by rw [hgh3, hgh]; simp⟩
      rw [h3top]
      exact liveEdgesH_redirect c.p _ (wNode c.p base w3) c.i w.top.rootKey q x w.next qn
        ⟨qn.leaf, l.ks⟩ ⟨n.leaf, last.ks⟩ k1 hT hV hqR hVq hk (updN_self _ _ _)
        (by rw [updN_ne _ _ _ _ (Ne.symm hxy)]; exact hnx) hfreshT hN'y hN'q rfl hq' hq'len hN'
    exact key _ rfl rfl rfl rfl
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w1 hlq1]
  apply writerWP_if
  · intro _
    refine writerWP_mono (hqsplit false) ?_
    intro _ w2 h
    simp only [writerWP_bind] at h
    exact h
  · intro hroom
    apply writerWP_if
    · intro _
      refine writerWP_mono (hqsplit true) ?_
      intro _ w2 h
      simp only [writerWP_bind] at h
      exact h
    · intro hdead
      exfalso; apply hfullq
      refine ⟨by simp at hroom; omega, ?_⟩
      simpa using hdead

/-! ## The case: the full leaf split in time below a made parent split in time in place -/

/-- A full leaf as in `DelFullTimeGM`, not made by the transaction, below the space
root, whose parent, not the space root, the transaction made, is full or compacting
with the copy's klong, and splits in time (its last version within a split's
bound): its split is in place, the copy stays below it. -/
def DelFullTimeMadeParentM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelFullTimeGM c base w op ∧ ∀ pre cv L n, op = .del (pre ++ [cv]) → KeyLeaf c base w pre cv L n →
    n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey ∧
    ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → q ≠ w.top.rootKey ∧ qn.firstTime = some c.i ∧
        (qn.lastVersion c.i).size ≤ c.p.splitAbove ∧
        ¬ (qn.size + 2 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false)

set_option maxHeartbeats 6400000 in
/-- (Below a made parent split in time in place.) The full leaf not made by the transaction, split in time below a parent with
room (bergdb 030-01, step 5): the delete calls `afterDelete` at the leaf's pair
(g, 0) from a state with `DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`,
the copy the hole (l4a's `writerWP_handleFull_timeRoom_liveGh`, `holeAtW_copy`). -/
theorem liveDel_fullTimeMadeParent (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeMadeParentM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0, hsz0⟩, hcase⟩ := hPc
  obtain ⟨hnm0, hnr0, hpar0⟩ := hcase pre cv L0 n0 hop' hK
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hSB : tx.base ≤ w.next := hS.1.1.1.2
  have hLC0 : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.2.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, hbw, hiw, hwfw0⟩ := hS.2.1
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (fun v => KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base v ∧
      HtJ0 (ctxOf p ts) (htOracleOf p (treeRun p ts)) tx.base v)
    (fun s f x v hJ hx => writerWP_and (kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ.1 hx)
      (htJ0_descendLte hvo hkw s f x v hJ.2 hx))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨kdJ_pathAdd _ _ tx.base top hB _ tx.base hv fd.c fd.y L n v hJ.1 hL hlk
        (kd_searchEq_mem n _ s fd hfd), htJ0_pathAdd hvo s fd L n v hJ.2 hL hlk hleaf hfd⟩)
    ⟨kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0, htJ0_start hvo w hbw hiw hwfw0⟩
    hrk (hI.pathUntaken _) hI.wf _ hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3h hlk3 hp3' hlinkP hXD hlkX
  have hJ3 := hJ3h.1
  have hH3 := hJ3h.2
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hH3.book hlk3
  obtain ⟨hne, hkeep, hfull, hsz, hnm, hnr, hpar⟩ := keyLeaf_all2 hK hrk
    (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m ∧
      ((m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ≤
        (ctxOf p ts).p.splitAbove ∨ ((∃ old, m.ks.getLast? = some (.del old)) ∧
        m.lastTime = some (ctxOf p ts).i) ∨ m.size + 1 < (ctxOf p ts).p.M) ∧
      m.firstTime ≠ some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
      ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i w.top.rootKey q →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L') ∈ qn.liveAt (ctxOf p ts).i → q ≠ w.top.rootKey ∧ qn.firstTime = some (ctxOf p ts).i ∧
          (qn.lastVersion (ctxOf p ts).i).size ≤ (ctxOf p ts).p.splitAbove ∧
          ¬ (qn.size + 2 ≤ (ctxOf p ts).p.M ∧
            deadOver (ctxOf p ts).p (qn.add (ctxOf p ts).i (.key k1 w.next)) = false))
    ⟨hne0, hkeep0, hfull0, hsz0, hnm0, hnr0, hpar0⟩ L n hL hn hnl
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have h3t : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
  obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
  have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
  have hJ3' : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJ hr03
  have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
    (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
    (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
    (by rw [hr03.1, hr03.2.1]; exact hRO) hJ3' (by rw [hr03.2.2.2.2]; exact hSB) hsa2
    P.length _ _ _ hPOK cv n (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
    hnl hne hfull (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
  simp only [hXD] at hJ2
  -- the path: L below its parent q
  have hPpos : 0 < P.length := by
    cases hPe : P with
    | nil => rw [hPe] at hXD; simp [nodeAt] at hXD; exact absurd hXD.symm hnr
    | cons _ _ => simp
  obtain ⟨d', hd'⟩ : ∃ d', P.length = d' + 1 := ⟨P.length - 1, by omega⟩
  obtain ⟨kq, qm, hPq, hqm, hkq⟩ := LinkedFrom.get _ _ _ P hlinkP d' (by omega)
  rw [← hd', hXD] at hPq hkq
  have hqR : TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey (nodeAt w.top.rootKey P d') :=
    (LinkedFrom.pathLen _ _ _ P hlinkP d' (by omega)).reach
  obtain ⟨hqroot, hqmade, hqsz, hqfull⟩ := hpar _ qm kq hqR hqm hkq
  have hI3 := putInv_of_readsAs _ _ w w3 hI hr03
  generalize hlast : n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
  have hlastl : last.leaf = n.leaf := by rw [← hlast]; rfl
  have hlastN : (⟨n.leaf, last.ks⟩ : KNode) = last := by rw [← hlastl]
  have hlive' : ∀ c', last.live.lookup c' = if c' == cv then none else n.live.lookup c' := by
    intro c'; rw [← hlast]; exact KNode.delete_live_lookup n _ cv c'
  have htl : ∀ s, Klong.time s ∈ last.ks → s ≤ (ctxOf p ts).i := by
    intro s hs
    rw [← hlast] at hs
    simp only [KNode.lastVersionGivenDel, List.mem_cons, List.mem_map] at hs
    rcases hs with he | ⟨_, _, he⟩
    · cases he; exact Nat.le_refl _
    · cases he
  have hwfl : klongsWf last.ks = true := by rw [← hlast]; exact KNode.lastVersionGivenDel_wf _ _ _
  have htn := hI.times L n hn
  obtain ⟨hsubl, _⟩ := live_shrink n last cv hlive'
  have hsub : ∀ q ∈ last.liveAt (ts.length + 1), q ∈ n.liveAt (ts.length + 1) := by
    rw [KNode.liveAt_of_times n (ts.length + 1) htn, KNode.liveAt_of_times last (ts.length + 1) htl]; exact hsubl
  have hposl : last.liveAt (ts.length + 1) ≠ [] := by
    rw [KNode.liveAt_of_times last (ts.length + 1) htl]; exact live_ne_of_keep n last cv hkeep hlive'
  -- names
  generalize hqdef : nodeAt w.top.rootKey P d' = q at hqm hkq hqR hqroot hPq
  obtain ⟨d'', hd''⟩ : ∃ d'', d' = d'' + 1 := by
    cases hd0 : d' with
    | zero =>
      exfalso; apply hqroot
      rw [← hqdef, hd0]; simp [nodeAt]
    | succ e => exact ⟨e, rfl⟩
  obtain ⟨kq0, qq0, _, hqq0, _⟩ := LinkedFrom.get _ _ _ P hlinkP d'' (by omega)
  have hlq0 : w3.nodes.lookup (nodeAt w.top.rootKey P d'') = some qq0 := by
    have := hlkX d'' (by omega)
    rw [hqq0] at this
    exact this
  have hqL : q ≠ L := by
    intro he
    rw [← hqdef, ← hXD] at he
    have := PathLen.depth_unique hI.tree _ _ _ (LinkedFrom.pathLen _ _ _ P hlinkP d' (by omega))
      (by rw [he]; exact LinkedFrom.pathLen _ _ _ P hlinkP P.length (Nat.le_refl _))
    omega
  have hqt : w.taken.contains q = false := hI.untaken q (tReach_reachS _ _ _ _ hqR)
  have hlq3 : w3.nodes.lookup q = some qm := by
    have := hlkX d' (by omega)
    rw [hqdef, hqm] at this
    exact this
  have hnx3 : w3.nodes.lookup w3.next = none := by
    cases h' : w3.nodes.lookup w3.next with
    | none => rfl
    | some m => have := hI3.ids.1 w3.next (by rw [h']; rfl); omega
  have hnt3 : w3.taken.contains w3.next = false := by
    cases h' : w3.taken.contains w3.next with
    | false => rfl
    | true => have := hI3.ids.2.2.1 w3.next h'; omega
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hNw3 : wNode p (viewOf (treeRun p ts)) w3 = wNode p (viewOf (treeRun p ts)) w := hr03.1
  -- the split's live part
  have hlive : WriterWP (appendDeleteKlong L P.length cv) (ctxOf p ts) w3 (fun _ v =>
      LiveEdgesH p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey (fun z => z = w3.next) ∧
      (∀ z, z ≠ q → z ≠ L → z ≠ w3.next → v.nodes.lookup z = w3.nodes.lookup z) ∧
      v.nodes.lookup w3.next = some last ∧
      (∃ l : KNode, klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ (ctxOf p ts).i) ∧
        (∀ c', l.live.lookup c' = if kq == c' then some w3.next else qm.live.lookup c') ∧
        v.nodes.lookup q = some ⟨qm.leaf, l.ks⟩) ∧
      v.taken = w3.taken ∧ v.top = w3.top ∧ v.gh.lookup w3.next = w3.gh.lookup L) := by
    refine writerWP_appendDeleteKlong_full_ofP L P.length cv n _ w3 hlk3 hne hfull _ ?_
    intro compact s hpath
    generalize hw4 : ({ w3 with trail := s :: w3.trail } : W) = w4
    have h4n : w4.nodes = w3.nodes := by rw [← hw4]
    have h4t : w4.taken = w3.taken := by rw [← hw4]
    have h4top : w4.top = w3.top := by rw [← hw4]
    have h4next : w4.next = w3.next := by rw [← hw4]
    have h4path : w4.path = w3.path := by rw [← hw4]
    have h4gh : w4.gh = w3.gh := by rw [← hw4]
    have hN4 : wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4 = wNode p (viewOf (treeRun p ts)) w := by
      rw [← hNw3]; unfold wNode; rw [h4n, h4t]; rfl
    have hroot4 : w4.top.rootKey = w.top.rootKey := by rw [h4top, hr03.2.1]
    have hcs : (!compact && decide (last.size > (ctxOf p ts).p.splitAbove)) = false := by
      rw [← hlast]; exact compact_time_of_path n (ctxOf p ts) cv compact hsz hpath
    rw [hlast]
    unfold handleFull
    rw [hd', hd'']
    have hn' : wNode p (viewOf (treeRun p ts)) w L = some n := hn
    have hTu : TreeOK (updN (wNode p (viewOf (treeRun p ts)) w) L n) (ts.length + 1) w.top.rootKey := by
      rw [updN_self_eq _ _ _ hn']; exact hI.tree
    obtain ⟨hTl, hRl⟩ := treeOK_updN_sub _ _ _ L n ⟨n.leaf, last.ks⟩ hTu
      (by rw [hlastN]; exact fun c z h => hsub (c, z) h)
    rw [updN_self_eq _ _ _ hn'] at hRl
    refine writerWP_mono (writerWP_handleFull_timeMadeParent_liveGh d'' L q (nodeAt w.top.rootKey P d'')
      n qm qq0 kq last compact (ctxOf p ts) (viewOf (treeRun p ts)) w4
      (by rw [h4n]; exact hlk3) (by rw [h4n]; exact hlq3)
      (by rw [h4t, hr03.2.2.1]; exact hqt) hqL
      (by rw [h4next]; exact hI3.ids.1 L (by rw [hlk3]; rfl))
      (by rw [h4next]; exact hI3.ids.1 q (by rw [hlq3]; rfl))
      (by rw [h4n]; exact hlq0) (by rw [h4next]; exact hI3.ids.1 _ (by rw [hlq0]; rfl)) hnm hcs
      (by
        rw [h4path, hp3']
        simp only [nodeAt]
        cases d'' with
        | zero => simp
        | succ e =>
          rw [List.getElem?_cons_succ]
          have hl : e < (P.map (·.2)).length := by simp; omega
          rw [← List.getElem?_map, List.getElem?_eq_getElem (by simp; omega)]
          simp [List.getElem?_eq_getElem hl])
      (by
        rw [← hd'']
        rw [h4path, hp3']
        rw [← hqdef]
        simp only [nodeAt]
        cases d' with
        | zero => simp
        | succ e =>
          rw [List.getElem?_cons_succ]
          have hl : e < (P.map (·.2)).length := by simp; omega
          rw [← List.getElem?_map, List.getElem?_eq_getElem (by simp; omega)]
          simp [List.getElem?_eq_getElem hl])
      (by rw [← hd'']; rw [h4path, hp3', List.getElem?_cons_succ]; exact hPq)
      (hI.times q qm hqm) hqmade hqsz (by rw [h4next, hnext3]; exact hqfull) hkq
      (by rw [hN4, hroot4]; exact hTl)
      (by
        rw [hN4, hroot4, ← hXD, ← hqdef]
        exact reach_path_updN_end _ _ _ P hlinkP hI.tree _ d' (by omega))
      (by
        simp only [wNode, h4t, hnt3, h4n, h4next, hnx3, Bool.false_eq_true, ↓reduceIte]
        exact (hI3.fresh w3.next (Nat.le_refl _)).1)
      (by rw [h4n, h4next]; exact hnx3) (by rw [h4t, h4next]; exact hnt3)
      (by
        rw [hN4, hroot4, h4next]
        intro u c' hu hl
        obtain ⟨mm, hmm, hcm⟩ := hl
        have huN := hRl u hu
        have hcm' : (c', w3.next) ∈ (Option.getD (wNode p (viewOf (treeRun p ts)) w u) n).liveAt (ts.length + 1) ∧
            wNode p (viewOf (treeRun p ts)) w u = some ((wNode p (viewOf (treeRun p ts)) w u).getD n) := by
          by_cases huL : u = L
          · rw [huL, updN_self] at hmm
            cases hmm
            rw [huL, hn']
            refine ⟨hsub _ (by rw [← hlastN]; exact hcm), rfl⟩
          · rw [updN_ne _ _ _ _ huL] at hmm
            rw [hmm]
            exact ⟨hcm, rfl⟩
        have := hI.links u _ c' w3.next (tReach_reachS _ _ _ _ huN) hcm'.2 hcm'.1
        rw [hnext3] at this
        omega)
      (by
        rw [hN4, hroot4]
        rw [hlastN]
        exact liveEdgesH_leaf_shrink p _ _ _ L n last (edges_of_liveCounts p _ _ _ hLC0) hn hnl
          (by rw [hlastl]; exact hnl) hsub hposl)) ?_
    rintro _ v ⟨hE, hfr, hny, hqv, hvt, hvtop, hgh⟩
    rw [h4next] at hE hfr hny hqv hgh
    refine ⟨hE, fun z h1 h2 h3 => by rw [hfr z h1 h2 h3, h4n], by rw [hny, hlastN], hqv,
      by rw [hvt, h4t], by rw [hvtop, h4top], by rw [hgh, h4gh]⟩
  refine writerWP_deleteUpward_gh (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v ∧
      PutBook (ctxOf p ts) tx.base top v ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v ∧
      LiveEdgesH p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey (fun z => z = w3.next) ∧
      (∀ z, z ≠ q → z ≠ L → z ≠ w3.next → v.nodes.lookup z = w3.nodes.lookup z) ∧
      v.nodes.lookup w3.next = some last ∧
      (∃ l : KNode, klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ (ctxOf p ts).i) ∧
        (∀ c', l.live.lookup c' = if kq == c' then some w3.next else qm.live.lookup c') ∧
        v.nodes.lookup q = some ⟨qm.leaf, l.ks⟩) ∧
      v.taken = w3.taken ∧ v.top = w3.top ∧ v.gh.lookup w3.next = w3.gh.lookup L)
    _ ?_ ?_
  · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
        _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO
        hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (ht_appendDeleteKlong tx.base L P.length cv _ w3 hvo hpos hH3.book hH3.inv g0 h0 hm0 a hpx
        (hH3.free.mono (by rw [hp3']; simp)))) hlive) ?_
    rintro _ v ⟨⟨⟨⟨hDT, hJv⟩, hpbv⟩, ⟨_, hhiv, _, _⟩⟩, hE, hfr, hny, hqv, hvt, hvtop, hgh⟩
    exact ⟨⟨hDT, hJv⟩, hpbv, hhiv, hE, hfr, hny, hqv, hvt, hvtop, hgh⟩
  · intro g h v hgh ⟨hD, hpbv, hhiv, hE, hfr, hny, hqv, hvt, hvtop, hghn⟩
    have hh0 : h = 0 := kd_h0 hH3.book hlk3 (bk_mem_of_lookup _ _ _ hgh) hnl
    subst hh0
    apply hA g v hD hpbv hhiv
    refine liveHoleW_of_hole (pre ++ [cv]) g 0 (ctxOf p ts) _ v w3.next hE ?_
    have hbv : Book tx.base (ctxOf p ts) v := hD.1.2.2.2.2.2.1
    have hkv : KdInv (kindOracleOf p (treeRun p ts)) tx.base v := hD.1.2.2.2.2.2.2
    have hs := segRd_of _ tx.base (ctxOf p ts) v hbv hkv hk
    have hgy : rdG (ctxOf p ts) v w3.next = some (g, 0) := by
      rw [rdG_of_lookup _ v _ last hny, hghn]; exact hgh
    obtain ⟨l, hlwf, hltm, hlkl, hqvl⟩ := hqv
    have e1 : P.length - 1 = d' := by omega
    have hqm' : wNode p (viewOf (treeRun p ts)) w q = some qm := hqm
    have hqg : (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P (P.length - 1))).getD n =
        qm := by
      show (wNode p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P (P.length - 1))).getD n = qm
      rw [e1, hqdef, hqm']; rfl
    have e2 : ((P[P.length - 1]?).bind (·.1)).getD 0 = kq := by rw [e1, hPq]; rfl
    have hqv' : v.nodes.lookup (nodeAt w.top.rootKey P (P.length - 1)) = some ⟨qm.leaf, l.ks⟩ := by
      rw [e1, hqdef]; exact hqvl
    have hlkm : ∀ c', (⟨qm.leaf, l.ks⟩ : KNode).live.lookup c' =
        if kq == c' then some w3.next else qm.live.lookup c' := by
      intro c'; rw [upf_live_ks (⟨qm.leaf, l.ks⟩ : KNode) l rfl]; exact hlkl c'
    have hqtm' := hI.times q qm hqm
    have hqwf' := hI.wf q qm hqm
    exact holeAtW_copyG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w w3 v pre cv rk L n P w3.next g last
      hI.tree (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.wf hI.times hrk hL hn hnl hr03 hp3'
      hlinkP hXD hlkX hkey hPpos ⟨qm.leaf, l.ks⟩ hqv' (by rw [hqg])
      (by
        rw [hqg, e2]
        intro cc
        exact KNode.searchLte_redirect qm _ (ctxOf p ts).i kq w3.next hqtm' hltm
          ⟨L, by rw [← KNode.liveAt_of_times qm _ hqtm']; exact hkq⟩ hlkm cc)
      (by
        rw [hqg, e2]
        intro cc
        rw [KNode.searchEq_live (⟨qm.leaf, l.ks⟩ : KNode) _ hlwf hltm, KNode.searchEq_live qm _ hqwf' hqtm', hlkm])
      hny (by rw [hlastl]; exact hnl) hnx3
      (fun z h1 h2 h3 => hfr z (by
        intro he; apply h1; rw [he, ← hqdef]; congr 1; omega) h2 h3) (hvtop.trans rfl) hs hgy

/-- (Below a made parent split in time in place.) The full leaf not made by the transaction, split in time below a parent with
room, keeps the live counts (bergdb 030-01, steps 5, 3 and 4), with the merges'
loop and root collapse from the hole, given its live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullTimeMadeParent_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hML : ∀ ts (tx : Tx), MergeLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts)))
    (hCL : ∀ ts (tx : Tx), CollapseLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeMadeParentM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc
  have hm : (ctxOf p ts).p.merges = true := by
    obtain ⟨⟨_, _, _, _, _, hm, _⟩, _⟩ := hPc
    exact hm
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (op :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  refine liveDel_fullTimeMadeParent p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ
    key hop hPc _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

/-! ## What is left of R4, and the successor top theorem -/

/-- A property of the key's leaf holds of every leaf a `KeyLeaf` of the same
delete names. -/
theorem keyLeaf_transfer {c : Ctx} {base : View BVal} {w : W} {pre : List Nat} {cv : Nat}
    {L : NodeId} {n : KNode} (hK : KeyLeaf c base w pre cv L n) (P : NodeId → KNode → Prop)
    (hP : P L n) (op : Op) (hop : op = .del (pre ++ [cv])) :
    ∀ pre' cv' L' n', op = .del (pre' ++ [cv']) → KeyLeaf c base w pre' cv' L' n' → P L' n' := by
  intro pre' cv' L' n' hop' hK'
  rw [hop] at hop'
  injection hop' with hk
  obtain ⟨h1, h2⟩ := List.append_inj hk (by simpa using congrArg List.length hk)
  have h3 : cv = cv' := by simpa using h2
  subst h1 h3
  obtain ⟨_, hrk', hL', hn', hnl'⟩ := hK'
  exact keyLeaf_all2 hK hrk' P hP L' n' hL' hn' hnl'

/-- What is left of R4 after the made parent split in time in place: the copy a
hole whose parent is the space root, or not made by the transaction, or splits in
space. -/
def DelFullTimeHole2M (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelFullTimeHoleM c base w op ∧ ∀ pre cv L n, op = .del (pre ++ [cv]) → KeyLeaf c base w pre cv L n →
    ¬ ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → q ≠ w.top.rootKey ∧ qn.firstTime = some c.i ∧
        (qn.lastVersion c.i).size ≤ c.p.splitAbove

/-- R4's hole case from its rest: the made parent split in time in place is proved
(`liveDel_fullTimeMadeParent`). -/
theorem delCaseLive_hole_of_hole2 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (h : DelCaseLive p R DelFullTimeHole2M) : DelCaseLive p R DelFullTimeHoleM := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨⟨⟨pre0, cv, L, n, hop', hm, hK, hne, hkeep, hfull, hTP⟩, hcase⟩, hhole⟩ := hPc
  have hT := hS.1.1.1.1.1.tree
  obtain ⟨hnm, hnr, hnoroom⟩ := hcase pre0 cv L n hop' hK
  by_cases hmp : ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
      w.top.rootKey q → wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
      (k1, L) ∈ qn.liveAt (ctxOf p ts).i → q ≠ w.top.rootKey ∧ qn.firstTime = some (ctxOf p ts).i ∧
        (qn.lastVersion (ctxOf p ts).i).size ≤ (ctxOf p ts).p.splitAbove
  · have hpar : ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
        w.top.rootKey q → wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L) ∈ qn.liveAt (ctxOf p ts).i → q ≠ w.top.rootKey ∧ qn.firstTime = some (ctxOf p ts).i ∧
          (qn.lastVersion (ctxOf p ts).i).size ≤ (ctxOf p ts).p.splitAbove ∧
          ¬ (qn.size + 2 ≤ (ctxOf p ts).p.M ∧
            deadOver (ctxOf p ts).p (qn.add (ctxOf p ts).i (.key k1 w.next)) = false) := by
      intro q qn k1 hq hqn hk
      obtain ⟨h1, h2, h3⟩ := hmp q qn k1 hq hqn hk
      refine ⟨h1, h2, h3, fun hroom => hnoroom ?_⟩
      intro q' qn' k1' hq' hqn' hk'
      obtain ⟨he, hc⟩ := hT.oneLink q k1 q' k1' L hq hq' ⟨qn, hqn, hk⟩ ⟨qn', hqn', hk'⟩
      subst he hc
      rw [hqn] at hqn'
      simp only [Option.some.injEq] at hqn'
      subst hqn'
      exact hroom
    exact liveDel_fullTimeMadeParent p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w
      hpre hS hJ key hop ⟨⟨pre0, cv, L, n, hop', hm, hK, hne, hkeep, hfull, hTP⟩,
        keyLeaf_transfer hK (fun L' m => m.firstTime ≠ some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
          ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
            w.top.rootKey q → wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
            (k1, L') ∈ qn.liveAt (ctxOf p ts).i → q ≠ w.top.rootKey ∧ qn.firstTime = some (ctxOf p ts).i ∧
              (qn.lastVersion (ctxOf p ts).i).size ≤ (ctxOf p ts).p.splitAbove ∧
              ¬ (qn.size + 2 ≤ (ctxOf p ts).p.M ∧
                deadOver (ctxOf p ts).p (qn.add (ctxOf p ts).i (.key k1 w.next)) = false))
          ⟨hnm, hnr, hpar⟩ op hop'⟩ Q hfresh hA
  · exact h ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop
      ⟨⟨⟨⟨pre0, cv, L, n, hop', hm, hK, hne, hkeep, hfull, hTP⟩, hcase⟩, hhole⟩,
        keyLeaf_transfer hK (fun L' _ => ¬ ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w)
          (ctxOf p ts).i w.top.rootKey q → wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
          (k1, L') ∈ qn.liveAt (ctxOf p ts).i → q ≠ w.top.rootKey ∧ qn.firstTime = some (ctxOf p ts).i ∧
            (qn.lastVersion (ctxOf p ts).i).size ≤ (ctxOf p ts).p.splitAbove) hmp op hop'⟩ Q hfresh hA

/-- `invGetScanOK_merges_noL4c` with R4 narrowed further: the leaf's copy a hole
below a parent that is the space root, not made by the transaction, or split in
space (`DelFullTimeHole2M`). Its premise `R3Calls` is believed false at unreached
states (030-01's log), so this theorem is believed vacuous until R3 is restated
with a made-for fact carried to `afterDelete`'s call. -/
theorem invGetScanOK_merges_noL4d (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hF : MergeTailRuns6 p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeHole2M)
    (hCasc : DelCaseLive p (RunTreeQ p (LatestQD p)) DelEmptyCascM) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  exact invGetScanOK_merges_noL4c p hp hth hF hR3
    (delCaseLive_hole_of_hole2 p _ (by omega) (by omega) (fun _ _ h => h.1) (fun _ _ h => h.1.1)
      (fun _ _ h => h.2.2.1.2.2.1) hR4) hCasc

end SIS.Tree
