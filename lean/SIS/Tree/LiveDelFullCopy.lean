/-
The delete's full leaf not made by the transaction, split in time (bergdb 030-01,
step 5): its copy, a new node that the leaf's parent names by the leaf's klong
instead, is the hole (l4a's `writerWP_handleFull_timeRoom_liveGh`, the parent with
room). R1 at the copy (`holeAtW_copy`): the key's descent after the split is the
walk's but at the parent, whose search now gives the copy (`lteP_redirect` in the
last segment's tree, or the parent's segment search when the leaf is a segment
root).
-/
import SIS.Tree.LiveDelFull
import SIS.Tree.LiveSplitRoom2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `descendLte` through a node q whose search now names y, a leaf: it ends at y,
the reads agreeing on the path's other nodes but its end. -/
theorem lteP_redirect (Rd Rd' : NodeId → Option KNode) (t : Time) (cv : Nat) (q y a : NodeId)
    (qn qn' : KNode) (hRq : Rd q = some qn) (hRq' : Rd' q = some qn') (hql' : qn'.leaf = false)
    (hsq : ∀ fd, qn.searchLte t cv = some fd → (∀ f' ext'', lteP Rd t cv f' fd.y = some (a, ext'') →
      ∃ fd', qn'.searchLte t cv = some fd' ∧ fd'.y = y))
    (hy : ∃ ny, Rd' y = some ny ∧ ny.leaf = true) :
    ∀ f x ext, lteP Rd t cv f x = some (a, ext) → q ∈ x :: ext.map (·.2) → q ≠ a →
      (∀ z ∈ x :: ext.map (·.2), z ≠ q → z ≠ a → Rd' z = Rd z) →
      ∃ ext', lteP Rd' t cv f x = some (y, ext') := by
  intro f
  induction f with
  | zero => intro x ext h; simp [lteP] at h
  | succ f ih =>
    intro x ext h hq hqa hag
    obtain ⟨m, hRx, ⟨hml, hax, hex⟩ | ⟨hml, fd, ext'', hfd, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · rw [hex] at hq
      simp only [List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
      exact absurd (hq.trans hax.symm) hqa
    · by_cases hxq : x = q
      · rw [hxq] at hRx
        rw [hxq]
        rw [hRq] at hRx
        cases hRx
        obtain ⟨fd', hfd', hfy⟩ := hsq fd hfd f ext'' hr
        obtain ⟨ny, hny, hnyl⟩ := hy
        have hf : 0 < f := by
          cases f with
          | zero => simp [lteP] at hr
          | succ _ => omega
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        refine ⟨[(some fd'.c, y)], ?_⟩
        simp [lteP, hRq', hql', hfd', hfy, hny, hnyl]
      · have hxa : x ≠ a := by
          intro he
          obtain ⟨⟨n', hn', hl'⟩, _⟩ := lteP_leaf Rd t cv (f + 1) x a _ h
          rw [← he, hRx] at hn'
          cases hn'
          rw [hml] at hl'
          cases hl'
        have hRx' : Rd' x = some m := by rw [hag x (by simp) hxq hxa]; exact hRx
        have hq' : q ∈ fd.y :: ext''.map (·.2) := by
          simp only [List.map_cons, List.mem_cons] at hq ⊢
          rcases hq with h1 | h1
          · exact absurd h1.symm hxq
          · exact h1
        obtain ⟨ext', he⟩ := ih fd.y ext'' hr hq' hqa (fun z hz hzq hza => hag z (by
          simp only [List.map_cons, List.mem_cons] at hz ⊢; exact Or.inr hz) hzq hza)
        exact ⟨(some fd.c, fd.y) :: ext', by simp [lteP, hRx', hml, hfd, he]⟩

theorem nodeAt_append_mem (root : NodeId) (sfx ext : List (Option Nat × NodeId)) (i : Nat)
    (h1 : sfx.length ≤ i) (h2 : i ≤ (sfx ++ ext).length) :
    nodeAt root (sfx ++ ext) i ∈ pathEnd root sfx :: ext.map (·.2) := by
  unfold nodeAt
  have hl : (root :: (sfx ++ ext).map (·.2)) = (root :: sfx.map (·.2)) ++ ext.map (·.2) := by simp
  rw [hl]
  rcases Nat.lt_or_ge i (root :: sfx.map (·.2)).length with h3 | h3
  · have hi : i = sfx.length := by simp at h3; omega
    subst hi
    rw [List.getElem?_append_left h3]
    have he : (root :: List.map (fun x => x.snd) sfx)[sfx.length]?.getD 0 = pathEnd root sfx := by
      rw [← nodeAt_last]; rfl
    rw [he]
    exact List.mem_cons_self
  · rw [List.getElem?_append_right h3]
    have h4 : i - (root :: sfx.map (·.2)).length < (ext.map (·.2)).length := by
      simp at h3 h2 ⊢; omega
    rw [List.getElem?_eq_getElem h4]
    exact List.mem_cons_of_mem _ (List.getElem_mem _)

set_option maxHeartbeats 3200000 in
/-- R1 at the copy (bergdb 030-01, step 5): after the key's leaf L, full, is split
in time below its parent q (at depth `P.length - 1`), q's klong of L naming the
copy y, a leaf, the merges' descent at y's cached segment and height 0 finds y. -/
theorem holeAtW_copy (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w w3 v : W)
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
    (hvq : v.nodes.lookup (nodeAt w.top.rootKey P (P.length - 1)) =
      some (((wNode c.p base w (nodeAt w.top.rootKey P (P.length - 1))).getD n).add c.i
        (.key (((P[P.length - 1]?).bind (·.1)).getD 0) y)))
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
  rw [hK] at hvq
  have hqmg : (wNode c.p base w (nodeAt root P (P.length - 1))).getD n = qm := by rw [hqm]; rfl
  rw [hqmg] at hvq
  have hqwf := hwfw _ _ hqm
  have hqtm := htmw _ _ hqm
  have hqR3 : rdN c w3 (nodeAt root P (P.length - 1)) = some qm := by
    have := hlkX (P.length - 1) (by omega)
    rw [hqmg] at this
    exact rdN_of_lookup _ w3 _ qm this
  have hqRv : rdN c v (nodeAt root P (P.length - 1)) = some (qm.add c.i (.key kq y)) :=
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
      (qm.add c.i (.key kq y)) hqR3 hqRv (by rw [KNode.add_leaf]; exact hqml) (by
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
        have h1 := KNode.add_key_searchLte qm c.i kq y hqwf hqtm hqlive cv
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
          ⟨_, by rw [← hqleaf']; exact hqRv, by rw [KNode.add_leaf]; exact hqml⟩
        intro z hz hzl
        apply hagi z _ (by rw [hqleaf']; exact hzl)
        rcases List.mem_cons.mp hz with rfl | hz
        · rw [List.map_append]
          exact List.mem_append_left _ (List.mem_of_getLast? hP'0)
        · rw [List.map_append]; exact List.mem_append_right _ hz
      have hse := KNode.add_key_searchEq qm c.i k' y hqwf hqtm k'
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

/-! ## The case: the full leaf split in time below a parent with room -/

/-- A full leaf as in `DelFullTimeM`, not made by the transaction, below the space
root, whose parent has room for the copy's klong. -/
def DelFullTimeRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelFullTimeM c base w op ∧ ∀ pre cv L n, op = .del (pre ++ [cv]) → KeyLeaf c base w pre cv L n →
    n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey ∧
    ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → qn.size + 2 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false

/-- The path's nodes but its end are reached after the end's node changes. -/
theorem reach_path_updN_end (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (P : List (Option Nat × NodeId)) (hlf : LinkedFrom N t r P) (hT : TreeOK N t r) (m : KNode) :
    ∀ i, i < P.length → TReach (updN N (nodeAt r P P.length) m) t r (nodeAt r P i) := by
  have hPL := LinkedFrom.pathLen N t r P hlf
  have hdist : ∀ i i', i ≤ P.length → i' ≤ P.length → nodeAt r P i = nodeAt r P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  intro i
  induction i with
  | zero => intro _; simpa [nodeAt] using (TReach.root : TReach (updN N (nodeAt r P P.length) m) t r r)
  | succ i ih =>
    intro hi
    obtain ⟨k, n, _, hn, hl⟩ := LinkedFrom.get N t r P hlf i (by omega)
    have hne : nodeAt r P i ≠ nodeAt r P P.length := by
      intro he; have := hdist _ _ (by omega) (Nat.le_refl _) he; omega
    exact TReach.link (ih (by omega)) ⟨n, by rw [updN_ne _ _ _ _ hne]; exact hn, hl⟩

set_option maxHeartbeats 6400000 in
/-- The full leaf not made by the transaction, split in time below a parent with
room (bergdb 030-01, step 5): the delete calls `afterDelete` at the leaf's pair
(g, 0) from a state with `DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`,
the copy the hole (l4a's `writerWP_handleFull_timeRoom_liveGh`, `holeAtW_copy`). -/
theorem liveDel_fullTimeRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
      (m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ≤
        (ctxOf p ts).p.splitAbove ∧ m.firstTime ≠ some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
      ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i w.top.rootKey q →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L') ∈ qn.liveAt (ctxOf p ts).i → qn.size + 2 ≤ (ctxOf p ts).p.M ∧
          deadOver (ctxOf p ts).p (qn.add (ctxOf p ts).i (.key k1 w.next)) = false)
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
  obtain ⟨hroom, hdead⟩ := hpar _ qm kq hqR hqm hkq
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
  generalize hqdef : nodeAt w.top.rootKey P d' = q at hqm hkq hqR hroom hdead hPq
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
      v.nodes.lookup q = some (qm.add (ts.length + 1) (.key kq w3.next)) ∧
      v.taken = w3.taken ∧ v.top = w3.top ∧ v.gh.lookup w3.next = w3.gh.lookup L) := by
    refine writerWP_appendDeleteKlong_full_of L P.length cv n _ w3 hlk3 hne hfull _ ?_
    intro compact s
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
      have : ¬ (last.size > (ctxOf p ts).p.splitAbove) := by rw [← hlast]; omega
      simp [this]
    rw [hlast]
    unfold handleFull
    rw [hd']
    have hn' : wNode p (viewOf (treeRun p ts)) w L = some n := hn
    have hTu : TreeOK (updN (wNode p (viewOf (treeRun p ts)) w) L n) (ts.length + 1) w.top.rootKey := by
      rw [updN_self_eq _ _ _ hn']; exact hI.tree
    obtain ⟨hTl, hRl⟩ := treeOK_updN_sub _ _ _ L n ⟨n.leaf, last.ks⟩ hTu
      (by rw [hlastN]; exact fun c z h => hsub (c, z) h)
    rw [updN_self_eq _ _ _ hn'] at hRl
    refine writerWP_mono (writerWP_handleFull_timeRoom_liveGh d' L q n qm kq last compact (ctxOf p ts)
      (viewOf (treeRun p ts)) w4
      (by rw [h4n]; exact hlk3) (by rw [h4t]; exact h3t) (by rw [h4n]; exact hlq3)
      (by rw [h4t, hr03.2.2.1]; exact hqt) hqL
      (by rw [h4next]; exact hI3.ids.1 L (by rw [hlk3]; rfl))
      (by rw [h4next]; exact hI3.ids.1 q (by rw [hlq3]; rfl)) hnm hcs
      (by
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
      (by rw [h4path, hp3', List.getElem?_cons_succ]; exact hPq)
      (hI.wf q qm hqm) (hI.times q qm hqm) hroom (by rw [h4next, hnext3]; exact hdead) hkq
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
    rintro _ v ⟨hE, hfr, hny, hqv, hvt, hvtop, _, _, hgh, _⟩
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
      v.nodes.lookup q = some (qm.add (ts.length + 1) (.key kq w3.next)) ∧
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
    have hqv' : v.nodes.lookup (nodeAt w.top.rootKey P (P.length - 1)) =
        some (((wNode p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P (P.length - 1))).getD n).add
          (ctxOf p ts).i (.key (((P[P.length - 1]?).bind (·.1)).getD 0) w3.next)) := by
      have e1 : P.length - 1 = d' := by omega
      have hqm' : wNode p (viewOf (treeRun p ts)) w q = some qm := hqm
      rw [e1, hqdef, hqm']
      have e2 : ((P[d']?).bind (·.1)).getD 0 = kq := by rw [hPq]; rfl
      rw [e2]
      exact hqv
    exact holeAtW_copy (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w w3 v pre cv rk L n P w3.next g last
      hI.tree (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.wf hI.times hrk hL hn hnl hr03 hp3'
      hlinkP hXD hlkX hkey hPpos hqv' hny (by rw [hlastl]; exact hnl) hnx3
      (fun z h1 h2 h3 => hfr z (by
        intro he; apply h1; rw [he, ← hqdef]; congr 1; omega) h2 h3) (hvtop.trans rfl) hs hgy

/-- The full leaf not made by the transaction, split in time below a parent with
room, keeps the live counts (bergdb 030-01, steps 5, 3 and 4), with the merges'
loop and root collapse from the hole, given its live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullTimeRoom_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
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
      ∀ key, op = .del key → DelFullTimeRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
  refine liveDel_fullTimeRoom p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ
    key hop hPc _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
