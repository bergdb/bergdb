/-
The hole at the upward delete's stop node (bergdb 030-01, step 6; R1 at the stop
node): the stop node is a segment leaf on the key's path whose klong to the
emptied chain is deleted, so the key's descent is cut there. The merges' descent
at the stop node's cached segment and height finds it (`holeAtW_cut`): as at the
leaf (`holeAtW_leaf`), by the segments along the descent, a successful descent
has a segment at most the number of the key's segments above the stop node,
since a descent through the stop node's segment leaf stops at the cut.

The stop node's place in the key's descent: the descent's path is linked in the
writer's tree (`lteP_linked`, `dsrFold_linked`), so it is the walk's path
(`linkedFrom_unique`), and a segment leaf on it is the end of one segment's
search (`dsrFold_leaf_mid`).
-/
import SIS.Tree.LiveUpLeaf
import SIS.Tree.LinkedUnique

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The descents' paths -/

/-- The nodes of `descendLte`'s path but its end are inner. -/
theorem lteP_mid_inner (Rd : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ f x a ext, lteP Rd t cv f x = some (a, ext) →
      ∀ y, y ∈ x :: ext.map (·.2) → y ≠ a → ∃ m, Rd y = some m ∧ m.leaf = false := by
  intro f
  induction f with
  | zero => intro x a ext h; simp [lteP] at h
  | succ f ih =>
    intro x a ext h y hy hya
    obtain ⟨n, hRx, ⟨_, hax, hex⟩ | ⟨hnl, fd, ext', _, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · rw [hex] at hy
      simp only [List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
      exact absurd (hy.trans hax.symm) hya
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨n, hRx, hnl⟩
      · simp only [List.map_cons] at hy
        exact ih fd.y a ext' hr y hy hya

/-- A reading's `descendLte` from a reached node is linked in N, the reads agreeing
with N at the reached nodes. -/
theorem lteP_linked (Rd N : NodeId → Option KNode) (t : Time) (r : NodeId) (cv : Nat)
    (hag : ∀ y m, TReach N t r y → Rd y = some m → N y = some m) :
    ∀ f x a ext, lteP Rd t cv f x = some (a, ext) → TReach N t r x →
      LinkedFrom N t x ext ∧ pathEnd x ext = a := by
  intro f
  induction f with
  | zero => intro x a ext h; simp [lteP] at h
  | succ f ih =>
    intro x a ext h hx
    obtain ⟨n, hRx, ⟨_, hax, hex⟩ | ⟨hnl, fd, ext', hfd, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · rw [hex, hax]
      exact ⟨LinkedFrom.nil _, by simp [pathEnd]⟩
    · have hNx := hag x n hx hRx
      have hmem := KNode.searchLte_mem n t _ fd hfd
      obtain ⟨h1, h2⟩ := ih fd.y a ext' hr (TReach.link hx ⟨n, hNx, hmem⟩)
      refine ⟨LinkedFrom.cons x n fd.c fd.y ext' hNx hmem h1, ?_⟩
      have := pathEnd_cons_append x fd.y (some fd.c) [] ext'
      simp only [List.nil_append] at this
      rw [this]; exact h2

/-- `descendToSegmentRoot`'s loop from a reached node is linked in N, the reads
agreeing with N at the reached nodes, of well-formed klongs. -/
theorem dsrFold_linked (Rd N : NodeId → Option KNode) (t : Time) (r : NodeId) (fuel : Nat)
    (hag : ∀ y m, TReach N t r y → Rd y = some m → N y = some m)
    (hwf : ∀ y m, N y = some m → klongsWf m.ks = true) :
    ∀ (cvs : List Nat) (x : NodeId) (ps : List (Option Nat × NodeId)) (a : NodeId)
      (P : List (Option Nat × NodeId)), cvs.foldl (dsrStep Rd t fuel) (some (x, ps)) = some (a, P) →
      TReach N t r x → ∃ sfx, P = ps ++ sfx ∧ LinkedFrom N t x sfx ∧ pathEnd x sfx = a := by
  intro cvs
  induction cvs with
  | nil =>
    intro x ps a P h hx
    simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, LinkedFrom.nil _, by simp [pathEnd]⟩
  | cons cv rest ih =>
    intro x ps a P h hx
    simp only [List.foldl] at h
    cases hst : dsrStep Rd t fuel (some (x, ps)) cv with
    | none => rw [hst, dsrFold_none] at h; cases h
    | some acc =>
      rw [hst] at h
      obtain ⟨leaf, ext, n, fd, hl, hRl, hfd, rfl⟩ := dsrStep_some Rd t fuel x ps cv acc hst
      obtain ⟨hlf, hle⟩ := lteP_linked Rd N t r cv hag fuel x leaf ext hl hx
      have hleafR : TReach N t r leaf := by
        rw [← hle, ← nodeAt_last]
        obtain ⟨k, hk⟩ := TReach.pathLen hx
        exact (PathLen.append hk ((LinkedFrom.pathLen N t x ext hlf ext.length (Nat.le_refl _)).toFrom)).reach
      have hNl := hag leaf n hleafR hRl
      have hmem : (fd.c, fd.y) ∈ n.liveAt t := by
        have := KNode.searchEq_mem n t cv fd (hwf leaf n hNl) hfd
        rw [KNode.searchEq_c n t cv fd hfd]
        exact this
      have hyR : TReach N t r fd.y := TReach.link hleafR ⟨n, hNl, hmem⟩
      obtain ⟨sfx, hsfx, hlsfx, hesfx⟩ := ih fd.y _ a P h hyR
      have hseg : LinkedFrom N t x (ext ++ [(some fd.c, fd.y)]) := by
        refine LinkedFrom.append N t x ext _ hlf ?_
        rw [hle]
        exact LinkedFrom.cons leaf n fd.c fd.y [] hNl hmem (LinkedFrom.nil _)
      refine ⟨ext ++ [(some fd.c, fd.y)] ++ sfx, by rw [hsfx]; simp, ?_, ?_⟩
      · refine LinkedFrom.append N t x _ _ hseg ?_
        have : pathEnd x (ext ++ [(some fd.c, fd.y)]) = fd.y := by
          have := pathEnd_cons_append x fd.y (some fd.c) ext []
          simpa [pathEnd] using this
        rw [this]
        exact hlsfx
      · have h1 : pathEnd x (ext ++ [(some fd.c, fd.y)]) = fd.y := by
          have := pathEnd_cons_append x fd.y (some fd.c) ext []
          simpa [pathEnd] using this
        rw [pathEnd_append_gen, h1, hesfx]

/-- A leaf on `descendToSegmentRoot`'s loop's path, not its end, ends one segment's
`descendLte`, and the loop goes on from it by that segment's search. -/
theorem dsrFold_leaf_mid (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    ∀ (cvs : List Nat) (x : NodeId) (ps : List (Option Nat × NodeId)) (a : NodeId)
      (P : List (Option Nat × NodeId)), cvs.foldl (dsrStep Rd t fuel) (some (x, ps)) = some (a, P) →
      ∀ y, y ∈ (P.drop ps.length).map (·.2) → (∃ m, Rd y = some m ∧ m.leaf = true) → y ≠ a →
      ∃ j c rj Pj ext ny fd, cvs[j]? = some c ∧
        (cvs.take j).foldl (dsrStep Rd t fuel) (some (x, ps)) = some (rj, Pj) ∧
        lteP Rd t c fuel rj = some (y, ext) ∧ Rd y = some ny ∧ ny.searchEq t c = some fd ∧
        ∃ sfx, P = Pj ++ ext ++ (some fd.c, fd.y) :: sfx := by
  intro cvs
  induction cvs with
  | nil =>
    intro x ps a P h y hy _ _
    simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp at hy
  | cons cv rest ih =>
    intro x ps a P h y hy hyl hya
    simp only [List.foldl] at h
    cases hst : dsrStep Rd t fuel (some (x, ps)) cv with
    | none => rw [hst, dsrFold_none] at h; cases h
    | some acc =>
      rw [hst] at h
      obtain ⟨leaf, ext, n, fd, hl, hRl, hfd, rfl⟩ := dsrStep_some Rd t fuel x ps cv acc hst
      obtain ⟨sfx, hP, _⟩ := dsrFold_prefix Rd t fuel rest fd.y _ a P h
      have hdrop : (P.drop ps.length).map (·.2) = ext.map (·.2) ++ fd.y :: sfx.map (·.2) := by
        rw [hP]; simp
      rw [hdrop] at hy
      rcases List.mem_append.mp hy with hy | hy
      · have hyl' : y = leaf := by
          apply Classical.byContradiction
          intro hne
          obtain ⟨m, hm, hml⟩ := lteP_mid_inner Rd t cv fuel x leaf ext hl y (List.mem_cons_of_mem _ hy) hne
          obtain ⟨m', hm', hml'⟩ := hyl
          rw [hm] at hm'
          cases hm'
          rw [hml] at hml'
          cases hml'
        subst hyl'
        exact ⟨0, cv, x, ps, ext, n, fd, rfl, rfl, hl, hRl, hfd, sfx, by rw [hP]; simp⟩
      · rcases List.mem_cons.mp hy with hy | hy
        · subst hy
          cases rest with
          | nil =>
            simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
            exact absurd h.1 hya
          | cons c2 rest2 =>
            simp only [List.foldl] at h
            cases hst2 : dsrStep Rd t fuel (some (fd.y, ps ++ ext ++ [(some fd.c, fd.y)])) c2 with
            | none => rw [hst2, dsrFold_none] at h; cases h
            | some acc2 =>
              rw [hst2] at h
              obtain ⟨leaf2, ext2, n2, fd2, hl2, hRl2, hfd2, rfl⟩ :=
                dsrStep_some Rd t fuel fd.y _ c2 acc2 hst2
              obtain ⟨⟨m2, hm2, _⟩, _⟩ := lteP_leaf Rd t c2 fuel fd.y leaf2 ext2 hl2
              obtain ⟨m, hm, hml⟩ := hyl
              have hle : lteP Rd t c2 fuel fd.y = some (fd.y, []) := by
                cases fuel with
                | zero => simp [lteP] at hl2
                | succ f => simp [lteP, hm, hml]
              rw [hle] at hl2
              simp only [Option.some.injEq, Prod.mk.injEq] at hl2
              obtain ⟨rfl, rfl⟩ := hl2
              obtain ⟨sfx2, hP2, _⟩ := dsrFold_prefix Rd t fuel rest2 fd2.y _ a P h
              refine ⟨1, c2, fd.y, ps ++ ext ++ [(some fd.c, fd.y)], [], n2, fd2, rfl, ?_, hle, hRl2, hfd2,
                sfx2, by rw [hP2]; simp⟩
              simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
              rw [hst]
        · obtain ⟨j, c, rj, Pj, ext', ny, fd', hc, hfold, hl', hRy, hfd', sfx', hP'⟩ :=
            ih fd.y _ a P h y (by rw [hP]; simpa using hy) hyl hya
          refine ⟨j + 1, c, rj, Pj, ext', ny, fd', by simpa using hc, ?_, hl', hRy, hfd', sfx', hP'⟩
          simp only [List.take_succ_cons, List.foldl_cons]
          rw [hst]
          exact hfold

/-- `descendLte` reads alike where its path reads alike, its end a leaf. -/
theorem lteP_congr_end (Rd Rd' : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ f x a ext, lteP Rd t cv f x = some (a, ext) →
      (∀ y ∈ x :: ext.map (·.2), y ≠ a → Rd' y = Rd y) → (∃ m, Rd' a = some m ∧ m.leaf = true) →
      lteP Rd' t cv f x = some (a, ext) := by
  intro f
  induction f with
  | zero => intro x a ext h; simp [lteP] at h
  | succ f ih =>
    intro x a ext h hag ha
    obtain ⟨n, hRx, ⟨_, hax, hex⟩ | ⟨hnl, fd, ext', hfd, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · subst hax
      rw [hex]
      obtain ⟨m, hm, hml⟩ := ha
      simp [lteP, hm, hml]
    · have hxa : x ≠ a := by
        intro he
        obtain ⟨⟨n', hn', hl'⟩, _⟩ := lteP_leaf Rd t cv (f + 1) x a _ h
        rw [← he, hRx] at hn'
        cases hn'
        rw [hnl] at hl'
        cases hl'
      have hRx' : Rd' x = some n := by rw [hag x (by simp) hxa]; exact hRx
      have hag' : ∀ y ∈ fd.y :: ext'.map (·.2), y ≠ a → Rd' y = Rd y := by
        intro y hy hya
        apply hag y _ hya
        simp only [List.map_cons, List.mem_cons] at hy ⊢
        exact Or.inr hy
      have he := ih fd.y a ext' hr hag' ha
      simp [lteP, hRx', hnl, hfd, he]

/-- The hole at a node whose key's descent is cut (bergdb 030-01, step 6; R1 at
the stop node): as `holeAtW_leaf`, for a key that goes on below the leaf L, whose
search there finds nothing. -/
theorem holeAtW_cut (c : Ctx) (v : W) (pre : List Nat) (cv : Nat) (rest : List Nat) (rk L : NodeId)
    (g0 h0 : Nat) (hs : SegRd (rdN c v) (rdG c v)) (hcvs : ∀ c' ∈ pre, segLen c' = 7)
    (hdsr : ∃ P, pre.foldl (dsrStep (rdN c v) c.i c.p.fuel)
      (some (v.top.rootKey, [(none, v.top.rootKey)])) = some (rk, P))
    (hlte : ∃ ext, lteP (rdN c v) c.i cv c.p.fuel rk = some (L, ext))
    (hcut : rest = [] ∨ ∃ nL, rdN c v L = some nL ∧ nL.searchEq c.i cv = none)
    (hgL : rdG c v L = some (g0, h0)) :
    HoleAtW (pre ++ cv :: rest) g0 h0 c v L := by
  intro d v' hrun
  obtain ⟨root', P0, cv', ext', hd1, hk, hdh, hpath, hdd, _⟩ :=
    writerWP_descendToHeight_rd (pre ++ cv :: rest) g0 h0 c v d v' hrun
  obtain ⟨P, hP⟩ := hdsr
  obtain ⟨ext, hext⟩ := hlte
  obtain ⟨s, hroot⟩ : ∃ s, ∀ n, rdN c v v.top.rootKey = some n →
      ∃ h, rdG c v v.top.rootKey = some (s, h) := by
    cases hr : rdN c v v.top.rootKey with
    | none => exact ⟨0, fun n hn => by cases hn⟩
    | some n =>
      obtain ⟨g, h, hG, _⟩ := hs _ n hr
      exact ⟨g, fun n' _ => ⟨h, hG⟩⟩
  have hseg_rk := dsrFold_seg _ _ hs c.i c.p.fuel pre _ _ rk P s hcvs hP hroot
  obtain ⟨hL, hGL⟩ := lteP_seg _ _ hs c.i cv c.p.fuel rk L ext (s + pre.length) hext hseg_rk
  rw [hgL] at hGL
  have e0 := Prod.mk.inj (Option.some.inj hGL)
  -- a successful descent does not pass the cut
  have hle : g0 ≤ pre.length := by
    apply Classical.byContradiction
    intro hgt
    obtain ⟨m, hm⟩ : ∃ m, g0 = pre.length + 1 + m := ⟨g0 - pre.length - 1, by omega⟩
    rcases hcut with hr | ⟨nL, hnL, hsn⟩
    · subst hr
      have := (List.getElem?_eq_some_iff.mp hk).1
      simp at this
      omega
    · have htake : (pre ++ cv :: rest).take g0 = pre ++ cv :: rest.take m := by
        rw [hm, List.take_append, List.take_of_length_le (show pre.length ≤ pre.length + 1 + m by omega),
          show pre.length + 1 + m - pre.length = m + 1 by omega, List.take_succ_cons]
      unfold dsrP at hd1
      rw [htake, List.foldl_append, hP] at hd1
      have hstep : dsrStep (rdN c v) c.i c.p.fuel (some (rk, P)) cv = none := by
        simp [dsrStep, hext, hnL, hsn]
      simp only [List.foldl_cons, hstep, dsrFold_none] at hd1
      cases hd1
  have hs0 : s = 0 := by omega
  subst hs0
  have hg0 : g0 = pre.length := by omega
  subst hg0
  have htake : (pre ++ cv :: rest).take pre.length = pre := List.take_left' rfl
  unfold dsrP at hd1
  rw [htake, hP] at hd1
  cases hd1
  have hcv : cv' = cv := by
    rw [List.getElem?_append_right (Nat.le_refl _)] at hk
    simpa using hk.symm
  subst hcv
  obtain ⟨⟨nL, hRL, hLl⟩, hlast⟩ := lteP_leaf _ c.i cv' c.p.fuel rk L ext hext
  obtain ⟨g1, h1, hG1, hl1, _⟩ := hs L nL hRL
  have e1 := Prod.mk.inj (Option.some.inj (hgL.symm.trans hG1))
  have hh0 : h0 = 0 := by rw [e1.2]; rw [hLl] at hl1; simpa using hl1.symm
  subst hh0
  rw [dhP_zero_of_lteP _ _ hs c.i cv' c.p.fuel rk L ext hext] at hdh
  cases hdh
  rw [hpath, hdd]
  apply path_last_map
  have hP' := (dsrFold_shape (rdN c v) c.i c.p.fuel pre _ _ rk _ hP (by simp)).1
  exact getLast_map_append _ _ rk L hP' hlast

/-! ## The hole at the stop node -/

theorem rdN_sub_wNode (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W) (y : NodeId)
    (m : KNode) (ht : w.taken.contains y = false) (h : rdN c w y = some m) :
    wNode c.p base w y = some m := by
  unfold rdN at h
  unfold wNode
  rw [ht]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hl : w.nodes.lookup y with
  | some n => rw [hl] at h; exact h
  | none =>
    rw [hl] at h
    simp only at h ⊢
    cases hv : c.view y with
    | none => rw [hv] at h; cases h
    | some nd =>
      rw [hv] at h
      have hb := hvc y nd hv
      simp only [knodeOf, hb]
      exact h

theorem rdN_congr_lookup (c : Ctx) (v w : W) (y : NodeId) (h : v.nodes.lookup y = w.nodes.lookup y) :
    rdN c v y = rdN c w y := by
  unfold rdN; rw [h]

theorem mem_prefix_index (Q R : List (Option Nat × NodeId)) (path : List (Option Nat × NodeId))
    (hp : path = Q ++ R) (y : NodeId) (hy : y ∈ Q.map (·.2)) :
    ∃ i, i < Q.length ∧ (path[i]?).map (·.2) = some y := by
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
  simp only [List.length_map] at hi
  refine ⟨i, hi, ?_⟩
  rw [hp, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.some.injEq]
  rw [← hiy]
  simp

set_option maxHeartbeats 1600000 in
/-- The hole at the upward delete's stop node (bergdb 030-01, step 6; R1 at the
stop node): X stop, a segment leaf on the walk's path above the key's leaf, at a
state v that reads as the walk's end w3 at the path's nodes above it, and where
the stop node, still a leaf, has no live klong of the path's next compare value
(the chain's): the merges' descent at its cached segment and height 0 finds it. -/
theorem holeAtW_stop (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w w3 v : W)
    (pre : List Nat) (cv : Nat) (rk L : NodeId) (n : KNode) (P : List (Option Nat × NodeId))
    (stop gs : Nat) (sn' : KNode)
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
    (hsD : stop < P.length)
    (hsl : ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf = true)
    (hvn : ∀ y, y ≠ nodeAt w.top.rootKey P stop →
      (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
      v.nodes.lookup y = w3.nodes.lookup y)
    (hvtop : v.top = w3.top)
    (hsn : v.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn') (hsl' : sn'.leaf = true)
    (hcutK : ∀ z, (((P[stop]?).bind (·.1)).getD 0, z) ∉ sn'.live)
    (hsw : klongsWf sn'.ks = true) (hst : ∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i)
    (hs : SegRd (rdN c v) (rdG c v))
    (hgL : rdG c v (nodeAt w.top.rootKey P stop) = some (gs, 0)) :
    HoleAtW (pre ++ [cv]) gs 0 c v (nodeAt w.top.rootKey P stop) := by
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
  -- the path's nodes above the stop node read alike at v
  have habove : ∀ i, i < stop → rdN c v (nodeAt root P i) = rdN c w3 (nodeAt root P i) := by
    intro i hi
    apply rdN_congr_lookup
    apply hvn
    · intro he; have := hdist _ _ (by omega) (by omega) he; omega
    · intro k h1 h2 he; have := hdist _ _ (by omega) h2 he; omega
  have hinA : ∀ y ∈ (Pj ++ extj).map (·.2), ∃ i, i ≤ stop ∧ y = nodeAt root P i := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := mem_prefix_index (Pj ++ extj) _ w3.path hw3p' y hy
    have h2 := hpX i (by omega)
    rw [hiy] at h2
    exact ⟨i, by omega, Option.some.inj h2⟩
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
      exact habove 0 (by simp at hAstop; omega)
    · intro y hy
      have hy' : y ∈ (Pj ++ extj).map (·.2) := by
        have : y ∈ Pj.map (·.2) := by
          rw [List.mem_map] at hy ⊢
          obtain ⟨e, he, rfl⟩ := hy
          exact ⟨e, List.dropLast_subset _ he, rfl⟩
        rw [List.map_append]; exact List.mem_append_left _ this
      obtain ⟨i, hi, rfl⟩ := hinA y hy'
      by_cases his : i = stop
      · exfalso
        -- the stop node is no node of Pj but its last
        have hPjne : Pj ≠ [] := by
          intro h0; rw [h0] at hPj0; simp at hPj0
        have hsplit : w3.path = Pj.dropLast ++ ((Pj.getLast hPjne) :: (extj ++
            (some fd.c, fd.y) :: (sfx' ++ ext))) := by
          rw [hw3p']
          conv => lhs; rw [← List.dropLast_concat_getLast hPjne]
          simp
        obtain ⟨i', hi', hiy'⟩ := mem_prefix_index Pj.dropLast _ w3.path hsplit _ hy
        have hlenPj : Pj.dropLast.length + 1 ≤ (Pj ++ extj).length := by
          rw [List.length_dropLast, List.length_append]
          have := List.length_pos_iff.mpr hPjne
          omega
        have h2 := hpX i' (by omega)
        rw [hiy', his] at h2
        have := hdist _ _ (by omega) (by omega) (Option.some.inj h2).symm
        omega
      · exact habove i (by omega)
  have hlv : lteP (rdN c v) c.i c' c.p.fuel rj = some (nodeAt root P stop, extj) := by
    refine lteP_congr_end (rdN c w3) (rdN c v) c.i c' c.p.fuel rj _ extj hlj ?_
      ⟨sn', rdN_of_lookup _ v _ sn' hsn, hsl'⟩
    intro y hy hyX
    have hy' : y ∈ (Pj ++ extj).map (·.2) := by
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [List.map_append]
        exact List.mem_append_left _ (List.mem_of_getLast? hPj0)
      · rw [List.map_append]; exact List.mem_append_right _ hy
    obtain ⟨i, hi, rfl⟩ := hinA y hy'
    have his : i ≠ stop := fun he => hyX (by rw [he])
    exact habove i (by omega)
  -- the cut: the stop node has no live klong of the chain's compare value
  have hcut : sn'.searchEq c.i c' = none := by
    have h1 := KNode.searchEq_live sn' c.i hsw hst c'
    cases h2 : sn'.searchEq c.i c' with
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
  refine holeAtW_cut c v (pre.take j) c' (pre.drop (j + 1) ++ [cv]) rj (nodeAt root P stop) gs 0 hs
    (fun x hx => keyWf_init_long pre cv hkey x (List.mem_of_mem_take hx)) ⟨Pj, by rw [hvroot]; exact hfv⟩
    ⟨extj, hlv⟩ (Or.inr ⟨sn', rdN_of_lookup _ v _ sn' hsn, hcut⟩) hgL


end SIS.Tree
