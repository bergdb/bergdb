/-
The merges' loop with the live counts (bergdb 030-01, step 3): from the hole's
form at a call of the loop, `LiveHoleW key g h` (LiveHolePilot.lean), every run
of `mergeUp` ends in the loop's exit form `LiveExit`: the live counts, but,
after a merge, at the root of segment g on the key's path, the node that root
collapse's descent finds (`SegRootW`).

The loop is the stratum's (`writerWP_mergeUp_delJW`, TakeDelMergeKd.lean) with
the hole carried beside its invariant: the heights' walk (`ht_descendToHeight`,
`ht_merge_of_J`) gives each round's descent its heights, and a merge of a
round, from the round's facts, keeps the hole's form one height up or ends with
no hole (`MergeLiveOK`, an obligation here; the pilot is its first case). A
round that merges nothing exits: the found node is the space root, a segment
root, or filled. Before any merge the hole is at height 0, a leaf, so an exit
then needs no collapse.
-/
import SIS.Tree.LiveHolePilot
import SIS.Tree.Stratum

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The root that root collapse's descent finds at v: every successful run of
`descendToSegmentRoot key g` at v ends at y. -/
def SegRootW (key : Key) (g : Nat) (c : Ctx) (v : W) (y : NodeId) : Prop :=
  ∀ r v', descendToSegmentRoot key g c v = .ok (r, v') → r = y

/-- The merges' loop's exit form: the live counts, but, after a merge (the flag
the loop returns), at the root of segment g on the key's path. -/
def LiveExit (key : Key) (g : Nat) (c : Ctx) (base : View BVal) (merged : Bool) (v : W) : Prop :=
  LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey (fun y => merged = true ∧ SegRootW key g c v y)

theorem liveExit_of_liveEdges (key : Key) (g : Nat) (c : Ctx) (base : View BVal) (merged : Bool)
    (v : W) (h : LiveEdges c.p (wNode c.p base v) c.i v.top.rootKey) :
    LiveExit key g c base merged v :=
  liveEdgesH_of_liveEdges _ _ _ _ _ h

/-! ## The descent's shape -/

/-- `dhP` passes inner nodes only, but its last. -/
theorem dhP_inner (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (t : Time)
    (cv h : Nat) :
    ∀ f y ext, dhP Rd Gh t cv h f y = some ext →
      ∀ z ∈ (y :: ext.map (·.2)).dropLast, ∃ n, Rd z = some n ∧ n.leaf = false := by
  intro f
  induction f with
  | zero => intro y ext hy; simp [dhP] at hy
  | succ f ih =>
    intro y ext hy z hz
    unfold dhP at hy
    split at hy
    · rename_i n g0 hx hn hG
      split at hy
      · cases hy; simp at hz
      · split at hy
        · cases hy
        · rename_i hlh
          split at hy
          · cases hy
          · rename_i fd hfd
            cases hr : dhP Rd Gh t cv h f fd.y with
            | none => rw [hr] at hy; cases hy
            | some ext' =>
              rw [hr] at hy
              simp only [Option.map_some, Option.some.injEq] at hy
              subst hy
              simp only [List.map_cons] at hz
              rw [List.dropLast_cons_cons] at hz
              rcases List.mem_cons.mp hz with h1 | h1
              · subst h1
                refine ⟨n, hn, ?_⟩
                cases hl : n.leaf
                · rfl
                · rw [hl] at hlh; simp at hlh
              · exact ih fd.y ext' hr z h1
    · cases hy

/-- `dhP` ends at a node of height h. -/
theorem dhP_last (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (t : Time)
    (cv h : Nat) :
    ∀ f y ext, dhP Rd Gh t cv h f y = some ext →
      ∀ z, (y :: ext.map (·.2)).getLast? = some z → ∃ g', Gh z = some (g', h) := by
  intro f
  induction f with
  | zero => intro y ext hy; simp [dhP] at hy
  | succ f ih =>
    intro y ext hy z hz
    unfold dhP at hy
    split at hy
    · rename_i n g' hx hn hG
      split at hy
      · rename_i hxh
        cases hy
        simp only [List.map_nil, List.getLast?_singleton, Option.some.injEq] at hz
        subst hz
        refine ⟨g', ?_⟩
        rw [hG]
        simp at hxh
        rw [hxh]
      · split at hy
        · cases hy
        · split at hy
          · cases hy
          · rename_i fd hfd
            cases hr : dhP Rd Gh t cv h f fd.y with
            | none => rw [hr] at hy; cases hy
            | some ext' =>
              rw [hr] at hy
              simp only [Option.map_some, Option.some.injEq] at hy
              subst hy
              simp only [List.map_cons, List.getLast?_cons_cons] at hz
              exact ih fd.y ext' hr z (by simpa using hz)
    · cases hy

/-- A successful descent of the loop, by the reads at w: the found node is the
path's last, of height h; if it is the space root or a segment leaf is above
it, it is the root of segment g that `descendToSegmentRoot` finds. -/
theorem descend_exit_shape (key : Key) (g h : Nat) (c : Ctx) (w w1 : W) (d : Nat)
    (hS : descendToHeight key g h c w = .ok (d, w1)) :
    ∃ x, (w1.path[d]?).map (·.2) = some x ∧ d + 1 = w1.path.length ∧
      (∃ g', rdG c w x = some (g', h)) ∧
      ((d = 0 ∨ ∃ e n, w1.path[d - 1]? = some e ∧ rdN c w e.2 = some n ∧ n.leaf = true) →
        ∃ P0, dsrP (rdN c w) c.i c.p.fuel key g w.top.rootKey = some (x, P0)) := by
  obtain ⟨root, P0, cv, ext, hdsr, _, hdh, hp1, hd1, _⟩ :=
    writerWP_descendToHeight_rd key g h c w d w1 hS
  obtain ⟨hlast, _, _⟩ := dsrP_shape (rdN c w) c.i c.p.fuel key g _ root P0 hdsr
  obtain ⟨B, hB⟩ := List.getLast?_eq_some_iff.mp hlast
  -- the path's nodes: B, then the segment root and the descent below it
  have hL : w1.path.map (·.2) = B ++ (root :: ext.map (·.2)) := by
    rw [hp1, List.map_append, hB]; simp
  have hlen : d + 1 = w1.path.length := by
    have := congrArg List.length hL
    simp only [List.length_map, List.length_append, List.length_cons] at this
    rw [hd1, List.length_append]
    have h2 := congrArg List.length hp1
    simp only [List.length_append] at h2
    omega
  -- the last node
  obtain ⟨x, hx⟩ : ∃ x, (root :: ext.map (·.2)).getLast? = some x := by
    cases h' : (root :: ext.map (·.2)).getLast? with
    | none => simp at h'
    | some x => exact ⟨x, rfl⟩
  have hxd : (w1.path[d]?).map (·.2) = some x := by
    rw [← List.getElem?_map, hL]
    have hd' : d = (B ++ (root :: ext.map (·.2))).length - 1 := by
      rw [← hL]; simp; omega
    rw [hd', ← List.getLast?_eq_getElem?, List.getLast?_append, hx]
    rfl
  refine ⟨x, hxd, hlen, dhP_last _ _ _ _ _ _ _ _ hdh x hx, fun hex => ⟨P0, ?_⟩⟩
  -- the descent below the segment root is empty
  have hext : ext = [] := by
    cases hE : ext with
    | nil => rfl
    | cons e ext' =>
      exfalso
      rcases hex with h0 | ⟨eq, nq, heq, hnq, hlq⟩
      · -- the path has at least two nodes
        have : 2 ≤ w1.path.length := by
          have := congrArg List.length hL
          simp only [List.length_map, List.length_append, List.length_cons, hE] at this
          omega
        omega
      · -- the node above the found one is inner
        have hin := dhP_inner _ _ _ _ _ _ _ _ hdh
        have hmem : eq.2 ∈ (root :: ext.map (·.2)).dropLast := by
          have h1 : (w1.path.map (·.2))[d - 1]? = some eq.2 := by
            rw [List.getElem?_map, heq]; rfl
          rw [hL] at h1
          have hlenB : d - 1 ≥ B.length := by
            have := congrArg List.length hL
            simp only [List.length_map, List.length_append, List.length_cons, hE] at this
            omega
          rw [List.getElem?_append_right hlenB] at h1
          have hl2 : (root :: ext.map (·.2)).length = (ext.map (·.2)).length + 1 := by simp
          have hidx : d - 1 - B.length < (root :: ext.map (·.2)).dropLast.length := by
            have := congrArg List.length hL
            simp only [List.length_map, List.length_append, List.length_cons, hE] at this
            simp [List.length_dropLast, hE]
            omega
          have h2 : ((root :: ext.map (·.2)).dropLast)[d - 1 - B.length]? = some eq.2 := by
            have hlt : d - 1 - B.length < (root :: ext.map (·.2)).length - 1 := by
              simpa [List.length_dropLast] using hidx
            simp only [List.getElem?_dropLast, hlt, ↓reduceIte]
            exact h1
          exact List.mem_of_getElem? h2
        obtain ⟨n', hn', hl'⟩ := hin eq.2 hmem
        rw [hnq] at hn'
        cases hn'
        rw [hlq] at hl'
        cases hl'
  subst hext
  simp only [List.map_nil, List.getLast?_singleton, Option.some.injEq] at hx
  subst hx
  exact hdsr

/-! ## The exits of a round -/

/-- The live counts from the hole's form with one hole x that meets `RootOK`'s
second half if it is the root and `ChildOK` at every link to it. -/
theorem liveEdges_of_oneHole (p : Params) (N : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (Hl : NodeId → Prop) (h : LiveEdgesH p N t r Hl) (hHl : ∀ y, Hl y → y = x)
    (hroot : ∀ xn, N x = some xn → x = r → xn.leaf = false → 2 ≤ (xn.liveAt t).length)
    (hq : ∀ u un cc xn, TReach N t r u → N u = some un → (cc, x) ∈ un.liveAt t → N x = some xn →
      xn.liveAt t ≠ [] → ChildOK p t un xn) :
    LiveEdges p N t r := by
  refine liveEdges_of_liveEdgesH p N t r Hl h (fun rn hrn hH hl => ?_) ?_
  · have hrx := hHl r hH
    rw [hrx] at hrn
    exact hroot rn hrn hrx.symm hl
  · intro u un cc y yn hu hun hc hyn hH
    have hyx := hHl y hH
    subst hyx
    exact hq u un cc yn hu hun hc hyn ((h.2 u un cc y yn hu hun hc hyn).2 hH)

/-- An exit of a round of the merges' loop at (g, h) from v, its descent ending
at v1 with x the found node, at a state v' that reads as v: the exit form holds
if x meets the live counts' conditions (no hole), or after a merge if x is the
space root or a segment leaf is above it (x the segment's root). -/
theorem liveExit_round (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (v v1 v' : W)
    (d : Nat) (merged : Bool) (hS : descendToHeight key g h c v = .ok (d, v1))
    (hr : ReadsAs c.p base v v') (hk : ObsKept c v v') (hLH : LiveHoleW key g h c base v)
    (x : NodeId) (hx : (v1.path[d]?).map (·.2) = some x)
    (hcase : ((∀ xn, wNode c.p base v x = some xn → x = v.top.rootKey → xn.leaf = false →
        2 ≤ (xn.liveAt c.i).length) ∧
      (∀ u un cc xn, TReach (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
        (cc, x) ∈ un.liveAt c.i → wNode c.p base v x = some xn → xn.liveAt c.i ≠ [] →
        ChildOK c.p c.i un xn)) ∨
      (merged = true ∧ (d = 0 ∨ ∃ e n, v1.path[d - 1]? = some e ∧ rdN c v e.2 = some n ∧
        n.leaf = true))) :
    LiveExit key g c base merged v' := by
  have hHl : ∀ y, HoleAtW key g h c v y → y = x := by
    intro y hy
    have := hy d v1 hS
    rw [hx] at this
    exact (Option.some.inj this).symm
  unfold LiveExit
  rw [hr.1, hr.2.1]
  rcases hcase with ⟨hroot, hq⟩ | ⟨hmg, hsh⟩
  · exact liveEdgesH_of_liveEdges _ _ _ _ _
      (liveEdges_of_oneHole c.p _ c.i _ x _ hLH hHl hroot hq)
  · obtain ⟨x', hx', _, _, hseg⟩ := descend_exit_shape key g h c v v1 d hS
    rw [hx] at hx'
    cases hx'
    obtain ⟨P0, hP0⟩ := hseg hsh
    refine liveEdgesH_mono c.p _ c.i _ _ _ (fun y hy => ⟨hmg, ?_⟩) ?_ hLH
    · rw [hHl y hy]
      intro r0 v'' hrun
      have hd := (writerWP_descendToSegmentRoot_rd key g c v' r0 v'' hrun).1
      rw [hk.1, hk.2.2, hP0] at hd
      exact (Prod.mk.inj (Option.some.inj hd)).1.symm
    · intro u un cc y yn hu hun hc hyn _ hnH
      exact ((hLH.2 u un cc y yn hu hun hc hyn).1 hnH).1

/-- At height 0 the found node is a leaf (the books: a node's height is 0 just
when it is a leaf). -/
theorem found_leaf_of_h0 (key : Key) (g : Nat) (c : Ctx) (v v1 : W) (d : Nat) {B : NodeId}
    (hS : descendToHeight key g 0 c v = .ok (d, v1)) (hb1 : Book B c v1)
    (x : NodeId) (hx : (v1.path[d]?).map (·.2) = some x) (n : KNode)
    (hn : v1.nodes.lookup x = some n) : n.leaf = true := by
  obtain ⟨x', hx', _, ⟨g', hG⟩, _⟩ := descend_exit_shape key g 0 c v v1 d hS
  rw [hx] at hx'
  cases hx'
  have hk01 : ObsKept c v v1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hk⟩ := writerWP_descendToHeight_rd key g 0 c v d v1 hS
    exact hk
  rw [← hk01.2.1, rdG_of_lookup c v1 x n hn] at hG
  have := kd_leaf hb1 hn (bk_mem_of_lookup _ _ _ hG)
  simpa using this

/-! ## The loop -/

/-- The live merge at a round of the merges' loop (bergdb 030-01, step 3): from
the round's facts at the merge's state v3 (the stratum's invariant at a fuel F,
the books, the path, the heights' walk at the descent's end v1 and at v3), a
merge of the found node x at depth d under its inner parent p keeps the hole's
form one height up (a merge into one node), or ends with no hole. The pilot
(`liveHoleW_merge_pilot`) is its case of a merge into one node of nodes the
transaction did not make, p with room and no compaction. -/
def MergeLiveOK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) : Prop :=
  ∀ (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (top0 : Top) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode),
    descendToHeight key g h c v = .ok (d, v1) → 0 < d →
    ReadsAs c.p base v1 v3 → ObsKept c v1 v3 → v3.path = v1.path →
    LiveHoleW key g h c base v →
    DelInvJ c base w0 k0 F KO B B v3 → PutBook c B top0 v3 → PathOK c v3 d X K Nn →
    Book B c v1 → HtInv H B c v1 → PathFreeTo v1 v1.path.length → HtInv H B c v3 →
    (v3.path[d]?).map (·.2) = some x → (v3.path[d - 1]?).map (·.2) = some p →
    v3.nodes.lookup p = some pn → pn.leaf = false → v3.nodes.lookup x = some xn →
    xn.cnt < c.p.mergeBelow →
    WriterWP (merge x d) c v3 (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
      (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

set_option maxHeartbeats 8000000 in
/-- The merges' loop with the hole (bergdb 030-01, step 3), the stratum's loop
(`writerWP_mergeUp_delJW`) at a fuel F with the hole and the heights beside its
invariant, all asked while the next id is below F: every run ends in the exit
form, given the live merge (`MergeLiveOK`). -/
theorem writerWP_mergeUp_liveJW (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR)
    (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hML : MergeLiveOK c base B H) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvJW c base w0 k0 fuelR (fun u => u.next < fuelR) KO B B v →
      (v.next < fuelR → PutBook c B top0 v ∧ HtInv H B c v ∧ LiveHoleW key g h c base v ∧
        (merged = false → h = 0)) →
      WriterWP (mergeUp key g fuel h merged) c v
        (fun merged' v' => v'.next < fuelR → LiveExit key g c base merged' v') := by
  have hMJ := mergeStepJ2OKF_of_root c base hvc fuelR B hpos hcap hsa2
    (mergeRootJ2OKF_holds c base fuelR B hpos hcap hsa2)
  have hM := mergeStepOKW_next c base fuelR hpos hcap hsa2
  intro fuel
  induction fuel with
  | zero => intro h merged v _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v ⟨⟨Bf, hBfv, hfc⟩, hD⟩ hL
    by_cases hC : v.next < fuelR
    rotate_left
    · refine writerWP_mono (freshCache_mergeUp key g (f + 1) h merged c v hBfv hfc) ?_
      rintro _ v' ⟨_, hle⟩ hlt
      exact absurd (Nat.lt_of_le_of_lt hle hlt) hC
    obtain ⟨⟨hI, hbk, hik⟩, hJ0, hB0⟩ := hD hC
    obtain ⟨hpb, hhi, hLH, hmh⟩ := hL hC
    have hT0 : TreeOK (wNode c.p base v) c.i v.top.rootKey := hI.1.tree
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    intro d v1 hS
    obtain ⟨hI1, X, K, Nn, hP1⟩ := descentOK c base fuelR w0 k0 key g h v hI d v1 hS
    obtain ⟨hbk1, hik1, _⟩ := kd_descendToHeight KO B key g h c v hv hk hbk hik d v1 hS
    have hr1 : ReadsAs c.p base v v1 := writerWP_descendToHeight_readsU key g h c base hvc v d v1 hS
    obtain ⟨hb1, hi1, _, hpf1, hd1⟩ := ht_descendToHeight B key g h c v hvo hpb.book hhi hkw hpb.klongs
      d v1 hS
    have hpb1 := putBook_descendToHeight key g h c base B top0 hB v hpb d v1 hS
    have hk01 : ObsKept c v v1 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hk⟩ := writerWP_descendToHeight_rd key g h c v d v1 hS
      exact hk
    have hJ1 : TakeJ2 c base B v1 := takeJ2_of_readsAs c base B v v1 hJ0 hr1
    have hBn1 : B ≤ v1.next := by rw [hr1.2.2.2.2]; exact hB0
    obtain ⟨hX1, _, hS21, hlink1, hX01⟩ := id hP1
    have hN1 : wNode c.p base v1 = wNode c.p base v := hr1.1
    have htop1 : v1.top = v.top := hr1.2.1
    -- the found node x = X d, its node at v1 and at v
    have hxd : (v1.path[d]?).map (·.2) = some (X d) := hX1 d (Nat.le_refl _)
    have hwX : ∀ i, i ≤ d → wNode c.p base v (X i) = some (Nn i) := by
      intro i hi
      obtain ⟨a, b⟩ := hS21 i hi
      rw [← hN1]
      simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
    have hRX : ∀ i, i ≤ d → TReach (wNode c.p base v) c.i v.top.rootKey (X i) := by
      intro i hi
      have := pathOK_reach c base v1 d X K Nn hP1 i hi
      rw [hN1, htop1] at this
      exact this
    -- the leaf at height 0
    have hleaf0 : h = 0 → (Nn d).leaf = true := fun h0 => by
      subst h0
      exact found_leaf_of_h0 key g c v v1 d hS hbk1 (X d) hxd (Nn d) (hS21 d (Nat.le_refl _)).1
    -- the only link to x is the path's from X (d - 1)
    have hone : 0 < d → ∀ u cc, TReach (wNode c.p base v) c.i v.top.rootKey u →
        TLink (wNode c.p base v) c.i u cc (X d) → u = X (d - 1) := by
      intro hd u cc hu hl
      have hl0 : TLink (wNode c.p base v) c.i (X (d - 1)) (K d) (X d) := by
        refine ⟨Nn (d - 1), hwX (d - 1) (by omega), ?_⟩
        have := hlink1 d hd (Nat.le_refl _)
        exact this
      exact (hT0.oneLink u cc (X (d - 1)) (K d) (X d) hu (hRX (d - 1) (by omega)) hl hl0).1
    split
    · -- the found node is the space root
      rename_i hd0
      have hd0' : d = 0 := by simpa using hd0
      simp only [writerWP_pure]
      intro _
      refine liveExit_round key g h c base v v1 v1 d merged hS hr1 hk01 hLH (X d) hxd ?_
      cases merged
      · left
        have hlf := hleaf0 (hmh rfl)
        refine ⟨fun xn hxn _ hl => ?_, fun u un cc xn hu hun hc _ _ => ?_⟩
        · rw [hwX d (Nat.le_refl _)] at hxn; cases hxn; rw [hlf] at hl; cases hl
        · exfalso
          have hx0 : X d = v.top.rootKey := by rw [hd0', hX01, htop1]
          exact hT0.rootFree u cc hu (by rw [← hx0]; exact ⟨un, hun, hc⟩)
      · exact Or.inr ⟨rfl, Or.inl hd0'⟩
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      unfold pathNode
      simp only [writerWP_bind, writerWP_get]
      cases hex : v1.path[d]? with
      | none => exact writerWP_throw _ _ _ _
      | some ex =>
        simp only [writerWP_pure]
        cases heq : v1.path[d - 1]? with
        | none => exact writerWP_throw _ _ _ _
        | some eq =>
          simp only [writerWP_pure]
          have hexX : ex.2 = X d := by
            have := hX1 d (Nat.le_refl _); rw [hex] at this; exact Option.some.inj this
          have heqX : eq.2 = X (d - 1) := by
            have := hX1 (d - 1) (by omega); rw [heq] at this; exact Option.some.inj this
          refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and
            (writerWP_getNode_all eq.2 c v1 base hvc) (writerWP_getNode_cache eq.2 c v1))
            (putBook_getNode eq.2 c base B top0 hB v1 hpb1))
            (kd_getNode KO B eq.2 c v1 hv hk hbk1 hik1))
            (hw_getNode B eq.2 c v1 hvo hb1 hi1))
            (writerWP_getNode_rd eq.2 c v1)) ?_
          rintro qn v2 ⟨⟨⟨⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hpb2⟩, hbk2, hik2, _⟩,
            _, hi2, _, _, _⟩, hrq, hk2, _, _⟩
          have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B, top0, hB, hpb2⟩
          have hJ2 : TakeJ2 c base B v2 := takeJ2_of_readsAs c base B v1 v2 hJ1 hr2
          have hBn2 : B ≤ v2.next := by rw [hr2.2.2.2.2]; exact hBn1
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          have hqn : Nn (d - 1) = qn := by
            have h1 := (hS21 (d - 1) (by omega)).1
            rw [heqX, hkeep2 _ _ h1] at hl2
            exact (Option.some.inj hl2)
          have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
          have hk02 := hk01.trans hk2
          split
          · -- the parent is a segment leaf: x is the segment's root
            rename_i hql
            simp only [writerWP_pure]
            intro _
            refine liveExit_round key g h c base v v1 v2 d merged hS hr02 hk02 hLH (X d) hxd ?_
            cases merged
            · left
              have hlf := hleaf0 (hmh rfl)
              refine ⟨fun xn hxn _ hl => ?_, fun u un cc xn hu hun hc hxn hne => ?_⟩
              · rw [hwX d (Nat.le_refl _)] at hxn; cases hxn; rw [hlf] at hl; cases hl
              · have hu' := hone hd u cc hu ⟨un, hun, hc⟩
                rw [hu', hwX (d - 1) (by omega), hqn] at hun
                cases hun
                rw [hwX d (Nat.le_refl _)] at hxn
                cases hxn
                exact ⟨hne, fun _ hl => (by rw [hlf] at hl; cases hl),
                  fun hl => (by rw [hql] at hl; cases hl)⟩
            · refine Or.inr ⟨rfl, Or.inr ⟨eq, qn, heq, ?_, hql⟩⟩
              rw [← hk01.1]; exact hrq
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and
              (writerWP_getNode_all ex.2 c v2 base hvc) (writerWP_getNode_cache ex.2 c v2))
              (putBook_getNode ex.2 c base B top0 hB v2 hpb2))
              (kd_getNode KO B ex.2 c v2 hv hk hbk2 hik2))
              (hw_getNode B ex.2 c v2 hvo hpb2.book hi2))
              (writerWP_getNode_rd ex.2 c v2)) ?_
            rintro xn v3 ⟨⟨⟨⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hpb3⟩, hbk3, hik3, _⟩,
              _, hi3, _, _, _⟩, _, hk3, _, _⟩
            have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B, top0, hB, hpb3⟩
            have hJ3 : TakeJ2 c base B v3 := takeJ2_of_readsAs c base B v2 v3 hJ2 hr3
            have hBn3 : B ≤ v3.next := by rw [hr3.2.2.2.2]; exact hBn2
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            have hxn : Nn d = xn := by
              have h1 := (hS21 d (Nat.le_refl _)).1
              rw [hexX, hkeep3 _ _ (hkeep2 _ _ h1)] at hl3
              exact (Option.some.inj hl3)
            have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr3
            have hk03 := hk02.trans hk3
            split
            · -- x is filled
              rename_i hcnt
              simp only [writerWP_pure]
              intro _
              refine liveExit_round key g h c base v v1 v3 d merged hS hr03 hk03 hLH (X d) hxd
                (Or.inl ⟨fun xn' hxn' hxr _ => ?_, fun u un cc xn' hu hun hc hxn' hne => ?_⟩)
              · exfalso
                have hl0 : TLink (wNode c.p base v) c.i (X (d - 1)) (K d) (X d) :=
                  ⟨Nn (d - 1), hwX (d - 1) (by omega), hlink1 d hd (Nat.le_refl _)⟩
                exact hT0.rootFree _ _ (hRX (d - 1) (by omega)) (by rw [← hxr]; exact hl0)
              · have hu' := hone hd u cc hu ⟨un, hun, hc⟩
                rw [hu', hwX (d - 1) (by omega), hqn] at hun
                cases hun
                rw [hwX d (Nat.le_refl _), hxn] at hxn'
                cases hxn'
                have hge : c.p.mergeBelow ≤ xn.cnt := by simpa using hcnt
                have htx : ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i := by
                  have := hI.1.times (X d) (Nn d) (hwX d (Nat.le_refl _))
                  rw [hxn] at this; exact this
                refine ⟨hne, fun hl => (by rw [hql'] at hl; cases hl), fun _ _ => ?_⟩
                rw [KNode.liveAt_of_times _ _ htx]
                exact hge
            · rename_i hcnt
              have hcnt' : xn.cnt < c.p.mergeBelow := by simpa using hcnt
              rw [writerWP_bind]
              have hxX : X d = ex.2 := hexX.symm
              have hqX : X (d - 1) = eq.2 := heqX.symm
              have hpx3 : v3.path[d]? = some ex := by rw [hp3, hp2, hex]
              have hpq3 : v3.path[d - 1]? = some eq := by rw [hp3, hp2, heq]
              have hql3 : v3.nodes.lookup eq.2 = some qn := hkeep3 _ _ hl2
              have hpf3 : PathFreeTo v3 (d + 1) := by
                refine PathFreeTo.congr (PathFreeTo.mono hpf1 (by omega)) (hp3.trans hp2) ?_
                rw [hr3.2.2.1, hr2.2.2.1]
              have hmg := writerWP_merge_get_inv fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1
                hI3.2.2.1 X K Nn hP3 hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn X K Nn hI3 hP3 hd (by rw [hpx3]; rfl)
                (by rw [hpq3]; rfl) hql3 hql' hl3 hcnt'
              have htr := writerWP_merge_tree_inv2 ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn
                hP3 hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hrg := writerWP_merge_range_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K
                Nn hP3 hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hkd := kd_merge KO B ex.2 d c v3 hv hk hbk3 hik3 (by omega) ex.1
                (by rw [hpx3]) (by
                  intro a q' hq'
                  rw [hpq3] at hq'
                  simp only [Option.some.injEq] at hq'
                  subst hq'
                  exact ⟨qn, hql3, hql'⟩)
              have hmj := hMJ w0 k0 ex.2 eq.2 d v3 qn xn X K Nn ⟨hI3, hJ3, hBn3⟩ hd
                (by rw [hpx3]; rfl) (by rw [hpq3]; rfl) hql3 hql' hl3 hcnt' hP3 hxX
              have hht := ht_merge_of_J c base hvc fuelR hcap hsa2 B top0 hB B hvo w0 k0 ex.2 eq.2 d v3
                qn xn hpb3.book hi3 X K Nn ⟨hI3, hJ3, hBn3⟩ hpb3 hd (by rw [hpx3]; rfl)
                (by rw [hpq3]; rfl) hql3 hql' hl3 hcnt' hP3 hxX ex.1 hpx3 hpf3
              have hlive := hML key g h v v1 v3 d fuelR w0 k0 KO top0 X K Nn ex.2 eq.2 qn xn hS hd
                (ReadsAs.trans _ _ _ _ _ hr2 hr3) (hk2.trans hk3) (hp3.trans hp2) hLH
                ⟨⟨hI3, hbk3, hik3⟩, hJ3, hBn3⟩ hpb3 hP3 hb1 hi1 hpf1 hi3 (by rw [hpx3]; rfl)
                (by rw [hpq3]; rfl) hql3 hql' hl3 hcnt'
              refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
                (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and hmg hms)
                (putBook_merge ex.2 d c base B top0 hB v3 hpb3)) htr) hrg) hkd) hmj)
                (writerWP_merge_next ex.2 d c v3)) hht) hlive) ?_
              rintro r v4 ⟨⟨⟨⟨⟨⟨⟨⟨⟨hread4, hu4, hF4⟩, hpb4⟩, hT4⟩, hR4⟩, hbk4, hik4, _, _⟩, hJ4⟩,
                hn4⟩, _, hi4, _, _⟩, hL1, hL2⟩
              obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B top0 hB hpb4 hT4 hu4 hR4
              have hICE4 := hICEk v4 hbk4 hik4 (fun y hy => hu4 y (tReach_reachS _ _ _ _ hy))
              have hQ4 : DelInvJW c base w0 k0 fuelR (fun u => u.next < fuelR) KO B B v4 := by
                refine ⟨⟨B, hB.good.ids, hpb4.fresh⟩, fun hC4 => ?_⟩
                have hF4' := hF4 hC4 hP4
                exact ⟨⟨⟨hP4, hG4, hR4, hICE4, hF4', fun key' hk' => by
                  rw [hread4 hF4' key']; exact hI3.2.2.2.2.2.1 key' hk', B, top0, hB, hpb4⟩, hbk4,
                  hik4⟩, hJ4, Nat.le_trans hBn3 hn4⟩
              split
              · rename_i hr2'
                have hr2'' : r = 2 := by simpa using hr2'
                simp only [writerWP_pure]
                intro _
                exact liveExit_of_liveEdges key g c base true v4 (hL2 (by rw [hr2'']; decide))
              · refine ih (h + 1) true v4 hQ4 (fun _ => ⟨hpb4, hi4, ?_, fun h' => by cases h'⟩)
                by_cases hr1 : r = 1
                · exact hL1 hr1
                · exact liveEdgesH_of_liveEdges _ _ _ _ _ (hL2 hr1)

/-- The merges' loop with the hole (bergdb 030-01, step 3): from the stratum's
invariant with no fit (`DelInvJAE`), the books, the heights' walk and the hole's
form at (g, h), at height 0 before any merge, every run of `mergeUp` ends in the
exit form, given the live merge (`MergeLiveOK`). -/
theorem writerWP_mergeUp_live (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hML : MergeLiveOK c base B H) :
    ∀ fuel h merged v, DelInvJAE c base KO B B v → PutBook c B top0 v → HtInv H B c v →
      LiveHoleW key g h c base v → (merged = false → h = 0) →
      WriterWP (mergeUp key g fuel h merged) c v
        (fun merged' v' => LiveExit key g c base merged' v') := by
  intro fuel h merged v ⟨u, hu⟩ hpb hhi hLH hmh r v' he
  have hF : c.p.fuel + 1 ≤ max (c.p.fuel + 1) (v'.next + 1) := Nat.le_max_left _ _
  have hp2 : 2 ≤ max (c.p.fuel + 1) (v'.next + 1) :=
    Nat.le_trans (by unfold Params.fuel; omega) hF
  exact writerWP_mergeUp_liveJW key g c base hvc _ hp2 KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    hML u [] fuel h merged v ⟨⟨B, hB.good.ids, hpb.fresh⟩, fun hlt => hu _ hF hlt⟩
    (fun _ => ⟨hpb, hhi, hLH, hmh⟩) r v' he
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))

/-- Root collapse from the loop's exit form after a merge ends with the live
counts (bergdb 030-01, step 4; an obligation here). -/
def CollapseLiveOK (c : Ctx) (base : View BVal) (B : NodeId) : Prop :=
  ∀ (key : Key) (g : Nat) (v : W) (KO : KindOracle) (top0 : Top),
    DelInvJAE c base KO B B v → PutBook c B top0 v → LiveExit key g c base true v →
    WriterWP (collapseRoot key g c.p.fuel) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey)

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the
stratum's invariant with no fit, the books, the heights' walk and the hole's
form at (g, 0), a leaf's height, the merges on, every run ends with the live
counts, given the live merge and root collapse from the exit form. -/
theorem writerWP_afterDelete_live (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (KO : KindOracle) (B : NodeId)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (hpos : 0 < c.i)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c) (hkw : ViewKlongsWf c.p c.view) (top0 : Top)
    (hB : PutBase c base B) (hML : MergeLiveOK c base B H) (hCL : CollapseLiveOK c base B)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
  unfold afterDelete
  simp only [writerWP_bind, writerWP_read, hm, ↓reduceIte]
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_mergeUp_live key g c base hvc KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB hML
      c.p.fuel 0 false v hJ hpb hhi hLH (fun _ => rfl))
    (writerWP_mergeUp_delJAE key g c base hvc hpos KO B hv hk hICEk hsa2 hcap B c.p.fuel 0 false v hJ))
    (putBook_mergeUp key g c.p.fuel 0 false c base B top0 hB v hpb)) ?_
  rintro merged v1 ⟨⟨hX, hJ1⟩, hpb1⟩
  split
  · rename_i hmg
    exact hCL key g v1 KO top0 hJ1 hpb1 (by rw [← hmg]; exact hX)
  · rename_i hmg
    simp only [writerWP_pure]
    refine liveEdges_of_liveEdgesH c.p _ c.i _ _ hX (fun _ _ hH => absurd hH.1 hmg) ?_
    intro _ _ _ _ _ _ _ _ _ hH
    exact absurd hH.1 hmg

end SIS.Tree
