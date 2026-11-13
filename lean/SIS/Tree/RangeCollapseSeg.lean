/-
Root collapse at any segment keeps the walk's ranges (bergdb 024-12, TP10;
`RangeOrder`): prover cost's loop `writerWP_collapseRoot_coll`
(WriterGetCollapseLoop.lean) with `RangeOrder` as its invariant J. The steps:
at the space root the root gives way to its child (`rangeOrder_collapseRoot`),
at a segment root the segment leaf's klong names the root's child
(`rangeOrder_segCollapse`), in place (`takeBackRoot`) or by a new klong with
room (`replaceRoot`). The upward delete then needs no premise on root collapse
at a segment but cost's room in the segment leaf.
-/
import SIS.Tree.WriterGetCollapseLoop
import SIS.Tree.RangeUpTake

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The collapse steps at the space root keep the walk's ranges. -/
theorem writerWP_rootStep_space_range (x : NodeId) (only : Nat) (n : KNode) (c : Ctx)
    (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey) (hx : x = v.top.rootKey)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) :
    WriterWP (takeBackRoot x 0 only) c v (fun _ v' =>
      RangeOrder (wNode c.p base v') c.i v'.top.rootKey) ∧
    WriterWP (replaceRoot x 0 only) c v (fun _ v' =>
      RangeOrder (wNode c.p base v') c.i v'.top.rootKey) := by
  have hxt : v.taken.contains x = false := by rw [hx]; exact hI.1.2.1 _ TReach.root
  have hroot : wNode c.p base v v.top.rootKey = some n := by
    rw [← hx]; simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hnt := hI.1.2.2.1 _ n TReach.root hroot
  have hstep : ∀ child, n.ptr? only = some child → ∀ w3 : W, w3.top.rootKey = child →
      (∀ z, z ≠ v.top.rootKey → w3.taken.contains z = v.taken.contains z) →
      (∀ z, z ≠ v.top.rootKey → w3.nodes.lookup z = v.nodes.lookup z) →
      RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by
    intro child hptr w3 h3top h3t h3n
    obtain ⟨hy, honlyy⟩ := onlyLiveKlong_liveAt n c.i only child hnt honly hptr hcv
    rw [h3top]
    refine rangeOrder_collapseRoot (wNode c.p base v) (wNode c.p base w3) c.i
      v.top.rootKey child n hR hI.1.1 hroot hxl hy honlyy ?_
    intro z hz
    simp only [wNode, h3t z hz, h3n z hz]
  constructor
  · cases hp : n.ptr? only with
    | none =>
      unfold takeBackRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_takeBackRoot_spaceV _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3n, _⟩
      apply hstep child hp w3 h3top
      · intro z hz
        rw [h3t, List.contains_cons]
        have : (z == x) = false := by rw [hx]; simpa using hz
        simp [this]
      · intro z _; rw [h3n]
  · cases hp : n.ptr? only with
    | none =>
      unfold replaceRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_replaceRoot_spaceV _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, _, h3n⟩
      apply hstep child hp w3 h3top
      · intro z _; rw [h3t]
      · intro z hz; exact h3n z (by rw [hx]; exact hz)

/-- `takeBackRoot` at a segment root x that the transaction made, below the
segment leaf `leaf` of the path, keeps the walk's ranges (cost's
`writerWP_takeBackRoot_seg_coll`). -/
theorem writerWP_takeBackRoot_seg_range (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x)) :
    WriterWP (takeBackRoot x (d + 1) only) c v (fun _ v' =>
      RangeOrder (wNode c.p base v') c.i v'.top.rootKey) := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    rw [writerWP_getNode_known leaf ln c _ (by simpa using hlkL)]
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    split
    · rename_i j hj
      split
      · exact writerWP_throw _ _ _ _
      · simp only [putNode, writerWP_bind, writerWP_modify]
        refine (writerWP_takenBack_iff x c _ _).mpr ?_
        simp only
        have hLt' : (x :: v.taken).contains leaf = false := by
          rw [List.contains_cons]
          have : (leaf == x) = false := by simpa using hlx
          rw [this, Bool.false_or]; exact hLt
        have hyt : ∀ y, y ≠ x → (x :: v.taken).contains y = v.taken.contains y := by
          intro y hyx
          rw [List.contains_cons]
          have : (y == x) = false := by simpa using hyx
          simp [this]
        have hfin : ∀ w' : W, w'.vals = v.vals → w'.taken = x :: v.taken →
            w'.nodes = upsert v.nodes leaf (ln.repoint j child) → w'.top = v.top →
            RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
          intro w' h'v h't h'n h'top
          have hL' : wNode c.p base w' leaf = some (ln.repoint j child) := by
            simp only [wNode, h't, hLt', Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
          have hoth : ∀ y, y ≠ leaf → y ≠ x → wNode c.p base w' y = wNode c.p base v y := by
            intro y hyl hyx
            simp only [wNode, h't, hyt y hyx, h'n, lookup_upsert, hyl, ↓reduceIte]
          have hlinks : ∀ c' z, (c', z) ∈ (ln.repoint j child).liveAt c.i →
              (c' = k ∧ z = child) ∨ ((c', z) ∈ ln.liveAt c.i ∧ c' ≠ k) := by
            intro c' z hmm
            rw [KNode.liveAt_of_times _ c.i (KNode.repoint_times ln j child c.i hlnt)] at hmm
            have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
            rw [KNode.repoint_live_lookup ln x child k j hj c'] at hlk
            by_cases hck : k = c'
            · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
            · have hb : (k == c') = false := by simpa using hck
              rw [hb] at hlk
              simp only [Bool.false_eq_true, ↓reduceIte] at hlk
              refine Or.inr ⟨?_, Ne.symm hck⟩
              rw [KNode.liveAt_of_times ln c.i hlnt]
              exact mem_of_lookup_nodup _ c' z hlk
          rw [h'top]
          refine rangeOrder_segCollapse (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey leaf x
            child ln (ln.repoint j child) n k hR hT hlf hwL hlnl hk hwx hxl hcl ?_ hL'
            (by rw [mrg_repoint_leaf]; exact hlnl) ?_ hoth
          · intro c' z hz
            rw [KNode.liveAt_of_times n c.i hnt] at hz
            exact (hlv c' z).mp hz
          · intro c' z hz
            rcases hlinks c' z hz with h | ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h2, h1⟩
        exact hfin _ rfl rfl rfl rfl
    · exact writerWP_throw _ _ _ _

/-- `replaceRoot` at a segment root x below the segment leaf `leaf` of the
path, the leaf with room for the klong to x's child, keeps the walk's ranges
(cost's `writerWP_replaceRoot_seg_coll`). -/
theorem writerWP_replaceRoot_seg_range (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 1 + 1 ≤ c.p.M)
    (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (replaceRoot x (d + 1) only) c v (fun _ v' =>
      RangeOrder (wNode c.p base v') c.i v'.top.rootKey) := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_frameV x c _) ?_
    intro _ w1 ⟨h1t, h1top, _, h1v, h1l⟩
    have hlk1 : w1.nodes.lookup leaf = some ln := by rw [h1l leaf hlx]; exact hlkL
    refine writerWP_mono (writerWP_appendKlongs_room d leaf ln k child c w1 hlk1 hroom (hdead _)) ?_
    intro _ w2 h2
    subst h2
    have hL' : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } leaf =
        some (ln.add c.i (.key k child)) := by
      simp only [wNode, h1t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    have hoth : ∀ y, y ≠ leaf → y ≠ x →
        wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } y =
          wNode c.p base v y := by
      intro y hyl hyx
      simp only [wNode, h1t, lookup_upsert, hyl, ↓reduceIte, h1l y hyx]
    show RangeOrder _ c.i w1.top.rootKey
    rw [h1top]
    refine rangeOrder_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf x
      child ln (ln.add c.i (.key k child)) n k hR hT hlf hwL hlnl hk hwx hxl hcl ?_ hL'
      (by rw [KNode.add_leaf]; exact hlnl) ?_ hoth
    · intro c' z hz
      rw [KNode.liveAt_of_times n c.i hnt] at hz
      exact (hlv c' z).mp hz
    · intro c' z hmm
      rcases KNode.add_key_liveAt_mem ln c.i k child hlnwf hlnt c' z hmm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩


/-- Root collapse at any segment keeps `CollGetInv` and the walk's ranges, given
room in the segment leaf above each segment root that is replaced (cost's
`writerWP_collapseRoot_coll` with J the ranges). -/
theorem writerWP_collapseRoot_range (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w0 : W)
    (hroom : ∀ v x n leaf ln k, CollGetInv c base w0 v →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    ∀ fuel v, CollGetInv c base w0 v → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollGetInv c base w0 v' ∧
        RangeOrder (wNode c.p base v') c.i v'.top.rootKey) := by
  refine writerWP_collapseRoot_coll key seg c base hvc w0
    (fun v => RangeOrder (wNode c.p base v) c.i v.top.rootKey) ?_ hroom ?_ ?_
  · intro v v' hJ hr
    show RangeOrder (wNode c.p base v') c.i v'.top.rootKey
    rw [hr.1, hr.2.1]
    exact hJ
  · intro v x n only hI hJ hP hlk hxl hm honly hcv
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_range x only n c base w0 v hI hJ hx hlk honly hcv hxl).1
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      rw [hlen]
      exact writerWP_takeBackRoot_seg_range x ps0.length only n L ln k c base w0 v hI hJ hLr hLlk hLl
        hk hlk honly hcv hxl hpd hpk
  · intro v x n only hI hJ hP hlk hxl hm honly hcv
    have hP0 := hP
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_range x only n c base w0 v hI hJ hx hlk honly hcv hxl).2
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      obtain ⟨hroom1, hdead⟩ := hroom v x n L ln k hI hJ hP0 hlk hxl hm hLr hLlk hLl hk
      rw [hlen]
      exact writerWP_replaceRoot_seg_range x ps0.length only n L ln k c base w0 v hI hJ hLr hLlk hLl
        hk hlk honly hcv hxl hpd hpk hroom1 hdead

/-- The upward delete with the take-back keeps the walk's ranges, root collapse
at a segment included, given room in the segment leaf above each segment root
that is replaced (`rangeOrder_deleteUpward_upT` with `writerWP_collapseRoot_range`). -/
theorem rangeOrder_deleteUpward_upT_room (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat)
    (rk : NodeId) (w : W) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel)
    (hp : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i))
    (hk : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (K i), X i))
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (htimes : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hne : bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hTimesR : ∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hfit : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hnovalAll : ∀ y yn, wNode c.p base w y = some yn → wValue base w y = none)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hstopOK : ∀ s, s < depth → (∀ i, s < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
        deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
          (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
        deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
          false) ∧
      ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
        ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false))
    (hmerges : c.p.merges = false)
    (hroom : ∀ w0 v x n leaf ln k, CollGetInv c base w0 v →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) :=
  rangeOrder_deleteUpward_upT c base hvc X Nn K depth cv pre rk w hdepth hfuel hp hk hlk htk htimes
    hdist hne hall hleaf hT hR hwf hRt hTimesR hICE hfit hnovalAll hreach hlinkK hrk hcv hvisL huniq
    hstopOK hmerges (fun seg _ w' hI hRO => writerWP_mono
      (writerWP_collapseRoot_range (pre ++ [cv]) seg c base hvc w' (hroom w') c.p.fuel w' hI hRO)
      (fun _ _ h => h.2))

end SIS.Tree
