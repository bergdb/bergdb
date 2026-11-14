/-
Root collapse at any segment keeps the walk's ranges (bergdb 024-12, TP10;
`RangeOrder`): the root collapse's loop `writerWP_collapseRoot_inv`
(WriterGetCollapseLoop.lean) with `RangeOrder` in its invariant. The steps:
at the space root the root gives way to its child (`rangeOrder_collapseRoot`),
at a segment root the segment leaf's klong names the root's child
(`rangeOrder_segCollapse`), in place (`takeBackRoot`) or by a new klong with
room (`replaceRoot`). The upward delete then needs no premise on root collapse
at a segment but cost's room in the segment leaf.
-/
import SIS.Tree.WriterGetCollapseLoop
import SIS.Tree.WriterGetUpTake
import SIS.Tree.RangeUpAll

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The collapse steps at the space root keep the walk's ranges.
For any state with `CollInv` and well-formed klongs (`CollGetInv`, `CollGetInvF`). -/
theorem writerWP_rootStep_space_rangeG (x : NodeId) (only : Nat) (n : KNode) (c : Ctx)
    (base : View BVal) (v : W) (A B E : Prop)
    (hI : CollInv c base v ∧ A ∧ B ∧ (∀ y yn, TReach (wNode c.p base v) c.i v.top.rootKey y →
      wNode c.p base v y = some yn → klongsWf yn.ks = true) ∧ E)
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
segment leaf `leaf` of the path, keeps the walk's ranges.
For any state with `CollInv` and well-formed klongs (`CollGetInv`, `CollGetInvF`). -/
theorem writerWP_takeBackRoot_seg_rangeG (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (v : W) (A B E : Prop)
    (hI : CollInv c base v ∧ A ∧ B ∧ (∀ y yn, TReach (wNode c.p base v) c.i v.top.rootKey y →
      wNode c.p base v y = some yn → klongsWf yn.ks = true) ∧ E)
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
              exact bk_mem_of_lookup _ c' z hlk
          rw [h'top]
          refine rangeOrder_segCollapse (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey leaf x
            child ln (ln.repoint j child) n k hR hT hlf hwL hlnl hk hwx hxl hcl ?_ hL'
            (by rw [bk_repoint_leaf]; exact hlnl) ?_ hoth
          · intro c' z hz
            rw [KNode.liveAt_of_times n c.i hnt] at hz
            exact (hlv c' z).mp hz
          · intro c' z hz
            rcases hlinks c' z hz with h | ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h2, h1⟩
        exact hfin _ rfl rfl rfl rfl
    · exact writerWP_throw _ _ _ _

end SIS.Tree
