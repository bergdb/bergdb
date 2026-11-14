/-
The upward delete with the take-back (bergdb 024-22): a node of the chain made
by the transaction is taken back, its parent retargeted; the stop node may be
retargeted so. Shape lemmas: what a node's klongs give without the pointers.
-/
import SIS.Tree.WriterGetUpAll

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node's klongs without their pointers. -/
def KNode.shapeOf (n : KNode) : KNode := { n with ks := n.ks.map klongShape }

theorem KNode.size_shapeOf (n : KNode) : n.shapeOf.size = n.size := by
  simp [KNode.shapeOf, KNode.size]

theorem KNode.lastBitmap_shapeOf (n : KNode) : n.shapeOf.lastBitmap = n.lastBitmap :=
  lastBitmapOf_map_shape n.ks

theorem KNode.lastTime_shapeOf (n : KNode) : n.shapeOf.lastTime = n.lastTime := by
  unfold KNode.lastTime KNode.shapeOf
  rw [List.foldl_map]
  congr 1
  funext t k
  cases k <;> rfl

theorem KNode.bitsOf_shapeOf (n : KNode) (c : Nat) : n.shapeOf.bitsOf c = n.bitsOf c := by
  unfold KNode.bitsOf KNode.shapeOf
  simp only [List.zipIdx_map, List.filterMap_map]
  congr 1
  funext q
  rcases q with ⟨k, i⟩
  cases k <;> rfl

theorem KNode.deadCount_shapeOf (n : KNode) : n.shapeOf.deadCount = n.deadCount := by
  unfold KNode.deadCount
  rw [KNode.lastBitmap_shapeOf]
  simp only [KNode.shapeOf, List.zipIdx_map, List.filter_map, List.length_map]
  congr 2
  funext q
  rcases q with ⟨k, i⟩
  cases k with
  | key c y =>
    simp only [Function.comp_def, Prod.map, id, klongShape, ← List.map_drop, List.any_map]
    congr 2
    funext k'
    cases k' <;> rfl
  | time t => rfl
  | del b => rfl

theorem KNode.shapeOf_eq_iff (a b : KNode) :
    a.shapeOf = b.shapeOf ↔ a.leaf = b.leaf ∧ a.ks.map klongShape = b.ks.map klongShape := by
  unfold KNode.shapeOf
  constructor
  · intro h; cases a; cases b; simp only [KNode.mk.injEq] at h ⊢; exact h
  · rintro ⟨h1, h2⟩; cases a; cases b; simp only [KNode.mk.injEq] at h1 h2 ⊢; exact ⟨h1, h2⟩

theorem KNode.lastBitmap_of_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) :
    a.lastBitmap = b.lastBitmap := by
  rw [← KNode.lastBitmap_shapeOf a, h, KNode.lastBitmap_shapeOf]

theorem KNode.lastTime_of_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) :
    a.lastTime = b.lastTime := by
  rw [← KNode.lastTime_shapeOf a, h, KNode.lastTime_shapeOf]

theorem KNode.bitsOf_of_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) (c : Nat) :
    a.bitsOf c = b.bitsOf c := by
  rw [← KNode.bitsOf_shapeOf a, h, KNode.bitsOf_shapeOf]

theorem KNode.size_of_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) : a.size = b.size := by
  rw [← KNode.size_shapeOf a, h, KNode.size_shapeOf]

theorem KNode.deadCount_of_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) :
    a.deadCount = b.deadCount := by
  rw [← KNode.deadCount_shapeOf a, h, KNode.deadCount_shapeOf]

theorem deadOver_of_shapeOf (p : Params) {a b : KNode} (h : a.shapeOf = b.shapeOf) :
    deadOver p a = deadOver p b := by
  unfold deadOver; rw [KNode.deadCount_of_shapeOf h]

theorem KNode.setAt_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) (i : Nat) (k : Klong) :
    (a.setAt i k).shapeOf = (b.setAt i k).shapeOf := by
  rw [KNode.shapeOf_eq_iff] at h ⊢
  simp only [KNode.setAt, List.map_set, h.2]
  exact ⟨h.1, trivial⟩

theorem KNode.add_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) (t : Time) (k : Klong) :
    (a.add t k).shapeOf = (b.add t k).shapeOf := by
  have ht := KNode.lastTime_of_shapeOf h
  rw [KNode.shapeOf_eq_iff] at h ⊢
  unfold KNode.add
  rw [ht]
  split
  · split <;> simp only [List.map_append, h.2] <;> exact ⟨h.1, trivial⟩
  · simp only [List.map_append, h.2]; exact ⟨h.1, trivial⟩

theorem KNode.repoint_shapeOf (a : KNode) (i : Nat) (y : NodeId) :
    (a.repoint i y).shapeOf = a.shapeOf := by
  rw [KNode.shapeOf_eq_iff]
  refine ⟨?_, KNode.repoint_shape a i y⟩
  unfold KNode.repoint
  split <;> rfl

theorem lebNode_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) (tt : Time) (htd lip : Bool)
    (e jcv : Nat) (jy : NodeId) :
    (lebNode a tt htd lip e jcv jy).shapeOf = (lebNode b tt htd lip e jcv jy).shapeOf := by
  unfold lebNode
  simp only
  rw [KNode.lastBitmap_of_shapeOf h, KNode.bitsOf_of_shapeOf h, KNode.size_of_shapeOf h]
  have h1 : (if htd then a.setAt (b.size - 1) (.del (bitsUnion b.lastBitmap (b.bitsOf jcv)))
      else a.add tt (.del (bitsUnion b.lastBitmap (b.bitsOf jcv)))).shapeOf =
      (if htd then b.setAt (b.size - 1) (.del (bitsUnion b.lastBitmap (b.bitsOf jcv)))
      else b.add tt (.del (bitsUnion b.lastBitmap (b.bitsOf jcv)))).shapeOf := by
    cases htd
    · exact KNode.add_shapeOf h _ _
    · exact KNode.setAt_shapeOf h _ _
  cases lip
  · exact KNode.add_shapeOf h1 _ _
  · simp only [↓reduceIte, KNode.repoint_shapeOf]; exact h1

theorem KNode.retarget_shapeOf (n : KNode) (ti : Nat) (src dst : NodeId) :
    ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).shapeOf = n.shapeOf := by
  rw [KNode.shapeOf_eq_iff]
  exact ⟨rfl, retargetKlongs_shape n.ks ti src dst⟩

/-- A node retargeted from src to dst: its live klongs other than of compare
value K are the node's, if src is named only by K's. -/
theorem KNode.retarget_liveAt_ne (n : KNode) (ti : Nat) (src dst : NodeId) (t : Time) (K : Nat)
    (hu : ∀ c', (c', src) ∈ n.liveAt t → c' = K) :
    ∀ c' z, ((c', z) ∈ ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).liveAt t ∧ c' ≠ K) ↔
      ((c', z) ∈ n.liveAt t ∧ c' ≠ K) := by
  intro c' z
  constructor
  · rintro ⟨h, hc⟩
    rcases KNode.retarget_liveAt n ti src dst t c' z h with h1 | ⟨_, h2⟩
    · exact ⟨h1, hc⟩
    · exact absurd (hu c' h2) hc
  · rintro ⟨h, hc⟩
    refine ⟨KNode.retarget_liveAt_of n ti src dst t c' z h ?_, hc⟩
    intro hz
    rw [hz] at h
    exact hc (hu c' h)

/-- `collGetInv_after_up` with nodes of the chain taken back: the taken nodes
agree but at the chain. -/
theorem collGetInv_after_upT (c : Ctx) (base : View BVal) (X : Nat → NodeId) (Nn : Nat → KNode)
    (K : Nat → Nat) (depth : Nat) (w : W)
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
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
    (stop : Nat) (w' : W) (sn' : KNode) (f : Nat → Nat) (hsD : stop < depth)
    (ht : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y)
    (htop : w'.top = w.top) (hv : w'.vals = w.vals)
    (hnodes : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
      w'.nodes.lookup y = w.nodes.lookup y)
    (hsn' : w'.nodes.lookup (X stop) = some sn') (hsl' : sn'.leaf = (Nn stop).leaf)
    (hsw' : klongsWf sn'.ks = true) (hst' : ∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i)
    (hlive' : ∀ c' z, (c', z) ∈ sn'.liveAt c.i →
      ∃ c0, (c0, z) ∈ (Nn stop).liveAt c.i ∧ c0 ≠ K (stop + 1) ∧ f c0 = c') :
    CollGetInv c base w' w' := by
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  -- the tree after, at tree level
  have hagree : ∀ u, u ≠ X stop → (∀ i, stop < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w' u = wNode c.p base w u := by
    intro u hus hnc
    simp only [wNode, ht u hnc, hnodes u hus hnc]
  have hsnw : wNode c.p base w' (X stop) = some sn' := by
    simp only [wNode, ht (X stop) (fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega),
      htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  have hlive1 : ∀ c' z, (c', z) ∈ sn'.liveAt c.i → ∃ c0, (c0, z) ∈ (Nn stop).liveAt c.i ∧ c0 ≠ K (stop + 1) :=
    fun c' z h => by obtain ⟨c0, h1, h2, _⟩ := hlive' c' z h; exact ⟨c0, h1, h2⟩
  have hdist' : ∀ i i', stop ≤ i → i ≤ depth → stop ≤ i' → i' ≤ depth → X i = X i' → i = i' :=
    fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he
  have hNs : ∀ i, stop ≤ i → i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i _ h2 => hN i h2
  have hlinks : ∀ i, stop < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i :=
    fun i h1 h2 => hlinkK i (by omega) h2
  rw [← htop] at hT hwf hRt hTimesR hICE hfit hreach
  have hT' := treeOK_up_tr (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
    hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw f hlive'
  have hsub := tReach_up_sub_tr (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
    hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw hlive1
  have hlsub := tLink_up_sub_tr (wNode c.p base w) (wNode c.p base w') c.i w'.top.rootKey X Nn K stop depth
    hsD hT (hreach stop (by omega)) hNs hlinks hdist' hagree sn' hsnw hlive1
  have hV : wValue base w' = wValue base w :=
    wValue_eq_of_taken base w w' hv (fun y => ∃ k, stop < k ∧ k ≤ depth ∧ y = X k)
      (fun y hy => ht y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
      (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk k h2, hnovalAll _ _ (hN k h2)⟩)
  -- a reached node's node after: the stop node's, or the one before
  have hnode : ∀ y yn, TReach (wNode c.p base w') c.i w'.top.rootKey y → wNode c.p base w' y = some yn →
      (y = X stop ∧ yn = sn') ∨ wNode c.p base w y = some yn := by
    intro y yn hy hyn
    by_cases hys : y = X stop
    · left; rw [hys, hsnw] at hyn; exact ⟨hys, (Option.some.inj hyn).symm⟩
    · right; rw [← hagree y hys (hsub y hy).2]; exact hyn
  show CollGetInv c base w' w'
  refine ⟨⟨hT', fun y hy => by rw [ht y (hsub y hy).2]; exact hRt y (hsub y hy).1, ?_, ?_⟩, fun _ => rfl, ?_, ?_, ?_⟩
  · intro y yn hy hyn
    rcases hnode y yn hy hyn with ⟨_, rfl⟩ | h
    · exact hst'
    · exact hTimesR y yn (hsub y hy).1 h
  · intro y yn cc z hy hyn hyl hcz
    have hzR : TReach (wNode c.p base w') c.i w'.top.rootKey z := TReach.link hy ⟨yn, hyn, hcz⟩
    obtain ⟨cc0, hl⟩ := hlsub y cc z hy ⟨yn, hyn, hcz⟩
    obtain ⟨m0, hm0, hcm0⟩ := hl
    by_cases hzs : z = X stop
    · exact ⟨sn', by rw [hzs]; exact hsnw⟩
    · rw [hagree z hzs (hsub z hzR).2]
      have hyN := (hsub y hy).1
      have hm0l : m0.leaf = false := by
        rcases hnode y yn hy hyn with ⟨hys, rfl⟩ | h
        · rw [hys, hN stop (by omega)] at hm0
          cases hm0
          rw [← hsl']; exact hyl
        · rw [h] at hm0; cases hm0; exact hyl
      exact hICE y m0 cc0 z hyN hm0 hm0l hcm0
  · refine segFits_transfer _ _ c.i _ _ _ hfit
      (fun u hu => tReach_reachS _ _ _ _ (hsub u (reachS_tReach _ _ _ _ hu)).1)
      (fun u un' hu hun' hl => ?_)
    rcases hnode u un' (reachS_tReach _ _ _ _ hu) hun' with ⟨hus, rfl⟩ | h
    · refine ⟨Nn stop, by rw [hus]; exact hN stop (by omega), by rw [← hsl']; exact hl,
        fun c' y' hy' => ?_⟩
      obtain ⟨c0, h1, _, _⟩ := hlive' c' y' hy'
      exact ⟨c0, h1⟩
    · exact ⟨un', h, hl, fun c' y' hy' => ⟨c', hy'⟩⟩
  · intro y yn hy hyn
    rcases hnode y yn hy hyn with ⟨_, rfl⟩ | h
    · exact hsw'
    · exact hwf y yn (hsub y hy).1 h
  · intro y yn hy hyn
    rw [hV]
    rcases hnode y yn hy hyn with ⟨hys, _⟩ | h
    · rw [hys]; exact hnovalAll _ _ (hN stop (by omega))
    · exact hnovalAll y yn h

end SIS.Tree
