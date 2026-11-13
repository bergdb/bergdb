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

/-- `retarget` with the whole frame. -/
theorem writerWP_retarget_frameW (p src dst : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some n) :
    WriterWP (retarget p src dst) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧
      (∀ y, y ≠ p → w'.nodes.lookup y = w.nodes.lookup y) ∧
      ∃ n', w'.nodes.lookup p = some n' ∧
        (n' = n ∨ ∃ ti, n' = { n with ks := retargetKlongs n.ks ti src dst })) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p n c w hlk]
  split
  · unfold putNode
    refine (writerWP_modify _ c w _).mpr ?_
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun y hy => ?_, { n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst },
      ?_, Or.inr ⟨_, rfl⟩⟩
    · show (upsert w.nodes p _).lookup y = _
      rw [lookup_upsert]; simp [hy]
    · show (upsert w.nodes p _).lookup p = _
      rw [lookup_upsert]; simp only [↓reduceIte]; rfl
  · refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, n, hlk, Or.inl rfl⟩

/-- `takeBack` of x with parent p: x is taken, p's node is retargeted from x or
kept; nothing else changes. -/
theorem writerWP_takeBack_frame (x p : NodeId) (cv : Nat) (pn : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) :
    WriterWP (takeBack x p cv) c w (fun _ w' => w'.taken = x :: w.taken ∧ w'.top = w.top ∧
      w'.vals = w.vals ∧ w'.path = w.path ∧
      (∀ y, y ≠ p → w'.nodes.lookup y = w.nodes.lookup y) ∧
      ∃ n', w'.nodes.lookup p = some n' ∧
        (n' = pn ∨ ∃ ti dst, n' = { pn with ks := retargetKlongs pn.ks ti x dst })) := by
  unfold takeBack replacedBy
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c w hlk]
  simp only [writerWP_get, writerWP_pure]
  split
  · rename_i old _ _ _
    split
    · exact writerWP_throw _ _ _ _
    · rw [writerWP_bind]
      refine writerWP_mono (writerWP_retarget_frameW p x old pn c w hlk) ?_
      rintro _ w1 ⟨h1t, h1top, h1v, h1p, _, h1n, n', h1l, hn'⟩
      rw [writerWP_bind]
      refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine ⟨by simp [h1t], h1top, h1v, h1p, h1n, n', h1l, ?_⟩
      rcases hn' with h | ⟨ti, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨ti, old, h⟩
  · exact writerWP_throw _ _ _ _

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
    (hfit : PathsFit (wNode c.p base w) c.i w.top.rootKey c.p.fuel)
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
  · intro z k hz
    apply hfit z k
    induction hz with
    | root => exact PathLen.root
    | link hx hl ih => obtain ⟨c0, h0⟩ := hlsub _ _ _ hx.reach hl; exact PathLen.link ih h0
  · intro y yn hy hyn
    rcases hnode y yn hy hyn with ⟨_, rfl⟩ | h
    · exact hsw'
    · exact hwf y yn (hsub y hy).1 h
  · intro y yn hy hyn
    rw [hV]
    rcases hnode y yn hy hyn with ⟨hys, _⟩ | h
    · rw [hys]; exact hnovalAll _ _ (hN stop (by omega))
    · exact hnovalAll y yn h

set_option linter.unusedSimpArgs false in
/-- The upward delete at the writer's level with the take-back (deleteUpward's UP
path): the key's leaf X depth, with cv its only live compare value, emptied; each
node of the chain below the stop node is taken back (its parent retargeted from
it) if the transaction made it, else unlinked; the stop node X stop, perhaps so
retargeted, gets its bitmap with room, or LE-b with room; the merges off. Then
the state before root collapse reads the key as nothing and every other key as
before, and what follows (`hcoll`, `hleafQ`, `hcollLeb`) is what the delete
gives. The taken nodes after agree with those before but at the chain. -/
theorem writerWP_deleteUpward_upT_get (c : Ctx) (base : View BVal) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat) (rk : NodeId)
    (w : W) (Q : W → Prop) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel)
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
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hnoval : ∀ i, i ≤ depth → wValue base w (X i) = none)
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
    (hcoll : ∀ (seg stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' => Q w''))
    (hleafQ : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      Q w')
    (hcollLeb : ∀ (seg stop : Nat) (w' : W) (sn' : KNode) (jcv : Nat) (jy : NodeId), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) → (Nn stop).leaf = false → K (stop + 1) = 0 →
      (jcv, jy) ∈ (Nn stop).liveAt c.i → 0 < jcv →
      (∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' ≠ 0 → jcv ≤ c') →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔
        (c' = 0 ∧ z = jy) ∨ ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ jcv)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' => Q w'')) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' => Q w') := by
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w (hlk depth (Nat.le_refl _))]
  have hne' : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = false := by
    simpa using hne
  simp only [hne', hall, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_climb c X Nn K depth w hp hk hlk) ?_
  rintro stop w1 ⟨hw1, hst, hbetween, hmadeOK, hstopNode, hself⟩
  have hw1' := hw1.symm
  subst hw1'
  have hsd : stop ≠ depth := fun h => by have := (hself h).1; omega
  have hsd' : (stop == depth) = false := by simpa using hsd
  simp only [hsd', Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by omega
  obtain ⟨hbitRoom, hlebRoom⟩ := hstopOK stop hsD hbetween
  rw [writerWP_bind]
  refine (writerWP_note_iff _ c w _).mpr ?_
  generalize hw0 : ({ w with trail := "up.climb" :: w.trail } : W) = w0
  have h0n : w0.nodes = w.nodes := by rw [← hw0]
  have h0p : w0.path = w.path := by rw [← hw0]
  have h0t : w0.taken = w.taken := by rw [← hw0]
  have h0top : w0.top = w.top := by rw [← hw0]
  have h0v : w0.vals = w.vals := by rw [← hw0]
  rw [writerWP_bind, writerWP_get, writerWP_bind]
  refine writerWP_mono (writerWP_foldlM_getNode c (fun s n => if n.leaf = true then s + 1 else s)
    (List.take stop w0.path) 0 w0 ?_) ?_
  · intro e he
    obtain ⟨i, hie⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_take] at hie
    split at hie
    · rename_i hi
      have h1 := hp i (by omega)
      rw [← h0p, hie] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [h1, h0n]
      exact ⟨_, hlk i (by omega)⟩
    · cases hie
  rintro seg w0' hw0'
  have hw0'' := hw0'.symm
  subst hw0''
  -- the loop: the chain's nodes unlinked or taken back
  let I : List Nat → W → Prop := fun rem v =>
    v.top = w0.top ∧ v.vals = w0.vals ∧ v.path = w0.path ∧
    (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.taken.contains y = w0.taken.contains y) ∧
    (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.nodes.lookup y = w0.nodes.lookup y) ∧
    ∃ a0, rem = List.range' a0 (depth - stop - a0) ∧ a0 ≤ depth - stop ∧
      (∀ j, a0 < j → j ≤ depth - stop → v.nodes.lookup (X (depth - j)) = some (Nn (depth - j))) ∧
      ∃ S, v.nodes.lookup (X (depth - a0)) = some S ∧
        (S = Nn (depth - a0) ∨ ∃ ti dst, S = { Nn (depth - a0) with
          ks := retargetKlongs (Nn (depth - a0)).ks ti (X (depth - a0 + 1)) dst })
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_forIn_inv c I _ ?_ (List.range (depth - stop)) w0
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, 0, by rw [List.range_eq_range']; rfl, Nat.zero_le _,
      fun j _ hj => by rw [h0n]; exact hlk _ (by omega),
      Nn (depth - 0), by rw [h0n]; exact hlk _ (by omega), Or.inl rfl⟩) ?_
  · intro a rest v ⟨hvtop, hvv, hvp, hvt, hvn, a0, hrem, ha0, hexact, S, hSl, hS⟩
    have hlen : 0 < depth - stop - a0 := by
      rcases h : depth - stop - a0 with _ | m
      · rw [h] at hrem; simp at hrem
      · omega
    have hra : a = a0 ∧ rest = List.range' (a0 + 1) (depth - stop - (a0 + 1)) := by
      rw [show depth - stop - a0 = (depth - stop - (a0 + 1)) + 1 by omega, List.range'_succ] at hrem
      simp only [List.cons.injEq] at hrem
      exact hrem
    obtain ⟨hae, hrest⟩ := hra
    subst hae
    have hpar : v.nodes.lookup (X (depth - (a + 1))) = some (Nn (depth - (a + 1))) :=
      hexact (a + 1) (by omega) (by omega)
    have hpne : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → y ≠ X (depth - (a + 1)) := by
      intro y hys hy he
      rcases Nat.lt_or_ge stop (depth - (a + 1)) with h | h
      · exact hy _ h (by omega) he
      · exact hys (by rw [he, show depth - (a + 1) = stop by omega])
    simp only [writerWP_bind]
    refine writerWP_pathNode_known (depth - a) (X (depth - a)) c v
      (by rw [hvp, h0p]; exact hp _ (by omega)) _ ?_
    rw [writerWP_getNode_known _ _ c v hSl]
    split
    · simp only [writerWP_bind]
      refine writerWP_pathNode_known (depth - a - 1) (X (depth - (a + 1))) c v
        (by rw [hvp, h0p, show depth - a - 1 = depth - (a + 1) by omega]; exact hp _ (by omega)) _ ?_
      refine writerWP_klongAt_known (depth - a) (K (depth - a)) (X (depth - a)) c v
        (by rw [hvp, h0p]; exact hk _ (by omega) (by omega)) _ ?_
      refine writerWP_mono (writerWP_takeBack_frame _ _ _ _ c v hpar) ?_
      rintro _ v2 ⟨h2t, h2top, h2v, h2p, h2n, n', h2l, hn'⟩
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp, fun y hy => ?_,
        fun y hys hy => ?_, a + 1, hrest, by omega, fun j h1 h2 => ?_, n', h2l, ?_⟩
      · have hne : (y == X (depth - a)) = false := by
          simpa using hy (depth - a) (by omega) (by omega)
        rw [h2t, List.contains_cons, hne, Bool.false_or]
        exact hvt y hy
      · rw [h2n y (hpne y hys hy)]
        exact hvn y hys hy
      · rw [h2n _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hexact j (by omega) h2
      · rw [show depth - (a + 1) + 1 = depth - a by omega]
        exact hn'
    · simp only [writerWP_bind]
      refine (writerWP_note_iff _ c v _).mpr ?_
      refine writerWP_mono (writerWP_unlink_frameP _ _ c _ hSl) ?_
      rintro _ v2 ⟨h2t, h2top, _, h2v, h2p, _, h2l⟩
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp,
        fun y hy => by rw [h2t]; exact hvt y hy, fun y hys hy => ?_, a + 1, hrest, by omega,
        fun j h1 h2 => ?_, Nn (depth - (a + 1)), ?_, Or.inl rfl⟩
      · rw [h2l y (hy (depth - a) (by omega) (by omega)), hvn y hys hy]
      · rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hexact j (by omega) h2
      · rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hpar
  rintro _ w2 ⟨h2top, h2v, h2p, h2t, h2n, a0, hrem, ha0, _, S, hSl, hS⟩
  have ha0' : a0 = depth - stop := by
    rcases h : depth - stop - a0 with _ | m
    · omega
    · rw [h, List.range'_succ] at hrem; cases hrem
  subst ha0'
  rw [show depth - (depth - stop) = stop by omega] at hSl hS
  simp only [writerWP_bind]
  refine writerWP_pathNode_known stop (X stop) c w2 (by rw [h2p, h0p]; exact hp stop (by omega)) _ ?_
  refine writerWP_klongAt_known (stop + 1) (K (stop + 1)) (X (stop + 1)) c w2
    (by rw [h2p, h0p]; exact hk _ (by omega) (by omega)) _ ?_
  rw [writerWP_getNode_known _ _ c w2 hSl]
  refine writerWP_ghOf_cached _ _ c w2 hSl _ (fun gh => ?_)
  have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
    fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn stop).ks → s' ≤ c.i := htimes stop (by omega)
  have hsx : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
    have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1))) ≠ (Nn stop).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx
    exact List.mem_map.mpr ⟨_, hsx, rfl⟩
  have hswf : klongsWf (Nn stop).ks = true := by
    have := hwf (X stop) (Nn stop) (hreach stop (by omega))
      (by simp only [wNode, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hlk stop (by omega)])
    exact this
  -- the stop node now: its node before, or that retargeted from the chain
  have hu : ∀ c', (c', X (stop + 1)) ∈ (Nn stop).liveAt c.i → c' = K (stop + 1) := by
    intro c' h
    have hNs : wNode c.p base w (X stop) = some (Nn stop) := by
      simp only [wNode, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hlk stop (by omega)]
    exact (hT.oneLink _ _ _ _ _ (hreach stop (by omega)) (hreach stop (by omega)) ⟨_, hNs, h⟩
      ⟨_, hNs, hsx⟩).2
  have hSf : S.shapeOf = (Nn stop).shapeOf ∧ S.leaf = (Nn stop).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (stop + 1)) ↔
        ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  -- the chain's facts
  have hone : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
    intro i h1 h2 c' z hm
    have ht := htimes i (by omega)
    have hm' : (c', z) ∈ (Nn i).live := by rw [← KNode.liveAt_of_times _ c.i ht]; exact hm
    have hc := allKeysIn_live_cv (Nn i) (K (i + 1)) (hbetween i h1 h2) c' z hm'
    have hl := hlinkK (i + 1) (by omega) (by omega)
    rw [show i + 1 - 1 = i by omega] at hl
    rw [KNode.liveAt_of_times _ c.i ht] at hl
    have hnd := KNode.live_keys_nodup (Nn i)
    have e1 := lookup_some_of_mem hnd hm'
    have e2 := lookup_some_of_mem hnd hl
    rw [hc] at e1
    rw [e1] at e2
    exact Option.some.inj e2
  have honly : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → c' = cv := by
    intro c' z hm
    have hm' : (c', z) ∈ (Nn depth).live := by
      rw [← KNode.liveAt_of_times _ c.i (htimes depth (Nat.le_refl _))]; exact hm
    exact allKeysIn_live_cv (Nn depth) cv hall c' z hm'
  -- the bitmap at the stop node, from any state with w2's nodes
  have hbit : ((Nn stop).leaf = true ∨ K (stop + 1) ≠ 0) →
      ∀ (v : W), v.nodes = w2.nodes → v.taken = w2.taken → v.top = w2.top → v.vals = w2.vals →
      ∀ (post : W → Prop), (∀ w3 n',
        (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w3.taken.contains y = w.taken.contains y) →
        w3.top = w.top → w3.vals = w.vals →
        (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
          w3.nodes.lookup y = w.nodes.lookup y) →
        w3.nodes.lookup (X stop) = some n' → n'.leaf = (Nn stop).leaf → klongsWf n'.ks = true →
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) →
        (∀ c' z, (c', z) ∈ n'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
        (∀ key', keyWf key' = true → wGet c.p c.i base w3 key' =
          if pre ++ [cv] == key' then none else wGet c.p c.i base w key') → post w3) →
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v (fun _ w3 => post w3) := by
    intro hkind v hvn hvt hvtop hvv post hpost
    obtain ⟨hroom, hd1, hd2⟩ := hbitRoom hkind
    have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))) ≠ S.lastBitmap := by
      rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
    have hroom' : S.size + 1 < c.p.M := by rw [KNode.size_of_shapeOf hSsh]; exact hroom
    have hd1' : deadOver c.p (S.setAt (S.size - 1)
        (.del (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1)))))) = false := by
      rw [deadOver_of_shapeOf c.p (KNode.setAt_shapeOf hSsh _ _), KNode.size_of_shapeOf hSsh,
        KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]
      exact hd1
    have hd2' : deadOver c.p (S.add c.i (.del (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1)))))) =
        false := by
      rw [deadOver_of_shapeOf c.p (KNode.add_shapeOf hSsh _ _),
        KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]
      exact hd2
    refine writerWP_mono (writerWP_appendDeleteKlong_room_frame (X stop) stop (K (stop + 1)) S
      c v (by rw [hvn]; exact hSl) hSt hSwf hneS' hroom' hd1' hd2') ?_
    rintro _ w3 ⟨h3t, h3top, h3v, _, _, _, n', h3n, hn'l, hn'w, hn't, hn'lk⟩
    have h3tw : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w3.taken.contains y = w.taken.contains y := by
      intro y hy; rw [h3t, hvt, h2t y hy, h0t]
    have h3top' : w3.top = w.top := by rw [h3top, hvtop, h2top, h0top]
    have h3v' : w3.vals = w.vals := by rw [h3v, hvv, h2v, h0v]
    have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w3.nodes.lookup y = w.nodes.lookup y := by
      intro y hys hnc
      rw [h3n, lookup_upsert]
      simp only [hys, ↓reduceIte]
      rw [hvn, h2n y hys hnc, h0n]
    have hsn3 : w3.nodes.lookup (X stop) = some n' := by rw [h3n, lookup_upsert]; simp
    have hlive' : ∀ c' z, (c', z) ∈ n'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1) := by
      intro c' z
      rw [liveAt_iff_of_delete_lookup S n' c.i (K (stop + 1)) hSt hn't hn'lk c' z]
      exact hSlive c' z
    refine hpost w3 n' h3tw h3top' h3v' hfr hsn3 (by rw [hn'l, hSleaf]) hn'w hn't hlive' ?_
    intro key' hkw
    have hV3 : wValue base w3 = wValue base w :=
      wValue_eq_of_taken base w w3 h3v' (fun y => ∃ k, stop < k ∧ k ≤ depth ∧ y = X k)
        (fun y hy => h3tw y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
        (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk k h2, hnoval k h2⟩)
    have hagree : ∀ u, TReach (wNode c.p base w) c.i w.top.rootKey u → u ≠ X stop →
        (∀ i, stop < i → i ≤ depth → u ≠ X i) → wNode c.p base w3 u = wNode c.p base w u := by
      intro u _ hus hnc
      simp only [wNode, h3tw u hnc, hfr u hus hnc]
    have hsnw : wNode c.p base w3 (X stop) = some n' := by
      simp only [wNode, h3tw (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn3]
    unfold wGet
    rw [hV3, h3top']
    cases hl : (Nn stop).leaf with
    | false =>
      have hK0 : K (stop + 1) ≠ 0 := by
        rcases hkind with h | h
        · rw [hl] at h; cases h
        · exact h
      exact getFromR_up_inner (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
        (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
        (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
        (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
        hrk hcv hvisL huniq hagree n' hl hsnw (by rw [hn'l, hSleaf]; exact hl) hlive' key' hkw
    | true =>
      exact getFromR_up_leaf (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
        (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
        (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
        (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
        hrk hcv hvisL huniq hagree n' hl hsnw (by rw [hn'l, hSleaf]; exact hl) hn'w hlive' key' hkw
  cases hsl : (Nn stop).leaf with
  | true =>
    have hsl' : S.leaf = true := hSleaf.trans hsl
    simp only [hsl', ↓reduceIte, writerWP_bind]
    refine (writerWP_note_iff _ c w2 _).mpr ?_
    refine hbit (Or.inl hsl) _ ?_ ?_ ?_ ?_ _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread
      unfold afterDelete
      simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
      exact hleafQ stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread
    all_goals rfl
  | false =>
    have hsl' : S.leaf = false := hSleaf.trans hsl
    simp only [hsl', Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    by_cases hK0 : K (stop + 1) = 0
    · -- LE-b
      have hK0' : (K (stop + 1) != 0) = false := by simp [hK0]
      simp only [hK0', Bool.false_eq_true, ↓reduceIte, writerWP_bind, hmerges]
      obtain ⟨hroomL, hdeadL⟩ := hlebRoom hsl hK0
      have hroomL' : S.size + 3 ≤ c.p.M := by rw [KNode.size_of_shapeOf hSsh]; exact hroomL
      have hdeadL' : ∀ b1 b2 e jcv jy, deadOver c.p (lebNode S c.i b1 b2 e jcv jy) = false := by
        intro b1 b2 e jcv jy
        rw [deadOver_of_shapeOf c.p (lebNode_shapeOf hSsh _ _ _ _ _ _)]
        exact hdeadL _ _ _ _ _
      refine writerWP_mono (writerWP_emptyKeyNext_room_frame (X stop) stop S c w2 hSl hSwf hSt
        hroomL' hdeadL') ?_
      rintro _ w3 ⟨h3t, h3top, h3v, _, _, _, n', jcv, jy, h3n, hn'l, hn'w, hn't, hjS, hj0, hmin, hn'lk⟩
      have hj : (jcv, jy) ∈ (Nn stop).liveAt c.i :=
        ((hSlive jcv jy).mp ⟨hjS, by rw [hK0]; omega⟩).1
      have h3tw : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w3.taken.contains y = w.taken.contains y := by
        intro y hy; rw [h3t, h2t y hy, h0t]
      have h3top' : w3.top = w.top := by rw [h3top, h2top, h0top]
      have h3v' : w3.vals = w.vals := by rw [h3v, h2v, h0v]
      have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
          w3.nodes.lookup y = w.nodes.lookup y := by
        intro y hys hnc
        rw [h3n, lookup_upsert]
        simp only [hys, ↓reduceIte]
        rw [h2n y hys hnc, h0n]
      have hsn3 : w3.nodes.lookup (X stop) = some n' := by rw [h3n, lookup_upsert]; simp
      have hliveS := liveAt_iff_of_leb_lookup S n' c.i jcv jy hSt hn't hn'lk
      have hlive' : ∀ c' z, (c', z) ∈ n'.liveAt c.i ↔
          (c' = 0 ∧ z = jy) ∨ ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ jcv) := by
        intro c' z
        rw [hliveS c' z]
        have e := hSlive c' z
        rw [hK0] at e
        constructor
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨(e.mp ⟨h1, h2⟩).1, h2, h3⟩
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨(e.mpr ⟨h1, h2⟩).1, h2, h3⟩
      have hmin' : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' = 0 ∨ jcv ≤ c' := by
        intro c' z hm
        by_cases hc : c' = 0
        · exact Or.inl hc
        · right
          have hm' := ((hSlive c' z).mpr ⟨hm, by rw [hK0]; exact hc⟩).1
          rw [KNode.liveAt_of_times _ c.i hSt] at hm'
          exact hmin c' z hm' hc
      refine writerWP_mono (hcollLeb seg stop w3 n' jcv jy hsD hbetween h3tw h3top' h3v' hfr hsn3
        (by rw [hn'l, hSleaf]) hn'w
        hn't hsl hK0 hj hj0 (fun c' z hm hc => by
          rcases hmin' c' z hm with h | h
          · exact absurd h hc
          · exact h) hlive' ?_) ?_
      · intro key' hkw
        have hV3 : wValue base w3 = wValue base w :=
          wValue_eq_of_taken base w w3 h3v' (fun y => ∃ k, stop < k ∧ k ≤ depth ∧ y = X k)
            (fun y hy => h3tw y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
            (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk k h2, hnoval k h2⟩)
        have hagree : ∀ u, TReach (wNode c.p base w) c.i w.top.rootKey u → u ≠ X stop →
            (∀ i, stop < i → i ≤ depth → u ≠ X i) → wNode c.p base w3 u = wNode c.p base w u := by
          intro u _ hus hnc
          simp only [wNode, h3tw u hnc, hfr u hus hnc]
        have hsnw : wNode c.p base w3 (X stop) = some n' := by
          simp only [wNode, h3tw (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn3]
        unfold wGet
        rw [hV3, h3top']
        exact getFromR_up_leb (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
          w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
          (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
          (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
          (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
          hrk hcv hvisL huniq hagree n' jy jcv hK0 hsl hj hj0 hmin' hsnw (by rw [hn'l, hSleaf]; exact hsl)
          hlive' key' hkw
      · intro _ w4 h4
        simp only [writerWP_pure]
        exact h4
    have hK0' : (K (stop + 1) != 0) = true := by simpa using hK0
    simp only [hK0', ↓reduceIte, writerWP_bind, hmerges, Bool.false_eq_true]
    refine hbit (Or.inr hK0) _ ?_ ?_ ?_ ?_ _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread
      refine writerWP_mono (hcoll seg stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't
        hlive' hread) ?_
      intro _ w4 h4
      simp only [writerWP_pure]
      exact h4
    all_goals rfl

/-- `writerWP_deleteUpward_up` with the take-back: a node of the chain made by
the transaction is taken back and its parent retargeted, the others unlinked.
The stop node a segment leaf or an inner node, its klong to the chain deleted by
a bitmap with room or, the empty key's, by LE-b with room; the merges off. The
writer's tree after is a tree, the key reads nothing and every other key as
before; at the space root's segment root collapse is part of it, at another
segment `hcollSeg` gives it. -/
theorem writerWP_deleteUpward_upT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hfit : PathsFit (wNode c.p base w) c.i w.top.rootKey c.p.fuel)
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
    (hcollSeg : ∀ seg, 0 < seg → ∀ w', CollGetInv c base w' w' →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' =>
        TreeOK (wNode c.p base w'') c.i w''.top.rootKey ∧ ∀ key', keyWf key' = true →
          wGet c.p c.i base w'' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧ ∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  have hpost := collGetInv_after_upT c base X Nn K depth w hlk htk hdist hT hwf hRt hTimesR hICE hfit
    hnovalAll hreach hlinkK
  have hcollAny : ∀ seg w', CollGetInv c base w' w' → (∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' =>
        TreeOK (wNode c.p base w'') c.i w''.top.rootKey ∧ ∀ key', keyWf key' = true →
          wGet c.p c.i base w'' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro seg w' hI hread
    by_cases hseg : seg = 0
    · subst hseg
      refine writerWP_mono (writerWP_collapseRoot_space_get (pre ++ [cv]) c base hvc w' c.p.fuel w' hI) ?_
      intro _ w'' h
      exact ⟨h.1.1, fun key' hkw => by rw [h.2.1 key']; exact hread key' hkw⟩
    · exact hcollSeg seg (by omega) w' hI hread
  apply writerWP_deleteUpward_upT_get c base X Nn K depth cv pre rk w _ hdepth hfuel hp hk hlk htk
    htimes hdist hne hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi))
    hrk hcv hvisL huniq hstopOK hmerges
  · intro seg stop w' sn' hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread
    exact hcollAny seg w' (hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)) hread
  · intro stop w' sn' hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread
    exact ⟨(hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)).1.1, hread⟩
  · intro seg stop w' sn' jcv jy hsD _ ht htop hv hnodes hsn' hsl' hsw' hst' _ hK0 hj hj0 _ hlive' hread
    refine hcollAny seg w' (hpost stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv
      hnodes hsn' hsl' hsw' hst' ?_) hread
    intro c' z h
    rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
      simp [h1]
    · exact ⟨c', h1, by omega, by simp [h3]⟩

end SIS.Tree
