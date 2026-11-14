import SIS.Tree.DelMergeCaseF3

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A segment collapse whose segment leaf is full (bergdb 024-12, case (4), the
collapse's room): `replaceRoot` at a segment root x, below the segment leaf
`leaf` of the key's path, unlinks x and adds the klong to x's only child to the
leaf, which may split with its cascade. The step keeps the collapse's invariant
(`CollGetInvF`) and the walk's ranges, given that the state after it fits the
fuel (cost's HeightInv route) and the take-back's `CollapseUnlinkOK`. -/

/-- The take-back's premise of a segment collapse: when the segment root x has a
klong of the transaction, the tree with x's previous version (what `unlink x`
leaves while the leaf still links x) is a tree from the space root, and that
version names ids below the next id. Checked at 96 replaceRoots of runs within
reach, 32 with a full segment leaf (`12-tree-model/collapse-unlink-check.lean.txt`). -/
def CollapseUnlinkOK (c : Ctx) (base : View BVal) (v : W) (x : NodeId) (n : KNode) : Prop :=
  n.lastTime = some c.i →
    TreeOK (updN (wNode c.p base v) x (n.toPrev (c.i - 1))) c.i v.top.rootKey ∧
    ∀ c' z, (c', z) ∈ (n.toPrev (c.i - 1)).liveAt c.i → z < v.next

/-- `unlink x` of a cached node x: x's node is its previous version or as it
was, and nothing else changes. -/
theorem writerWP_unlink_seg (x : NodeId) (n : KNode) (c : Ctx) (base : View BVal) (w : W)
    (hx : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false) :
    WriterWP (unlink x) c w (fun _ w1 => w1.taken = w.taken ∧ w1.top = w.top ∧ w1.next = w.next ∧
      w1.vals = w.vals ∧ w1.path = w.path ∧
      (∀ y, y ≠ x → w1.nodes.lookup y = w.nodes.lookup y) ∧
      ∃ m, w1.nodes.lookup x = some m ∧ wNode c.p base w1 = updN (wNode c.p base w) x m ∧
        (m = n ∨ (n.lastTime = some c.i ∧ m = n.toPrev (c.i - 1)))) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hx]
  split
  · rename_i h
    simp only [putNode, writerWP_modify]
    refine ⟨by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial,
      by first | rfl | trivial, by first | rfl | trivial,
      fun y hy => by simp only [lookup_upsert, hy, ↓reduceIte],
      n.toPrev (c.i - 1), by simp only [lookup_upsert, ↓reduceIte],
      wNode_upsert_updN c.p base w _ x _ rfl rfl hxt, Or.inr ⟨by simpa using h, rfl⟩⟩
  · refine (writerWP_pure _ c _ _).mpr ?_
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, n, hx, ?_, Or.inl rfl⟩
    funext z
    by_cases hz : z = x
    · subst hz
      rw [updN_self]
      simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hx]
    · rw [updN_ne _ _ _ _ hz]

set_option maxHeartbeats 4000000 in
/-- `replaceRoot` at a segment root x below the segment leaf `leaf` of the key's
path, the leaf full or not: the writer's tree after it is a tree whose reached
nodes are not taken back, every node's klongs are well formed, the reading is
w0's when the state after fits the fuel, and the walk's ranges hold. The leaf's
cascade starts from the tree that `unlink x` leaves (`CollapseUnlinkOK`); it
reads as the tree of the room case, where the leaf names x's child
(`collGetInv_segStepF`, `rangeOrder_segCollapse`), by `writerWP_appendKlongs_chainGRVf`
and `writerWP_appendKlongs_chainGRange`. -/
theorem writerWP_replaceRoot_seg_cascadeF (fuelR : Nat) (hfR : 2 ≤ fuelR) (x : NodeId) (only : Nat)
    (n : KNode) (leaf : NodeId) (ln : KNode) (k : Nat) (ps0 : List (Option Nat × NodeId))
    (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInvF c base w0 v fuelR)
    (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey) (hG : PutInvG c base v)
    (hsa2 : 2 ≤ c.p.splitAbove)
    (hvp : v.path = (none, v.top.rootKey) :: (ps0 ++ [(some k, x)]))
    (hlf : LinkedFrom (wNode c.p base v) c.i v.top.rootKey (ps0 ++ [(some k, x)]))
    (hPC : PathCached v)
    (hLr : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hpd : (v.path[ps0.length]?).map (·.2) = some leaf)
    (hpk : v.path[ps0.length + 1]? = some (some k, x))
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hU : CollapseUnlinkOK c base v x n) :
    WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' =>
      TreeOK (wNode c.p base v') c.i v'.top.rootKey ∧
      (∀ z, TReach (wNode c.p base v') c.i v'.top.rootKey z → v'.taken.contains z = false) ∧
      (∀ z zn, wNode c.p base v' z = some zn → klongsWf zn.ks = true) ∧
      v'.taken = v.taken ∧ v'.vals = v.vals ∧
      (SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey →
        ∀ key, wGetAt c.p c.i base v' fuelR key = wGetAt c.p c.i base w0 fuelR key) ∧
      RangeOrder (wNode c.p base v') c.i v'.top.rootKey) := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hLr
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hLr ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hLr hwL
  have hlnwf := hI.2.2.2.1 leaf ln hLr hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hLr ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  -- the key's path down to x
  have hP0 := pathOK_of_linked c base v v (ps0 ++ [(some k, x)]) (ReadsAs.refl _ _ _) hvp hlf hPC
    (fun y hy => hI.1.2.1 y hy)
  have hlen0 : (ps0 ++ [(some k, x)]).length = ps0.length + 1 := by simp
  rw [hlen0] at hP0
  obtain ⟨X, K, Nn, hP⟩ : ∃ X K Nn, PathOK c v (ps0.length + 1) X K Nn := ⟨_, _, _, hP0⟩
  clear hP0
  have hP' := hP
  obtain ⟨hX, hK, hS2v, hlink, h0⟩ := hP'
  generalize hd : ps0.length = d at hpd hpk hP hX hK hS2v hlink ⊢
  have hXd : X d = leaf := by
    have := hX d (by omega); rw [hpd] at this; exact (Option.some.inj this).symm
  have hXx : X (d + 1) = x := by
    have := hX (d + 1) (Nat.le_refl _)
    rw [hpk] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact this.symm
  have hNd : Nn d = ln := by
    have := (hS2v d (by omega)).1; rw [hXd, hlkL] at this; exact (Option.some.inj this).symm
  have hw : ∀ j, j ≤ d + 1 → wNode c.p base v (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2v j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hreach := pathOK_reach c base v (d + 1) X K Nn hP
  have hdist := pathOK_dist c base v (d + 1) X K Nn hP hT
  have hXne : ∀ i, i ≤ d → X i ≠ x := by
    intro i hi he
    rw [← hXx] at he
    have := hdist i (d + 1) (by omega) (Nat.le_refl _) he
    omega
  have hO := ordG_of_rangeOrder c _ _ hR hG.times
  -- the program
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
    have hchn : child < v.next := hG.links x n 0 child hwx hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_seg x n c base _ (by exact hlkx) (by exact hxt)) ?_
    rintro _ w1 ⟨h1t, h1top, h1next, h1v, h1path, h1l, mx, h1x, hW1, hmx⟩
    -- the state after unlink: x's node is mx, the rest as before
    have h1t' : w1.taken = v.taken := h1t
    have h1top' : w1.top = v.top := h1top
    have h1next' : w1.next = v.next := h1next
    have h1v' : w1.vals = v.vals := h1v
    have h1path' : w1.path = v.path := h1path
    have h1l' : ∀ y, y ≠ x → w1.nodes.lookup y = v.nodes.lookup y := h1l
    have hW1' : wNode c.p base w1 = updN (wNode c.p base v) x mx := hW1
    have hxn : x < v.next := hG.ids.1 x (by rw [hlkx]; rfl)
    have hmxwf : klongsWf mx.ks = true := by
      rcases hmx with h | ⟨_, h⟩ <;> rw [h]
      · exact hG.wf x n hwx
      · exact KNode.toPrev_wf _ _ (hG.wf x n hwx)
    have hT1 : TreeOK (wNode c.p base w1) c.i w1.top.rootKey := by
      rw [hW1', h1top']
      rcases hmx with h | ⟨hlt, h⟩
      · rw [h]
        have he : updN (wNode c.p base v) x n = wNode c.p base v := by
          funext z
          by_cases hz : z = x
          · subst hz; rw [updN_self, hwx]
          · rw [updN_ne _ _ _ _ hz]
        rw [he]; exact hT
      · rw [h]; exact (hU hlt).1
    have hS6' : ∀ u c' z, TLink (wNode c.p base w1) c.i u c' z → z < w1.next := by
      intro u c' z hl
      obtain ⟨un, hun, hc⟩ := hl
      rw [h1next']
      rw [hW1'] at hun
      by_cases hux : u = x
      · subst hux
        rw [updN_self] at hun
        cases hun
        rcases hmx with h | ⟨hlt, h⟩
        · rw [h] at hc; exact hG.links _ n c' z hwx hc
        · rw [h] at hc; exact (hU hlt).2 c' z hc
      · rw [updN_ne _ _ _ _ hux] at hun; exact hG.links u un c' z hun hc
    have hW' : ∀ z zn, wNode c.p base w1 z = some zn → klongsWf zn.ks = true := by
      intro z zn hz
      rw [hW1'] at hz
      by_cases hzx : z = x
      · subst hzx; rw [updN_self] at hz; cases hz; exact hmxwf
      · rw [updN_ne _ _ _ _ hzx] at hz; exact hG.wf z zn hz
    have hP1 : PathOK c w1 d X K Nn := by
      refine ⟨fun i hi => by rw [h1path']; exact hX i (by omega),
        fun i h1 h2 => by rw [h1path']; exact hK i h1 (by omega),
        fun i hi => ⟨by rw [h1l' (X i) (hXne i hi)]; exact (hS2v i (by omega)).1,
          by rw [h1t']; exact (hS2v i (by omega)).2⟩,
        fun i h1 h2 => hlink i h1 (by omega), by rw [h1top']; exact h0⟩
    have hreach1 := pathOK_reach c base w1 d X K Nn hP1
    have hS5' : ∀ z, w1.next ≤ z → w1.nodes.lookup z = none ∧ w1.taken.contains z = false ∧
        knodeOf c.p base z = none := by
      intro z hz
      rw [h1next'] at hz
      have hzx : z ≠ x := by intro h; rw [h] at hz; omega
      refine ⟨?_, ?_, (hG.fresh z hz).1⟩
      · rw [h1l' z hzx]
        cases h : v.nodes.lookup z with
        | none => rfl
        | some _ => have := hG.ids.1 z (by rw [h]; rfl); omega
      · rw [h1t']
        cases h : v.taken.contains z with
        | false => rfl
        | true => have := hG.ids.2.2.1 z h; omega
    -- the virtual state: the room case's, the leaf naming x's child
    have hlk1L : w1.nodes.lookup leaf = some ln := by rw [h1l' leaf hlx]; exact hlkL
    have hLt1 : w1.taken.contains leaf = false := by rw [h1t']; exact hLt
    have hWV : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } =
        updN (wNode c.p base w1) leaf (ln.add c.i (.key k child)) :=
      wNode_upsert_updN c.p base w1 _ leaf _ rfl rfl hLt1
    have hL' : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } leaf =
        some (ln.add c.i (.key k child)) := by rw [hWV, updN_self]
    have hoth : ∀ y, y ≠ leaf → y ≠ x →
        wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } y =
          wNode c.p base v y := by
      intro y hyl hyx
      rw [hWV, updN_ne _ _ _ _ hyl, hW1', updN_ne _ _ _ _ hyx]
    have hVv : wValue base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } =
        wValue base v := wValue_congr' base _ v h1t' h1v'
    have hlinksL : ∀ c' z, (c', z) ∈ (ln.add c.i (.key k child)).liveAt c.i →
        (c' = k ∧ z = child) ∨ ((c', z) ∈ ln.liveAt c.i ∧ c' ≠ k) := by
      intro c' z hmm
      rcases KNode.add_key_liveAt_mem ln c.i k child hlnwf hlnt c' z hmm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
    have hVI : CollGetInvF c base w0
        { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } fuelR := by
      refine collGetInv_segStepF fuelR hfR c base w0 v _ leaf x child k 0 ln
        (ln.add c.i (.key k child)) n hI hLr hwL hk hwx hcl hL' (by rw [KNode.add_leaf]; exact hlnl)
        (KNode.add_key_wf ln c.i k child hlnwf)
        (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt) hlinksL hoth h1top' h1v'
        (fun z _ => by rw [show ({ w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } : W).taken
          = v.taken from h1t']) ?_
      intro key
      unfold wGetAt
      rw [hVv]
      show getFromR _ (wValue base v) c.i fuelR key w1.top.rootKey = _
      rw [h1top']
      exact getFromR_segCollapse (wNode c.p base v) _ (wValue base v) c.i fuelR v.top.rootKey
        leaf x child k ln (ln.add c.i (.key k child)) n hT hLr hwL hL' hlnl
        (by rw [KNode.add_leaf]; exact hlnl) hlnwf (KNode.add_key_wf ln c.i k child hlnwf) hlnt
        (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt)
        (fun cc => KNode.add_key_live_lookup_of_wf ln c.i k cc child hlnwf) hk hwx hxl hlv hnt ⟨m, hm⟩
        hoth hwfS hI.2.2.1 (by rw [hI.2.2.2.2 child m hchR hm, hI.2.2.2.2 x n hxR hwx]) key
    have hVR : RangeOrder (wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) })
        c.i v.top.rootKey := by
      refine rangeOrder_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf x
        child ln (ln.add c.i (.key k child)) n k hR hT hLr hwL hlnl hk hwx hxl hcl ?_ hL'
        (by rw [KNode.add_leaf]; exact hlnl) ?_ hoth
      · intro c' z hz
        rw [KNode.liveAt_of_times n c.i hnt] at hz
        exact (hlv c' z).mp hz
      · intro c' z hmm
        rcases KNode.add_key_liveAt_mem ln c.i k child hlnwf hlnt c' z hmm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    have hVeq : updN (wNode c.p base w1) (X d) ([(k, child)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn d)) = wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } := by
      rw [hXd, hNd, hWV]; rfl
    -- the leaf's cascade
    have hrangeC : ∀ i, 0 < i → i ≤ d → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
        ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
        K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'' :=
      fun i h1 hi hNR hql' c' z hz hpos =>
        rangeG_of_rangeOrder c _ _ hR hG.times (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
          (hreach (i - 1) (by omega)) (hw (i - 1) (by omega)) hql' (hlink i h1 (by omega))
          (hw i (by omega)) hNR c' z hz hpos
    have hlenC : ∀ i, 0 ≤ i → i ≤ d → ¬ ChainRoom c (Nn i) →
        c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length :=
      fun i _ hi hNR hsp => lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach i (by omega))
        (hw i (by omega)) hNR hsp
    have hch := writerWP_appendKlongs_chainGRVf c base v.path 0 d X K Nn fuelR hfR
      (fun i _ hi => hX i (by omega)) (fun i h1 hi => hK i h1 (by omega))
      (fun i h1 hi => hlink i h1 (by omega)) hrangeC hlenC
      (fun i _ hi => hG.wf _ _ (hw i (by omega))) (fun i _ hi => hG.times _ _ (hw i (by omega)))
      (Or.inr rfl)
      (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he)
      (by
        intro i _ hi hNR hsp
        rcases Nat.eq_zero_or_pos i with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inr (fun _ i' h1 h2 =>
            chainOrd_of_ordG c base v (d + 1) X K Nn hP hO i' h1 (by omega))⟩)
      d (by omega) w1 [(k, child)] (Or.inl ⟨k, child, rfl⟩)
      (by
        intro q hq
        simp only [List.mem_singleton] at hq
        rw [hq, h1next']; exact hchn)
      h1path'
      (fun i _ hi => ⟨by rw [h1l' (X i) (hXne i (by omega))]; exact (hS2v i (by omega)).1,
        by rw [h1t']; exact (hS2v i (by omega)).2⟩)
      hT1 (fun i _ hi => hreach1 i (by omega)) hS5' hS6'
      (fun _ _ => by rw [h1top']; exact h0.symm) hW'
      (by simp only [Nat.zero_add]; rw [hVeq]; exact hVI.1.1)
    have hrg := writerWP_appendKlongs_chainGRange c base v.path 0 d X K Nn
      (fun i _ hi => hX i (by omega)) (fun i h1 hi => hK i h1 (by omega))
      (fun i h1 hi => hlink i h1 (by omega)) hrangeC hlenC
      (fun i _ hi => hG.wf _ _ (hw i (by omega))) (fun i _ hi => hG.times _ _ (hw i (by omega)))
      (Or.inr rfl)
      (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he)
      d (by omega) w1 [(k, child)] (Or.inl ⟨k, child, rfl⟩)
      (by
        intro q hq
        simp only [List.mem_singleton] at hq
        rw [hq, h1next']; exact hchn)
      h1path'
      (fun i _ hi => ⟨by rw [h1l' (X i) (hXne i (by omega))]; exact (hS2v i (by omega)).1,
        by rw [h1t']; exact (hS2v i (by omega)).2⟩)
      hT1 (fun i _ hi => hreach1 i (by omega)) hS5' hS6'
      (fun _ => by rw [h1top']; exact h0.symm)
      (by simp only [Nat.zero_add]; rw [hVeq]; exact hVI.1.1)
      (by simp only [Nat.zero_add]; rw [hVeq, h1top']; exact hVR)
    simp only [Nat.zero_add] at hch hrg
    rw [hXd] at hch hrg
    refine writerWP_mono (writerWP_and hch hrg) ?_
    rintro _ w2 ⟨⟨hT2, ⟨_, ht2, _, _, hv2⟩, _, hreach2, hW2, hread2, _⟩, _, _, _, _, hRO2⟩
    have hVeq' : updN (wNode c.p base w1) leaf ([(k, child)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn d)) = wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } := by
      rw [hNd, hWV]; rfl
    refine ⟨hT2, fun z hz => ?_, hW2, by rw [ht2, h1t'], by rw [hv2, h1v'], fun hfit key => ?_, hRO2⟩
    · rw [ht2]
      rcases hreach2 z hz with h | ⟨h1, _⟩
      · rw [hVeq'] at h
        exact hVI.1.2.1 z h
      · cases h : w1.taken.contains z with
        | false => rfl
        | true =>
          have := hG.ids.2.2.1 z (by rw [← h1t']; exact h)
          rw [h1next'] at h1; omega
    · have hValNone : ∀ z, (w1.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ d ∧ z = X i) →
          wValue base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } z = none := by
        intro z hz
        rw [hVv]
        rcases hz with hz | ⟨i, _, hi, rfl⟩
        · rw [h1next'] at hz
          have htz : v.taken.contains z = false := by
            cases h' : v.taken.contains z with
            | false => rfl
            | true => have := hG.ids.2.2.1 z h'; omega
          have hvz : v.vals.lookup z = none := by
            cases h' : v.vals.lookup z with
            | none => rfl
            | some _ =>
              have hm := lookup_some_mem h'
              have := hG.ids.2.2.2 _ hm
              simp only at this; omega
          simp only [wValue, htz, Bool.false_eq_true, ↓reduceIte, hvz, (hG.fresh z hz).2]
        · exact hG.keyNoValue (X i) (Nn i) (hw i (by omega))
      unfold wGetAt
      have hVal2 : wValue base w2 =
          wValue base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } :=
        wValue_congr' base w2 _ ht2 hv2
      rw [hVal2, hread2 _ hValNone (Or.inl hfit) key, hVeq']
      have := hVI.2.1 key
      unfold wGetAt at this
      exact this

/-! ## The collapse loop without the room premise -/

/-- The collapse's steps keep the fresh cache, the writer's state invariants. -/
theorem freshCache_takeBackRoot {base : NodeId} (x : NodeId) (depth only : Nat) :
    KeepsFreshCache base (takeBackRoot x depth only) := by
  intro c w hview hw
  repeat' first
    | wpSimplify
    | frDeleteSimplify
    | frCore base
    | frAppend base
    | wpSplit
    | split
    | contradiction

theorem freshCache_replaceRoot {base : NodeId} (x : NodeId) (depth only : Nat) :
    KeepsFreshCache base (replaceRoot x depth only) := by
  intro c w hview hw
  repeat' first
    | wpSimplify
    | frDeleteSimplify
    | frCore base
    | frAppend base
    | wpSplit
    | split
    | contradiction

section
variable [inv : WriterStateInvariant]

theorem state_takeBackRoot (x : NodeId) (depth only : Nat) : KeepsState (takeBackRoot x depth only) := by
  intro c w hw
  repeat' first
    | siSimplify
    | siDeleteSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

theorem state_replaceRoot (x : NodeId) (depth only : Nat) : KeepsState (replaceRoot x depth only) := by
  intro c w hw
  repeat' first
    | siSimplify
    | siDeleteSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

end

theorem putBook_takeBackRoot (x : NodeId) (depth only : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) (hx : B ≤ x) :
    WriterWP (takeBackRoot x depth only) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_takeBackRoot x depth only)
    (fun c' w' hv hw' => good_takeBackRoot B x depth only c' w' hv hw' hx) (book_takeBackRoot B x depth only)
    (@state_takeBackRoot (allocatedIdsInvariant B) x depth only)
    (@state_takeBackRoot (commitInvariant top0) x depth only)
    (freshCache_takeBackRoot x depth only) (ptrs_takeBackRoot _ x depth only)

theorem putBook_replaceRoot (x : NodeId) (depth only : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (replaceRoot x depth only) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_replaceRoot x depth only)
    (good_replaceRoot B x depth only) (book_replaceRoot B x depth only)
    (@state_replaceRoot (allocatedIdsInvariant B) x depth only)
    (@state_replaceRoot (commitInvariant top0) x depth only)
    (freshCache_replaceRoot x depth only) (ptrs_replaceRoot _ x depth only)

theorem putBook_descendToSegmentRoot (key : Key) (seg : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (descendToSegmentRoot key seg) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_descendToSegmentRoot key seg)
    (good_descendToSegmentRoot B key seg) (book_descendToSegmentRoot B key seg)
    (@state_descendToSegmentRoot (allocatedIdsInvariant B) key seg)
    (@state_descendToSegmentRoot (commitInvariant top0) key seg)
    (freshCache_descendToSegmentRoot key seg) (ptrs_descendToSegmentRoot _ key seg)

/-- The nodes of a linked path: its end, or a node before it, which has a node. -/
theorem linkedFrom_mem (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (ps : List (Option Nat × NodeId)) (h : LinkedFrom N t r ps) :
    ∀ z ∈ r :: ps.map (·.2), z = pathEnd r ps ∨
      (z ∈ (r :: ps.map (·.2)).dropLast ∧ ∃ zn, N z = some zn) := by
  induction h with
  | nil x =>
    intro z hz
    simp only [List.map_nil, List.mem_singleton] at hz
    left; rw [hz]; rfl
  | cons x n k y rest hn _ _ ih =>
    intro z hz
    simp only [List.map_cons, List.mem_cons] at hz
    have hpe : pathEnd x ((some k, y) :: rest) = pathEnd y rest := by
      unfold pathEnd
      cases rest with
      | nil => rfl
      | cons e es =>
        rw [List.getLast?_cons_cons]
        cases h : (e :: es).getLast? with
        | none => simp at h
        | some q => rfl
    rcases hz with hz | hz
    · right
      refine ⟨?_, n, by rw [hz]; exact hn⟩
      rw [hz]; simp
    · rcases ih z (by simpa using hz) with h | ⟨h1, h2⟩
      · left; rw [hpe]; exact h
      · right
        refine ⟨?_, h2⟩
        simp only [List.map_cons, List.dropLast_cons_cons] at h1 ⊢
        exact List.mem_cons_of_mem _ h1

/-- The path down to a segment root is cached, given the segment root. -/
theorem pathCached_of_segDesc (c : Ctx) (base : View BVal) (x : NodeId) (v : W) (n : KNode)
    (h : SegDesc c base x v) (hlk : v.nodes.lookup x = some n) : PathCached v := by
  obtain ⟨_, ps, hvp, hlf, hend, hcache, _⟩ := h
  intro e he
  rw [hvp] at he
  have hz : e.2 ∈ v.top.rootKey :: ps.map (·.2) := by
    rcases List.mem_cons.mp he with h1 | h1
    · rw [h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem h1)
  rcases linkedFrom_mem _ _ _ ps hlf e.2 hz with h1 | ⟨h1, zn, h2⟩
  · rw [h1, hend]; exact ⟨n, hlk⟩
  · exact ⟨zn, hcache e.2 h1 zn h2⟩

/-- The last entry of the key's path down to a segment root names it. -/
theorem segDesc_pathLast (c : Ctx) (base : View BVal) (x : NodeId) (v : W) (h : SegDesc c base x v) :
    ∃ a, v.path[v.path.length - 1]? = some (a, x) := by
  obtain ⟨_, ps, hvp, _, hend, _, hlast⟩ := h
  rcases hlast with hps | ⟨ps0, k, L, ln, hps, _, _, _⟩
  · subst hps
    refine ⟨none, ?_⟩
    rw [hvp]
    simp only [List.length_singleton, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq, true_and]
    exact hend
  · subst hps
    refine ⟨some k, ?_⟩
    rw [hvp]
    have hend' : x = x := rfl
    simp

set_option maxHeartbeats 1600000 in
/-- The root collapse keeps `CollGetInvF`, the walk's ranges, the books and the
kinds' walk, with no room premise: a replaceRoot at a segment root takes the
leaf's cascade (`writerWP_replaceRoot_seg_cascadeF`), given that the state after
it fits the fuel (`hfits`, cost's HeightInv route) and `CollapseUnlinkOK`
(`hunl`, the take-back's). -/
theorem writerWP_collapseRoot_collF4 (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hfits : ∀ v x n only, CollGetInvF c base w0 v fuelR →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey))
    (hunl : ∀ v x n, CollGetInvF c base w0 v fuelR → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      CollapseUnlinkOK c base v x n) :
    ∀ fuel v, CollGetInvF c base w0 v fuelR → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
      PutBook c B top0 v → Book BK c v → KdInv KO BK v →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollGetInvF c base w0 v' fuelR ∧
        RangeOrder (wNode c.p base v') c.i v'.top.rootKey ∧ PutBook c B top0 v' ∧ Book BK c v' ∧
        KdInv KO BK v') := by
  intro fuel v hI hR hb hbk hik
  refine writerWP_collapseRoot_inv key seg c (fun v => CollGetInvF c base w0 v fuelR ∧
      RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧ PutBook c B top0 v ∧ Book BK c v ∧
      KdInv KO BK v) (SegDesc c base) ?_ ?_ ?_ ?_ fuel v ⟨hI, hR, hb, hbk, hik⟩
  · rintro v ⟨hI, hR, hb, hbk, hik⟩
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_descendToSegmentRoot_linked key seg c base hvc v hI.1.2.1 hI.2.2.2.1)
      (putBook_descendToSegmentRoot key seg c base B top0 hB v hb))
      (kd_descendToSegmentRoot KO BK key seg c v hv hk hbk hik)) ?_
    rintro x v' ⟨⟨⟨hr, _, hx, ps, hvp, hlf, hend, hcache, hlast⟩, hb'⟩, hbk', hik', _, _⟩
    refine ⟨⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI, by rw [hr.1, hr.2.1]; exact hR,
      hb', hbk', hik'⟩, ?_⟩
    unfold SegDesc
    rw [hr.1, hr.2.1]
    exact ⟨hx, ps, hvp, hlf, hend, hcache, hlast⟩
  · rintro x v ⟨hI, hR, hb, hbk, hik⟩ hP
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_getNode_all x c v base hvc)
      (writerWP_getNode_cache x c v)) (putBook_getNode x c base B top0 hB v hb))
      (kd_getNode KO BK x c v hv hk hbk hik)) ?_
    rintro n v' ⟨⟨⟨⟨hr, hl, _, hpre, _⟩, _, _, hp⟩, hb'⟩, hbk', hik', _⟩
    exact ⟨⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI, by rw [hr.1, hr.2.1]; exact hR,
      hb', hbk', hik'⟩, segDesc_of_readsAs c base x v v' hP hr hpre hp, hl, hp⟩
  · rintro x v n only ⟨hI, hR, hb, hbk, hik⟩ hP hlk hxl hm _ honly hcv
    obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hbk hlk
    have hh : h ≠ 0 := by
      intro h0; subst h0
      have := kd_leaf hbk hlk hgh
      simp at this; rw [this] at hxl; cases hxl
    obtain ⟨a, hpa⟩ := segDesc_pathLast c base x v hP
    have hBx : B ≤ x := Blank.ge B c x hB.good
      (blank_of_firstTime B c x n hB.good.pos (cacheGood_lookup B c v hb.good x n hlk) (by simp [hm]))
    have hcr : WriterWP (takeBackRoot x (v.path.length - 1) only) c v
        (fun _ v' => CollGetInvF c base w0 v' fuelR ∧ RangeOrder (wNode c.p base v') c.i v'.top.rootKey) := by
      obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
      rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
      · subst hps
        have hx : x = v.top.rootKey := by rw [← hend]; rfl
        rw [hvp]
        exact writerWP_and
          (writerWP_rootStep_space_collF fuelR hfR x only n c base w0 v hI hx hlk honly hcv hxl).1
          (writerWP_rootStep_space_rangeG x only n c base v _ _ _ hI hR hx hlk honly hcv hxl).1
      · subst hps
        obtain ⟨hLr, hLlk, hk', hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
        rw [hlen]
        exact writerWP_and
          (writerWP_takeBackRoot_seg_collF fuelR hfR x ps0.length only n L ln k c base w0 v hI hLr hLlk
            hLl hk' hlk honly hcv hxl hpd hpk)
          (writerWP_takeBackRoot_seg_rangeG x ps0.length only n L ln k c base v _ _ _ hI hR hLr hLlk
            hLl hk' hlk honly hcv hxl hpd hpk)
    refine writerWP_mono (writerWP_and (writerWP_and hcr
      (putBook_takeBackRoot x _ only c base B top0 hB v hb hBx))
      (kd_takeBackRoot KO BK x _ only c v hv hk hbk hik a hpa g h hgh hh)) ?_
    rintro _ v' ⟨⟨⟨hI', hR'⟩, hb'⟩, hbk', hik', _, _⟩
    exact ⟨hI', hR', hb', hbk', hik'⟩
  · rintro x v n only ⟨hI, hR, hb, hbk, hik⟩ hP hlk hxl hm honly hcv
    obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hbk hlk
    have hh : h ≠ 0 := by
      intro h0; subst h0
      have := kd_leaf hbk hlk hgh
      simp at this; rw [this] at hxl; cases hxl
    obtain ⟨a, hpa⟩ := segDesc_pathLast c base x v hP
    have hG := putInvG_of_book c base B top0 v hB hb
    have hPC := pathCached_of_segDesc c base x v n hP hlk
    have hU := hunl v x n hI hP hlk hxl hm
    have hfit := hfits v x n only hI hR hP hlk hxl hm honly hcv
    have hbook := putBook_replaceRoot x (v.path.length - 1) only c base B top0 hB v hb
    have hkd := kd_replaceRoot KO BK x _ only c v hv hk hbk hik a hpa g h hgh hh
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      have hrg := (writerWP_rootStep_space_rangeG x only n c base v _ _ _ hI hR hx hlk honly hcv hxl).2
      have hcl := (writerWP_rootStep_space_collF fuelR hfR x only n c base w0 v hI hx hlk honly hcv hxl).2
      rw [hvp] at hbook hkd ⊢
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hcl hrg) hbook) hkd) ?_
      rintro _ v' ⟨⟨⟨hI', hR'⟩, hb'⟩, hbk', hik', _, _⟩
      exact ⟨hI', hR', hb', hbk', hik'⟩
    · subst hps
      obtain ⟨hLr, hLlk, hk', hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      rw [hlen] at hfit hbook hkd ⊢
      have hcas := writerWP_replaceRoot_seg_cascadeF fuelR hfR x only n L ln k ps0 c base w0 v hI hR hG hsa2
        hvp hlf hPC hLr hLlk hLl hk' hpd hpk hlk honly hcv hxl hU
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hcas hfit) hbook) hkd) ?_
      rintro _ v' ⟨⟨⟨⟨hT', hU', hW', _, _, hread', hR'⟩, hf'⟩, hb'⟩, hbk', hik', _, _⟩
      have hG' := putInvG_of_book c base B top0 v' hB hb'
      refine ⟨⟨⟨hT', hU', fun y yn _ hy => hG'.times y yn hy,
        fun y yn cc z hy hyn hl hc => hICEk v' hbk' hik' hU' y yn cc z hy hyn hl hc⟩,
        hread' hf', hf', fun y yn _ hy => hW' y yn hy, fun y yn _ hy => hG'.keyNoValue y yn hy⟩,
        hR', hb', hbk', hik'⟩

/-! ## Case 4 without the collapse's room premise -/

/-- Obligation (the collapse at a fuel f, with no room premise): a replaceRoot at
a segment root leaves a state that fits f (cost's HeightInv route), and the
take-back's `CollapseUnlinkOK` holds there. The collapse's ranges are proved
(`writerWP_collapseRoot_collF4`). -/
def CollapseStepOKF4 (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  (∀ w0 v x n only, CollGetInvF c base w0 v f → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
      SegDesc c base x v → v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => SegFits (wNode c.p base v') c.i (f - 1) v'.top.rootKey)) ∧
  (∀ w0 v x n, CollGetInvF c base w0 v f → SegDesc c base x v → v.nodes.lookup x = some n →
      n.leaf = false → n.firstTime ≠ some c.i → CollapseUnlinkOK c base v x n)

/-- The collapse keeps `DelInvF3`, given `CollapseStepOKF4`. -/
theorem writerWP_collapseRoot_delF4 (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hC : CollapseStepOKF4 c base f) (w0 : W)
    (k0 : Key) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (v : W) (hI : DelInvF3 c base w0 k0 f KO BK v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvF3 c base w0 k0 f KO BK v') := by
  obtain ⟨⟨hP, hG, hR, hICE, hF, hread, B, top0, hB, hbook⟩, hbk, hik⟩ := hI
  have hCI : CollGetInvF c base v v f := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_collapseRoot_collF4 f hf2 key seg c base hvc v B top0 hB KO BK hv hk
    hICEk hsa2 (hC.1 v) (hC.2 v) c.p.fuel v hCI hR hbook hbk hik) ?_
  rintro _ v' ⟨⟨⟨hT', hu', _, hICE'⟩, hread', hF', _, _⟩, hR', hbook', hbk', hik'⟩
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨hP', hG', hR', hICE', hF', fun key' hk' => ?_, B, top0, hB, hbook'⟩, hbk', hik'⟩
  rw [hread' key']
  exact hread key' hk'

/-- `afterDelete` keeps `DelInvF3`, given the merge's obligation and `CollapseStepOKF4`. -/
theorem writerWP_afterDelete_delF4 (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF3 c base fuelR)
    (hC : CollapseStepOKF4 c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) (v : W) (hI : DelInvF3 c base w0 k0 fuelR KO BK v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvF3 c base w0 k0 fuelR KO BK v') :=
  writerWP_afterDelete_inv key g h c (DelInvF3 c base w0 k0 fuelR KO BK)
    (fun v hI => writerWP_mergeUp_delF3 key g c base hvc fuelR hfR hM KO BK hv hk hICEk hsa2 hcap w0 k0
      c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_delF4 key g c base hvc fuelR hfR hC w0 k0 KO BK hv hk hICEk hsa2
      v hI) v hI

/-- Case 4 at the reading fuel p.fuel + 1 inside the delete, with no room premise
of the collapse: `OpGetCaseOK'` from `DelStepsOKF3`, `MergeStepOKF3`,
`CollapseStepOKF4` and the pointers of every run within reach (TP4). -/
theorem opGetCaseOK'_delMerge4 (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF3 p R)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    OpGetCaseOK' p R DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 hP
  obtain ⟨key, hop, hmerges⟩ := hP
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hK := treeRun_kindsAllOK p hMM hPtr ts hwts
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hPtr ts hwts) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hPtr ts hwts) hb hi.cache hun
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop hmerges
    (fun g h v hv' => writerWP_afterDelete_delF4 key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delF3 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delF4 key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

/-- Case 4 (`OpGetCaseOK`) with no room premise of the collapse: from
`DelStepsOKF3`, `MergeStepOKF3`, `CollapseStepOKF4`, `TxSegFitsOK` and TP4. -/
theorem opGetCaseOK_delMergeF4 (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF3 p R)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R DelMergeCase :=
  opGetCaseOK_of' p R DelMergeCase (opGetCaseOK'_delMerge4 p R hS hM hC hsa2 hcap hMM hPtr) hfit

end SIS.Tree
