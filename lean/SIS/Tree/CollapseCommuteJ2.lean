/-
The take-back's replaceRoot through a full segment leaf without `CollapseUnlinkOK`
(bergdb 026-16, section 5.3; 024-22, section 11.1): `ReplaceRootFullJ2OK` with that
hypothesis dropped (`ReplaceRootFullJ2OKC`). When the root x has no klong of the
transaction the unlink changes nothing and `replaceRootFullJ2OK_holds` applies as
it stands. Else the leaf's cascade runs from the state before the unlink
(`xwp_appendKlongs`), where the writer's tree is a tree; the take-back's facts after
it come from that run, with x out of reach and its previous version holding no
klong of the transaction.
-/
import SIS.Tree.TakeReplaceFull
import SIS.Tree.CollapseCommuteStep

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `ReplaceRootFullJ2OK` without its `CollapseUnlinkOK` hypothesis. -/
def ReplaceRootFullJ2OKC (c : Ctx) (base : View BVal) (f : Nat) (B : NodeId) : Prop :=
  ∀ (w0 v : W) (x : NodeId) (n : KNode) (only : Nat) (leaf : NodeId) (ln : KNode) (k : Nat)
    (ps0 : List (Option Nat × NodeId)), CollGetInvF c base w0 v f →
    RangeOrder (wNode c.p base v) c.i v.top.rootKey → TakeJ2 c base B v → B ≤ v.next →
    v.path = (none, v.top.rootKey) :: (ps0 ++ [(some k, x)]) →
    LinkedFrom (wNode c.p base v) c.i v.top.rootKey (ps0 ++ [(some k, x)]) → PathCached v →
    TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln → ln.leaf = true →
    (k, x) ∈ ln.liveAt c.i → (v.path[ps0.length]?).map (·.2) = some leaf →
    v.path[ps0.length + 1]? = some (some k, x) → v.nodes.lookup x = some n →
    n.onlyLiveKlong = some only → n.cv? only = some 0 → n.leaf = false → n.firstTime ≠ some c.i →
    PutInvG c base v →
    ¬ (ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) →
    WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' => TakeJ2 c base B v' ∧ B ≤ v'.next)

set_option maxHeartbeats 3200000 in
/-- The replaceRoot of a root x with a klong of the transaction keeps `TakeJ2`
and B at most the next id, with no hypothesis on the tree after the unlink. -/
theorem replaceRootJ2_unlinked (c : Ctx) (base : View BVal) (f : Nat) (hf2 : 2 ≤ f) (B : NodeId)
    (hpos : 0 < c.i) (hsa2 : 2 ≤ c.p.splitAbove) (w0 v : W) (x : NodeId) (n : KNode) (only : Nat)
    (leaf : NodeId) (ln : KNode) (k : Nat) (ps0 : List (Option Nat × NodeId))
    (hI : CollGetInvF c base w0 v f) (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey)
    (hJ : TakeJ2 c base B v) (hBn : B ≤ v.next)
    (hvp : v.path = (none, v.top.rootKey) :: (ps0 ++ [(some k, x)]))
    (hlf : LinkedFrom (wNode c.p base v) c.i v.top.rootKey (ps0 ++ [(some k, x)])) (hPC : PathCached v)
    (hLr : TReach (wNode c.p base v) c.i v.top.rootKey leaf) (hlkL : v.nodes.lookup leaf = some ln)
    (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hpd : (v.path[ps0.length]?).map (·.2) = some leaf)
    (hpk : v.path[ps0.length + 1]? = some (some k, x)) (hlkx : v.nodes.lookup x = some n)
    (honly : n.onlyLiveKlong = some only) (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hnm : n.firstTime ≠ some c.i) (hG : PutInvG c base v) (hlt : n.lastTime = some c.i) :
    WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' => TakeJ2 c base B v' ∧ B ≤ v'.next) := by
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
    have hxn : x < v.next := hG.ids.1 x (by rw [hlkx]; rfl)
    have hpx : ∀ i e, i < d → v.path[i]? = some e → e.2 ≠ x := by
      intro i e hi he'
      have h1 := hX i (by omega)
      rw [he'] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [h1]; exact hXne i (by omega)
    show WriterWP (unlink x) c { v with trail := "rc.replace.segment" :: v.trail } _
    unfold unlink
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known x n c { v with trail := "rc.replace.segment" :: v.trail } hlkx]
    rw [if_pos (by simp [hlt])]
    simp only [putNode, writerWP_modify]
    -- the run after the unlink is one from the state before it (`xwp_appendKlongs`)
    refine writerWP_setX_of_xwp (m := n.toPrev (c.i - 1))
      (u := { v with trail := "rc.replace.segment" :: v.trail }) ?_
    generalize hw1 : ({ v with trail := "rc.replace.segment" :: v.trail } : W) = w1
    have h1t' : w1.taken = v.taken := by rw [← hw1]
    have h1top' : w1.top = v.top := by rw [← hw1]
    have h1next' : w1.next = v.next := by rw [← hw1]
    have h1v' : w1.vals = v.vals := by rw [← hw1]
    have h1path' : w1.path = v.path := by rw [← hw1]
    have h1l' : ∀ y, y ≠ x → w1.nodes.lookup y = v.nodes.lookup y := fun y _ => by rw [← hw1]
    have hlk1x : w1.nodes.lookup x = some n := by rw [← hw1]; exact hlkx
    have he : updN (wNode c.p base v) x n = wNode c.p base v := by
      funext z
      by_cases hz : z = x
      · subst hz; rw [updN_self, hwx]
      · rw [updN_ne _ _ _ _ hz]
    have hW1' : wNode c.p base w1 = updN (wNode c.p base v) x n := by
      rw [he, ← hw1]; try rfl
    have hT1 : TreeOK (wNode c.p base w1) c.i w1.top.rootKey := by
      rw [hW1', h1top', he]; exact hT
    have hS6' : ∀ u c' z, TLink (wNode c.p base w1) c.i u c' z → z < w1.next := by
      intro u c' z hl
      obtain ⟨un, hun, hc⟩ := hl
      rw [h1next']
      rw [hW1', he] at hun
      exact hG.links u un c' z hun hc
    have hW' : ∀ z zn, wNode c.p base w1 z = some zn → klongsWf zn.ks = true := by
      intro z zn hz
      rw [hW1', he] at hz
      exact hG.wf z zn hz
    have hJ0 : RJ x n v.path w1 := ⟨hlk1x, by rw [h1next']; exact hxn, h1path'⟩
    have hW := xwp_appendKlongs (m := n.toPrev (c.i - 1)) v.path d leaf [(k, child)] c w1 hJ0 hlx hpx
    refine ⟨hW.1, ?_⟩
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
        { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } f := by
      refine collGetInv_segStepF f hf2 c base w0 v _ leaf x child k 0 ln
        (ln.add c.i (.key k child)) n hI hLr hwL hk hwx hcl hL' (by rw [KNode.add_leaf]; exact hlnl)
        (KNode.add_key_wf ln c.i k child hlnwf)
        (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt) hlinksL hoth h1top' h1v'
        (fun z _ => by rw [show ({ w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } : W).taken
          = v.taken from h1t']) ?_
      intro key
      unfold wGetAt
      rw [hVv]
      show getFromR _ (wValue base v) c.i f key w1.top.rootKey = _
      rw [h1top']
      exact getFromR_segCollapse (wNode c.p base v) _ (wValue base v) c.i f v.top.rootKey
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
    -- the take-back's facts at the state before the unlink, which are v's
    have hxB : x < B := lt_of_firstTime_ne _ _ _ hJ.2.2.2.2.1 x n hwx hnm
    have hnwf : klongsWf n.ks = true := hG.wf x n hwx
    have hmxE : n.toPrev (c.i - 1) = (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
      simp [hlt]
    have hmxT : Klong.time c.i ∉ (n.toPrev (c.i - 1)).ks := by
      rw [hmxE]; exact unlinked_no_time n c.i hpos hnwf hnt
    have hJw : J2N (wNode c.p base w1) c.i w1.top.rootKey B (v.vals.map (·.1)) := by
      rw [hW1', he, h1top']; exact hJ
    have hspaceC : ∀ i, 0 ≤ i → i ≤ d → ¬ ChainRoom c (Nn i) →
        c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (0 < i ∧ ((Nn (i - 1)).leaf = false ∨
          ((Nn i).firstTime ≠ some c.i → ∀ i', 0 < i' → i' < i → ChainOrd c K Nn i'))) := by
      intro i _ hi hNR hsp
      rcases Nat.eq_zero_or_pos i with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Or.inr (fun _ i' h1 h2 =>
          chainOrd_of_ordG c base v (d + 1) X K Nn hP hO i' h1 (by omega))⟩
    have hord : ∀ i, 0 < i → i ≤ d → ChainOrd c K Nn i :=
      fun i h1 h2 => chainOrd_of_ordG c base v (d + 1) X K Nn hP hO i h1 (by omega)
    have hS2w1 : ∀ i, 0 ≤ i → i ≤ 0 + d →
        w1.nodes.lookup (X i) = some (Nn i) ∧ w1.taken.contains (X i) = false :=
      fun i _ hi => ⟨by rw [h1l' (X i) (hXne i (by omega))]; exact (hS2v i (by omega)).1,
        by rw [h1t']; exact (hS2v i (by omega)).2⟩
    have hN1 : ∀ i, 0 ≤ i → i ≤ 0 + d → wNode c.p base w1 (X i) = some (Nn i) := fun i a b => by
      simp only [wNode, (hS2w1 i a (by omega)).2, Bool.false_eq_true, ↓reduceIte, (hS2w1 i a (by omega)).1]
    -- the cascade from w1: the reading's facts, the shapes, the cache, the next id
    have hG2 := writerWP_appendKlongs_chainGRVf c base v.path 0 d X K Nn f hf2
      (fun i _ hi => hX i (by omega)) (fun i h1 hi => hK i h1 (by omega))
      (fun i h1 hi => hlink i h1 (by omega)) hrangeC hlenC
      (fun i _ hi => hG.wf _ _ (hw i (by omega))) (fun i _ hi => hG.times _ _ (hw i (by omega)))
      (Or.inr rfl)
      (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he) hspaceC
      d (by omega) w1 [(k, child)] (Or.inl ⟨k, child, rfl⟩)
      (by
        intro q hq
        simp only [List.mem_singleton] at hq
        rw [hq, h1next']; exact hchn)
      h1path' hS2w1 hT1 (fun i _ hi => hreach1 i (by omega)) hS5' hS6'
      (fun _ _ => by rw [h1top']; exact h0.symm) hW'
      (by simp only [Nat.zero_add]; rw [hVeq]; exact hVI.1.1)
    have hSh := writerWP_appendKlongs_chainShape c v.path 0 d X K Nn
      (fun i _ hi => hX i (by omega)) (fun i h1 hi => hK i h1 (by omega))
      (fun i h1 hi => hlink i h1 (by omega)) hrangeC hlenC hord
      (fun i _ hi => hG.times _ _ (hw i (by omega))) (Or.inr rfl)
      (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he)
      d (by omega) w1 [(k, child)] (Or.inl ⟨k, child, rfl⟩) (List.pairwise_singleton _ _) h1path'
      (fun i a b => ⟨(hS2w1 i a (by omega)).1, by
        rw [h1next']; exact hG.ids.1 (X i) (by rw [← h1l' (X i) (hXne i (by omega)), (hS2w1 i a (by omega)).1]; rfl)⟩)
      (fun z hz => (hS5' z hz).1)
    have hca := writerWP_appendKlongs_cached d leaf [(k, child)] c w1
    have hnx := @state_appendKlongs (nextFromInvariant w1) d leaf [(k, child)] c w1 (Nat.le_refl _)
    simp only [Nat.zero_add] at hG2 hSh
    rw [hXd] at hG2 hSh
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and hW.2 hG2) hSh) hca) hnx) ?_
    rintro _ u2 ⟨⟨⟨⟨hJ2, hG2'⟩, hSh'⟩, hca'⟩, hn2⟩
    obtain ⟨_, ⟨_, ht2, _, _, hv2⟩, hf2', hreach2, _, _, _, hkeep2, hchain2⟩ := hG2'
    have hVeq' : updN (wNode c.p base w1) leaf ([(k, child)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn d)) = wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } := by
      rw [hNd, hWV]; rfl
    -- x is out of reach in the room case's tree, and after the cascade
    have hxV : ¬ TReach (wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) })
        c.i v.top.rootKey x := fun h => by
      obtain ⟨len, hlen⟩ := h.pathLen
      exact (segCollapse_pathLen (wNode c.p base v) _ c.i v.top.rootKey leaf x child k 0 ln
        (ln.add c.i (.key k child)) n hT hLr hwL hk hwx hcl hL' hlinksL hoth x len hlen).1 rfl
    have hx2 : ¬ TReach (wNode c.p base u2) c.i u2.top.rootKey x := by
      intro h
      rcases hreach2 x h with h' | ⟨h1, _⟩
      · rw [hVeq', h1top'] at h'; exact hxV h'
      · rw [h1next'] at h1; omega
    have hxt2 : u2.taken.contains x = false := by rw [ht2, h1t']; exact hxt
    have hWN : wNode c.p base (setX x (n.toPrev (c.i - 1)) u2) =
        updN (wNode c.p base u2) x (n.toPrev (c.i - 1)) :=
      wNode_upsert_updN c.p base u2 _ x _ rfl rfl hxt2
    have hw2x : wNode c.p base u2 x = some n := by
      simp only [wNode, hxt2, Bool.false_eq_true, ↓reduceIte, hJ2.1]
    have hfwd2 : ∀ z, TReach (wNode c.p base u2) c.i u2.top.rootKey z →
        TReach (updN (wNode c.p base u2) x (n.toPrev (c.i - 1))) c.i u2.top.rootKey z :=
      tReach_of_agree (updN (wNode c.p base u2) x (n.toPrev (c.i - 1))) (wNode c.p base u2) c.i
        u2.top.rootKey (fun y hy => (updN_ne _ _ _ _ (fun he => hx2 (by
          rw [← he]; exact tReach_updN_unreach _ _ _ _ _ hx2 y hy))).symm)
    refine ⟨?_, by show B ≤ u2.next; exact Nat.le_trans hBn (by rw [← h1next']; exact hn2)⟩
    unfold TakeJ2
    rw [hWN]
    show J2N (updN (wNode c.p base u2) x (n.toPrev (c.i - 1))) c.i u2.top.rootKey B (u2.vals.map (·.1))
    rw [hv2, h1v']
    -- the rest of the node facts at u2, as in `writerWP_appendKlongs_j2U`
    have hnd : ([(k, child)].map Prod.fst).Nodup := by simp
    obtain ⟨_, _, _, hshape⟩ := hSh'
    obtain ⟨_, hD, hO, hS, hM, hV0⟩ := hJw
    have hrest := j2rest_cascade2 (wNode c.p base w1) (wNode c.p base u2) c.i w1.top.rootKey B
      (v.vals.map (·.1)) X Nn 0 d w1.next hpos hT1 hD hO hS hM hV0 (fun i a b => hN1 i a (by omega))
      (fun i a b => hG.wf _ _ (hw i (by omega))) (fun i a b => hG.times _ _ (hw i (by omega)))
      (fun i a b => hreach1 i (by omega))
      (by
        intro y hy
        rw [h1next']
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        exact hG.ids.2.2.2 e he)
      (by
        intro z hz hnc
        simp only [wNode, ht2, hf2' z hz hnc]) ?_
    · obtain ⟨hD2, hO2, hS2', hM2, hV2⟩ := hrest
      obtain ⟨hupre, hufirst⟩ := unlinked_facts n c.i hpos
      have hfirst : (n.toPrev (c.i - 1)).firstTime = n.firstTime := by
        obtain ⟨s, hs, hsf⟩ := hS2' x n hw2x hxB
        rw [hsf, hmxE]; exact hufirst s hs hsf
      have hfacts := j2facts_step (wNode c.p base u2) (updN (wNode c.p base u2) x (n.toPrev (c.i - 1)))
        c.i B (v.vals.map (·.1)) x x n (n.toPrev (c.i - 1)) hpos hO2 hS2' hM2 hV2 hw2x (updN_self _ _ _)
        (by rw [hmxE]; exact hupre) hfirst
        (fun xn2 h => by
          rw [updN_self] at h
          cases h
          exact ⟨n, hw2x, by rw [hmxE]; exact hupre, hxB, fun s hs hf => by rw [hmxE]; exact hufirst s hs hf⟩)
        (fun z _ hzx => updN_ne _ _ _ _ hzx)
      have hDL : DeadLiveN (updN (wNode c.p base u2) x (n.toPrev (c.i - 1))) c.i B (v.vals.map (·.1)) := by
        intro q qn hq
        by_cases hqx : q = x
        · subst hqx
          rw [updN_self] at hq
          cases hq
          rw [hmxE]
          exact (unlinked_j2 (wNode c.p base u2) c.i B _ hpos hD2 hO2 hS2' q n hw2x hxB).1
        · rw [updN_ne _ _ _ _ hqx] at hq
          exact hD2 q qn hq
      -- the nodes of the transaction's time are reached
      have hTtV : TtReachedN (updN (wNode c.p base
          { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) }) x (n.toPrev (c.i - 1)))
          c.i v.top.rootKey :=
        ttReachedN_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf x child ln
          (ln.add c.i (.key k child)) n k hT hLr hwL hk hwx
          (fun c' z hz => by
            rw [KNode.liveAt_of_times n c.i hnt] at hz
            exact ((hlv c' z).mp hz).2)
          (by rw [updN_ne _ _ _ _ hlx]; exact hL') (KNode.add_liveAt_new ln k child c.i hlnwf hlnt)
          (fun c' z hz hck => KNode.add_liveAt_keep ln k child c.i hlnwf hlnt c' z hz hck)
          (fun z h1 h2 => by rw [updN_ne _ _ _ _ h2]; exact hoth z h1 h2) hJ.1
          (fun xn2 h => by rw [updN_self] at h; cases h; exact hmxT)
      have hTt : TtReachedN (updN (wNode c.p base u2) x (n.toPrev (c.i - 1))) c.i u2.top.rootKey := by
        apply ttReachedN_cascadeU (updN (wNode c.p base w1) x (n.toPrev (c.i - 1)))
          (updN (wNode c.p base u2) x (n.toPrev (c.i - 1)))
          (wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) })
          c.i v.top.rootKey u2.top.rootKey w1.next (fun z => ∃ i, 0 ≤ i ∧ i ≤ d ∧ z = X i)
        · intro q qn hq hm
          by_cases hqx : q = x
          · subst hqx; rw [updN_self] at hq; cases hq; exact absurd hm hmxT
          rw [updN_ne _ _ _ _ hqx] at hq
          by_cases hql : q = leaf
          · subst hql
            rw [hWV, ← h1top']
            have h1 := hreach1 d (Nat.le_refl _)
            rw [hXd] at h1
            exact tReach_updN_self _ c.i _ _ _ hT1 h1
          · have hVm : updN (wNode c.p base
                { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) })
                x (n.toPrev (c.i - 1)) q = some qn := by
              rw [updN_ne _ _ _ _ hqx, hWV, updN_ne _ _ _ _ hql]; exact hq
            exact tReach_of_agree _ _ c.i v.top.rootKey
              (fun y hy => updN_ne _ _ _ _ (fun he => hxV (by rw [← he]; exact hy))) q (hTtV q qn hVm hm)
        · intro z hz hnc
          refine hfwd2 z (hkeep2 hord z ?_ (fun i hi1 hi2 he => hnc ⟨i, hi1, hi2, he⟩))
          rw [hVeq', h1top']; exact hz
        · rintro z ⟨i, hi1, hi2, rfl⟩
          rcases (hchain2 hord).1 i hi1 hi2 with h | h
          · exact Or.inl (hfwd2 _ h)
          · right
            intro zn hzn
            rw [updN_ne _ _ _ _ (hXne i hi2)] at hzn
            have hw' : wNode c.p base u2 (X i) = some ((Nn i).toPrev (c.i - 1)) := by
              simp only [wNode, ht2, (hS2w1 i hi1 (by omega)).2, Bool.false_eq_true, ↓reduceIte, h]
            rw [hw'] at hzn
            cases hzn
            exact time_not_mem_prefixAt (Nn i).ks c.i hpos
        · intro z zn hz hzn
          have hzx : z ≠ x := by intro hh; rw [hh, h1next'] at hz; omega
          rw [updN_ne _ _ _ _ hzx] at hzn
          apply hfwd2 z
          apply (hchain2 hord).2 z hz
          obtain ⟨_, htz, hkz⟩ := hS5' z hz
          unfold wNode at hzn
          rw [ht2, htz] at hzn
          simp only [Bool.false_eq_true, ↓reduceIte] at hzn
          cases hl : u2.nodes.lookup z with
          | none => rw [hl, hkz] at hzn; cases hzn
          | some _ => rfl
        · intro z hz hnc
          by_cases hzx : z = x
          · subst hzx; rw [updN_self, updN_self]
          · rw [updN_ne _ _ _ _ hzx, updN_ne _ _ _ _ hzx]
            simp only [wNode, ht2, hf2' z hz (fun i hi1 hi2 he => hnc ⟨i, hi1, hi2, he⟩)]
      exact ⟨hTt, hDL, hfacts.1, hfacts.2.1, hfacts.2.2.1, hfacts.2.2.2⟩
    · intro z zn hzn hz
      have htz : u2.taken.contains z = false := by
        rw [ht2]
        rcases hz with hz | ⟨i, a, b, rfl⟩
        · exact (hS5' z hz).2.1
        · exact (hS2w1 i a (by omega)).2
      have hlk : u2.nodes.lookup z = some zn := by
        unfold wNode at hzn
        rw [htz] at hzn
        simp only [Bool.false_eq_true, ↓reduceIte] at hzn
        cases hl : u2.nodes.lookup z with
        | some m => rw [hl] at hzn; exact hzn
        | none =>
          exfalso
          rw [hl] at hzn
          rcases hz with hz | ⟨i, a, b, rfl⟩
          · rw [(hS5' z hz).2.2] at hzn; cases hzn
          · have := hca' (X i) (by rw [(hS2w1 i a (by omega)).1]; rfl)
            rw [hl] at this; cases this
      exact cascadeShapeJ2_of c (wNode c.p base w1) B _ X K Nn 0 d [(k, child)] w1.next hS hM (fun i a b => hN1 i a (by omega))
        (fun i a b => hG.times _ _ (hw i (by omega))) (by rw [h1next']; exact hBn) hnd
        (by
          intro q hq y hy
          simp only [List.mem_singleton] at hq
          rw [hq] at hy
          rw [hNd] at hy
          have hyx : y = x := KNode.liveAt_fun _ _ _ _ _ hy hk
          exact Or.inl (by rw [hyx]; exact hxB))
        z zn hz (hshape z zn hlk hz)

/-- `ReplaceRootFullJ2OKC` holds: with no klong of the transaction in the root the
unlink changes nothing, so `CollapseUnlinkOK` holds and `replaceRootFullJ2OK_holds`
applies; else `replaceRootJ2_unlinked`. -/
theorem replaceRootFullJ2OKC_holds (c : Ctx) (base : View BVal) (f : Nat) (hf2 : 2 ≤ f) (B : NodeId)
    (hpos : 0 < c.i) (hsa2 : 2 ≤ c.p.splitAbove) : ReplaceRootFullJ2OKC c base f B := by
  intro w0 v x n only leaf ln k ps0 hI hR hJ hBn hvp hlf hPC hLr hlkL hlnl hk hpd hpk hlkx honly hcv hxl hnm
    hG hroom
  by_cases hlt : n.lastTime = some c.i
  · exact replaceRootJ2_unlinked c base f hf2 B hpos hsa2 w0 v x n only leaf ln k ps0 hI hR hJ hBn hvp hlf
      hPC hLr hlkL hlnl hk hpd hpk hlkx honly hcv hxl hnm hG hlt
  · exact replaceRootFullJ2OK_holds c base f hf2 B hpos hsa2 w0 v x n only leaf ln k ps0 hI hR hJ hBn hvp hlf
      hPC hLr hlkL hlnl hk hpd hpk hlkx honly hcv hxl hnm hG (fun h => absurd h hlt) hroom

/-- `ReplaceRootFullJ2OKC` at every run. -/
theorem replaceRootFullJ2OKC_run (p : Params) (hsa2 : 2 ≤ p.splitAbove) :
    ∀ ts B, ReplaceRootFullJ2OKC (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B := by
  intro ts B
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  exact replaceRootFullJ2OKC_holds (ctxOf p ts) _ (p.fuel + 1) hf2 B (by simp [ctxOf])
    (by simpa [ctxOf] using hsa2)

/-! ## The take-back's collapse without `CollapseUnlinkOK` -/

/-- `CollInvW` with the take-back's facts (bergdb 025-05, route P). -/
def CollInvJW (c : Ctx) (base : View BVal) (w0 : W) (fuelR : Nat) (C : W → Prop) (B : NodeId)
    (top0 : Top) (KO : KindOracle) (BK : NodeId) (BJ : NodeId) (v : W) : Prop :=
  FreshCache B v ∧ (C v → CollGetInvF c base w0 v fuelR ∧
    RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧ PutBook c B top0 v ∧ Book BK c v ∧
    KdInv KO BK v ∧ TakeJ2 c base BJ v ∧ BJ ≤ v.next)

set_option maxHeartbeats 1600000 in
/-- `writerWP_collapseRoot_collJC` for a condition C as `writerWP_collapseRoot_collW`
(bergdb 025-05, route P). -/
theorem writerWP_collapseRoot_collJW (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (C : W → Prop) (hC : ∀ v v', v.next ≤ v'.next → C v' → C v)
    (hfits : ∀ v x n only, C v → CollGetInvF c base w0 v fuelR →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => C v' → TreeOK (wNode c.p base v') c.i v'.top.rootKey → PutInvG c base v' →
          SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey))
    (BJ : NodeId) (hpos : 0 < c.i)
    (hRJ : ReplaceRootFullJ2OKC c base fuelR BJ) :
    ∀ fuel v, CollInvJW c base w0 fuelR C B top0 KO BK BJ v →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollInvJW c base w0 fuelR C B top0 KO BK BJ v') := by
  intro fuel v hCI
  have hBv : ViewIdsBelow B c.view := hB.good.ids
  refine writerWP_collapseRoot_inv key seg c (CollInvJW c base w0 fuelR C B top0 KO BK BJ)
    (fun x v => C v → SegDesc c base x v) ?_ ?_ ?_ ?_ fuel v hCI
  · rintro v ⟨hfc, hD⟩
    by_cases hno : ¬ C v
    · refine writerWP_mono (freshCache_descendToSegmentRoot key seg c v hBv hfc) ?_
      rintro _ v' ⟨hf', hle⟩
      exact ⟨⟨hf', fun hC' => absurd (hC v v' hle hC') hno⟩, fun hC' => absurd (hC v v' hle hC') hno⟩
    obtain ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ := hD (Classical.byContradiction hno)
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_descendToSegmentRoot_linked key seg c base hvc v hI.1.2.1 hI.2.2.2.1)
      (putBook_descendToSegmentRoot key seg c base B top0 hB v hb))
      (kd_descendToSegmentRoot KO BK key seg c v hv hk hbk hik)) ?_
    rintro x v' ⟨⟨⟨hr, _, hx, ps, hvp, hlf, hend, hcache, hlast⟩, hb'⟩, hbk', hik', _, _⟩
    refine ⟨⟨hb'.fresh, fun _ => ⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI,
      by rw [hr.1, hr.2.1]; exact hR, hb', hbk', hik', takeJ2_of_readsAs c base BJ v v' hJ hr,
      by rw [hr.2.2.2.2]; exact hBn⟩⟩, fun _ => ?_⟩
    unfold SegDesc
    rw [hr.1, hr.2.1]
    exact ⟨hx, ps, hvp, hlf, hend, hcache, hlast⟩
  · rintro x v ⟨hfc, hD⟩ hPw
    by_cases hno : ¬ C v
    · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_getNode_freshCache B x c v hBv hfc)
        (writerWP_getNode_all x c v base hvc)) (writerWP_getNode_cache x c v)) ?_
      rintro n v' ⟨⟨⟨hf', hle, _⟩, _, hl, _, _, _⟩, _, _, hp⟩
      exact ⟨⟨hf', fun hC' => absurd (hC v v' hle hC') hno⟩,
        fun hC' => absurd (hC v v' hle hC') hno, hl, hp⟩
    have hCv : C v := Classical.byContradiction hno
    obtain ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ := hD hCv
    have hP := hPw hCv
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_getNode_all x c v base hvc)
      (writerWP_getNode_cache x c v)) (putBook_getNode x c base B top0 hB v hb))
      (kd_getNode KO BK x c v hv hk hbk hik)) ?_
    rintro n v' ⟨⟨⟨⟨hr, hl, _, hpre, _⟩, _, _, hp⟩, hb'⟩, hbk', hik', _⟩
    exact ⟨⟨hb'.fresh, fun _ => ⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI,
      by rw [hr.1, hr.2.1]; exact hR, hb', hbk', hik', takeJ2_of_readsAs c base BJ v v' hJ hr,
      by rw [hr.2.2.2.2]; exact hBn⟩⟩, fun _ => segDesc_of_readsAs c base x v v' hP hr hpre hp, hl, hp⟩
  · rintro x v n only ⟨hfc, hD⟩ hPw hlk hxl hm _ honly hcv
    by_cases hno : ¬ C v
    · refine writerWP_mono (freshCache_takeBackRoot x _ only c v hBv hfc) ?_
      rintro _ v' ⟨hf', hle⟩
      exact ⟨hf', fun hC' => absurd (hC v v' hle hC') hno⟩
    have hCv : C v := Classical.byContradiction hno
    obtain ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ := hD hCv
    have hP := hPw hCv
    obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hbk hlk
    have hh : h ≠ 0 := by
      intro h0; subst h0
      have := kd_leaf hbk hlk hgh
      simp at this; rw [this] at hxl; cases hxl
    obtain ⟨a, hpa⟩ := segDesc_pathLast c base x v hP
    have hBx : B ≤ x := Blank.ge B c x hB.good
      (blank_of_firstTime B c x n hB.good.pos (cacheGood_lookup B c v hb.good x n hlk) (by simp [hm]))
    have hcr : WriterWP (takeBackRoot x (v.path.length - 1) only) c v
        (fun _ v' => (CollGetInvF c base w0 v' fuelR ∧ RangeOrder (wNode c.p base v') c.i v'.top.rootKey) ∧
          TakeJ2 c base BJ v') := by
      obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
      rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
      · subst hps
        have hx : x = v.top.rootKey := by rw [← hend]; rfl
        rw [hvp]
        exact writerWP_and (writerWP_and
          (writerWP_rootStep_space_collF fuelR hfR x only n c base w0 v hI hx hlk honly hcv hxl).1
          (writerWP_rootStep_space_rangeG x only n c base v _ _ _ hI hR hx hlk honly hcv hxl).1)
          (writerWP_rootStep_space_j2F x only n c base w0 v fuelR hI BJ hpos hJ hx hlk honly).1
      · subst hps
        obtain ⟨hLr, hLlk, hk', hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
        rw [hlen]
        exact writerWP_and (writerWP_and
          (writerWP_takeBackRoot_seg_collF fuelR hfR x ps0.length only n L ln k c base w0 v hI hLr hLlk
            hLl hk' hlk honly hcv hxl hpd hpk)
          (writerWP_takeBackRoot_seg_rangeG x ps0.length only n L ln k c base v _ _ _ hI hR hLr hLlk
            hLl hk' hlk honly hcv hxl hpd hpk))
          (writerWP_takeBackRoot_seg_j2F x ps0.length only n L ln k c base w0 v fuelR hI BJ hpos hJ hLr hLlk
            hLl hk' hlk honly hcv hxl hm hpd hpk)
    have hnx := @state_takeBackRoot (nextFromInvariant v) x (v.path.length - 1) only c v (Nat.le_refl _)
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hcr
      (putBook_takeBackRoot x _ only c base B top0 hB v hb hBx))
      (kd_takeBackRoot KO BK x _ only c v hv hk hbk hik a hpa g h hgh hh)) hnx) ?_
    rintro _ v' ⟨⟨⟨⟨⟨hI', hR'⟩, hJ'⟩, hb'⟩, hbk', hik', _, _⟩, hn'⟩
    exact ⟨hb'.fresh, fun _ => ⟨hI', hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩⟩
  · rintro x v n only ⟨hfc, hD⟩ hPw hlk hxl hm honly hcv
    by_cases hno : ¬ C v
    · refine writerWP_mono (freshCache_replaceRoot x _ only c v hBv hfc) ?_
      rintro _ v' ⟨hf', hle⟩
      exact ⟨hf', fun hC' => absurd (hC v v' hle hC') hno⟩
    have hCv : C v := Classical.byContradiction hno
    obtain ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ := hD hCv
    have hP := hPw hCv
    obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hbk hlk
    have hh : h ≠ 0 := by
      intro h0; subst h0
      have := kd_leaf hbk hlk hgh
      simp at this; rw [this] at hxl; cases hxl
    obtain ⟨a, hpa⟩ := segDesc_pathLast c base x v hP
    have hG := putInvG_of_book c base B top0 v hB hb
    have hPC := pathCached_of_segDesc c base x v n hP hlk
    have hfit := hfits v x n only hCv hI hR hP hlk hxl hm honly hcv
    have hbook := putBook_replaceRoot x (v.path.length - 1) only c base B top0 hB v hb
    have hkd := kd_replaceRoot KO BK x _ only c v hv hk hbk hik a hpa g h hgh hh
    have hnx := @state_replaceRoot (nextFromInvariant v) x (v.path.length - 1) only c v (Nat.le_refl _)
    have hP0 := hP
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      have hrg := (writerWP_rootStep_space_rangeG x only n c base v _ _ _ hI hR hx hlk honly hcv hxl).2
      have hcl := (writerWP_rootStep_space_collF fuelR hfR x only n c base w0 v hI hx hlk honly hcv hxl).2
      have hj := (writerWP_rootStep_space_j2F x only n c base w0 v fuelR hI BJ hpos hJ hx hlk honly).2 hm
      rw [hvp] at hbook hkd hnx ⊢
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and hcl hrg) hbook)
        hkd) hj) hnx) ?_
      rintro _ v' ⟨⟨⟨⟨⟨hI', hR'⟩, hb'⟩, hbk', hik', _, _⟩, hJ'⟩, hn'⟩
      exact ⟨hb'.fresh, fun _ => ⟨hI', hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩⟩
    · subst hps
      obtain ⟨hLr, hLlk, hk', hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      have hj : WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' => TakeJ2 c base BJ v') := by
        by_cases hroom : ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false
        · exact writerWP_replaceRoot_seg_j2F x ps0.length only n L ln k c base w0 v fuelR hI BJ hpos hJ hLr hLlk
            hLl hk' hlk honly hcv hxl hm hpd hpk hroom.1 hroom.2
        · exact writerWP_mono (hRJ w0 v x n only L ln k ps0 hI hR hJ hBn hvp hlf hPC hLr hLlk hLl hk' hpd hpk
            hlk honly hcv hxl hm hG hroom) (fun _ v' h' => h'.1)
      rw [hlen] at hfit hbook hkd hnx ⊢
      have hcas := writerWP_replaceRoot_seg_cascadeC fuelR hfR x only n L ln k ps0 c base w0 v hI hR hG hsa2
        hvp hlf hPC hLr hLlk hLl hk' hpd hpk hlk honly hcv hxl
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and hcas hfit) hbook)
        hkd) hj) hnx) ?_
      rintro _ v' ⟨⟨⟨⟨⟨⟨hT', hU', hW', _, _, hread', hR'⟩, hf'⟩, hb'⟩, hbk', hik', _, _⟩, hJ'⟩, hn'⟩
      have hG' := putInvG_of_book c base B top0 v' hB hb'
      refine ⟨hb'.fresh, fun hC' => ?_⟩
      have hf'' := hf' hC' hT' hG'
      refine ⟨⟨⟨hT', hU', fun y yn _ hy => hG'.times y yn hy,
        fun y yn cc z hy hyn hl hc => hICEk v' hbk' hik' hU' y yn cc z hy hyn hl hc⟩,
        hread' hf'', hf'', fun y yn _ hy => hW' y yn hy, fun y yn _ hy => hG'.keyNoValue y yn hy⟩,
        hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩

/-- `writerWP_collapseRoot_collJ` without `CollapseUnlinkOK` (`hunl`): the
reading's step by `writerWP_replaceRoot_seg_cascadeC`, the take-back's through a
full leaf by `ReplaceRootFullJ2OKC`. -/
theorem writerWP_collapseRoot_collJC (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hfits : ∀ v x n only, CollGetInvF c base w0 v fuelR →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey))
    (BJ : NodeId) (hpos : 0 < c.i)
    (hRJ : ReplaceRootFullJ2OKC c base fuelR BJ) :
    ∀ fuel v, CollGetInvF c base w0 v fuelR → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
      PutBook c B top0 v → Book BK c v → KdInv KO BK v → TakeJ2 c base BJ v → BJ ≤ v.next →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollGetInvF c base w0 v' fuelR ∧
        RangeOrder (wNode c.p base v') c.i v'.top.rootKey ∧ PutBook c B top0 v' ∧ Book BK c v' ∧
        KdInv KO BK v' ∧ TakeJ2 c base BJ v' ∧ BJ ≤ v'.next) := by
  intro fuel v hI hR hb hbk hik hJ hBn
  refine writerWP_mono (writerWP_collapseRoot_collJW fuelR hfR key seg c base hvc w0 B top0 hB KO BK hv hk
    hICEk hsa2 (fun _ => True) (fun _ _ _ _ => trivial)
    (fun v x n only _ hI hR hP hlk hxl hm honly hcv => writerWP_mono
      (hfits v x n only hI hR hP hlk hxl hm honly hcv) (fun _ _ hf _ _ _ => hf))
    BJ hpos hRJ fuel v ⟨hb.fresh, fun _ => ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩⟩) ?_
  exact fun _ _ h => h.2 trivial
/-- The collapse keeps `DelInvJ`, given `CollapseFitsOK` and
`ReplaceRootFullJ2OKC`. -/
theorem writerWP_collapseRoot_delJC (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hC : CollapseFitsOK c base f) (w0 : W)
    (k0 : Key) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (BJ : NodeId) (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OKC c base f BJ)
    (v : W) (hI : DelInvJ c base w0 k0 f KO BK BJ v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvJ c base w0 k0 f KO BK BJ v') := by
  obtain ⟨⟨⟨hP, hG, hR, hICE, hF, hread, B, top0, hB, hbook⟩, hbk, hik⟩, hJ, hBn⟩ := hI
  have hCI : CollGetInvF c base v v f := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_collapseRoot_collJC f hf2 key seg c base hvc v B top0 hB KO BK hv hk
    hICEk hsa2 (hC v) BJ hpos hRJ c.p.fuel v hCI hR hbook hbk hik hJ hBn) ?_
  rintro _ v' ⟨⟨⟨hT', hu', _, hICE'⟩, hread', hF', _, _⟩, hR', hbook', hbk', hik', hJ', hBn'⟩
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨⟨hP', hG', hR', hICE', hF', fun key' hk' => ?_, B, top0, hB, hbook'⟩, hbk', hik'⟩, hJ', hBn'⟩
  rw [hread' key']
  exact hread key' hk'

/-- `afterDelete` keeps `DelInvJ`, given `MergeStepOK`, `CollapseFitsOK`
and `ReplaceRootFullJ2OKC`. -/
theorem writerWP_afterDelete_delJC (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (hC : CollapseFitsOK c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (BJ : NodeId) (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OKC c base fuelR BJ)
    (w0 : W) (k0 : Key) (v : W) (hI : DelInvJ c base w0 k0 fuelR KO BK BJ v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvJ c base w0 k0 fuelR KO BK BJ v') :=
  writerWP_afterDelete_inv key g h c (DelInvJ c base w0 k0 fuelR KO BK BJ)
    (fun v hI => writerWP_mergeUp_delJ key g c base hvc fuelR hfR hM KO BK hv hk hICEk hsa2 hcap BJ hpos
      w0 k0 c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_delJC key g c base hvc fuelR hfR hC w0 k0 KO BK hv hk hICEk hsa2
      BJ hpos hRJ v hI) v hI

end SIS.Tree
