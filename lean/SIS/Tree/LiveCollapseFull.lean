/-
Root collapse's step at a segment root below a full segment leaf, with the live
counts (bergdb 030-01, step 4's rest): `replaceRoot`'s cascade at the leaf. The
tree there has no hole (the leaf's klong names x's child, filled), so the
cascade's walk keeps the live counts as it stands (`writerWP_appendKlongs_chainGL`).
`writerWP_replaceRoot_seg_cascadeL` is `writerWP_replaceRoot_seg_cascadeC`
(CollapseCommuteStep.lean) with that walk beside the tree's and the live counts
in its post; `collapseSegFullLiveOK_holds` discharges `CollapseSegFullLiveOK`.
-/
import SIS.Tree.LiveCollapseStep

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node out of reach changes no live count. -/
theorem liveEdges_updN_unreach (p : Params) (N : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (m : KNode) (hx : ¬ TReach N t r x) (h : LiveEdges p N t r) : LiveEdges p (updN N x m) t r := by
  have hback := tReach_updN_unreach N t r x m hx
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · have hrx : r ≠ x := fun he => hx (by rw [← he]; exact TReach.root)
    rw [updN_ne _ _ _ _ hrx] at hrn; exact h.1 rn hrn
  · have hu' := hback u hu
    have hux : u ≠ x := fun he => hx (by rw [← he]; exact hu')
    rw [updN_ne _ _ _ _ hux] at hun
    have hyx : y ≠ x := fun he => hx (by rw [← he]; exact TReach.link hu' ⟨un, hun, hc⟩)
    rw [updN_ne _ _ _ _ hyx] at hyn
    exact h.2 u un c y yn hu' hun hc hyn

set_option maxHeartbeats 4000000 in
/-- `writerWP_replaceRoot_seg_cascadeF` without `CollapseUnlinkOK`: the leaf's
cascade runs from the state before the unlink (the two steps commute,
`replaceRoot_linkFirst`), and x is out of reach after it. -/
theorem writerWP_replaceRoot_seg_cascadeL (fuelR : Nat) (hfR : 2 ≤ fuelR) (x : NodeId) (only : Nat)
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
    (hmg : c.p.merges = true) (hMP : MergeParamsOK c.p) (Hl : NodeId → Prop)
    (hLX : LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' =>
      (TreeOK (wNode c.p base v') c.i v'.top.rootKey ∧
      (∀ z, TReach (wNode c.p base v') c.i v'.top.rootKey z → v'.taken.contains z = false) ∧
      (∀ z zn, wNode c.p base v' z = some zn → klongsWf zn.ks = true) ∧
      v'.taken = v.taken ∧ v'.vals = v.vals ∧
      (SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey →
        ∀ key, wGetAt c.p c.i base v' fuelR key = wGetAt c.p c.i base w0 fuelR key) ∧
      RangeOrder (wNode c.p base v') c.i v'.top.rootKey) ∧
      LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
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
    -- the cascade from the state before the unlink, where x's node is n (026-16, 5.3)
    have hcas : WriterWP (appendKlongs d leaf [(k, child)]) c
        { v with trail := "rc.replace.segment" :: v.trail } (fun _ v' =>
          (TreeOK (wNode c.p base v') c.i v'.top.rootKey ∧
          (∀ z, TReach (wNode c.p base v') c.i v'.top.rootKey z → v'.taken.contains z = false) ∧
          (∀ z zn, wNode c.p base v' z = some zn → klongsWf zn.ks = true) ∧
          v'.taken = v.taken ∧ v'.vals = v.vals ∧
          (SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey →
            ∀ key, wGetAt c.p c.i base v' fuelR key = wGetAt c.p c.i base w0 fuelR key) ∧
          RangeOrder (wNode c.p base v') c.i v'.top.rootKey) ∧
          ¬ TReach (wNode c.p base v') c.i v'.top.rootKey x ∧
          LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
      generalize hw1 : ({ v with trail := "rc.replace.segment" :: v.trail } : W) = w1
      have h1t' : w1.taken = v.taken := by rw [← hw1]
      have h1top' : w1.top = v.top := by rw [← hw1]
      have h1next' : w1.next = v.next := by rw [← hw1]
      have h1v' : w1.vals = v.vals := by rw [← hw1]
      have h1path' : w1.path = v.path := by rw [← hw1]
      have h1l' : ∀ y, y ≠ x → w1.nodes.lookup y = v.nodes.lookup y := fun y _ => by rw [← hw1]
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
      have hli := writerWP_appendKlongs_chainGL c base v.path 0 d X K Nn
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
      simp only [Nat.zero_add] at hch hrg hli
      rw [hXd] at hch hrg hli
      refine writerWP_mono (writerWP_and (writerWP_and hch hrg) hli) ?_
      rintro _ w2 ⟨⟨⟨hT2, ⟨_, ht2, _, _, hv2⟩, _, hreach2, hW2, hread2, _⟩, _, _, _, _, hRO2⟩,
        ⟨_, _, _, _, hLE2⟩⟩
      have hVeq' : updN (wNode c.p base w1) leaf ([(k, child)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
          (Nn d)) = wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } := by
        rw [hNd, hWV]; rfl
      refine ⟨⟨hT2, fun z hz => ?_, hW2, by rw [ht2, h1t'], by rw [hv2, h1v'], fun hfit key => ?_, hRO2⟩, ?_,
        ?_⟩
      rotate_right
      · -- the live counts: the room case's tree has them, and the cascade keeps them
        refine hLE2 hMP ?_
        rw [hVeq', h1top']
        exact liveEdges_collapseSeg c.p (wNode c.p base v) _ c.i v.top.rootKey leaf x child ln
          (ln.add c.i (.key k child)) n k 0 Hl hT hLX hHl hLr hwL hlnl hk hwx hxl hcl hmg hMP.1 hL'
          (by rw [KNode.add_leaf]) hlinksL (addKeys_liveAt_length c.i [(k, child)] ln hlnwf hlnt) hoth
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
      · -- x is out of reach after the cascade
        intro hx2
        rcases hreach2 x hx2 with h | ⟨h1, _⟩
        · rw [hVeq', h1top'] at h
          obtain ⟨len, hlen⟩ := h.pathLen
          exact (segCollapse_pathLen (wNode c.p base v) _ c.i v.top.rootKey leaf x child k 0 ln
            (ln.add c.i (.key k child)) n hT hLr hwL hk hwx hcl hL' hlinksL hoth x len hlen).1 rfl
        · rw [h1next'] at h1; omega
    -- the unlink, then the cascade: from the state with x's previous version, it
    -- runs as from the state before (`xwp_appendKlongs`), where x is out of reach after
    unfold unlink
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known x n c { v with trail := "rc.replace.segment" :: v.trail } hlkx]
    split
    · simp only [putNode, writerWP_modify]
      have hJ : RJ x n v.path { v with trail := "rc.replace.segment" :: v.trail } := ⟨hlkx, hxn, rfl⟩
      have hW := xwp_appendKlongs (m := n.toPrev (c.i - 1)) v.path d leaf [(k, child)] c _ hJ hlx hpx
      refine writerWP_setX_of_xwp (m := n.toPrev (c.i - 1))
        (u := { v with trail := "rc.replace.segment" :: v.trail }) ⟨hW.1, writerWP_mono hcas ?_⟩
      rintro _ u2 ⟨⟨hT2, hU2, hW2, ht2, hv2, hread2, hR2⟩, hx2, hLE2⟩
      have hxt2 : u2.taken.contains x = false := by rw [ht2]; exact hxt
      obtain ⟨a1, a2, a3, a4, a5⟩ := collapsePost_setX c base w0 u2 fuelR x (n.toPrev (c.i - 1)) hxt2 hx2
        (KNode.toPrev_wf _ _ (hG.wf x n hwx)) hT2 hU2 hW2 hread2 hR2
      refine ⟨⟨a1, a2, a3, ht2, hv2, a4, a5⟩, ?_⟩
      have hWN : wNode c.p base (setX x (n.toPrev (c.i - 1)) u2) =
          updN (wNode c.p base u2) x (n.toPrev (c.i - 1)) :=
        wNode_upsert_updN c.p base u2 _ x _ rfl rfl hxt2
      rw [hWN]
      exact liveEdges_updN_unreach c.p _ c.i _ x _ hx2 hLE2
    · simp only [writerWP_pure]
      exact writerWP_mono hcas (fun _ w2 h => ⟨h.1, h.2.2⟩)

/-- The collapse's step at a segment root below a full segment leaf keeps the
live counts (bergdb 030-01, step 4's rest): `CollapseSegFullLiveOK` holds. -/
theorem collapseSegFullLiveOK_holds (c : Ctx) (base : View BVal) (B : NodeId) (hm : c.p.merges = true)
    (hMP : MergeParamsOK c.p) (hsa2 : 2 ≤ c.p.splitAbove) (hB : PutBase c base B) :
    CollapseSegFullLiveOK c base B := by
  intro x v n only w0 F top0 Hl d leaf ln k hCI hR hpb hsd hX hHl hl hleaf honly hcv _ hpd hpk hlen hlkL
    _ _
  have hG : PutInvG c base v := putInvG_of_book c base B top0 v hB hpb
  -- the collapse's invariant at a fuel of two at least, read against v itself
  have hF2 : 2 ≤ max F 2 := Nat.le_max_right _ _
  have hI : CollGetInvF c base v v (max F 2) :=
    ⟨hCI.1, fun _ => rfl, segFits_mono _ _ _ _ _ hCI.2.2.1 (Nat.sub_le_sub_right (Nat.le_max_left F 2) 1),
      hCI.2.2.2.1, hCI.2.2.2.2⟩
  obtain ⟨_, ps, hvp, hlf, _, hcache, hlast⟩ := id hsd
  have hPC := pathCached_of_segDesc c base x v n hsd hl
  rcases hlast with hps | ⟨ps0, k', L, ln', hps, hL, hLn, hLl'⟩
  · exfalso; rw [hvp, hps] at hlen; simp at hlen
  · rw [hps] at hvp hlf hcache
    obtain ⟨hLR, hlkL', hk', hlen', hpd', hpk'⟩ :=
      segDesc_seg c base x v ps0 k' L ln' hvp hlf hcache hL hLn
    have hd : d = ps0.length := by omega
    subst hd
    have hLe : L = leaf := by rw [hpd'] at hpd; exact Option.some.inj hpd
    subst hLe
    have hke : k' = k := by
      rw [hpk'] at hpk
      simp only [Option.some.injEq, Prod.mk.injEq] at hpk
      exact hpk.1
    subst hke
    have hlne : ln' = ln := by rw [hlkL'] at hlkL; exact Option.some.inj hlkL
    subst hlne
    exact writerWP_mono (writerWP_replaceRoot_seg_cascadeL (max F 2) hF2 x only n L ln' k' ps0 c base v v hI
      hR hG hsa2 hvp hlf hPC hLR hlkL' hLl' hk' hpd' hpk' hl honly hcv hleaf hm hMP Hl hX hHl)
      (fun _ _ h => h.2)

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts, every run ends with the live counts, given the merges with a full or
compacting parent (`MergeLiveFullOK`) and R3 after the merges' loop. -/
theorem writerWP_afterDelete_liveFR (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeLiveFullOK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveRF key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB hF
    (collapseSegFullLiveOK_holds c base B hm hMP hsa2 hB) v hJ hpb hhi hLH hR3

end SIS.Tree
