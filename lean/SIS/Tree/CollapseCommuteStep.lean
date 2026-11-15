/-
Root collapse at a segment root without `CollapseUnlinkOK` (bergdb 026-16, section
5.3; 024-22, section 11.1): the leaf's cascade runs from the state before the
unlink of the root x (`xwp_appendKlongs`, CollapseCommute.lean), where the tree is
the writer's, and after it x is out of reach, so x's previous version changes
nothing that is read (`collapsePost_setX`).
-/
import SIS.Tree.LatestTop
import SIS.Tree.CollapseCommute

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- After the cascade x is out of reach: a change of x's node keeps the tree, the
untaken reached nodes, the klongs' form, the reading and the walk's ranges. -/
theorem collapsePost_setX (c : Ctx) (base : View BVal) (w0 u2 : W) (fuelR : Nat) (x : NodeId)
    (mx : KNode) (hxt : u2.taken.contains x = false)
    (hx : ¬ TReach (wNode c.p base u2) c.i u2.top.rootKey x) (hmx : klongsWf mx.ks = true)
    (hT : TreeOK (wNode c.p base u2) c.i u2.top.rootKey)
    (hU : ∀ z, TReach (wNode c.p base u2) c.i u2.top.rootKey z → u2.taken.contains z = false)
    (hW : ∀ z zn, wNode c.p base u2 z = some zn → klongsWf zn.ks = true)
    (hread : SegFits (wNode c.p base u2) c.i (fuelR - 1) u2.top.rootKey →
      ∀ key, wGetAt c.p c.i base u2 fuelR key = wGetAt c.p c.i base w0 fuelR key)
    (hR : RangeOrder (wNode c.p base u2) c.i u2.top.rootKey) :
    TreeOK (wNode c.p base (setX x mx u2)) c.i (setX x mx u2).top.rootKey ∧
    (∀ z, TReach (wNode c.p base (setX x mx u2)) c.i (setX x mx u2).top.rootKey z →
      (setX x mx u2).taken.contains z = false) ∧
    (∀ z zn, wNode c.p base (setX x mx u2) z = some zn → klongsWf zn.ks = true) ∧
    (SegFits (wNode c.p base (setX x mx u2)) c.i (fuelR - 1) (setX x mx u2).top.rootKey →
      ∀ key, wGetAt c.p c.i base (setX x mx u2) fuelR key = wGetAt c.p c.i base w0 fuelR key) ∧
    RangeOrder (wNode c.p base (setX x mx u2)) c.i (setX x mx u2).top.rootKey := by
  have hWN : wNode c.p base (setX x mx u2) = updN (wNode c.p base u2) x mx :=
    wNode_upsert_updN c.p base u2 _ x mx rfl rfl hxt
  have htop : (setX x mx u2).top = u2.top := rfl
  have htk : (setX x mx u2).taken = u2.taken := rfl
  rw [hWN, htop, htk]
  generalize hN : wNode c.p base u2 = N at hx hT hU hW hread hR
  have hag : ∀ z, TReach N c.i u2.top.rootKey z → updN N x mx z = N z :=
    fun z hz => updN_ne N x mx z (fun he => hx (he ▸ hz))
  have hback : ∀ z, TReach (updN N x mx) c.i u2.top.rootKey z → TReach N c.i u2.top.rootKey z :=
    tReach_updN_unreach N c.i u2.top.rootKey x mx hx
  have hfwd : ∀ z, TReach N c.i u2.top.rootKey z → TReach (updN N x mx) c.i u2.top.rootKey z :=
    tReach_of_agree (updN N x mx) N c.i u2.top.rootKey (fun z hz => (hag z (hback z hz)).symm)
  have hxS : ¬ ReachS N c.i u2.top.rootKey x := fun h => hx (reachS_tReach _ _ _ _ h)
  have hwfS : ∀ z zn, ReachS N c.i u2.top.rootKey z → N z = some zn → klongsWf zn.ks = true :=
    fun z zn _ h => hW z zn h
  refine ⟨treeOK_updN_unreach N c.i u2.top.rootKey x mx hT hx, fun z hz => hU z (hback z hz),
    fun z zn hz => ?_, fun hfit key => ?_, rangeOrder_agree N _ c.i u2.top.rootKey hR hag⟩
  · by_cases hzx : z = x
    · subst hzx; rw [updN_self] at hz; cases hz; exact hmx
    · rw [updN_ne _ _ _ _ hzx] at hz; exact hW z zn hz
  · have hfit' : SegFits N c.i (fuelR - 1) u2.top.rootKey := by
      refine segFits_transfer (updN N x mx) N c.i (fuelR - 1) u2.top.rootKey u2.top.rootKey hfit
        (fun z hz => tReach_reachS _ _ _ _ (hfwd z (reachS_tReach _ _ _ _ hz))) ?_
      intro z zn hz hzn hl
      have hzx : z ≠ x := fun he => hxS (he ▸ hz)
      exact ⟨zn, by rw [updN_ne _ _ _ _ hzx]; exact hzn, hl, fun c' y hy => ⟨c', hy⟩⟩
    have h1 := hread hfit' key
    unfold wGetAt at h1 ⊢
    rw [hN] at h1
    have hV : wValue base (setX x mx u2) = wValue base u2 := wValue_congr' base _ _ rfl rfl
    rw [hWN, hN, htop, hV, ← h1]
    exact getFromR_updN_unreach N (wValue base u2) c.i fuelR u2.top.rootKey x mx hwfS hxS key

set_option maxHeartbeats 4000000 in
/-- `writerWP_replaceRoot_seg_cascadeF` without `CollapseUnlinkOK`: the leaf's
cascade runs from the state before the unlink (the two steps commute,
`replaceRoot_linkFirst`), and x is out of reach after it. -/
theorem writerWP_replaceRoot_seg_cascadeC (fuelR : Nat) (hfR : 2 ≤ fuelR) (x : NodeId) (only : Nat)
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
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) :
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
          ¬ TReach (wNode c.p base v') c.i v'.top.rootKey x) := by
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
      simp only [Nat.zero_add] at hch hrg
      rw [hXd] at hch hrg
      refine writerWP_mono (writerWP_and hch hrg) ?_
      rintro _ w2 ⟨⟨hT2, ⟨_, ht2, _, _, hv2⟩, _, hreach2, hW2, hread2, _⟩, _, _, _, _, hRO2⟩
      have hVeq' : updN (wNode c.p base w1) leaf ([(k, child)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
          (Nn d)) = wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } := by
        rw [hNd, hWV]; rfl
      refine ⟨⟨hT2, fun z hz => ?_, hW2, by rw [ht2, h1t'], by rw [hv2, h1v'], fun hfit key => ?_, hRO2⟩, ?_⟩
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
      rintro _ u2 ⟨⟨hT2, hU2, hW2, ht2, hv2, hread2, hR2⟩, hx2⟩
      have hxt2 : u2.taken.contains x = false := by rw [ht2]; exact hxt
      obtain ⟨a1, a2, a3, a4, a5⟩ := collapsePost_setX c base w0 u2 fuelR x (n.toPrev (c.i - 1)) hxt2 hx2
        (KNode.toPrev_wf _ _ (hG.wf x n hwx)) hT2 hU2 hW2 hread2 hR2
      exact ⟨a1, a2, a3, ht2, hv2, a4, a5⟩
    · simp only [writerWP_pure]
      exact writerWP_mono hcas (fun _ w2 h => h.1)

set_option maxHeartbeats 1600000 in
/-- `writerWP_collapseRoot_coll` without `CollapseUnlinkOK` (`hunl`): a
replaceRoot at a segment root takes the leaf's cascade from the state before the
unlink (`writerWP_replaceRoot_seg_cascadeC`). -/
theorem writerWP_collapseRoot_collC (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hfits : ∀ v x n only, CollGetInvF c base w0 v fuelR →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey)) :
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
      have hcas := writerWP_replaceRoot_seg_cascadeC fuelR hfR x only n L ln k ps0 c base w0 v hI hR hG hsa2
        hvp hlf hPC hLr hLlk hLl hk' hpd hpk hlk honly hcv hxl
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hcas hfit) hbook) hkd) ?_
      rintro _ v' ⟨⟨⟨⟨hT', hU', hW', _, _, hread', hR'⟩, hf'⟩, hb'⟩, hbk', hik', _, _⟩
      have hG' := putInvG_of_book c base B top0 v' hB hb'
      refine ⟨⟨⟨hT', hU', fun y yn _ hy => hG'.times y yn hy,
        fun y yn cc z hy hyn hl hc => hICEk v' hbk' hik' hU' y yn cc z hy hyn hl hc⟩,
        hread' hf', hf', fun y yn _ hy => hW' y yn hy, fun y yn _ hy => hG'.keyNoValue y yn hy⟩,
        hR', hb', hbk', hik'⟩


/-! ## Case 4 with `CollapseFitsOK` alone -/

/-- The collapse keeps `DelInv`, given `CollapseFitsOK` alone. -/
theorem writerWP_collapseRoot_delC (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hC : CollapseFitsOK c base f) (w0 : W)
    (k0 : Key) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (v : W) (hI : DelInv c base w0 k0 f KO BK v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInv c base w0 k0 f KO BK v') := by
  obtain ⟨⟨hP, hG, hR, hICE, hF, hread, B, top0, hB, hbook⟩, hbk, hik⟩ := hI
  have hCI : CollGetInvF c base v v f := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_collapseRoot_collC f hf2 key seg c base hvc v B top0 hB KO BK hv hk
    hICEk hsa2 (hC v) c.p.fuel v hCI hR hbook hbk hik) ?_
  rintro _ v' ⟨⟨⟨hT', hu', _, hICE'⟩, hread', hF', _, _⟩, hR', hbook', hbk', hik'⟩
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨hP', hG', hR', hICE', hF', fun key' hk' => ?_, B, top0, hB, hbook'⟩, hbk', hik'⟩
  rw [hread' key']
  exact hread key' hk'

/-- `afterDelete` keeps `DelInv`, given the merge's obligation and `CollapseFitsOK` alone. -/
theorem writerWP_afterDelete_delC (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (hC : CollapseFitsOK c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) (v : W) (hI : DelInv c base w0 k0 fuelR KO BK v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInv c base w0 k0 fuelR KO BK v') :=
  writerWP_afterDelete_inv key g h c (DelInv c base w0 k0 fuelR KO BK)
    (fun v hI => writerWP_mergeUp_del key g c base hvc fuelR hfR hM KO BK hv hk hICEk hsa2 hcap w0 k0
      c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_delC key g c base hvc fuelR hfR hC w0 k0 KO BK hv hk hICEk hsa2
      v hI) v hI


/-- Case 4 at the reading fuel p.fuel + 1 inside the delete, with no room premise
of the collapse: `OpGetCaseOK'` from `DelStepsOK`, `MergeStepOK`,
`CollapseFitsOK` (no `CollapseUnlinkOK`) and the pointers of every run within reach (TP4). -/
theorem opGetCaseOK'_delMergeC (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOK p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
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
    (fun g h v hv' => writerWP_afterDelete_delC key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_del key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delC key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

/-- Case 4 (`OpGetCaseOK`) with no room premise of the collapse: from
`DelStepsOK`, `MergeStepOK`, `CollapseFitsOK` (no `CollapseUnlinkOK`), `TxSegFitsOK` and TP4. -/
theorem opGetCaseOK_delMergeC (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOK p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R DelMergeCase :=
  opGetCaseOK_of' p R DelMergeCase (opGetCaseOK'_delMergeC p R hS hM hC hsa2 hcap hMM hPtr) hfit

end SIS.Tree
