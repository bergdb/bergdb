/-
Case (4) of the take-back, a delete with the merges on (bergdb 024-12, TP7;
`DelMergeCase`): the merge's step for the take-back (`MergeStepJ2OKF`, from the
delete's inner invariant with the take-back's facts, `DelInvJF`), with the
merge below a parent with room (`writerWP_merge_made_j2`), and the take-back's
collapse steps for `CollGetInvF` (`writerWP_takeBackRoot_seg_j2F`,
`writerWP_replaceRoot_seg_j2F`, `writerWP_rootStep_space_j2F`). The case runs on
latest's F3/F4 route (TakeDelMergeF4.lean, TakeDelStepsF4.lean).
-/
import SIS.Tree.DelMergeCaseF
import SIS.Tree.DelMergeCaseF2
import SIS.Tree.TakeNextGrows
import SIS.Tree.TakeDeadNewSegFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The delete's inner invariant at the reading fuel f with the take-back's
(B), (C) and node facts. -/
def DelInvJF (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat) (B : NodeId) (v : W) : Prop :=
  DelInvF c base w0 key f v ∧ TakeJ2 c base B v ∧ B ≤ v.next

/-- Obligation: a merge of the loop, from a state inside a delete with the path
down to the merged node (`PathOK`), keeps `TakeJ2`. -/
def MergeStepJ2OKF (c : Ctx) (base : View BVal) (f : Nat) (B : NodeId) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode),
    DelInvJF c base w0 key f B v → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    PathOK c v d X K Nn → X d = x →
    WriterWP (merge x d) c v (fun _ v' => TakeJ2 c base B v')

/-! ## The collapse -/

/-- `takeBackRoot` at a segment root x that the transaction made keeps `TakeJ2`. -/
theorem writerWP_takeBackRoot_seg_j2F (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (f : Nat) (hI : CollGetInvF c base w0 v f)
    (B : NodeId) (hpos : 0 < c.i) (hJ : TakeJ2 c base B v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) (hmade : n.firstTime = some c.i)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x)) :
    WriterWP (takeBackRoot x (d + 1) only) c v (fun _ v' => TakeJ2 c base B v') := by
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
            TakeJ2 c base B w' := by
          intro w' h'v h't h'n h'top
          have hL' : wNode c.p base w' leaf = some (ln.repoint j child) := by
            simp only [wNode, h't, hLt', Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
          have hoth : ∀ y, y ≠ leaf → y ≠ x → wNode c.p base w' y = wNode c.p base v y := by
            intro y hyl hyx
            simp only [wNode, h't, hyt y hyx, h'n, lookup_upsert, hyl, ↓reduceIte]
          have hX : wNode c.p base w' x = none := by simp [wNode, h't]
          have hBx : B ≤ x := ge_of_firstTime2 _ _ _ hJ.2.2.2.1 x n hwx hmade
          have hxv : x ∉ v.vals.map (·.1) := fun h => by rw [hJ.2.2.2.2.2 x h] at hwx; cases hwx
          have hjk := kd_linkIndex_some ln x k j hj
          have hlen : (prefixAt ln.ks (c.i - 1)).length ≤ j := by
            rcases Nat.lt_or_ge j (prefixAt ln.ks (c.i - 1)).length with hlt | hge
            · have := hJ.2.2.1 leaf ln hwL k x (mem_prefixAt_of_lt ln.ks _ j _ hlt hjk)
              omega
            · exact hge
          have hpre : prefixAt (ln.repoint j child).ks (c.i - 1) = prefixAt ln.ks (c.i - 1) := by
            unfold KNode.repoint
            rw [hjk]
            exact prefixAt_set_late ln.ks (c.i - 1) j k child hlen
              (fun k0 h0 => by rw [hjk] at h0; cases h0; exact ⟨k, x, rfl⟩)
          have hfacts := j2facts_step (wNode c.p base v) (wNode c.p base w') c.i B (v.vals.map (·.1))
            leaf x ln (ln.repoint j child) hpos hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2.1 hJ.2.2.2.2.2 hwL hL' hpre
            (KNode.firstTime_repoint ln j child) (fun xn2 h => by rw [hX] at h; cases h) hoth
          unfold TakeJ2 J2N
          rw [h'top, h'v]
          refine ⟨?_, ?_, hfacts⟩
          · exact ttReachedN_segCollapse (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey leaf
              x child ln (ln.repoint j child) n k hT hlf hwL hk hwx
              (fun c' z hz => by
                rw [KNode.liveAt_of_times n c.i hnt] at hz
                exact ((hlv c' z).mp hz).2)
              hL' (KNode.repoint_liveAt_new ln x child k j c.i hj hlnt)
              (fun c' z hz hck => KNode.repoint_liveAt_keep ln x child k j c.i hj hlnt c' z hz hck)
              hoth hJ.1 (fun xn2 h => by rw [hX] at h; cases h)
          · exact deadLiveN_segTake (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey B _ leaf x
              child ln k j hT hJ.2.1 hlf hwL hlnl hlnt hj hk hBx hxv hL' hX hoth
        exact hfin _ rfl rfl rfl rfl
    · exact writerWP_throw _ _ _ _

/-- `replaceRoot` at a segment root x below the segment leaf, with room, keeps
`TakeJ2`. -/
theorem writerWP_replaceRoot_seg_j2F (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (f : Nat) (hI : CollGetInvF c base w0 v f)
    (B : NodeId) (hpos : 0 < c.i) (hJ : TakeJ2 c base B v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) (hnm : n.firstTime ≠ some c.i)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 1 + 1 ≤ c.p.M)
    (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (replaceRoot x (d + 1) only) c v (fun _ v' => TakeJ2 c base B v') := by
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
    refine writerWP_mono (writerWP_unlink_fate x n c _ (by simpa using hlkx)) ?_
    intro _ w1 ⟨h1t, h1top, h1v, h1x, h1l⟩
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
    have hX : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } x =
        some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
      simp only [wNode, h1t, hxt, Bool.false_eq_true, ↓reduceIte, lookup_upsert, Ne.symm hlx, h1x]
    have hnwf := hI.2.2.2.1 x n hxR hwx
    have hxB : x < B := lt_of_firstTime_ne _ _ _ hJ.2.2.2.2.1 x n hwx hnm
    obtain ⟨s0, hs0⟩ : ∃ s0, ln.firstTime = some s0 := by
      rcases Nat.lt_or_ge leaf B with h | h
      · obtain ⟨s, _, hf⟩ := hJ.2.2.2.1 leaf ln hwL h
        exact ⟨s, hf⟩
      · exact ⟨c.i, hJ.2.2.2.2.1 leaf ln hwL h⟩
    obtain ⟨hupre, hufirst⟩ := unlinked_facts n c.i hpos
    have hfacts := j2facts_step (wNode c.p base v) _ c.i B (v.vals.map (·.1))
      leaf x ln (ln.add c.i (.key k child)) hpos hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2.1 hJ.2.2.2.2.2 hwL hL'
      (KNode.prefixAt_add ln c.i _ hpos) (by rw [KNode.firstTime_add_some ln c.i _ s0 hs0, hs0])
      (fun xn2 h => by
        rw [hX] at h
        cases h
        exact ⟨n, hwx, hupre, hxB, hufirst⟩) hoth
    show J2N _ c.i w1.top.rootKey B (w1.vals.map (·.1))
    rw [show w1.top.rootKey = v.top.rootKey by rw [h1top],
      show w1.vals.map (·.1) = v.vals.map (·.1) by rw [h1v]]
    refine ⟨?_, ?_, hfacts⟩
    · exact ttReachedN_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf
        x child ln (ln.add c.i (.key k child)) n k hT hlf hwL hk hwx
        (fun c' z hz => by
          rw [KNode.liveAt_of_times n c.i hnt] at hz
          exact ((hlv c' z).mp hz).2)
        hL' (KNode.add_liveAt_new ln k child c.i hlnwf hlnt)
        (fun c' z hz hck => KNode.add_liveAt_keep ln k child c.i hlnwf hlnt c' z hz hck)
        hoth hJ.1 (fun xn2 h => by
          rw [hX] at h
          cases h
          exact unlinked_no_time n c.i hpos hnwf hnt)
    · exact deadLiveN_segReplace (wNode c.p base v) _ c.i B _ leaf x child ln n k hpos hJ.2.1 hJ.2.2.1
        hwL hlnwf hlnt hk hxB hwx hnwf hnt hL' hX hoth



/-- The collapse steps at the space root keep `TakeJ2`. -/
theorem writerWP_rootStep_space_j2F (x : NodeId) (only : Nat) (n : KNode) (c : Ctx)
    (base : View BVal) (w0 v : W) (f : Nat) (hI : CollGetInvF c base w0 v f) (B : NodeId) (hpos : 0 < c.i)
    (hJ : TakeJ2 c base B v) (hx : x = v.top.rootKey)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only) :
    WriterWP (takeBackRoot x 0 only) c v (fun _ v' => TakeJ2 c base B v') ∧
    (n.firstTime ≠ some c.i → WriterWP (replaceRoot x 0 only) c v (fun _ v' => TakeJ2 c base B v')) := by
  have hxt : v.taken.contains x = false := by rw [hx]; exact hI.1.2.1 _ TReach.root
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hroot : wNode c.p base v v.top.rootKey = some n := by rw [← hx]; exact hwx
  have hnt := hI.1.2.2.1 _ n TReach.root hroot
  have hnwf := hI.2.2.2.1 _ n TReach.root hroot
  have hfin : ∀ child, n.ptr? only = some child → ∀ w3 : W, w3.top.rootKey = child →
      w3.vals = v.vals →
      (∀ z, z ≠ x → wNode c.p base w3 z = wNode c.p base v z) →
      (∀ xn2, wNode c.p base w3 x = some xn2 → Klong.time c.i ∉ xn2.ks ∧
        (∀ cv y, Klong.key cv y ∈ xn2.ks → y < B) ∧
        prefixAt xn2.ks (c.i - 1) = prefixAt n.ks (c.i - 1) ∧ x < B ∧
        (∀ s, s < c.i → n.firstTime = some s → xn2.firstTime = some s)) →
      TakeJ2 c base B w3 := by
    intro child hptr w3 h3top h3v hN2 hx2
    obtain ⟨c0, _, hlv⟩ := onlyLiveKlong_live_iff n only child honly hptr
    unfold TakeJ2 J2N
    rw [h3top, h3v]
    refine ⟨?_, ?_, ?_⟩
    · refine ttReachedN_spaceCollapse (wNode c.p base v) (wNode c.p base w3) c.i v.top.rootKey child
        n hroot ?_ (fun z hz => hN2 z (by rw [hx]; exact hz)) hJ.1
        (fun xn2 h => (hx2 xn2 (by rw [hx]; exact h)).1)
      intro c' z hz
      rw [KNode.liveAt_of_times n c.i hnt] at hz
      exact ((hlv c' z).mp hz).2
    · exact deadLiveN_only (wNode c.p base v) (wNode c.p base w3) c.i B _ x hJ.2.1
        (fun xn2 h => (hx2 xn2 h).2.1) hN2
    · exact j2facts_only (wNode c.p base v) (wNode c.p base w3) c.i B _ x hJ.2.2.1 hJ.2.2.2.1
        hJ.2.2.2.2.1 hJ.2.2.2.2.2
        (fun xn2 h => ⟨n, hwx, (hx2 xn2 h).2.2.1, (hx2 xn2 h).2.2.2.1, (hx2 xn2 h).2.2.2.2⟩) hN2
  constructor
  · cases hp : n.ptr? only with
    | none =>
      unfold takeBackRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_takeBackRoot_spaceV _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3n, h3v⟩
      have hX : wNode c.p base w3 x = none := by simp [wNode, h3t]
      refine hfin child hp w3 h3top h3v (fun z hz => ?_) (fun xn2 h => by rw [hX] at h; cases h)
      have : w3.taken.contains z = v.taken.contains z := by
        rw [h3t, List.contains_cons]
        have : (z == x) = false := by simpa using hz
        simp [this]
      simp only [wNode, this, h3n]
  · intro hnm
    have hxB : x < B := lt_of_firstTime_ne _ _ _ hJ.2.2.2.2.1 x n hwx hnm
    cases hp : n.ptr? only with
    | none =>
      unfold replaceRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_replaceRoot_spaceT _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3v, h3x, h3l⟩
      have hX : wNode c.p base w3 x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
        simp only [wNode, h3t, hxt, Bool.false_eq_true, ↓reduceIte, h3x]
      refine hfin child hp w3 h3top h3v (fun z hz => by simp only [wNode, h3t, h3l z hz]) ?_
      intro xn2 h
      rw [hX] at h
      cases h
      obtain ⟨hupre, hufirst⟩ := unlinked_facts n c.i hpos
      exact ⟨unlinked_no_time n c.i hpos hnwf hnt,
        unlinked_old_ptrs n c.i B hpos (fun cv y h => hJ.2.2.1 x n hwx cv y h) hnwf hnt,
        hupre, hxB, hufirst⟩

/-! ## A merge below a parent with room -/

/-! ## The case -/

end SIS.Tree
