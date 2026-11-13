/-
Case (4) of the take-back, a delete with the merges on (bergdb 024-12, TP7;
`DelMergeCase`), reduced to named obligations on cost's reduction of the case
at the reading fuel f = p.fuel + 1 inside the delete (DelMergeCaseF.lean,
option (a)): the delete's inner invariant with the take-back's (B), (C) and
node facts (`DelInvJF`: `DelInvF`, `TakeJ2`, B at or below the next id) is kept
by the merges' loop and the root collapse, given cost's step obligations
(`MergeStepOKF`, `DescentOKF`, `CollapseStepOKF`) and

* `MergeFullJ2OKF`: a merge of the loop below a parent without room for the
  merge's klongs in place keeps `TakeJ2` (below a parent with room it is
  `writerWP_merge_made_j2`);
* `DelStepsJ2OKF`: the delete's other steps (the walk, the leaf's bitmap or its
  cascade, the upward delete) end in `TakeJ2` when the merges' loop,
  `afterDelete` and the collapse keep `DelInvJF`.

The collapse keeps `TakeJ2` by `writerWP_collapseRoot_collF` with the walk's
ranges and `TakeJ2` together, the steps by cost's `CollapseStepOKF` and the
take-back's collapse steps (TakeDeadCollapse.lean, here for `CollGetInvF`).
-/
import SIS.Tree.DelMergeCaseF
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
down to the merged node and the merge's conditions on it (cost's `PathOK`,
`MergePathCond`), keeps `TakeJ2`. -/
def MergeStepJ2OKF (c : Ctx) (base : View BVal) (f : Nat) (B : NodeId) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode),
    DelInvJF c base w0 key f B v → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    PathOK c v d X K Nn → MergePathCond c X K Nn d → X d = x →
    WriterWP (merge x d) c v (fun _ v' => TakeJ2 c base B v')

/-- The merges' loop keeps `DelInvJF`, given the obligations at f. -/
theorem writerWP_mergeUp_delJF (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF c base fuelR)
    (hD : DescentOKF c base fuelR) (B : NodeId) (hMJ : MergeStepJ2OKF c base fuelR B)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvJF c base w0 k0 fuelR B v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvJF c base w0 k0 fuelR B v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v hI
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    obtain ⟨hI0, hJ0, hB0⟩ := hI
    refine writerWP_mono (writerWP_and (hD w0 k0 key g h v hI0)
      (writerWP_descendToHeight_readsU key g h c base hvc v)) ?_
    intro d v1 ⟨⟨hI1, hPF⟩, hr1⟩
    have hJ1 : TakeJ2 c base B v1 := takeJ2_of_readsAs c base B v v1 hJ0 hr1
    have hBn1 : B ≤ v1.next := by rw [hr1.2.2.2.2]; exact hB0
    split
    · simp only [writerWP_pure]; exact ⟨hI1, hJ1, hBn1⟩
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      obtain ⟨X, K, Nn, hP1, hcond⟩ := hPF hd
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
          obtain ⟨B1, t1, hB1, hb1⟩ := hI1.2.2.2.2.2.2
          refine writerWP_mono (writerWP_and (writerWP_and (writerWP_getNode_all eq.2 c v1 base hvc)
            (writerWP_getNode_cache eq.2 c v1)) (putBook_getNode eq.2 c base B1 t1 hB1 v1 hb1)) ?_
          rintro qn v2 ⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hb2⟩
          have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B1, t1, hB1, hb2⟩
          have hJ2 : TakeJ2 c base B v2 := takeJ2_of_readsAs c base B v1 v2 hJ1 hr2
          have hBn2 : B ≤ v2.next := by rw [hr2.2.2.2.2]; exact hBn1
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          split
          · simp only [writerWP_pure]; exact ⟨hI2, hJ2, hBn2⟩
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_and (writerWP_getNode_all ex.2 c v2 base hvc)
              (writerWP_getNode_cache ex.2 c v2)) (putBook_getNode ex.2 c base B1 t1 hB1 v2 hb2)) ?_
            rintro xn v3 ⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hb3⟩
            have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B1, t1, hB1, hb3⟩
            have hJ3 : TakeJ2 c base B v3 := takeJ2_of_readsAs c base B v2 v3 hJ2 hr3
            have hBn3 : B ≤ v3.next := by rw [hr3.2.2.2.2]; exact hBn2
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            split
            · simp only [writerWP_pure]; exact ⟨hI3, hJ3, hBn3⟩
            · rename_i hcnt
              have hcnt' : xn.cnt < c.p.mergeBelow := by simpa using hcnt
              rw [writerWP_bind]
              obtain ⟨hX3, _, hS23, _, _⟩ := id hP3
              have hxX : X d = ex.2 := by
                have := hX3 d (Nat.le_refl _)
                rw [hp3, hp2, hex] at this
                exact (Option.some.inj this).symm
              have hqX : X (d - 1) = eq.2 := by
                have := hX3 (d - 1) (by omega)
                rw [hp3, hp2, heq] at this
                exact (Option.some.inj this).symm
              have hqn : Nn (d - 1) = qn := by
                have h1 := (hS23 (d - 1) (by omega)).1
                rw [hqX, hkeep3 _ _ hl2] at h1
                exact (Option.some.inj h1).symm
              have hmj := hMJ w0 k0 ex.2 eq.2 d v3 qn xn X K Nn ⟨hI3, hJ3, hBn3⟩ hd
                (by rw [hp3, hp2, hex]; rfl) (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
                hP3 hcond hxX
              obtain ⟨hc1, hc2, hc3⟩ := hcond
              have hmg := writerWP_merge_get_invF fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3 hd
                hxX (by rw [hqn]; exact hql') hsa2 hcap hc1 hc2 hc3
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn hI3 hd (by rw [hp3, hp2, hex]; rfl)
                (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
              have htr := writerWP_merge_tree_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3 hd
                hxX (by rw [hqn]; exact hql') hsa2 hcap hc3
              refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and hmg hms)
                (putBook_merge ex.2 d c base B1 t1 hB1 v3 hb3)) htr) hmj) (writerWP_merge_next ex.2 d c v3)) ?_
              rintro r v4 ⟨⟨⟨⟨⟨hread4, ⟨hu4, hR4, hICE4⟩, hF4⟩, hb4⟩, hT4⟩, hJ4⟩, hn4⟩
              obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B1 t1 hB1 hb4 hT4 hu4 hR4
              have hI4 : DelInvJF c base w0 k0 fuelR B v4 :=
                ⟨⟨hP4, hG4, hR4, hICE4, hF4, fun key' hk => by rw [hread4 hF4 key']; exact hI3.2.2.2.2.2.1 key' hk,
                  B1, t1, hB1, hb4⟩, hJ4, Nat.le_trans hBn3 hn4⟩
              split
              · simp only [writerWP_pure]; exact hI4
              · exact ih (h + 1) true v4 hI4



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

/-- The collapse keeps `DelInvJF`, given cost's collapse obligation at f. -/
theorem writerWP_collapseRoot_delJF (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hC : CollapseStepOKF c base f) (w0 : W)
    (k0 : Key) (B : NodeId) (hpos : 0 < c.i) (v : W) (hI : DelInvJF c base w0 k0 f B v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvJF c base w0 k0 f B v') := by
  obtain ⟨⟨hP, hG, hR, hICE, hF, hread, B', top0, hB, hbook⟩, hJ, hBn⟩ := hI
  have hCI : CollGetInvF c base v v f := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_collapseRoot_collF f hf2 key seg c base hvc v
    (fun v => CollRange c base v ∧ TakeJ2 c base B v)
    (fun v v' hJ hr => ⟨⟨by rw [hr.1, hr.2.1]; exact hJ.1.1, by rw [hr.1, hr.2.1]; exact hJ.1.2⟩,
      takeJ2_of_readsAs c base B v v' hJ.2 hr⟩)
    (fun v' x n leaf ln k hI' hJ' => hC.1 v v' x n leaf ln k hI' hJ'.1) ?_ ?_ c.p.fuel v hCI
    ⟨⟨hR, hICE⟩, hJ⟩)
    (putBook_collapseRoot key seg c.p.fuel c base B' top0 hB v hbook))
    (writerWP_collapseRoot_next key seg c.p.fuel c v)) ?_
  · intro v' x n only hI' hJ' hP' hlk hxl hm honly hcv
    refine writerWP_and (hC.2.1 v v' x n only hI' hJ'.1 hP' hlk hxl hm honly hcv) ?_
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP'
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v'.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_j2F x only n c base v v' f hI' B hpos hJ'.2 hx hlk honly).1
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v' ps0 k L ln hvp hlf hcache hL hLn
      rw [hlen]
      exact writerWP_takeBackRoot_seg_j2F x ps0.length only n L ln k c base v v' f hI' B hpos hJ'.2 hLr
        hLlk hLl hk hlk honly hcv hxl hm hpd hpk
  · intro v' x n only hI' hJ' hP' hlk hxl hm honly hcv
    refine writerWP_and (hC.2.2 v v' x n only hI' hJ'.1 hP' hlk hxl hm honly hcv) ?_
    have hP0 := hP'
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP'
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v'.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_j2F x only n c base v v' f hI' B hpos hJ'.2 hx hlk honly).2 hm
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v' ps0 k L ln hvp hlf hcache hL hLn
      obtain ⟨hroom1, hdead⟩ := hC.1 v v' x n L ln k hI' hJ'.1 hP0 hlk hxl hm hLr hLlk hLl hk
      rw [hlen]
      exact writerWP_replaceRoot_seg_j2F x ps0.length only n L ln k c base v v' f hI' B hpos hJ'.2 hLr
        hLlk hLl hk hlk honly hcv hxl hm hpd hpk hroom1 hdead
  rintro _ v' ⟨⟨⟨⟨⟨hT', hu', _, _⟩, hread', hF', _, _⟩, ⟨hR', hICE'⟩, hJ'⟩, hbook'⟩, hn'⟩
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B' top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨hP', hG', hR', hICE', hF', fun key' hk => ?_, B', top0, hB, hbook'⟩, hJ', Nat.le_trans hBn hn'⟩
  rw [hread' key']
  exact hread key' hk

/-- `afterDelete` keeps `DelInvJF`, given the obligations at f. -/
theorem writerWP_afterDelete_delJF (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hM : MergeStepOKF c base f)
    (hD : DescentOKF c base f) (hC : CollapseStepOKF c base f) (B : NodeId)
    (hMJ : MergeStepJ2OKF c base f B) (hpos : 0 < c.i)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (w0 : W) (k0 : Key) (v : W) (hI : DelInvJF c base w0 k0 f B v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvJF c base w0 k0 f B v') :=
  writerWP_afterDelete_inv key g h c (DelInvJF c base w0 k0 f B)
    (fun v hI => writerWP_mergeUp_delJF key g c base hvc f hf2 hM hD B hMJ hsa2 hcap w0 k0 c.p.fuel h false
      v hI)
    (fun v hI => writerWP_collapseRoot_delJF key g c base hvc f hf2 hC w0 k0 B hpos v hI) v hI

/-! ## A merge below a parent with room -/

/-- Obligation: a merge of the loop below a parent without room for the merge's
klongs in place (`writerWP_merge_made_j2`'s room: four klongs and no more dead
klongs than theta) keeps `TakeJ2`. -/
def MergeFullJ2OKF (c : Ctx) (base : View BVal) (f : Nat) (B : NodeId) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode),
    DelInvJF c base w0 key f B v → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    PathOK c v d X K Nn → MergePathCond c X K Nn d → X d = x →
    ¬ (qn.size + 4 ≤ c.p.M ∧
      ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode qn c.i il cL m1 ir cR m2) = false) →
    WriterWP (merge x d) c v (fun _ v' => TakeJ2 c base B v')

/-- A merge keeps `TakeJ2`: below a parent with room by `writerWP_merge_made_j2`,
else by the obligation. -/
theorem mergeStepJ2OKF_of_full (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (f : Nat)
    (B : NodeId) (hpos : 0 < c.i) (hcap : 1 ≤ c.p.mergeMax) (hF : MergeFullJ2OKF c base f B) :
    MergeStepJ2OKF c base f B := by
  intro w0 key x q d v qn xn X K Nn hI hd hx hq hqn hql hxn hcnt hP hcond hXd
  by_cases hroom : qn.size + 4 ≤ c.p.M ∧
      ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode qn c.i il cL m1 ir cR m2) = false
  · obtain ⟨⟨hPI, hG, hR, _, _, _, _⟩, hJ, hBn⟩ := hI
    obtain ⟨hX, _, hS2, _, _⟩ := id hP
    have hXq : X (d - 1) = q := by
      have := hX (d - 1) (by omega)
      rw [hq] at this
      exact (Option.some.inj this).symm
    have hqt : v.taken.contains q = false := by rw [← hXq]; exact (hS2 (d - 1) (by omega)).2
    have hwq : wNode c.p base v q = some qn := by
      simp only [wNode, hqt, Bool.false_eq_true, ↓reduceIte, hqn]
    have hqR : TReach (wNode c.p base v) c.i v.top.rootKey q := by
      rw [← hXq]; exact (pathOK_depth c base v d X K Nn hP (d - 1) (by omega)).reach
    refine writerWP_merge_made_j2 x d c base B hvc v hPI.tree ?_
      (fun y hy => hPI.untaken y (tReach_reachS _ _ _ _ hy))
      ⟨hPI.ids.1, hPI.ids.2.1, hPI.ids.2.2.1⟩ (fun z hz => (hPI.fresh z hz).1) ?_ hR hcap hPI.wf hpos
      hJ hBn ?_
    · intro p' hp'
      rw [hq] at hp'
      cases hp'
      exact ⟨hqR, qn, hwq, hql, hroom.1, hroom.2, hPI.wf q qn hwq, hPI.times q qn hwq,
        fun cc z zn _ hz => hPI.times z zn hz⟩
    · intro z hz u c' _ hl
      obtain ⟨un, hun, hc⟩ := hl
      have := hG.links u un c' z hun hc
      omega
    · intro y hy
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hy
      exact hPI.ids.2.2.2.1 q' hq'
  · exact hF w0 key x q d v qn xn X K Nn hI hd hx hq hqn hql hxn hcnt hP hcond hXd hroom

/-! ## The case -/

/-- Obligation (the delete's other steps with the take-back's facts): a delete
with the merges on, from a state between operations of a transaction within
reach with S and `TakeJ2`, ends in `TakeJ2`, given that the merges' loop,
`afterDelete` and the collapse keep `DelInvJF` at f = p.fuel + 1. It holds the
walk, the leaf's bitmap or its cascade and the upward delete
(`takeJ2_deleteUpward_upT` with the merges' steps given). -/
def DelStepsJ2OKF (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    S ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
    ∀ key, op = .del key → p.merges = true →
    (∀ g h v, DelInvJF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v
        (fun _ v' => DelInvJF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) tx.base v')) →
    (∀ g h merged v, DelInvJF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInvJF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) tx.base v')) →
    (∀ seg v, DelInvJF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DelInvJF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w')

/-- (4) A delete with the merges on keeps `J2At`, from the named obligations at
f = p.fuel + 1: the delete's other steps (`DelStepsJ2OKF`), cost's merge,
descent and collapse steps, and a merge below a parent without room keeping
`TakeJ2` (`MergeFullJ2OKF`), for 2 ≤ splitAbove and 1 ≤ mergeMax. -/
theorem opJ2Case_delMergeF (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hS : DelStepsJ2OKF p R S)
    (hM : ∀ ts, MergeStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hD : ∀ ts, DescentOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hMF : ∀ ts B, MergeFullJ2OKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) :
    OpJ2CaseOK p R S DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre _ hSw hJ hP
  obtain ⟨key, hop, hmerges⟩ := hP
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hMJ := mergeStepJ2OKF_of_full (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (p.fuel + 1) tx.base hpos
    hcap (hMF ts tx.base)
  refine writerWP_mono (hS ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ key hop hmerges
    (fun g h v hv => writerWP_afterDelete_delJF key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hD ts) (hC ts) tx.base hMJ hpos hsa2 hcap w key v hv)
    (fun g h merged v hv => writerWP_mergeUp_delJF key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hD ts) tx.base hMJ hsa2 hcap w key p.fuel h merged v hv)
    (fun seg v hv => writerWP_collapseRoot_delJF key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key tx.base hpos v hv)) ?_
  intro _ w' h' _
  exact h'

/-- TP7's take-back statement with the merges on, for 2 ≤ splitAbove and
1 ≤ mergeMax, from the named obligations of case (4) at f = p.fuel + 1: cost's
`MergeStepOKF`, `DescentOKF` and `CollapseStepOKF`, and `MergeFullJ2OKF` and
`DelStepsJ2OKF`. -/
theorem takeBackOK_of_mergesF (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hcap : 1 ≤ p.mergeMax) (hm : p.merges = true)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (hDS : DelStepsJ2OKF p (RunTreeQ p Q) (TakeS3 p))
    (hMS : ∀ ts, MergeStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hDe : ∀ ts, DescentOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hMF : ∀ ts B, MergeFullJ2OKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B) :
    TakeBackOKUnder p (RunLinksOK p) :=
  takeBackOK_of_cases_merges4 p hM hsa hm Q hQ0 hQs hQP hQK ho hPI hRO hB
    (opJ2Case_delMergeF p _ _ hDS hMS hDe hCo hMF hsa hcap)

end SIS.Tree
