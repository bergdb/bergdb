/-
The take-back's case (4) on latest's F3/F4 route (bergdb 024-12, TP7): the
delete's loop invariant with the kinds' books and the take-back's facts
(`DelInvJF3`), through the merges' loop (`writerWP_mergeUp_delJF3`, every
merge's `TakeJ2` proved) and the collapse.
-/
import SIS.Tree.TakeMergeRoot
import SIS.Tree.CollapseCascade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The delete's loop invariant on the F3 route with the take-back's facts. -/
def DelInvJF3 (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat) (KO : KindOracle) (BK : NodeId)
    (B : NodeId) (v : W) : Prop :=
  DelInvF3 c base w0 key f KO BK v ∧ TakeJ2 c base B v ∧ B ≤ v.next

set_option maxHeartbeats 1600000 in
/-- The merges' loop keeps `DelInvJF3`: latest's `writerWP_mergeUp_delF3` with
each merge's `TakeJ2` (`mergeStepJ2OKF_of_root`, `mergeRootJ2OKF_holds`). -/
theorem writerWP_mergeUp_delJF3 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF3 c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (B : NodeId) (hpos : 0 < c.i) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvJF3 c base w0 k0 fuelR KO BK B v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvJF3 c base w0 k0 fuelR KO BK B v') := by
  have hMJ := mergeStepJ2OKF_of_root c base hvc fuelR B hpos hcap hsa2
    (mergeRootJ2OKF_holds c base fuelR B hpos hcap hsa2)
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v ⟨⟨hI, hbk, hik⟩, hJ0, hB0⟩
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and (descentOKF2 c base fuelR w0 k0 key g h v hI)
      (kd_descendToHeight KO BK key g h c v hv hk hbk hik))
      (writerWP_descendToHeight_readsU key g h c base hvc v)) ?_
    intro d v1 ⟨⟨⟨hI1, hPF⟩, hbk1, hik1, _⟩, hr1⟩
    have hJ1 : TakeJ2 c base B v1 := takeJ2_of_readsAs c base B v v1 hJ0 hr1
    have hBn1 : B ≤ v1.next := by rw [hr1.2.2.2.2]; exact hB0
    split
    · simp only [writerWP_pure]; exact ⟨⟨hI1, hbk1, hik1⟩, hJ1, hBn1⟩
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      obtain ⟨X, K, Nn, hP1⟩ := hPF
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
          refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
            (writerWP_getNode_all eq.2 c v1 base hvc) (writerWP_getNode_cache eq.2 c v1))
            (putBook_getNode eq.2 c base B1 t1 hB1 v1 hb1))
            (kd_getNode KO BK eq.2 c v1 hv hk hbk1 hik1)) ?_
          rintro qn v2 ⟨⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hb2⟩, hbk2, hik2, _⟩
          have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B1, t1, hB1, hb2⟩
          have hJ2 : TakeJ2 c base B v2 := takeJ2_of_readsAs c base B v1 v2 hJ1 hr2
          have hBn2 : B ≤ v2.next := by rw [hr2.2.2.2.2]; exact hBn1
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          split
          · simp only [writerWP_pure]; exact ⟨⟨hI2, hbk2, hik2⟩, hJ2, hBn2⟩
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
              (writerWP_getNode_all ex.2 c v2 base hvc) (writerWP_getNode_cache ex.2 c v2))
              (putBook_getNode ex.2 c base B1 t1 hB1 v2 hb2))
              (kd_getNode KO BK ex.2 c v2 hv hk hbk2 hik2)) ?_
            rintro xn v3 ⟨⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hb3⟩, hbk3, hik3, _⟩
            have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B1, t1, hB1, hb3⟩
            have hJ3 : TakeJ2 c base B v3 := takeJ2_of_readsAs c base B v2 v3 hJ2 hr3
            have hBn3 : B ≤ v3.next := by rw [hr3.2.2.2.2]; exact hBn2
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            split
            · simp only [writerWP_pure]; exact ⟨⟨hI3, hbk3, hik3⟩, hJ3, hBn3⟩
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
              have hmg := writerWP_merge_get_invF2 fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1
                X K Nn hP3 hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn X K Nn hI3 hP3 hd (by rw [hp3, hp2, hex]; rfl)
                (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
              have htr := writerWP_merge_tree_inv2 ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
                hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hrg := writerWP_merge_range_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
                hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hkd := kd_merge KO BK ex.2 d c v3 hv hk hbk3 hik3 (by omega) ex.1
                (by rw [hp3, hp2, hex]) (by
                  intro a q' hq'
                  rw [hp3, hp2, heq] at hq'
                  simp only [Option.some.injEq] at hq'
                  subst hq'
                  exact ⟨qn, hkeep3 _ _ hl2, hql'⟩)
              have hmj := hMJ w0 k0 ex.2 eq.2 d v3 qn xn X K Nn ⟨hI3, hJ3, hBn3⟩ hd
                (by rw [hp3, hp2, hex]; rfl) (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
                hP3 hxX
              refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and
                (writerWP_and (writerWP_and hmg hms) (putBook_merge ex.2 d c base B1 t1 hB1 v3 hb3)) htr) hrg) hkd)
                hmj) (writerWP_merge_next ex.2 d c v3)) ?_
              rintro r v4 ⟨⟨⟨⟨⟨⟨⟨hread4, hu4, hF4⟩, hb4⟩, hT4⟩, hR4⟩, hbk4, hik4, _, _⟩, hJ4⟩, hn4⟩
              obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B1 t1 hB1 hb4 hT4 hu4 hR4
              have hICE4 := hICEk v4 hbk4 hik4 (fun y hy => hu4 y (tReach_reachS _ _ _ _ hy))
              have hI4 : DelInvF c base w0 k0 fuelR v4 :=
                ⟨hP4, hG4, hR4, hICE4, hF4, fun key' hk' => by
                  rw [hread4 hF4 key']; exact hI3.2.2.2.2.2.1 key' hk', B1, t1, hB1, hb4⟩
              split
              · simp only [writerWP_pure]; exact ⟨⟨hI4, hbk4, hik4⟩, hJ4, Nat.le_trans hBn3 hn4⟩
              · exact ih (h + 1) true v4 ⟨⟨hI4, hbk4, hik4⟩, hJ4, Nat.le_trans hBn3 hn4⟩

/-- Obligation (the take-back at a replaceRoot whose segment leaf is full): the
leaf's cascade after `unlink x` keeps `TakeJ2` and B at most the next id, given
the state's global facts (`PutInvG`) and the tree after the unlink
(`CollapseUnlinkOK`). -/
def ReplaceRootFullJ2OK (c : Ctx) (base : View BVal) (f : Nat) (B : NodeId) : Prop :=
  ∀ (w0 v : W) (x : NodeId) (n : KNode) (only : Nat) (leaf : NodeId) (ln : KNode) (k : Nat)
    (ps0 : List (Option Nat × NodeId)), CollGetInvF c base w0 v f →
    RangeOrder (wNode c.p base v) c.i v.top.rootKey → TakeJ2 c base B v → B ≤ v.next →
    v.path = (none, v.top.rootKey) :: (ps0 ++ [(some k, x)]) →
    LinkedFrom (wNode c.p base v) c.i v.top.rootKey (ps0 ++ [(some k, x)]) → PathCached v →
    TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln → ln.leaf = true →
    (k, x) ∈ ln.liveAt c.i → (v.path[ps0.length]?).map (·.2) = some leaf →
    v.path[ps0.length + 1]? = some (some k, x) → v.nodes.lookup x = some n →
    n.onlyLiveKlong = some only → n.cv? only = some 0 → n.leaf = false → n.firstTime ≠ some c.i →
    PutInvG c base v → CollapseUnlinkOK c base v x n →
    ¬ (ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) →
    WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' => TakeJ2 c base B v' ∧ B ≤ v'.next)

set_option maxHeartbeats 1600000 in
/-- The root collapse keeps latest's `writerWP_collapseRoot_collF4` invariant and
`TakeJ2` with B at most the next id: the take-back's steps of the collapse
(`writerWP_takeBackRoot_seg_j2F`, `writerWP_replaceRoot_seg_j2F`,
`writerWP_rootStep_space_j2F`), a replaceRoot into a full segment leaf by
`ReplaceRootFullJ2OK`. -/
theorem writerWP_collapseRoot_collJF4 (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
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
      CollapseUnlinkOK c base v x n)
    (BJ : NodeId) (hpos : 0 < c.i)
    (hRJ : ReplaceRootFullJ2OK c base fuelR BJ) :
    ∀ fuel v, CollGetInvF c base w0 v fuelR → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
      PutBook c B top0 v → Book BK c v → KdInv KO BK v → TakeJ2 c base BJ v → BJ ≤ v.next →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollGetInvF c base w0 v' fuelR ∧
        RangeOrder (wNode c.p base v') c.i v'.top.rootKey ∧ PutBook c B top0 v' ∧ Book BK c v' ∧
        KdInv KO BK v' ∧ TakeJ2 c base BJ v' ∧ BJ ≤ v'.next) := by
  intro fuel v hI hR hb hbk hik hJ hBn
  refine writerWP_collapseRoot_inv key seg c (fun v => CollGetInvF c base w0 v fuelR ∧
      RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧ PutBook c B top0 v ∧ Book BK c v ∧
      KdInv KO BK v ∧ TakeJ2 c base BJ v ∧ BJ ≤ v.next) (SegDesc c base) ?_ ?_ ?_ ?_ fuel v
      ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩
  · rintro v ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_descendToSegmentRoot_linked key seg c base hvc v hI.1.2.1 hI.2.2.2.1)
      (putBook_descendToSegmentRoot key seg c base B top0 hB v hb))
      (kd_descendToSegmentRoot KO BK key seg c v hv hk hbk hik)) ?_
    rintro x v' ⟨⟨⟨hr, _, hx, ps, hvp, hlf, hend, hcache, hlast⟩, hb'⟩, hbk', hik', _, _⟩
    refine ⟨⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI, by rw [hr.1, hr.2.1]; exact hR,
      hb', hbk', hik', takeJ2_of_readsAs c base BJ v v' hJ hr, by rw [hr.2.2.2.2]; exact hBn⟩, ?_⟩
    unfold SegDesc
    rw [hr.1, hr.2.1]
    exact ⟨hx, ps, hvp, hlf, hend, hcache, hlast⟩
  · rintro x v ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ hP
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_getNode_all x c v base hvc)
      (writerWP_getNode_cache x c v)) (putBook_getNode x c base B top0 hB v hb))
      (kd_getNode KO BK x c v hv hk hbk hik)) ?_
    rintro n v' ⟨⟨⟨⟨hr, hl, _, hpre, _⟩, _, _, hp⟩, hb'⟩, hbk', hik', _⟩
    exact ⟨⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI, by rw [hr.1, hr.2.1]; exact hR,
      hb', hbk', hik', takeJ2_of_readsAs c base BJ v v' hJ hr, by rw [hr.2.2.2.2]; exact hBn⟩,
      segDesc_of_readsAs c base x v v' hP hr hpre hp, hl, hp⟩
  · rintro x v n only ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ hP hlk hxl hm _ honly hcv
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
    exact ⟨hI', hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩
  · rintro x v n only ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ hP hlk hxl hm honly hcv
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
      exact ⟨hI', hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩
    · subst hps
      obtain ⟨hLr, hLlk, hk', hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      have hj : WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' => TakeJ2 c base BJ v') := by
        by_cases hroom : ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false
        · exact writerWP_replaceRoot_seg_j2F x ps0.length only n L ln k c base w0 v fuelR hI BJ hpos hJ hLr hLlk
            hLl hk' hlk honly hcv hxl hm hpd hpk hroom.1 hroom.2
        · exact writerWP_mono (hRJ w0 v x n only L ln k ps0 hI hR hJ hBn hvp hlf hPC hLr hLlk hLl hk' hpd hpk
            hlk honly hcv hxl hm hG hU hroom) (fun _ v' h' => h'.1)
      rw [hlen] at hfit hbook hkd hnx ⊢
      have hcas := writerWP_replaceRoot_seg_cascadeF fuelR hfR x only n L ln k ps0 c base w0 v hI hR hG hsa2
        hvp hlf hPC hLr hLlk hLl hk' hpd hpk hlk honly hcv hxl hU
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and hcas hfit) hbook)
        hkd) hj) hnx) ?_
      rintro _ v' ⟨⟨⟨⟨⟨⟨hT', hU', hW', _, _, hread', hR'⟩, hf'⟩, hb'⟩, hbk', hik', _, _⟩, hJ'⟩, hn'⟩
      have hG' := putInvG_of_book c base B top0 v' hB hb'
      refine ⟨⟨⟨hT', hU', fun y yn _ hy => hG'.times y yn hy,
        fun y yn cc z hy hyn hl hc => hICEk v' hbk' hik' hU' y yn cc z hy hyn hl hc⟩,
        hread' hf', hf', fun y yn _ hy => hW' y yn hy, fun y yn _ hy => hG'.keyNoValue y yn hy⟩,
        hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩

/-- The collapse keeps `DelInvJF3`, given `CollapseStepOKF4` and
`ReplaceRootFullJ2OK`. -/
theorem writerWP_collapseRoot_delJF4 (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hC : CollapseStepOKF4 c base f) (w0 : W)
    (k0 : Key) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (BJ : NodeId) (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OK c base f BJ)
    (v : W) (hI : DelInvJF3 c base w0 k0 f KO BK BJ v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvJF3 c base w0 k0 f KO BK BJ v') := by
  obtain ⟨⟨⟨hP, hG, hR, hICE, hF, hread, B, top0, hB, hbook⟩, hbk, hik⟩, hJ, hBn⟩ := hI
  have hCI : CollGetInvF c base v v f := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_collapseRoot_collJF4 f hf2 key seg c base hvc v B top0 hB KO BK hv hk
    hICEk hsa2 (hC.1 v) (hC.2 v) BJ hpos hRJ c.p.fuel v hCI hR hbook hbk hik hJ hBn) ?_
  rintro _ v' ⟨⟨⟨hT', hu', _, hICE'⟩, hread', hF', _, _⟩, hR', hbook', hbk', hik', hJ', hBn'⟩
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨⟨hP', hG', hR', hICE', hF', fun key' hk' => ?_, B, top0, hB, hbook'⟩, hbk', hik'⟩, hJ', hBn'⟩
  rw [hread' key']
  exact hread key' hk'

/-- `afterDelete` keeps `DelInvJF3`, given `MergeStepOKF3`, `CollapseStepOKF4`
and `ReplaceRootFullJ2OK`. -/
theorem writerWP_afterDelete_delJF4 (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF3 c base fuelR)
    (hC : CollapseStepOKF4 c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (BJ : NodeId) (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OK c base fuelR BJ)
    (w0 : W) (k0 : Key) (v : W) (hI : DelInvJF3 c base w0 k0 fuelR KO BK BJ v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvJF3 c base w0 k0 fuelR KO BK BJ v') :=
  writerWP_afterDelete_inv key g h c (DelInvJF3 c base w0 k0 fuelR KO BK BJ)
    (fun v hI => writerWP_mergeUp_delJF3 key g c base hvc fuelR hfR hM KO BK hv hk hICEk hsa2 hcap BJ hpos
      w0 k0 c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_delJF4 key g c base hvc fuelR hfR hC w0 k0 KO BK hv hk hICEk hsa2
      BJ hpos hRJ v hI) v hI

end SIS.Tree
