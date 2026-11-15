/-
Root collapse's check proved (bergdb 024-12, section 1). `hchk`'s `checkRoot`
passes at every state of root collapse inside a delete, from the delete's loop
invariant with the take-back's facts (`DelInvJ`) and the books of the
transaction's first id at `afterDelete`'s call. The premise is now
`OpDelChk6OKL`: the writer's delete runs as the copy that checks, at each call
of `afterDelete`, that `DelInvJ` and the books hold and that the merges' loop
from there runs as its copy with the merge's `checkFree` (`afterDeleteJ`), and
then runs the writer's `afterDelete`. `opDelChk5OKR_of_chk6` gives
`OpDelChk5OKR` from it:

* root collapse with the check runs as without it from every state of the
  collapse's invariant (`rwp_collapseRoot_chkJ`): `checkRoot_ok_of_J2` at each
  take-back, from the path that `descendToSegmentRoot` leaves
  (`checkRoot_ok_of_segDesc`);
* so at every state that passes `afterDeleteJ`'s check, `afterDelete` runs as
  `afterDeleteChk` (`rwp_afterDelete_of_J`, the merges' loop keeping `DelInvJ`
  and the books), and the delete with `afterDeleteJ` as `putKvDelChk5`
  (`rwp_putKvDP`, `putKvDelChk5_eq`).
-/
import SIS.Tree.DelHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The copy with the check at `afterDelete`'s calls -/

open Classical in
/-- `afterDelete` from a state of J only, where the merges' loop runs as its
copy with the merge's `checkFree`. -/
noncomputable def afterDeleteJ (J : W → Prop) (key : Key) (g h : Nat) : M Unit := do
  let c ← read
  let v ← (MonadState.get : M W)
  if J v ∧ RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v then
    afterDelete key g h
  else throw "check: the state at a call of afterDelete"

/-- The delete with `afterDeleteJ J` at `afterDelete`'s calls. -/
noncomputable def putKvDelChk6 (J : W → Prop) (key : Key) : M Bool := putKvDP (afterDeleteJ J) key

/-- The state at a call of `afterDelete` in the delete of `key` from w0: the
delete's loop invariant with the take-back's facts (`DelInvJ`) and the books of
the transaction's first id. -/
def DelHoleJ (p : Params) (ts : List Tx) (tx : Tx) (top : Top) (w0 : W) (key : Key) (v : W) : Prop :=
  DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w0 key (p.fuel + 1) (kindOracleOf p (treeRun p ts))
    tx.base tx.base v ∧ PutBook (ctxOf p ts) tx.base top v

/-- `OpDelChk5OKR` with `putKvDelChk6`: at the deletes of the runs of R, the
delete runs as its copy that checks `DelHoleJ` and the merges' loop at each call
of `afterDelete`, root collapse without a check. -/
def OpDelChk6OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk6 (DelHoleJ p ts tx top w key) key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk6OKR` at the induction's runs. -/
def OpDelChk6OKL (p : Params) : Prop := OpDelChk6OKR p (RunTreeQ p (LatestQD p))

/-! ## Root collapse's check -/

theorem rwp_throw_bind {α β : Type} (e : String) (k : α → M β) (g : M β) (c : Ctx) (w : W) :
    RWP ((throw e : M α) >>= k) g c w := by
  intro x hx
  obtain ⟨a, w', h1, _⟩ := (m_bind_ok _ _ c w x).mp hx
  exact ((writerWP_throw e c w (fun _ _ => False)) a w' h1).elim

theorem rwp_check_right {β : Type} {f : M β} {chk : M Unit} {k : Unit → M β} {c : Ctx} {v : W}
    (hc : chk c v = .ok ((), v)) (h : RWP f (k ()) c v) : RWP f (chk >>= k) c v := by
  intro x hx
  exact (m_bind_ok chk k c v x).mpr ⟨(), v, hc, h x hx⟩

/-- Root collapse with the check runs as without it from every state of an
invariant that the loop's steps keep, where the check passes before each
take-back. -/
theorem rwp_collapseRoot_chk (key : Key) (seg : Nat) (c : Ctx) (Inv : W → Prop)
    (Pd : NodeId → W → Prop)
    (hdesc : ∀ v, Inv v → WriterWP (descendToSegmentRoot key seg) c v (fun x v' => Inv v' ∧ Pd x v'))
    (hget : ∀ x v, Inv v → Pd x v → WriterWP (getNode x) c v (fun n v' =>
      Inv v' ∧ Pd x v' ∧ v'.nodes.lookup x = some n ∧ v'.path = v.path))
    (hstepT : ∀ x v n only, Inv v → Pd x v → v.nodes.lookup x = some n → n.leaf = false →
      n.firstTime = some c.i → (v.madeFor.lookup x).isSome = true →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v (fun _ v' => Inv v'))
    (hstepR : ∀ x v n only, Inv v → Pd x v → v.nodes.lookup x = some n → n.leaf = false →
      n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v (fun _ v' => Inv v'))
    (hchk : ∀ x v n, Inv v → Pd x v → v.nodes.lookup x = some n → n.firstTime = some c.i →
      checkRoot x (v.path.length - 1) c v = .ok ((), v)) :
    ∀ fuel v, Inv v → RWP (collapseRoot key seg fuel) (collapseRootChk key seg fuel) c v := by
  intro fuel
  induction fuel with
  | zero => intro v _; unfold collapseRoot collapseRootChk; exact rwp_refl _ _ _
  | succ f ih =>
    intro v hI
    unfold collapseRoot collapseRootChk
    refine rwp_read ?_
    refine rwp_bind (fun x v' => Inv v' ∧ Pd x v') (hdesc v hI) ?_
    rintro x v1 ⟨hI1, hP1⟩
    refine rwp_bind _ (hget x v1 hI1 hP1) ?_
    rintro n v2 ⟨hI2, hP2, hl2, _⟩
    by_cases hleaf : n.leaf = true
    · simp only [hleaf, ↓reduceIte]; exact rwp_refl _ _ _
    · have hleaf' : n.leaf = false := by simpa using hleaf
      simp only [hleaf', Bool.false_eq_true, ↓reduceIte]
      refine rwp_bind (fun r v' => r = v2.madeFor.lookup x ∧ v' = v2)
        (by unfold replacedBy; simp only [writerWP_bind, writerWP_get, writerWP_pure, and_self]) ?_
      rintro rb v3 ⟨hrb, hv3⟩
      subst v3; subst rb
      refine rwp_ite (fun _ => rwp_refl _ _ _) (fun hmr => ?_)
      cases honly : n.onlyLiveKlong with
      | none => exact rwp_refl _ _ _
      | some only =>
        refine rwp_ite (fun _ => rwp_throw_bind _ _ _ _ _) (fun hcv => ?_)
        have hcv' : n.cv? only = some 0 := by simpa using hcv
        refine rwp_bind (fun s v' => s = v2.path.length ∧ v' = v2)
          (by unfold pathSize; simp only [writerWP_bind, writerWP_get, writerWP_pure, and_self]) ?_
        rintro s v4 ⟨hs, hv4⟩
        subst v4; subst s
        by_cases hmade : (n.firstTime == some c.i) = true
        · have hm : n.firstTime = some c.i := by simpa using hmade
          have hrb : (v2.madeFor.lookup x).isSome = true := by
            simp only [hmade, Bool.true_and, Option.isNone_iff_eq_none] at hmr
            cases h : v2.madeFor.lookup x with
            | none => exact absurd h hmr
            | some _ => rfl
          simp only [hmade, ↓reduceIte]
          refine rwp_check_right (hchk x v2 n hI2 hP2 hl2 hm) ?_
          exact rwp_bind (fun _ v' => Inv v') (hstepT x v2 n only hI2 hP2 hl2 hleaf' hm hrb honly hcv')
            (fun _ v3 h3 => ih v3 h3)
        · have hm : n.firstTime ≠ some c.i := by simpa using hmade
          simp only [hmade, Bool.false_eq_true, ↓reduceIte]
          exact rwp_bind (fun _ v' => Inv v') (hstepR x v2 n only hI2 hP2 hl2 hleaf' hm honly hcv')
            (fun _ v3 h3 => ih v3 h3)

set_option maxHeartbeats 1600000 in
/-- `checkRoot` passes before root collapse takes back x, a node that the
transaction made, at the end of the path that `descendToSegmentRoot` left, at a
state of the collapse's invariant with the books and the take-back's facts of one
first id B (`checkRoot_ok_of_J2`). -/
theorem checkRoot_ok_of_segDesc (c : Ctx) (base : View BVal) (w0 : W) (f : Nat) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (v : W) (hI : CollGetInvF c base w0 v f)
    (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey) (hb : PutBook c B top0 v) (hbk : Book B c v)
    (hJ : TakeJ2 c base B v) (x : NodeId) (n : KNode) (hP : SegDesc c base x v)
    (hlk : v.nodes.lookup x = some n) (hft : n.firstTime = some c.i) :
    checkRoot x (v.path.length - 1) c v = .ok ((), v) := by
  obtain ⟨hx, ps, hvp, hlf, hend, _, _⟩ := hP
  have hT := hI.1.1
  have hu := hI.1.2.1
  have hPI := (putInv_after_step c base v B top0 hB hb hT (fun y hy => hu y (reachS_tReach _ _ _ _ hy)) hR).1
  have hnd : (v.nodes.map Prod.fst).Nodup := by rw [hbk.ids]; exact ht_nodup_reverse hbk.nodup
  have hxt : v.taken.contains x = false := hu x hx
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hXD : nodeAt v.top.rootKey ps ps.length = x := by rw [nodeAt_last, hend]
  have hgetP := LinkedFrom.get _ _ _ ps hlf
  have hXN : ∀ i, i ≤ ps.length → wNode c.p base v (nodeAt v.top.rootKey ps i) =
      some ((wNode c.p base v (nodeAt v.top.rootKey ps i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = ps.length := by omega
      subst this
      rw [hXD, hwx]; rfl
  have hKP : ∀ i, 0 < i → i ≤ ps.length →
      ps[i - 1]? = some (some (((ps[i - 1]?).bind (·.1)).getD 0), nodeAt v.top.rootKey ps i) ∧
      (((ps[i - 1]?).bind (·.1)).getD 0, nodeAt v.top.rootKey ps i) ∈
        ((wNode c.p base v (nodeAt v.top.rootKey ps (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hpX : ∀ i, i ≤ ps.length → (v.path[i]?).map (·.2) = some (nodeAt v.top.rootKey ps i) := by
    intro i hi
    have hl : i < (v.top.rootKey :: ps.map (·.2)).length := by simp; omega
    rw [hvp, ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ ps.length →
      v.path[i]? = some (some (((ps[i - 1]?).bind (·.1)).getD 0), nodeAt v.top.rootKey ps i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hvp, List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  have hlen : v.path.length - 1 = ps.length := by rw [hvp]; simp
  rw [hlen, ← hXD]
  exact checkRoot_ok_of_J2 c base v B hB.good hPI hJ hb.good hnd (fun i => nodeAt v.top.rootKey ps i)
    (fun i => (wNode c.p base v (nodeAt v.top.rootKey ps i)).getD n)
    (fun i => ((ps[i - 1]?).bind (·.1)).getD 0) ps.length (by simp [nodeAt]) hXN
    (fun i h1 h2 => (hKP i h1 h2).2) hpX hpK n (by rw [hXD]; exact hlk) hft

set_option maxHeartbeats 1600000 in
/-- Root collapse with the check runs as without it from every state of
`writerWP_collapseRoot_collJC`'s invariant with one first id B for the books, the
kinds' books and the take-back's facts: that lemma's steps, and
`checkRoot_ok_of_segDesc` before each take-back. -/
theorem rwp_collapseRoot_chkJ (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hfits : ∀ v x n only, CollGetInvF c base w0 v fuelR →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey))
    (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OKC c base fuelR B) :
    ∀ fuel v, CollGetInvF c base w0 v fuelR → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
      PutBook c B top0 v → Book B c v → KdInv KO B v → TakeJ2 c base B v → B ≤ v.next →
      RWP (collapseRoot key seg fuel) (collapseRootChk key seg fuel) c v := by
  intro fuel v hI hR hb hbk hik hJ hBn
  refine rwp_collapseRoot_chk key seg c (fun v => CollGetInvF c base w0 v fuelR ∧
      RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧ PutBook c B top0 v ∧ Book B c v ∧
      KdInv KO B v ∧ TakeJ2 c base B v ∧ B ≤ v.next) (SegDesc c base) ?_ ?_ ?_ ?_ ?_ fuel v
      ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩
  · rintro v ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_descendToSegmentRoot_linked key seg c base hvc v hI.1.2.1 hI.2.2.2.1)
      (putBook_descendToSegmentRoot key seg c base B top0 hB v hb))
      (kd_descendToSegmentRoot KO B key seg c v hv hk hbk hik)) ?_
    rintro x v' ⟨⟨⟨hr, _, hx, ps, hvp, hlf, hend, hcache, hlast⟩, hb'⟩, hbk', hik', _, _⟩
    refine ⟨⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI, by rw [hr.1, hr.2.1]; exact hR,
      hb', hbk', hik', takeJ2_of_readsAs c base B v v' hJ hr, by rw [hr.2.2.2.2]; exact hBn⟩, ?_⟩
    unfold SegDesc
    rw [hr.1, hr.2.1]
    exact ⟨hx, ps, hvp, hlf, hend, hcache, hlast⟩
  · rintro x v ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩ hP
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_getNode_all x c v base hvc)
      (writerWP_getNode_cache x c v)) (putBook_getNode x c base B top0 hB v hb))
      (kd_getNode KO B x c v hv hk hbk hik)) ?_
    rintro n v' ⟨⟨⟨⟨hr, hl, _, hpre, _⟩, _, _, hp⟩, hb'⟩, hbk', hik', _⟩
    exact ⟨⟨collGetInv_of_readsAsF fuelR hfR c base w0 v v' hr hI, by rw [hr.1, hr.2.1]; exact hR,
      hb', hbk', hik', takeJ2_of_readsAs c base B v v' hJ hr, by rw [hr.2.2.2.2]; exact hBn⟩,
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
          TakeJ2 c base B v') := by
      obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
      rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
      · subst hps
        have hx : x = v.top.rootKey := by rw [← hend]; rfl
        rw [hvp]
        exact writerWP_and (writerWP_and
          (writerWP_rootStep_space_collF fuelR hfR x only n c base w0 v hI hx hlk honly hcv hxl).1
          (writerWP_rootStep_space_rangeG x only n c base v _ _ _ hI hR hx hlk honly hcv hxl).1)
          (writerWP_rootStep_space_j2F x only n c base w0 v fuelR hI B hpos hJ hx hlk honly).1
      · subst hps
        obtain ⟨hLr, hLlk, hk', hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
        rw [hlen]
        exact writerWP_and (writerWP_and
          (writerWP_takeBackRoot_seg_collF fuelR hfR x ps0.length only n L ln k c base w0 v hI hLr hLlk
            hLl hk' hlk honly hcv hxl hpd hpk)
          (writerWP_takeBackRoot_seg_rangeG x ps0.length only n L ln k c base v _ _ _ hI hR hLr hLlk
            hLl hk' hlk honly hcv hxl hpd hpk))
          (writerWP_takeBackRoot_seg_j2F x ps0.length only n L ln k c base w0 v fuelR hI B hpos hJ hLr hLlk
            hLl hk' hlk honly hcv hxl hm hpd hpk)
    have hnx := @state_takeBackRoot (nextFromInvariant v) x (v.path.length - 1) only c v (Nat.le_refl _)
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hcr
      (putBook_takeBackRoot x _ only c base B top0 hB v hb hBx))
      (kd_takeBackRoot KO B x _ only c v hv hk hbk hik a hpa g h hgh hh)) hnx) ?_
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
    have hfit := hfits v x n only hI hR hP hlk hxl hm honly hcv
    have hbook := putBook_replaceRoot x (v.path.length - 1) only c base B top0 hB v hb
    have hkd := kd_replaceRoot KO B x _ only c v hv hk hbk hik a hpa g h hgh hh
    have hnx := @state_replaceRoot (nextFromInvariant v) x (v.path.length - 1) only c v (Nat.le_refl _)
    have hP0 := hP
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      have hrg := (writerWP_rootStep_space_rangeG x only n c base v _ _ _ hI hR hx hlk honly hcv hxl).2
      have hcl := (writerWP_rootStep_space_collF fuelR hfR x only n c base w0 v hI hx hlk honly hcv hxl).2
      have hj := (writerWP_rootStep_space_j2F x only n c base w0 v fuelR hI B hpos hJ hx hlk honly).2 hm
      rw [hvp] at hbook hkd hnx ⊢
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and hcl hrg) hbook)
        hkd) hj) hnx) ?_
      rintro _ v' ⟨⟨⟨⟨⟨hI', hR'⟩, hb'⟩, hbk', hik', _, _⟩, hJ'⟩, hn'⟩
      exact ⟨hI', hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩
    · subst hps
      obtain ⟨hLr, hLlk, hk', hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      have hj : WriterWP (replaceRoot x (ps0.length + 1) only) c v (fun _ v' => TakeJ2 c base B v') := by
        by_cases hroom : ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false
        · exact writerWP_replaceRoot_seg_j2F x ps0.length only n L ln k c base w0 v fuelR hI B hpos hJ hLr hLlk
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
      refine ⟨⟨⟨hT', hU', fun y yn _ hy => hG'.times y yn hy,
        fun y yn cc z hy hyn hl hc => hICEk v' hbk' hik' hU' y yn cc z hy hyn hl hc⟩,
        hread' hf', hf', fun y yn _ hy => hW' y yn hy, fun y yn _ hy => hG'.keyNoValue y yn hy⟩,
        hR', hb', hbk', hik', hJ', Nat.le_trans hBn hn'⟩
  · rintro x v n ⟨hI, hR, hb, hbk, hik, hJ, _⟩ hP hlk hft
    exact checkRoot_ok_of_segDesc c base w0 fuelR B top0 hB v hI hR hb hbk hJ x n hP hlk hft

/-- The merges' loop keeps the books. -/
theorem putBook_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) (c : Ctx) (base : View BVal)
    (B : NodeId) (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (mergeUp key g fuel h merged) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_mergeUp key g fuel h merged)
    (good_mergeUp B key g fuel h merged) (book_mergeUp B key g fuel h merged)
    (@state_mergeUp (allocatedIdsInvariant B) key g fuel h merged)
    (@state_mergeUp (commitInvariant top0) key g fuel h merged)
    (freshCache_mergeUp key g fuel h merged) (ptrs_mergeUp _ key g fuel h merged)

set_option maxHeartbeats 1600000 in
/-- `afterDelete` runs as `afterDeleteChk` from a state with `DelInvJ` and the
books of one first id B, where the merges' loop runs as its checked copy: the
merges' loop keeps both (`writerWP_mergeUp_delJ`, `putBook_mergeUp`), and root
collapse runs as its checked copy (`rwp_collapseRoot_chkJ`). -/
theorem rwp_afterDelete_of_J (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (hC : CollapseFitsOK c base fuelR) (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OKC c base fuelR B)
    (top0 : Top) (hB : PutBase c base B) (w0 : W) (k0 : Key) (v : W)
    (hJ : DelInvJ c base w0 k0 fuelR KO B B v) (hb : PutBook c B top0 v)
    (hmu : RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v) :
    RWP (afterDelete key g h) (afterDeleteChk key g h) c v := by
  unfold afterDelete afterDeleteChk
  refine rwp_read ?_
  refine rwp_ite (fun _ => ?_) (fun _ => rwp_refl _ _ _)
  refine rwp_bind2 (fun _ v1 => DelInvJ c base w0 k0 fuelR KO B B v1 ∧ PutBook c B top0 v1) hmu
    (writerWP_and (writerWP_mergeUp_delJ key g c base hvc fuelR hfR hM KO B hv hk hICEk hsa2 hcap B hpos
      w0 k0 c.p.fuel h false v hJ) (putBook_mergeUp key g c.p.fuel h false c base B top0 hB v hb)) ?_
  rintro r v1 ⟨hJ1, hb1⟩
  refine rwp_ite (fun _ => ?_) (fun _ => rwp_refl _ _ _)
  obtain ⟨⟨⟨hP, _, hR, hICE, hF, _, _⟩, hbk, hik⟩, hJ', hBn⟩ := hJ1
  have hCI : CollGetInvF c base v1 v1 fuelR := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  exact rwp_collapseRoot_chkJ fuelR hfR key g c base hvc v1 B top0 hB KO hv hk hICEk hsa2 (hC v1) hpos hRJ
    c.p.fuel v1 hCI hR hb1 hbk hik hJ' hBn

/-- At every state, `afterDeleteJ J` runs as `afterDeleteChk` when every state of
J lets `afterDelete` run as `afterDeleteChk` where the merges' loop runs as its
checked copy. -/
theorem rwp_afterDeleteJ (J : W → Prop) (key : Key) (g h : Nat) (c : Ctx)
    (hJ : ∀ v, J v → RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v →
      RWP (afterDelete key g h) (afterDeleteChk key g h) c v) (v : W) :
    RWP (afterDeleteJ J key g h) (afterDeleteChk key g h) c v := by
  intro x hx
  unfold afterDeleteJ at hx
  obtain ⟨a, v1, h1, h2⟩ := (m_bind_ok _ _ c v x).mp hx
  obtain ⟨ha, hv1⟩ := ((writerWP_read c v (fun a w' => a = c ∧ w' = v)).mpr ⟨rfl, rfl⟩) a v1 h1
  subst a; subst v1
  obtain ⟨b, v2, h3, h4⟩ := (m_bind_ok _ _ c v x).mp h2
  obtain ⟨hb, hv2⟩ := ((writerWP_get c v (fun b w' => b = v ∧ w' = v)).mpr ⟨rfl, rfl⟩) b v2 h3
  subst b; subst v2
  split at h4
  · rename_i hc
    exact hJ v hc.1 hc.2 x h4
  · exact ((writerWP_throw _ c v (fun _ _ => False)) _ _ h4).elim

set_option maxHeartbeats 1600000 in
/-- `OpDelChk5OKR` from `OpDelChk6OKR`, given the merges' fuel (`MergeStepOK`,
from `hMSF`) and the collapse's (`CollapseFitsOK`, `hCoF`): root collapse's
check is proved. -/
theorem opDelChk5OKR_of_chk6 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (h6 : OpDelChk6OKR p R) : OpDelChk5OKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have h6' := h6 ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hfR : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  rw [putKvDelChk5_eq]
  refine rwp_putKvDP (afterDeleteJ (DelHoleJ p ts tx top w key)) afterDeleteChk (ctxOf p ts) ?_ key w _ h6'
  intro key' g h v'
  refine rwp_afterDeleteJ _ key' g h (ctxOf p ts) ?_ v'
  rintro v'' ⟨hJ'', hb''⟩ hmu
  exact rwp_afterDelete_of_J key' g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (p.fuel + 1) hfR (hMS ts) (hCo ts)
    _ tx.base hv hk hICEk (by simpa [ctxOf] using hsa2) (by simpa [ctxOf] using hcap) (by simp [ctxOf])
    (replaceRootFullJ2OKC_run p hsa2 ts tx.base) top hB w key v'' hJ'' hb'' hmu

/-! ## The top theorem without root collapse's check -/

/-- `invGetScanOK_merges` with `hchk6` (`OpDelChk6OKL`) in place of `hchk5`:
root collapse's check is proved (`opDelChk5OKR_of_chk6`). -/
theorem invGetScanOK_merges_chk6 (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk6 : OpDelChk6OKL p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  exact invGetScanOK_merges p hp hth
    (opDelChk5OKR_of_chk6 p _ (by omega) hsa hcap (fun _ _ h => h.1) (fun _ _ h => h.1.1)
      (fun _ _ h => h.2.2.1.2.2.1)
      (fun ts => mergeStepOK_of_segFits (ctxOf p ts) _ _ (Nat.succ_pos _) hcap hsa (hMSF ts)) hCoF hchk6)
    htb d4 l4 hU hMSF hCoF

end SIS.Tree
