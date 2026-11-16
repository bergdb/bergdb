/-
`htb`'s sites (bergdb 025-05, step 8), whole: the premise `htbL` of
`invGetScanOK_merges_tbL` holds (`takeBelowFuelDelSL_holds`). At a delete of the
induction's runs, the nodes found at its start with a cached height at or above the fuel
(`TallAt`) are inner nodes of the transaction with two live klongs or more (the live
counts and the take-back's node facts at the start, `tallOK_start`). The delete runs as
its checked copy that checks, at each call of `afterDelete`, the state the stratum gives
there, and after the merges' loop the take-back's node facts (`opDelChkH_holds`). That
copy keeps the frame (`tk_putKvDelChk2G`), so it takes no tall node back.
-/
import SIS.Tree.HtbExc

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node found at a delete's start w0, not taken back, with a cached height at or above
the fuel. -/
def TallAt (p : Params) (w0 : W) (y : NodeId) : Prop :=
  ∃ g h, (y, g, h) ∈ w0.gh ∧ w0.taken.contains y = false ∧ p.fuel ≤ h

theorem tallAt_def (p : Params) (w0 : W) :
    ∀ y, TallAt p w0 y → ∃ g hy, (y, g, hy) ∈ w0.gh ∧ p.fuel ≤ hy :=
  fun _ ⟨g, h, hm, _, hle⟩ => ⟨g, h, hm, hle⟩

theorem KNode.time_mem_of_firstTime (n : KNode) (t : Time) (h : n.firstTime = some t) :
    Klong.time t ∈ n.ks := by
  unfold KNode.firstTime at h
  obtain ⟨k, hk, hks⟩ := List.exists_of_findSome?_eq_some h
  cases k with
  | time x => simp at hks; subst hks; exact hk
  | key _ _ => simp at hks
  | del _ => simp at hks

theorem Params.H_lt_fuel (p : Params) : p.H < p.fuel := by
  unfold Params.fuel
  have : p.H + 2 ≤ (p.G + 1) * (p.H + 2) := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem merges_of_mergeParamsOK (p : Params) (hp : MergeParamsOK p) : p.merges = true := by
  have := hp.1
  unfold Params.merges; simp only [decide_eq_true_eq]; omega

/-- At a delete's start, every tall node is an inner node of the transaction with two
live klongs or more: it is no node of P (whose heights are at most H), so the
transaction made it; it is reached (the take-back's node facts) and so has two live
klongs (the live counts). -/
theorem tallOK_start (p : Params) (hp : MergeParamsOK p) (ts : List Tx) (tx : Tx) (w : W)
    (hb : Book tx.base (ctxOf p ts) w) (hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hL : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hJ : J2At p (treeRun p ts) (ts.length + 1) tx.base w) :
    TallOK (viewOf (treeRun p ts)) (TallAt p w) (ctxOf p ts) w := by
  intro y ⟨g, h, hm, hun, hle⟩
  have hH := Params.H_lt_fuel p
  refine ⟨hb.bound _ hm, hun, ?_⟩
  have hB : tx.base ≤ y := by
    rcases hb.tag y g h hm with ⟨nd, _, _, _, _, hh⟩ | ⟨hB, _⟩
    · have := heightOf_le p nd.level
      simp only [ctxOf] at hh
      omega
    · exact hB
  have hmem : y ∈ w.nodes.map (·.1) := by
    rw [hb.ids]; exact List.mem_reverse.mpr (List.mem_map.mpr ⟨_, hm, rfl⟩)
  obtain ⟨⟨y', n⟩, hyn, hye⟩ := List.mem_map.mp hmem
  simp only at hye
  subst hye
  obtain ⟨n', hl⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem' _ _ _ hyn)
  have hw : wNode p (viewOf (treeRun p ts)) w y' = some n' := by
    unfold wNode; simp only [hun, Bool.false_eq_true, ↓reduceIte, hl]
  have hleaf : n'.leaf = false := by
    have := kd_leaf hb hl hm
    rw [this]
    cases h with
    | zero => omega
    | succ k => rfl
  have hft : n'.firstTime = some (ts.length + 1) := hJ.2.2.2.2.1 y' n' hw hB
  refine ⟨n', hw, hleaf, by simpa [ctxOf] using hft, ?_⟩
  have hreach : TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey y' :=
    hJ.1 y' n' hw (KNode.time_mem_of_firstTime n' _ hft)
  obtain ⟨b, s, hF⟩ := tReach_fReach hreach
  have hLC := hL y' b s n' hF hw
  have htimes : ∀ s, Klong.time s ∈ n'.ks → s ≤ ts.length + 1 := hI.times y' n' (by simpa [ctxOf] using hw)
  rw [KNode.liveAt_of_times n' _ htimes] at hLC
  have hm2 := hp.1
  have hmg := merges_of_mergeParamsOK p hp
  unfold KNode.cnt
  cases b with
  | true => exact hLC.2.1 hleaf rfl
  | false => have := hLC.2.2 hmg rfl; omega

/-! ## The last merge's case and the check after the merges' loop -/

/-- After the loop's last merge with a tall parent q: the frame but at q, and q, not taken
back, an inner node of the transaction that names two nodes of the transaction, or has
two live klongs. -/
def ExcE (B : NodeId) (base : View BVal) (T : NodeId → Prop) (c : Ctx) (v : W) : Prop :=
  ∃ q nq, TallOK base (fun y => T y ∧ y ≠ q) c v ∧ v.taken.contains q = false ∧
    v.nodes.lookup q = some nq ∧ nq.leaf = false ∧ nq.firstTime = some c.i ∧
    ((∃ (i j cv1 cv2 : Nat) (y1 y2 : NodeId), nq.ks[i]? = some (Klong.key cv1 y1) ∧
      nq.ks[j]? = some (Klong.key cv2 y2) ∧
      y1 ≠ y2 ∧ B ≤ y1 ∧ B ≤ y2 ∧ y1 ∈ v.gh.map (·.1) ∧ y2 ∈ v.gh.map (·.1)) ∨ 2 ≤ nq.cnt)

/-- The check after the merges' loop: the take-back's node facts, and no value in `gh`. -/
def TcH (c : Ctx) (base : View BVal) (B : NodeId) (v : W) : Prop :=
  TakeJ2 c base B v ∧ ∀ q ∈ v.vals, q.1 ∉ v.gh.map (·.1)

/-- With the take-back's node facts, the last merge's case is the frame: a node that names
two nodes of the transaction has both live, so two live klongs. -/
theorem excE_conv {H : NodeId → Nat → Prop} (B : NodeId) (base : View BVal) (T : NodeId → Prop)
    (c : Ctx) (w0 v : W) (hTdef : ∀ y, T y → ∃ g hy, (y, g, hy) ∈ w0.gh ∧ c.p.fuel ≤ hy)
    (hb : Book B c v) (hi : HtInv H B c v) (hk : Kept w0 v) (hE : ExcE B base T c v)
    (hTc : TcH c base B v) : TallOK base T c v := by
  obtain ⟨q, nq, hT', hqt, hql, hnl, hnf, hcnt⟩ := hE
  intro y hTy
  by_cases hyq : y = q
  · subst hyq
    obtain ⟨g, hy, hm, -⟩ := hTdef y hTy
    have hm' := hk.2 _ hm
    have hw : wNode c.p base v y = some nq := by
      unfold wNode; simp only [hqt, Bool.false_eq_true, ↓reduceIte, hql]
    refine ⟨hb.bound _ hm', hqt, nq, hw, hnl, hnf, ?_⟩
    rcases hcnt with ⟨i, j, cv1, cv2, y1, y2, h1, h2, hne, hB1, hB2, hg1, hg2⟩ | h
    · have hval : ∀ z, z ∈ v.gh.map (·.1) → z ∉ v.vals.map (·.1) := by
        intro z hz hv
        obtain ⟨⟨z', a⟩, hzm, hze⟩ := List.mem_map.mp hv
        simp only at hze
        subst hze
        exact hTc.2 _ hzm hz
      have hDL := hTc.1.2.1
      obtain ⟨c1, hc1⟩ := (hDL y nq hw i cv1 y1 h1 hB1 (hval y1 hg1)).1
      obtain ⟨c2, hc2⟩ := (hDL y nq hw j cv2 y2 h2 hB2 (hval y2 hg2)).1
      have hc12 : c1 ≠ c2 := by
        intro e; subst e; exact hne (KNode.liveAt_fun nq c.i c1 y1 y2 hc1 hc2)
      have htimes : ∀ s, Klong.time s ∈ nq.ks → s ≤ c.i :=
        (hi.cache y nq g hy (bk_mem_of_lookup _ _ _ hql) hm' hqt).times
      rw [KNode.liveAt_of_times nq c.i htimes] at hc1 hc2
      have hsub : ∀ k ∈ [c1, c2], k ∈ nq.live.map Prod.fst := by
        intro k hk'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk'
        rcases hk' with rfl | rfl
        · exact List.mem_map.mpr ⟨_, hc1, rfl⟩
        · exact List.mem_map.mpr ⟨_, hc2, rfl⟩
      have hnd : [c1, c2].Nodup := by simp [hc12]
      have := hnd.length_le_of_subset hsub
      simpa [KNode.cnt] using this
    · exact h
  · exact hT' y ⟨hTy, hyq⟩

/-! ## The delete runs as the copy with the checks -/

open Classical in
theorem rwp_get_check {β : Type} {f g : M β} {P : W → Prop} {e : String} {c : Ctx} {v : W}
    (hP : P v) (h : RWP f g c v) :
    RWP f (do let v' ← (MonadState.get : M W); if P v' then g else throw e) c v := by
  intro x hx
  refine (m_bind_ok _ _ c v x).mpr ⟨v, v, rfl, ?_⟩
  simp only [hP, ↓reduceIte]
  exact h x hx

set_option maxHeartbeats 1600000 in
/-- `rwp_afterDelete_of_JA` with the check after the merges' loop: the stratum's
invariant after the loop gives the take-back's node facts and the kinds' books. -/
theorem rwp_afterDelete_TH (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i) (KO : KindOracle) (B : NodeId)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (top0 : Top) (hB : PutBase c base B)
    (w0 : W) (k0 : Key) (v : W) (hA : DelInvJA c base w0 k0 KO B B v) (hb : PutBook c B top0 v)
    (hmu : RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v) :
    RWP (afterDelete key g h) (afterDeleteChkT (TcH c base B) key g h) c v := by
  unfold afterDelete afterDeleteChkT
  refine rwp_read ?_
  refine rwp_ite (fun _ => ?_) (fun _ => rwp_refl _ _ _)
  refine rwp_bind2 (fun _ v1 => DelInvJA c base w0 k0 KO B B v1 ∧ PutBook c B top0 v1) hmu
    (writerWP_and (writerWP_mergeUp_delJA key g c base hvc hpos KO B hv hk hICEk hsa2 hcap B w0 k0
      c.p.fuel h false v hA) (putBook_mergeUp key g c.p.fuel h false c base B top0 hB v hb)) ?_
  rintro r v1 ⟨hA1, hb1⟩
  have hTc : TcH c base B v1 := by
    obtain ⟨F, hF, hn⟩ := exists_fuel_above c v1
    obtain ⟨⟨_, _, hki⟩, hJ, _⟩ := hA1 F hF hn
    exact ⟨hJ, fun q hq => (hki.vals q hq).2.2⟩
  refine rwp_get_check hTc ?_
  refine rwp_ite (fun _ => ?_) (fun _ => rwp_refl _ _ _)
  intro x hx
  obtain ⟨F, hF, hn⟩ := exists_fuel_above c x.2
  have hp2 : 2 ≤ F := by unfold Params.fuel at hF; omega
  have hle : v1.next ≤ x.2.next :=
    (freshCache_collapseRoot key g c.p.fuel c v1 hB.good.ids hb1.fresh x.1 x.2 hx).2
  obtain ⟨⟨⟨hP, _, hR, hICE, hFv, _, _⟩, hbk, hik⟩, hJ, hBn⟩ := hA1 F hF (Nat.lt_of_le_of_lt hle hn)
  have hCI : CollInvJW c base v1 F (fun u => u.next < F) B top0 KO B B v1 :=
    ⟨hb1.fresh, fun _ => ⟨⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hFv, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩,
      hR, hb1, hbk, hik, hJ, hBn⟩⟩
  exact rwp_collapseRoot_chkJW F hp2 key g c base hvc v1 B top0 hB KO hv hk hICEk hsa2 (fun u => u.next < F)
    (fun _ _ hle hlt => Nat.lt_of_le_of_lt hle hlt) (collFitsW_next c base v1 F) hpos
    (replaceRootFullJ2OKC_holds c base F hp2 B hpos hsa2) c.p.fuel v1 hCI x hx hn

/-- `afterDeleteJ J` runs as `afterDeleteH J Tc` where J gives `afterDelete` as
`afterDeleteChkT Tc`. -/
theorem rwp_afterDeleteJH (J Tc : W → Prop) (key : Key) (g h : Nat) (c : Ctx)
    (hJ : ∀ v, J v → RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v →
      RWP (afterDelete key g h) (afterDeleteChkT Tc key g h) c v) (v : W) :
    RWP (afterDeleteJ J key g h) (afterDeleteH J Tc key g h) c v := by
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
    unfold afterDeleteH
    exact rwp_get_check hc.1 (hJ v hc.1 hc.2) x h4
  · exact ((writerWP_throw _ c v (fun _ _ => False)) _ _ h4).elim

set_option maxHeartbeats 1600000 in
/-- At the deletes of the induction's runs, the delete runs as its checked copy with the
checks of `afterDeleteH`: the stratum's state at each call of `afterDelete`, and the
take-back's node facts after the merges' loop. -/
theorem opDelChkH_holds (p : Params) (hp : MergeParamsOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hr : RunTreeQ p (LatestQD p) (treeRun p ts) ts.length)
    (z : NodeId) (top : Top) (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre : List Op) (key : Key) (post : List Op)
    (hs : tx.ops = pre ++ Op.del key :: post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hL : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hH : HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w)
    (hJ : J2At p (treeRun p ts) (ts.length + 1) tx.base w)
    (r' : Bool) (v : W) (he : putKv (.del key) (ctxOf p ts) w = .ok (r', v)) :
    putKvDelChk2G (afterDeleteH (DelHoleJE p ts tx top) (TcH (ctxOf p ts) (viewOf (treeRun p ts)) tx.base))
      key (ctxOf p ts) w = .ok (r', v) := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM4 := four_le_M p hp
  have hm : p.merges = true := merges_of_mergeParamsOK p hp
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRP : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have h6 := opDelChk6TOKR_of_chk7T p _ (by omega) hsa hRL hRP hRK
    (opDelChk7TOKR_of_chk8 p _ hM4 hsa hm hRL hRP hRK (opDelChk8OKR_holdsT p _ hM4 hsa hm hRL hRP hRK hcap))
    ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  obtain ⟨hv, hk, hICEk⟩ := viewFacts_of_run p _ hRP hRK ts tx hw hr
  have h5 : putKvDP (afterDeleteH (DelHoleJE p ts tx top) (TcH (ctxOf p ts) (viewOf (treeRun p ts)) tx.base))
      key (ctxOf p ts) w = .ok (r', v) := by
    refine rwp_putKvDP (afterDeleteJ (DelHoleJE p ts tx top)) _ (ctxOf p ts) ?_ key w _ h6
    intro key' g h v'
    refine rwp_afterDeleteJH _ _ key' g h (ctxOf p ts) ?_ v'
    intro v'' hJ'' hmu
    obtain ⟨u, hu⟩ := hJ''.1
    exact rwp_afterDelete_TH key' g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (by simp [ctxOf]) _ tx.base
      hv hk hICEk (by simpa [ctxOf] using hsa) (by simpa [ctxOf] using hcap) top hB u [] v'' hu hJ''.2 hmu
  have hmf := stateOK_madeForView p hM4 _ hRL ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
  have hbk := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
  obtain ⟨hvg, hu⟩ := uniqueCache_reached p ts tx hw (hRL _ _ hr) top pre r w hpre
  exact rwp_putKvDelChk5G _ (ctxOf p ts) (viewOf (treeRun p ts)) (viewCoherent_ctxOf p ts) w tx.base hvg hI hJ
    hbk.good hu hL hm (fun x o ho => (hmf x o ho).2) key _ h5

/-- The merges' loop's last merge with a tall parent q (bergdb 025-05, step 8): the frame
but at q, and q a node that names two nodes of the transaction or has two live klongs. -/
theorem tk_exc {H : NodeId → Nat → Prop} (B : NodeId) (base : View BVal) (T : NodeId → Prop) (c : Ctx)
    (w0 : W) (hvo : ViewHtOK H B c) (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base)
    (hpos : 0 < c.i) (hHb : ∀ y h, H y h → h ≤ c.p.H) (K : KindOracle) (hkK : ViewKinds K B c)
    (hTdef : ∀ y, T y → ∃ g hy, (y, g, hy) ∈ w0.gh ∧ c.p.fuel ≤ hy) :
    ∀ x d v, Book B c v → HtInv H B c v → WriterKlongsWf v → Kept w0 v → TallOK base T c v →
      KdInv K B v → d ≠ 0 → (∃ a, v.path[d]? = some (a, x)) → d + 1 = v.path.length →
      PathFreeTo v v.path.length →
      (∀ a q, v.path[d - 1]? = some (a, q) → v.taken.contains q = false ∧ T q ∧
        ∀ qn, wNode c.p base v q = some qn → ∀ cv y, (cv, y) ∈ qn.live → ¬ T y) →
      WriterWP (mergeChk x d) c v (fun r v' => r = 2 → ExcE B base T c v') := by
  intro x d v hb hi _ hk0 hT hki hd ⟨ax, hpx⟩ hlen hpf hq
  have hdl : d - 1 < v.path.length := by omega
  obtain ⟨aq, q, hpq⟩ : ∃ aq q, v.path[d - 1]? = some (aq, q) :=
    ⟨(v.path[d - 1]).1, (v.path[d - 1]).2, by simp [hdl]⟩
  obtain ⟨hqf, hTq, hch⟩ := hq aq q hpq
  obtain ⟨hqn, -, nq, hwq, hql, hqfirst, -⟩ := hT q hTq
  have hqg : q ∈ v.gh.map (·.1) := hi.pathGh (d - 1) aq q hpq (by omega)
  have hlk : v.nodes.lookup q = some nq := by
    have hmem : q ∈ v.nodes.map (·.1) := by rw [hb.ids]; exact List.mem_reverse.mpr hqg
    obtain ⟨⟨q'', n'⟩, hn', hne⟩ := List.mem_map.mp hmem
    simp only at hne
    subst hne
    obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem' _ _ _ hn')
    have : wNode c.p base v q'' = some n0 := by
      unfold wNode; simp only [hqf, Bool.false_eq_true, ↓reduceIte, hn0]
    rw [this] at hwq
    cases hwq
    exact hn0
  obtain ⟨⟨q', gq, hq⟩, hqm, hqe⟩ := List.mem_map.mp hqg
  simp only at hqe
  subst hqe
  obtain ⟨g0, hq0, hm0, hle0⟩ := hTdef q' hTq
  have hqh : hq = hq0 := (kd_tag_eq hb hqm (hk0.2 _ hm0)).2
  have hfuel : c.p.H + 2 < c.p.fuel := by
    unfold Params.fuel
    have : c.p.H + 2 ≤ (c.p.G + 1) * (c.p.H + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hq0' : hq ≠ 0 := by omega
  have hNq : NodeHt c H v hq nq := hi.cache q' nq gq hq (bk_mem_of_lookup _ _ _ hlk) hqm hqf
  -- the children of q: nodes of the transaction one height below
  let S0 : NodeId → Prop := fun y => B ≤ y ∧ ∃ g, (y, g, hq - 1) ∈ v.gh
  have hS : ∀ cv y, (cv, y) ∈ nq.live → S0 y := by
    intro cv y hy
    rcases (hNq.live cv y hy).2 hq0' with ⟨g, hg⟩ | hH
    · refine ⟨?_, g, hg⟩
      rcases hb.tag y g (hq - 1) hg with ⟨nd, -, -, -, -, hh'⟩ | ⟨hB, -⟩
      · exfalso; have := heightOf_le c.p nd.level; omega
      · exact hB
    · exfalso; have := hHb y _ hH; omega
  have hS0 : ∀ y, S0 y → y < v.next := fun y hy => hb.bound _ hy.2.choose_spec
  have hSq : ∀ y, S0 y → y ≠ q' := by
    rintro y ⟨_, g, hg⟩ rfl
    have := (kd_tag_eq hb hqm hg).2
    omega
  -- x, the last node of the path
  obtain ⟨k, hak⟩ : ∃ k, ax = some k := by
    cases ax with
    | none => exact absurd rfl (hi.pathSome (d - 1) none x (by rw [show d - 1 + 1 = d by omega]; exact hpx))
    | some k => exact ⟨k, rfl⟩
  have hxh : HasHt H v x (hq - 1) :=
    hi.path (d - 1) aq q' k x hpq (by rw [show d - 1 + 1 = d by omega, hpx, hak]) gq hq hqm hqf hq0'
  have hall : ∀ (j : Nat) (a : Option Nat) (z : NodeId), v.path[j]? = some (a, z) →
      z ∈ v.gh.map (·.1) := by
    intro j a z hz
    by_cases hj : j + 1 < v.path.length
    · exact hi.pathGh j a z hz hj
    · have hjd : j = d := by have := (List.getElem?_eq_some_iff.mp hz).1; omega
      subst hjd
      rw [hpx] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨-, rfl⟩ := hz
      rcases hxh with ⟨g, hg⟩ | hH
      · exact List.mem_map.mpr ⟨_, hg, rfl⟩
      · exfalso; have := hHb x _ hH; omega
  have hpd : ∀ j a z, j < d - 1 → v.path[j]? = some (a, z) → z ≠ q' :=
    fun j a z hj hz => ht_path_ne hb hvo hi hkK hki hpf hall (by omega : j ≠ d - 1) hz hpq
  have hFD : FrameD q' nq (d - 1) v.next v := ⟨hqn, hlk, hqf, hpd, Nat.le_refl _⟩
  have hT' : TallOK base (fun y => T y ∧ y ≠ q') c v := fun y hy => hT y hy.1
  have hpq5 : ∀ a q2, v.path[d - 1]? = some (a, q2) →
      ∃ nq, v.nodes.lookup q2 = some nq ∧ nq.leaf = false := by
    intro a q2 hq2
    rw [hpq] at hq2
    simp only [Option.some.injEq, Prod.mk.injEq] at hq2
    obtain ⟨-, rfl⟩ := hq2
    exact ⟨nq, hlk, hql⟩
  have hpfd : PathFreeTo v (d + 1) := fun j a z hj hz => hpf j a z (by omega) hz
  refine writerWP_mono (writerWP_and (writerWP_and
    (tk_mergeChk (T := fun y => T y ∧ y ≠ q') x d c v hmp hvc hT' (fun a q2 hq2 => ?_))
    (ht_mergeChk B x d c v hvo hpos hb hi hd (some k) (by rw [hpx, hak]) hpfd hpq5))
    (qx_mergeChk B x d c hmp hpos v q' nq S0 aq hpq hFD hb.next hS0 hqfirst hql hNq.times hS hSq)) ?_
  · rw [hpq] at hq2
    simp only [Option.some.injEq, Prod.mk.injEq] at hq2
    obtain ⟨-, rfl⟩ := hq2
    exact ⟨hqf, fun h => h.2 rfl, fun qn hqn cv y hy h => hch qn hqn cv y hy h.1⟩
  rintro r v' ⟨⟨hT'', -, -, hkv, -⟩, hqx⟩ hr2
  obtain ⟨m1, m2, e1, e2, ⟨he1, he2, n, hfd, hnl, hnf, hsh⟩, rfl, rfl, hB1, hB2, -⟩ := hqx hr2
  refine ⟨q', n, hT'', hfd.2.2.1, hfd.2.1, hnl, hnf, ?_⟩
  rcases hsh with ⟨i, j, cv1, cv2, y1, hi1, hj1, hne, hy1⟩ | h2
  · left
    refine ⟨i, j, cv1, cv2, y1, e2.1, hi1, hj1, hne, ?_, hB2, ?_, List.mem_map.mpr ⟨e2, he2, rfl⟩⟩
    · rcases hy1 with rfl | ⟨hB, -⟩
      · exact hB1
      · exact hB
    · rcases hy1 with rfl | ⟨-, g, hg⟩
      · exact List.mem_map.mpr ⟨e1, he1, rfl⟩
      · exact List.mem_map.mpr ⟨_, hkv.2 _ hg, rfl⟩
  · exact Or.inr h2

/-- `htbL` holds (bergdb 025-05, step 8): at a delete of the induction's runs, a node found
at its start and taken back by it has its cached height below the fuel. -/
theorem takeBelowFuelDelSL_holds (p : Params) (hp : MergeParamsOK p) : TakeBelowFuelDelSL p := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hT hJ a v he x g h hm hx hv
  rcases Nat.lt_or_ge h p.fuel with hlt | hge
  · exact hlt
  exfalso
  have hTx : TallAt p w x := ⟨g, h, hm, hx, hge⟩
  have hrun := opDelChkH_holds p hp ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ a v he
  have hRL : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRP : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t := fun _ _ h => h.2.2.1.2.2.2.1
  have hM4 := four_le_M p hp
  obtain ⟨hvo, hkw, -, -, hb, -, hwf⟩ := htStart0_of_ht p _ hRL hRK hRH ts tx hw hr z top htop pre r w hpre hH
  obtain ⟨hvB, hk, -, hki⟩ := kd_contextR p (by omega) ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre
    (Op.del key :: post) hs r w hpre
  have hT0 := tallOK_start p hp ts tx w hb hI hL hJ
  have hJK : ∀ v, DelHoleJE p ts tx top v → KdInv (kindOracleOf p (treeRun p ts)) tx.base v := by
    intro v hv
    obtain ⟨u, hu⟩ := hv.1
    obtain ⟨F, hF, hn⟩ := exists_fuel_above (ctxOf p ts) v
    exact (hu F hF hn).1.2.2
  have hHb : ∀ y h, htOracleOf p (treeRun p ts) y h → h ≤ (ctxOf p ts).p.H := by
    rintro y h ⟨ny, -, -, -, rfl⟩
    simpa [ctxOf] using heightOf_le p ny.level
  have hAd := tk_afterDeleteH tx.base (DelHoleJE p ts tx top)
    (TcH (ctxOf p ts) (viewOf (treeRun p ts)) tx.base) (ctxOf p ts) hvo (by simp [ctxOf]) hkw hp
    (viewCoherent_ctxOf p ts) _ hvB hk hJK w (tallAt_def p w) _
    (tk_exc tx.base _ _ _ w hvo hp (viewCoherent_ctxOf p ts) (by simp [ctxOf]) hHb _ hk (tallAt_def p w))
    (fun v hb hi hk hE hTc => excE_conv tx.base _ _ _ w v (tallAt_def p w) hb hi hk hE hTc)
  have hwalk := tk_putKvDelChk2G tx.base _ key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hH hwf hk hki
    (by simp [ctxOf]; omega) hp (viewCoherent_ctxOf p ts) hT0 hAd
  obtain ⟨-, -, -, -, hTv⟩ := hwalk a v hrun
  have := (hTv x hTx).2.1
  rw [this] at hv
  cases hv

end SIS.Tree
