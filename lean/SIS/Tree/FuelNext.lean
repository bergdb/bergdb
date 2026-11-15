/-
Route P of bergdb 025-05 (section 4.1) for the reading's case of a delete with the
merges (TP10): a fuel above every node id. Every writer state with `PutInv` fits
its next id (P1, the pigeonhole bound: a chain of inner nodes has distinct ids,
all below the next id). So inside a delete the reading at every fuel above
p.fuel and the next id (`DelInvA`, P2) is kept by the merges' loop and root
collapse with no fit premise (P3), and case 4 of the reading
(`opGetCaseOK_delMergeA`, P5) needs neither `MergeStepOK` (`hMSF`) nor
`CollapseFitsOK` (`hCoF`): the family over an invariant (`DelStepsOKG`, P4) at
`DelInvA` takes the fit p.fuel - 1 only at the operation's end, where it holds.
-/
import SIS.Tree.CollapseCommuteRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## P1: every writer state fits its next id -/

/-- A segment tree deeper than d from a node at depth k has a chain of d + 1
key nodes, at depths k or more, each one id. -/
theorem chain_of_not_segDepthLe (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hT : TreeOK N t r) :
    ∀ d x k, PathLen N t r x k → ¬ SegDepthLe N t d x →
      ∃ l : List NodeId, l.length = d + 1 ∧ l.Nodup ∧ (∀ y ∈ l, ∃ m, N y = some m) ∧
        (∀ y ∈ l, ∃ j, k ≤ j ∧ PathLen N t r y j) := by
  intro d
  induction d with
  | zero =>
    intro x k hx hn
    have hm : ∃ m, N x = some m := by
      cases h : N x with
      | none => exact absurd (fun n hn' => by rw [h] at hn'; cases hn') hn
      | some m => exact ⟨m, rfl⟩
    refine ⟨[x], rfl, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_, ?_⟩
    · intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact hm
    · intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨k, Nat.le_refl _, hx⟩
  | succ d ih =>
    intro x k hx hn
    have hex : ∃ m, N x = some m ∧ m.leaf = false ∧
        ∃ c y, (c, y) ∈ m.liveAt t ∧ ¬ SegDepthLe N t d y := by
      refine Classical.byContradiction (fun hno => hn ?_)
      intro m hm hl c y hy
      exact Classical.byContradiction (fun hy' => hno ⟨m, hm, hl, c, y, hy, hy'⟩)
    obtain ⟨m, hm, _, c, y, hy, hy'⟩ := hex
    have hyk : PathLen N t r y (k + 1) := PathLen.link hx ⟨m, hm, hy⟩
    obtain ⟨l, hlen, hnd, hnode, hdep⟩ := ih y (k + 1) hyk hy'
    refine ⟨x :: l, by simp [hlen], ?_, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨fun hxl => ?_, hnd⟩
      obtain ⟨j, hj, hpj⟩ := hdep x hxl
      have := PathLen.depth_unique hT k x j hx hpj
      omega
    · intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h; exact ⟨m, hm⟩
      · exact hnode z h
    · intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h; exact ⟨k, Nat.le_refl _, hx⟩
      · obtain ⟨j, hj, hpj⟩ := hdep z h
        exact ⟨j, by omega, hpj⟩

/-- P1, the pigeonhole bound: in a tree whose nodes all have ids below n, every
segment tree reached is at most n deep. -/
theorem segFits_of_idsBelow (N : NodeId → Option KNode) (t : Time) (r : NodeId) (n : Nat)
    (hT : TreeOK N t r) (hid : ∀ x m, N x = some m → x < n) : SegFits N t n r := by
  intro x hx
  obtain ⟨k, hk⟩ := (reachS_tReach N t r x hx).pathLen
  refine Classical.byContradiction (fun hno => ?_)
  obtain ⟨l, hlen, hnd, hnode, -⟩ := chain_of_not_segDepthLe N t r hT n x k hk hno
  have hsub : l ⊆ List.range n := by
    intro y hy
    obtain ⟨m, hm⟩ := hnode y hy
    exact List.mem_range.mpr (hid y m hm)
  have := List.Nodup.length_le_of_subset hnd hsub
  rw [hlen, List.length_range] at this
  omega

/-- P1 from the books: a tree whose state has `PutInvG` fits its next id. -/
theorem segFits_next_of_putInvG (c : Ctx) (base : View BVal) (v : W) (hG : PutInvG c base v)
    (hT : TreeOK (wNode c.p base v) c.i v.top.rootKey) :
    SegFits (wNode c.p base v) c.i v.next v.top.rootKey := by
  refine segFits_of_idsBelow _ _ _ _ hT ?_
  intro x m hm
  rcases (wNode_cases c.p base v x m hm).2 with h | ⟨_, h⟩
  · exact hG.ids.1 x (by rw [h]; rfl)
  · rcases Nat.lt_or_ge x v.next with hlt | hge
    · exact hlt
    · have := (hG.fresh x hge).1
      rw [this] at h
      cases h

/-- P1 for the writer: every state with `PutInv` fits its next id. -/
theorem segFits_next_of_putInv (c : Ctx) (base : View BVal) (v : W) (hI : PutInv c base v) :
    SegFits (wNode c.p base v) c.i v.next v.top.rootKey := by
  refine segFits_of_idsBelow _ _ _ _ hI.tree ?_
  intro x m hm
  rcases (wNode_cases c.p base v x m hm).2 with h | ⟨_, h⟩
  · exact hI.ids.1 x (by rw [h]; rfl)
  · rcases Nat.lt_or_ge x v.next with hlt | hge
    · exact hlt
    · have := (hI.fresh x hge).1
      rw [this] at h
      cases h

/-! ## P2: the invariant above the next id, and its conversions -/

/-- The reading at two fuels, once the state fits below both. -/
theorem wGetAt_fuel_eq (c : Ctx) (base : View BVal) (w : W) (d f f' : Nat)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hfit : SegFits (wNode c.p base w) c.i d w.top.rootKey) (hf : d < f) (hf' : d < f') (key : Key) :
    wGetAt c.p c.i base w f key = wGetAt c.p c.i base w f' key := by
  unfold wGetAt
  exact getFromR_fuel_mono _ _ _ d _ hwf hfit f f' hf hf' key _ ReachS.root

/-- `DelInvF` moved from one fuel to another, both at least p.fuel, the state
fitting below the new one, the delete's start fitting p.fuel - 1. -/
theorem delInvF_fuel (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f F : Nat) (v : W)
    (hI0 : PutInv c base w0)
    (hF0 : SegFits (wNode c.p base w0) c.i (c.p.fuel - 1) w0.top.rootKey)
    (hf : c.p.fuel ≤ f) (hF : c.p.fuel ≤ F) (h : DelInvF c base w0 key f v)
    (hfit : SegFits (wNode c.p base v) c.i (F - 1) v.top.rootKey) : DelInvF c base w0 key F v := by
  obtain ⟨hP, hG, hR, hICE, hFf, hread, hbk⟩ := h
  have hp1 : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwf : ∀ x xn, ReachS (wNode c.p base v) c.i v.top.rootKey x → wNode c.p base v x = some xn →
      klongsWf xn.ks = true := fun x xn _ hx => hP.wf x xn hx
  have hwf0 : ∀ x xn, ReachS (wNode c.p base w0) c.i w0.top.rootKey x → wNode c.p base w0 x = some xn →
      klongsWf xn.ks = true := fun x xn _ hx => hI0.wf x xn hx
  refine ⟨hP, hG, hR, hICE, hfit, fun key' hk => ?_, hbk⟩
  have hv : wGetAt c.p c.i base v F key' = wGetAt c.p c.i base v f key' := by
    rcases Nat.le_total f F with hle | hle
    · exact wGetAt_fuel_eq c base v (f - 1) F f hwf hFf (by omega) (by omega) key'
    · exact wGetAt_fuel_eq c base v (F - 1) F f hwf hfit (by omega) (by omega) key'
  have h0 : wGetAt c.p c.i base w0 F key' = wGetAt c.p c.i base w0 f key' :=
    wGetAt_fuel_eq c base w0 (c.p.fuel - 1) F f hwf0 hF0 (by omega) (by omega) key'
  rw [hv, hread key' hk, h0]

/-- The delete's invariant at every fuel above p.fuel and the next id (bergdb
025-05, P2). -/
def DelInvA (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (KO : KindOracle) (BK : NodeId)
    (v : W) : Prop :=
  ∀ F, c.p.fuel + 1 ≤ F → v.next < F → DelInv c base w0 key F KO BK v

/-- P2, up: `DelInv` at p.fuel + 1 gives `DelInvA` (the fit at each larger fuel by P1). -/
theorem delInvA_of_delInv (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (KO : KindOracle)
    (BK : NodeId) (v : W) (hI0 : PutInv c base w0)
    (hF0 : SegFits (wNode c.p base w0) c.i (c.p.fuel - 1) w0.top.rootKey)
    (h : DelInv c base w0 key (c.p.fuel + 1) KO BK v) : DelInvA c base w0 key KO BK v := by
  intro F hF hn
  refine ⟨delInvF_fuel c base w0 key (c.p.fuel + 1) F v hI0 hF0 (by omega) (by omega) h.1 ?_, h.2.1, h.2.2⟩
  exact segFits_mono _ _ _ _ _ (segFits_next_of_putInv c base v h.1.1) (by omega)

/-- P2, down: `DelInvA` with the fit between operations gives `DelInv` at p.fuel + 1. -/
theorem delInv_of_delInvA (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (KO : KindOracle)
    (BK : NodeId) (v : W) (hI0 : PutInv c base w0)
    (hF0 : SegFits (wNode c.p base w0) c.i (c.p.fuel - 1) w0.top.rootKey)
    (h : DelInvA c base w0 key KO BK v)
    (hF : SegFits (wNode c.p base v) c.i (c.p.fuel - 1) v.top.rootKey) :
    DelInv c base w0 key (c.p.fuel + 1) KO BK v := by
  have hI := h (max (c.p.fuel + 1) (v.next + 1)) (Nat.le_max_left _ _)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
  refine ⟨delInvF_fuel c base w0 key _ (c.p.fuel + 1) v hI0 hF0 (by omega) (by omega) hI.1 ?_,
    hI.2.1, hI.2.2⟩
  exact segFits_mono _ _ _ _ _ hF (by omega)

/-! ## P3: the merges' loop and root collapse above the next id, no fit premise -/

/-- The merge's obligation where the next id is below f, for every state: the
untaken part proved (`mergeStepOK_untaken`), the fit by P1. -/
theorem mergeStepOKW_next (c : Ctx) (base : View BVal) (f : Nat) (hpos : 0 < c.i)
    (hcap : 1 ≤ c.p.mergeMax) (hsa2 : 2 ≤ c.p.splitAbove) :
    MergeStepOKW c base f (fun v => v.next < f) :=
  fun w0 key x q d v qn xn X K Nn h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    writerWP_mono (mergeStepOK_untaken c base f hpos hcap hsa2 w0 key x q d v qn xn X K Nn
      h1 h2 h3 h4 h5 h6 h7 h8 h9)
      (fun _ v' hu => ⟨hu, fun hlt hP =>
        segFits_mono _ _ _ _ _ (segFits_next_of_putInv c base v' hP) (by omega)⟩)

/-- P3: the merges' loop keeps `DelInvA`, with no fit premise. -/
theorem writerWP_mergeUp_delA (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvA c base w0 k0 KO BK v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvA c base w0 k0 KO BK v') := by
  intro fuel h merged v hA r v' he F hF hn
  have hp2 : 2 ≤ F := by unfold Params.fuel at hF; omega
  have hQ : DelInvW c base w0 k0 F (fun u => u.next < F) KO BK v := by
    obtain ⟨B, _, hB, hb⟩ := (hA (max (c.p.fuel + 1) (v.next + 1)) (Nat.le_max_left _ _)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))).1.2.2.2.2.2.2
    exact ⟨⟨B, hB.good.ids, hb.fresh⟩, fun hlt => hA F hF hlt⟩
  exact (writerWP_mergeUp_delW key g c base hvc F hp2 (fun u => u.next < F)
    (fun _ _ hle hlt => Nat.lt_of_le_of_lt hle hlt) (mergeStepOKW_next c base F hpos hcap hsa2)
    KO BK hv hk hICEk hsa2 hcap w0 k0 fuel h merged v hQ r v' he).2 hn

/-- Root collapse's fit obligation where the next id is below F, for every state: P1. -/
theorem collFitsW_next (c : Ctx) (base : View BVal) (w0 : W) (F : Nat) :
    ∀ u x n only, u.next < F → CollGetInvF c base w0 u F →
      RangeOrder (wNode c.p base u) c.i u.top.rootKey → SegDesc c base x u →
      u.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (u.path.length - 1) only) c u
        (fun _ u' => u'.next < F → TreeOK (wNode c.p base u') c.i u'.top.rootKey → PutInvG c base u' →
          SegFits (wNode c.p base u') c.i (F - 1) u'.top.rootKey) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ u' _ hlt hT hG
  exact segFits_mono _ _ _ _ _ (segFits_next_of_putInvG c base u' hG hT) (by omega)

/-- P3: root collapse keeps `DelInvA`, with no `CollapseFitsOK`. -/
theorem writerWP_collapseRoot_delA (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w0 : W) (k0 : Key) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (v : W) (hA : DelInvA c base w0 k0 KO BK v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvA c base w0 k0 KO BK v') := by
  intro r v' he F hF hn
  have hp2 : 2 ≤ F := by unfold Params.fuel at hF; omega
  obtain ⟨⟨_, _, _, _, _, _, B, top0, hB, hbook⟩, _, _⟩ :=
    hA (max (c.p.fuel + 1) (v.next + 1)) (Nat.le_max_left _ _)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
  have hle : v.next ≤ v'.next :=
    (freshCache_collapseRoot key seg c.p.fuel c v hB.good.ids hbook.fresh r v' he).2
  obtain ⟨⟨hP, _, hR, hICE, hFv, hread, _⟩, hbk, hik⟩ := hA F hF (Nat.lt_of_le_of_lt hle hn)
  have hCI : CollInvW c base v F (fun u => u.next < F) B top0 KO BK v := by
    refine ⟨hbook.fresh, fun _ => ⟨⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hFv, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩,
      hR, hbook, hbk, hik⟩⟩
  obtain ⟨⟨⟨hT', hu', _, hICE'⟩, hread', hF', _, _⟩, hR', hbook', hbk', hik'⟩ :=
    (writerWP_collapseRoot_collW F hp2 key seg c base hvc v B top0 hB KO BK hv hk hICEk hsa2
      (fun u => u.next < F) (fun _ _ hle hlt => Nat.lt_of_le_of_lt hle hlt) (collFitsW_next c base v F)
      c.p.fuel v hCI r v' he).2 hn
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨hP', hG', hR', hICE', hF', fun key' hk' => ?_, B, top0, hB, hbook'⟩, hbk', hik'⟩
  rw [hread' key']
  exact hread key' hk'

/-- P3: `afterDelete` keeps `DelInvA`, with no `MergeStepOK` and no `CollapseFitsOK`. -/
theorem writerWP_afterDelete_delA (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) (v : W)
    (hA : DelInvA c base w0 k0 KO BK v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvA c base w0 k0 KO BK v') :=
  writerWP_afterDelete_inv key g h c (DelInvA c base w0 k0 KO BK)
    (fun v hA => writerWP_mergeUp_delA key g c base hvc hpos KO BK hv hk hICEk hsa2 hcap w0 k0
      c.p.fuel h false v hA)
    (fun v hA => writerWP_collapseRoot_delA key g c base hvc w0 k0 KO BK hv hk hICEk hsa2 v hA) v hA

/-! ## P5: case 4 of the reading with no `MergeStepOK` and no `CollapseFitsOK` -/

/-- The reading's family at `DelInvA`. -/
abbrev DelStepsOKA (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  DelStepsOKG p R (fun ts tx w key v => DelInvA (ctxOf p ts) (viewOf (treeRun p ts)) w key
    (kindOracleOf p (treeRun p ts)) tx.base v)

/-- Case 4 at the reading fuel p.fuel + 1 inside the delete (`OpGetCaseOK'`), from
the family at `DelInvA`, with no `MergeStepOK` and no `CollapseFitsOK`. -/
theorem opGetCaseOK'_delMergeA (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKA p R)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    OpGetCaseOK' p R DelMergeCase := by
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
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop hmerges
    (fun v hv' => delInvA_of_delInv (ctxOf p ts) _ w key _ _ v hI hF0 hv')
    (fun v hv' hFv => delInv_of_delInvA (ctxOf p ts) _ w key _ _ v hI hF0 hv' hFv)
    (fun g h v hv' => writerWP_afterDelete_delA key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hpos
      _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delA key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hpos
      _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delA key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w key
      _ _ hv hk hICEk hsa2 v hv')

/-- Case 4 (`OpGetCaseOK`) from the family at `DelInvA`, `TxSegFitsOK` and TP4, with
no `MergeStepOK` and no `CollapseFitsOK` (`opGetCaseOK_delMergeC` without `hM`, `hC`). -/
theorem opGetCaseOK_delMergeA (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKA p R)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R DelMergeCase :=
  opGetCaseOK_of' p R DelMergeCase (opGetCaseOK'_delMergeA p R hS hsa2 hcap hMM hPtr) hfit

/-! ## The take-back's family (step 2): `DelInvJ` above the next id -/

/-- `DelInvJ` at every fuel above p.fuel and the next id (bergdb 025-05, step 2). -/
def DelInvJA (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (KO : KindOracle) (BK B : NodeId)
    (v : W) : Prop :=
  ∀ F, c.p.fuel + 1 ≤ F → v.next < F → DelInvJ c base w0 key F KO BK B v

theorem delInvJA_of_delInvJ (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (KO : KindOracle)
    (BK B : NodeId) (v : W) (hI0 : PutInv c base w0)
    (hF0 : SegFits (wNode c.p base w0) c.i (c.p.fuel - 1) w0.top.rootKey)
    (h : DelInvJ c base w0 key (c.p.fuel + 1) KO BK B v) : DelInvJA c base w0 key KO BK B v :=
  fun F hF hn => ⟨delInvA_of_delInv c base w0 key KO BK v hI0 hF0 h.1 F hF hn, h.2.1, h.2.2⟩

/-- `DelInvJA` gives the take-back's facts, which speak of no fuel. -/
theorem takeJ2_of_delInvJA (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (KO : KindOracle)
    (BK B : NodeId) (v : W) (h : DelInvJA c base w0 key KO BK B v) : TakeJ2 c base B v :=
  (h (max (c.p.fuel + 1) (v.next + 1)) (Nat.le_max_left _ _)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))).2.1

/-- The merges' loop keeps `DelInvJA`, with no fit premise. -/
theorem writerWP_mergeUp_delJA (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (B : NodeId) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvJA c base w0 k0 KO BK B v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvJA c base w0 k0 KO BK B v') := by
  intro fuel h merged v hA r v' he F hF hn
  have hp2 : 2 ≤ F := by unfold Params.fuel at hF; omega
  have hQ : DelInvJW c base w0 k0 F (fun u => u.next < F) KO BK B v :=
    ⟨(delInvW_of_delInv c base w0 k0 _ (fun u => u.next < F) KO BK v
      (hA (max (c.p.fuel + 1) (v.next + 1)) (Nat.le_max_left _ _)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))).1).1,
      fun hlt => hA F hF hlt⟩
  exact (writerWP_mergeUp_delJW key g c base hvc F hp2 (fun u => u.next < F)
    (fun _ _ hle hlt => Nat.lt_of_le_of_lt hle hlt) (mergeStepOKW_next c base F hpos hcap hsa2)
    KO BK hv hk hICEk hsa2 hcap B hpos w0 k0 fuel h merged v hQ r v' he).2 hn

/-- Root collapse keeps `DelInvJA`, with no `CollapseFitsOK`. -/
theorem writerWP_collapseRoot_delJA (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w0 : W) (k0 : Key) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (BJ : NodeId) (hpos : 0 < c.i) (v : W)
    (hA : DelInvJA c base w0 k0 KO BK BJ v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvJA c base w0 k0 KO BK BJ v') := by
  intro r v' he F hF hn
  have hp2 : 2 ≤ F := by unfold Params.fuel at hF; omega
  obtain ⟨⟨⟨_, _, _, _, _, _, B, top0, hB, hbook⟩, _, _⟩, _, _⟩ :=
    hA (max (c.p.fuel + 1) (v.next + 1)) (Nat.le_max_left _ _)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
  have hle : v.next ≤ v'.next :=
    (freshCache_collapseRoot key seg c.p.fuel c v hB.good.ids hbook.fresh r v' he).2
  obtain ⟨⟨⟨hP, _, hR, hICE, hFv, hread, _⟩, hbk, hik⟩, hJ, hBn⟩ := hA F hF (Nat.lt_of_le_of_lt hle hn)
  have hCI : CollInvJW c base v F (fun u => u.next < F) B top0 KO BK BJ v := by
    refine ⟨hbook.fresh, fun _ => ⟨⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hFv, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩,
      hR, hbook, hbk, hik, hJ, hBn⟩⟩
  obtain ⟨⟨⟨hT', hu', _, hICE'⟩, hread', hF', _, _⟩, hR', hbook', hbk', hik', hJ', hBn'⟩ :=
    (writerWP_collapseRoot_collJW F hp2 key seg c base hvc v B top0 hB KO BK hv hk hICEk hsa2
      (fun u => u.next < F) (fun _ _ hle hlt => Nat.lt_of_le_of_lt hle hlt) (collFitsW_next c base v F)
      BJ hpos (replaceRootFullJ2OKC_holds c base F hp2 BJ hpos hsa2) c.p.fuel v hCI r v' he).2 hn
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨⟨hP', hG', hR', hICE', hF', fun key' hk' => ?_, B, top0, hB, hbook'⟩, hbk', hik'⟩, hJ', hBn'⟩
  rw [hread' key']
  exact hread key' hk'

/-- `afterDelete` keeps `DelInvJA`, with no `MergeStepOK` and no `CollapseFitsOK`. -/
theorem writerWP_afterDelete_delJA (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (BJ : NodeId) (w0 : W) (k0 : Key) (v : W)
    (hA : DelInvJA c base w0 k0 KO BK BJ v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvJA c base w0 k0 KO BK BJ v') :=
  writerWP_afterDelete_inv key g h c (DelInvJA c base w0 k0 KO BK BJ)
    (fun v hA => writerWP_mergeUp_delJA key g c base hvc hpos KO BK hv hk hICEk hsa2 hcap BJ w0 k0
      c.p.fuel h false v hA)
    (fun v hA => writerWP_collapseRoot_delJA key g c base hvc w0 k0 KO BK hv hk hICEk hsa2 BJ hpos v hA)
    v hA

/-- The take-back's family at `DelInvJA`. -/
abbrev DelStepsJ2OKA (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  DelStepsJ2OKG p R S (fun ts tx w key v => DelInvJA (ctxOf p ts) (viewOf (treeRun p ts)) w key
    (kindOracleOf p (treeRun p ts)) tx.base tx.base v)

/-- (4) A delete with the merges on keeps `J2At` (`opJ2Case_delMergeRC`), from the
take-back's family at `DelInvJA`, with no `MergeStepOK` and no `CollapseFitsOK`;
S gives `PutInv` and the fit p.fuel - 1 at the delete's start. -/
theorem opJ2Case_delMergeA (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hS : DelStepsJ2OKA p R S)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpJ2CaseOK p R S DelMergeCase := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre _ hSw hJ hPc
  obtain ⟨key, hop, hmerges⟩ := hPc
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hK := hRK _ _ hr
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hRP _ _ hr) hb hi.cache hun
  refine writerWP_mono (hS ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ key hop hmerges
    (fun v hv' => delInvJA_of_delInvJ (ctxOf p ts) _ w key _ _ _ v (hSI ts tx w hSw) (hSF ts tx w hSw) hv')
    (fun v hv' => takeJ2_of_delInvJA (ctxOf p ts) _ w key _ _ _ v hv')
    (fun g h v hv' => writerWP_afterDelete_delJA key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hpos
      _ _ hv hk hICEk hsa2 hcap tx.base w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delJA key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hpos
      _ _ hv hk hICEk hsa2 hcap tx.base w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delJA key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w key
      _ _ hv hk hICEk hsa2 tx.base hpos v hv')) ?_
  intro _ w' h' _
  exact h'

/-- TP7's take-back induction with the merges on (`runTreeQ_of_mergesSC`), from the
take-back's family at `DelInvJA`, with no `MergeStepOK` and no `CollapseFitsOK`. -/
theorem runTreeQ_of_mergesSA (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
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
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (hDS : DelStepsJ2OKA p (RunTreeQ p Q) (TakeS4 p)) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases_merges4S p hM hsa hm Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q) hFS hMF
    (opJ2Case_delMergeA p _ _ hDS (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.2.1) hsa hcap
      (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

end SIS.Tree
