/-
The merges' loop for the two copies (bergdb 024-12, section 1): from a state
with the delete's loop invariant, the take-back's facts (`DelInvJ`) and the
books of the transaction's first id, `mergeUp` runs as `mergeUpChk`. The loop
is latest's `writerWP_mergeUp_delJ`, read for the two copies; at each merge
the merge runs as its checked copy (`rwpq_merge`), with the merge's end
(`MergeEnd`) from the merge's own results: `TakeJ2` (`mergeStepJ2OKF_of_root`),
the reached nodes untaken (`MergeStepOK`) and the times of the books
(`putBook_merge`, `putInvG_of_book`).
-/
import SIS.Tree.DelMergeFree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The cache of a state with the books has no id twice. -/
theorem uniqueCache_of_putBook (c : Ctx) (B : NodeId) (top0 : Top) (w : W) (h : PutBook c B top0 w) :
    UniqueCache B w := by
  refine ⟨h.fresh, ?_⟩
  have hids := h.book.ids
  have h2 : (w.nodes.map (·.1)).Nodup := by
    rw [hids]
    have hn := h.book.nodup
    unfold List.Nodup at *
    rw [List.pairwise_reverse]
    exact hn.imp (fun h1 h2 => h1 h2.symm)
  exact h2

/-- `pathNode d` for the two copies: it reads the path of the state. -/
theorem rwp_pathNode {β : Type} {k1 k2 : NodeId → M β} (d : Nat) (c : Ctx) (v : W)
    (h : ∀ e, v.path[d]? = some e → RWP (k1 e.2) (k2 e.2) c v) :
    RWP (pathNode d >>= k1) (pathNode d >>= k2) c v := by
  cases hex : v.path[d]? with
  | none =>
    refine rwp_bind (fun _ _ => False) ?_ (fun _ _ hf => hf.elim)
    unfold pathNode
    simp only [writerWP_bind, writerWP_get]
    rw [hex]
    exact writerWP_throw _ _ _ _
  | some e =>
    refine rwp_bind (fun r v' => r = e.2 ∧ v' = v)
      (writerWP_pathNode_known d e.2 c v (by rw [hex]; rfl) _ ⟨rfl, rfl⟩) ?_
    rintro r v' ⟨hr', hv'⟩
    subst r; subst v'
    exact h e hex

/-- `rwp_pathNode` for the runs that end in a state of C. -/
theorem rwpc_pathNode {β : Type} {k1 k2 : NodeId → M β} (d : Nat) (c : Ctx) (v : W) {C : W → Prop}
    (h : ∀ e, v.path[d]? = some e → RWPC (k1 e.2) (k2 e.2) c v C) :
    RWPC (pathNode d >>= k1) (pathNode d >>= k2) c v C := by
  cases hex : v.path[d]? with
  | none =>
    refine rwpc_bind (fun _ _ => False) ?_ (fun _ _ hf => hf.elim)
    unfold pathNode
    simp only [writerWP_bind, writerWP_get]
    rw [hex]
    exact writerWP_throw _ _ _ _
  | some e =>
    refine rwpc_bind (fun r v' => r = e.2 ∧ v' = v)
      (writerWP_pathNode_known d e.2 c v (by rw [hex]; rfl) _ ⟨rfl, rfl⟩) ?_
    rintro r v' ⟨hr', hv'⟩
    subst r; subst v'
    exact h e hex

set_option maxHeartbeats 3200000 in
/-- `rwp_mergeUp_of_J` for the runs that end in a state of C (bergdb 025-05, route P):
`DelInvJ` asked only where C holds, the fit at a merge's end by `MergeStepOKW`. -/
theorem rwp_mergeUp_of_JW (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (C : W → Prop)
    (hC : ∀ v v', v.next ≤ v'.next → C v' → C v) (hM : MergeStepOKW c base fuelR C)
    (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) (hvg : ViewGood B c) (hkv : ViewKlongsWf c.p c.view) (top0 : Top)
    (hB : PutBase c base B) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, (C v → DelInvJ c base w0 k0 fuelR KO B B v) → PutBook c B top0 v →
      RWPC (mergeUp key g fuel h merged) (mergeUpChk key g fuel h merged) c v C := by
  have hMJ := mergeStepJ2OKF_of_root c base hvc fuelR B hpos hcap hsa2
    (mergeRootJ2OKF_holds c base fuelR B hpos hcap hsa2)
  intro fuel
  induction fuel with
  | zero =>
    intro h merged v _ _
    exact fun x hx _ => ((writerWP_throw _ c v (fun _ _ => False)) x.1 x.2 hx).elim
  | succ f ih =>
    intro h merged v hD hb0
    by_cases hno : ¬ C v
    · intro x hx hCx
      exact absurd (hC v x.2 (freshCache_mergeUp key g (f + 1) h merged c v hB.good.ids hb0.fresh
        x.1 x.2 hx).2 hCx) hno
    obtain ⟨⟨hI, hbk, hik⟩, hJ0, hB0⟩ := hD (Classical.byContradiction hno)
    unfold mergeUp mergeUpChk
    refine rwpc_read ?_
    refine rwpc_bind _ (writerWP_and (writerWP_and (writerWP_and (descentOK c base fuelR w0 k0 key g h v hI)
      (kd_descendToHeight KO B key g h c v hv hk hbk hik))
      (writerWP_descendToHeight_readsU key g h c base hvc v))
      (putBook_descendToHeight key g h c base B top0 hB v hb0)) ?_
    rintro d v1 ⟨⟨⟨⟨hI1, hPF⟩, hbk1, hik1, _⟩, hr1⟩, hc1⟩
    have hJ1 : TakeJ2 c base B v1 := takeJ2_of_readsAs c base B v v1 hJ0 hr1
    have hBn1 : B ≤ v1.next := by rw [hr1.2.2.2.2]; exact hB0
    refine rwpc_ite (fun _ => rwpc_refl _ _ _ _) (fun hd0 => ?_)
    have hd : 0 < d := by
      cases d with
      | zero => simp at hd0
      | succ _ => omega
    obtain ⟨X, K, Nn, hP1⟩ := hPF
    refine rwpc_pathNode d c v1 (fun ex hex => ?_)
    refine rwpc_pathNode (d - 1) c v1 (fun eq heq => ?_)
    obtain ⟨B1, t1, hB1, hb1⟩ := hI1.2.2.2.2.2.2
    refine rwpc_bind _ (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_getNode_all eq.2 c v1 base hvc) (writerWP_getNode_cache eq.2 c v1))
      (putBook_getNode eq.2 c base B1 t1 hB1 v1 hb1))
      (kd_getNode KO B eq.2 c v1 hv hk hbk1 hik1))
      (putBook_getNode eq.2 c base B top0 hB v1 hc1)) ?_
    rintro qn v2 ⟨⟨⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hb2⟩, hbk2, hik2, _⟩, hc2⟩
    have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B1, t1, hB1, hb2⟩
    have hJ2 : TakeJ2 c base B v2 := takeJ2_of_readsAs c base B v1 v2 hJ1 hr2
    have hBn2 : B ≤ v2.next := by rw [hr2.2.2.2.2]; exact hBn1
    have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
      fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
    have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
    refine rwpc_ite (fun _ => rwpc_refl _ _ _ _) (fun hql => ?_)
    have hql' : qn.leaf = false := by simpa using hql
    refine rwpc_bind _ (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_getNode_all ex.2 c v2 base hvc) (writerWP_getNode_cache ex.2 c v2))
      (putBook_getNode ex.2 c base B1 t1 hB1 v2 hb2))
      (kd_getNode KO B ex.2 c v2 hv hk hbk2 hik2))
      (putBook_getNode ex.2 c base B top0 hB v2 hc2)) ?_
    rintro xn v3 ⟨⟨⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hb3⟩, hbk3, hik3, _⟩, hc3⟩
    have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B1, t1, hB1, hb3⟩
    have hJ3 : TakeJ2 c base B v3 := takeJ2_of_readsAs c base B v2 v3 hJ2 hr3
    have hBn3 : B ≤ v3.next := by rw [hr3.2.2.2.2]; exact hBn2
    have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
      fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
    have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
    refine rwpc_ite (fun _ => rwpc_refl _ _ _ _) (fun hcnt => ?_)
    have hcnt' : xn.cnt < c.p.mergeBelow := by simpa using hcnt
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
    have hmg := writerWP_merge_get_inv fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1
      X K Nn hP3 hd hxX (by rw [hqn]; exact hql') hsa2 hcap
    have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn X K Nn hI3 hP3 hd (by rw [hp3, hp2, hex]; rfl)
      (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
    have htr := writerWP_merge_tree_inv2 ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
      hd hxX (by rw [hqn]; exact hql') hsa2 hcap
    have hrg := writerWP_merge_range_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
      hd hxX (by rw [hqn]; exact hql') hsa2 hcap
    have hkd := kd_merge KO B ex.2 d c v3 hv hk hbk3 hik3 (by omega) ex.1
      (by rw [hp3, hp2, hex]) (by
        intro a q' hq'
        rw [hp3, hp2, heq] at hq'
        simp only [Option.some.injEq] at hq'
        subst hq'
        exact ⟨qn, hkeep3 _ _ hl2, hql'⟩)
    have hmj := hMJ w0 k0 ex.2 eq.2 d v3 qn xn X K Nn ⟨hI3, hJ3, hBn3⟩ hd
      (by rw [hp3, hp2, hex]; rfl) (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
      hP3 hxX
    have hall := writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_and (writerWP_and hmg hms) (putBook_merge ex.2 d c base B1 t1 hB1 v3 hb3)) htr) hrg) hkd)
      hmj) (writerWP_merge_next ex.2 d c v3)) (putBook_merge ex.2 d c base B top0 hB v3 hc3)
    have hEnd : WriterWP (merge ex.2 d) c v3 (fun _ v4 => MergeEnd c base B v4) := by
      refine writerWP_mono hall ?_
      rintro r v4 ⟨⟨⟨⟨⟨⟨⟨⟨_, hu4, _⟩, _⟩, _⟩, _⟩, _⟩, hJ4⟩, _⟩, hc4⟩
      exact ⟨hJ4.1, hJ4.2.2.1, (putInvG_of_book c base B top0 v4 hB hc4).times,
        fun y hy => hu4 y (tReach_reachS _ _ _ _ hy)⟩
    refine rwpc_bind2 _ (rwp_of_rwpq (rwpq_merge c base hvc B hvg hkv hv v3 hI3.1 hJ3 hc3.good
      (uniqueCache_of_putBook c B top0 v3 hc3) hc3.klongs ex.2 d hd X K Nn hP3 hxX) hEnd) hall ?_
    rintro r v4 ⟨⟨⟨⟨⟨⟨⟨⟨hread4, hu4, hF4⟩, hb4⟩, hT4⟩, hR4⟩, hbk4, hik4, _, _⟩, hJ4⟩, hn4⟩, hc4⟩
    obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B1 t1 hB1 hb4 hT4 hu4 hR4
    have hICE4 := hICEk v4 hbk4 hik4 (fun y hy => hu4 y (tReach_reachS _ _ _ _ hy))
    refine rwpc_ite (fun _ => rwpc_refl _ _ _ _) (fun _ => ?_)
    refine ih (h + 1) true v4 (fun hC4 => ?_) hc4
    have hF4' := hF4 hC4 hP4
    exact ⟨⟨⟨hP4, hG4, hR4, hICE4, hF4', fun key' hk' => by
      rw [hread4 hF4' key']; exact hI3.2.2.2.2.2.1 key' hk', B1, t1, hB1, hb4⟩, hbk4, hik4⟩,
      hJ4, Nat.le_trans hBn3 hn4⟩

/-- The merges' loop runs as its checked copy from `DelInvJ` and the books of
the first id B (`writerWP_mergeUp_delJ` for the two copies, `rwpq_merge` at
each merge). -/
theorem rwp_mergeUp_of_J (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) (hvg : ViewGood B c) (hkv : ViewKlongsWf c.p c.view) (top0 : Top)
    (hB : PutBase c base B) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvJ c base w0 k0 fuelR KO B B v → PutBook c B top0 v →
      RWP (mergeUp key g fuel h merged) (mergeUpChk key g fuel h merged) c v :=
  fun fuel h merged v hJ hb => rwp_of_rwpc (rwp_mergeUp_of_JW key g c base hvc fuelR hfR (fun _ => True)
    (fun _ _ _ _ => trivial) (mergeStepOKW_of c base fuelR _ hM) KO B hv hk hICEk hsa2 hcap hpos hvg hkv
    top0 hB w0 k0 fuel h merged v (fun _ => hJ) hb) (fun _ => trivial)
/-! ## The heights through a merge of the loop -/

/-- A program that runs as one that keeps P keeps P. -/
theorem writerWP_of_rwp {α : Type} {f g : M α} {c : Ctx} {w : W} {P : α → W → Prop}
    (h : RWP f g c w) (hg : WriterWP g c w P) : WriterWP f c w P :=
  fun a w' hf => hg a w' (h (a, w') hf)

/-- A merge of the merges' loop runs as its checked copy: from `DelInvJF` and the
books of the first id B, with the path down to the merged node, the merge's end
is `MergeEnd` (`mergeStepOK_untaken`, `mergeStepJ2OKF_of_root`, `putBook_merge`),
so `rwpq_merge` applies. -/
theorem rwp_merge_of_J (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (f : Nat)
    (hcap : 1 ≤ c.p.mergeMax) (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hIJ : DelInvJF c base w0 key f B v) (hb : PutBook c B top0 v) (hd : 0 < d)
    (hx : (v.path[d]?).map (·.2) = some x) (hq : (v.path[d - 1]?).map (·.2) = some q)
    (hqn : v.nodes.lookup q = some qn) (hql : qn.leaf = false) (hxn : v.nodes.lookup x = some xn)
    (hcnt : xn.cnt < c.p.mergeBelow) (hP : PathOK c v d X K Nn) (hXd : X d = x) :
    RWP (merge x d) (mergeChk x d) c v := by
  have hpos : 0 < c.i := hB.good.pos
  have hMJ := mergeStepJ2OKF_of_root c base hvc f B hpos hcap hsa2
    (mergeRootJ2OKF_holds c base f B hpos hcap hsa2)
  have hEnd : WriterWP (merge x d) c v (fun _ v4 => MergeEnd c base B v4) := by
    refine writerWP_mono (writerWP_and (writerWP_and
      (mergeStepOK_untaken c base f hpos hcap hsa2 w0 key x q d v qn xn X K Nn hIJ.1 hP hd hx hq hqn hql hxn
        hcnt)
      (hMJ w0 key x q d v qn xn X K Nn hIJ hd hx hq hqn hql hxn hcnt hP hXd))
      (putBook_merge x d c base B top0 hB v hb)) ?_
    rintro _ v4 ⟨⟨hu4, hJ4⟩, hc4⟩
    exact ⟨hJ4.1, hJ4.2.2.1, (putInvG_of_book c base B top0 v4 hB hc4).times,
      fun y hy => hu4 y (tReach_reachS _ _ _ _ hy)⟩
  exact rwp_of_rwpq (rwpq_merge c base hvc B hB.good hB.wf hB.good.ids v hIJ.1.1 hIJ.2.1 hb.good
    (uniqueCache_of_putBook c B top0 v hb) hb.klongs x d hd X K Nn hP hXd) hEnd

/-- The heights through a merge of the merges' loop with no holder premise:
the merge runs as its checked copy (`rwp_merge_of_J`), whose heights' walk is
`ht_mergeChk`. -/
theorem ht_merge_of_J {H : NodeId → Nat → Prop} (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (f : Nat) (hcap : 1 ≤ c.p.mergeMax) (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (BH : NodeId) (hvo : ViewHtOK H BH c)
    (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode)
    (hbh : Book BH c v) (hi : HtInv H BH c v)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hIJ : DelInvJF c base w0 key f B v) (hb : PutBook c B top0 v) (hd : 0 < d)
    (hx : (v.path[d]?).map (·.2) = some x) (hq : (v.path[d - 1]?).map (·.2) = some q)
    (hqn : v.nodes.lookup q = some qn) (hql : qn.leaf = false) (hxn : v.nodes.lookup x = some xn)
    (hcnt : xn.cnt < c.p.mergeBelow) (hP : PathOK c v d X K Nn) (hXd : X d = x)
    (ax : Option Nat) (hpx : v.path[d]? = some (ax, x)) (hpf : PathFreeTo v (d + 1)) :
    WriterWP (merge x d) c v (fun _ v' => Book BH c v' ∧ HtInv H BH c v' ∧ Kept v v' ∧ v'.path = v.path) := by
  refine writerWP_of_rwp (rwp_merge_of_J c base hvc f hcap hsa2 B top0 hB w0 key x q d v qn xn X K Nn hIJ hb
    hd hx hq hqn hql hxn hcnt hP hXd) ?_
  refine ht_mergeChk BH x d c v hvo hB.good.pos hbh hi (by omega) ax hpx hpf ?_
  intro a q' hq'
  have : q' = q := by
    rw [hq'] at hq
    exact Option.some.inj hq
  subst this
  exact ⟨qn, hqn, hql⟩

/-! ## The delete with the merges' loop at each call of `afterDelete` -/

/-- `afterDelete` runs as its copy that checks the merges' loop only, at a
state where the merges' loop runs as its checked copy. -/
theorem rwp_afterDelete_T (key : Key) (g h : Nat) (c : Ctx) (v : W)
    (hmu : RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v) :
    RWP (afterDelete key g h) (afterDeleteJ (fun _ => True) key g h) c v := by
  intro x hx
  unfold afterDeleteJ
  refine (m_bind_ok _ _ c v x).mpr ⟨c, v, rfl, (m_bind_ok _ _ c v x).mpr ⟨v, v, rfl, ?_⟩⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨trivial, hmu⟩)]
  exact hx

theorem rwp_trans {α : Type} {f g k : M α} {c : Ctx} {w : W} (h1 : RWP f g c w) (h2 : RWP g k c w) :
    RWP f k c w := fun x hx => h2 x (h1 x hx)

theorem deleteUpward_eqP (leaf : NodeId) (depth cv : Nat) (key : Key) :
    deleteUpward leaf depth cv key = deleteUpwardP afterDelete leaf depth cv key := rfl

theorem putSegs_none_eqP (key : Key) :
    ∀ (segs : List Nat) (r : NodeId), putSegs key none segs r = putSegsDP afterDelete key segs r := by
  intro segs
  induction segs with
  | nil => intro r; rfl
  | cons cv rest ih =>
    intro r
    cases rest with
    | nil => rfl
    | cons d rest' =>
      unfold putSegs putSegsDP
      simp only [ih]
      rfl

/-- The delete is `putKvDP afterDelete`. -/
theorem putKv_del_eqP (key : Key) : putKv (.del key) = putKvDP afterDelete key := by
  unfold putKv putKvDP
  simp only [putSegs_none_eqP]

set_option maxHeartbeats 3200000 in
/-- `OpDelChk8OKR` given that the merges' loop runs as its checked copy from the states
with `DelInvJ` and the books (`hMC`; bergdb 025-05): at each call of
`afterDelete`, the state has `DelHoleJ` (the leaf's call as in
`opDelChk6OKR_of_chk7`, the upward delete's call as in `opDelChk7OKR_of_chk8`),
where the merges' loop runs as its checked copy. -/
theorem opDelChk8OKR_of_mergeChk (p : Params) (R : Struct BVal → Time → Prop) (hM4 : 4 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hm : p.merges = true)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (htb : TakeBelowFuelDelOK p)
    (hMC : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ (top : Top) (w : W),
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
      ∀ (k : Key) (g h : Nat) (v' : W),
      DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w k (p.fuel + 1) (kindOracleOf p (treeRun p ts))
        tx.base tx.base v' → PutBook (ctxOf p ts) tx.base top v' →
      RWP (mergeUp k g (ctxOf p ts).p.fuel h false) (mergeUpChk k g (ctxOf p ts).p.fuel h false)
        (ctxOf p ts) v') : OpDelChk8OKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hLC hH hJ r' v he
  have hM : 2 ≤ p.M := by omega
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
  have hHS := htStart_of_ht p R hRL hRK hRH htb ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre hH
  have hF := segFits_of_htStart p ts tx w hHS
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := hHS
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post) hs r w
    hpre (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hSV := leafVals_reached p hM ts tx hw top pre (Op.del key :: post) hs r w hpre (hRP _ _ hr) (hRK _ _ hr)
  have hkey' : keyWf key = true := within_op_keyWf p ts tx hw pre _ post hs
  have hJw : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w := hJ
  have hSB : tx.base ≤ w.next := hb0.next
  have hMF := stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hC := upCascJ2OKHGJ_of_noU (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
    tx.base (htOracleOf p (treeRun p ts)) rfl (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))
  have hmu : ∀ (k : Key) (g h : Nat) (v' : W),
      DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w k (p.fuel + 1) (kindOracleOf p (treeRun p ts))
        tx.base tx.base v' → PutBook (ctxOf p ts) tx.base top v' →
      RWP (afterDelete k g h) (afterDeleteJ (fun _ => True) k g h) (ctxOf p ts) v' :=
    fun k g h v' hJv hbv => rwp_afterDelete_T k g h _ v' (hMC ts tx hw hr top w hI hF k g h v' hJv hbv)
  rw [putKv_del_eqP, putKvDP_eqG, deleteUpwardP_eq2] at he
  unfold putKvDelChk8
  rw [putKvDP_eqG, deleteUpwardP_eq2]
  refine rwp_putKvG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w hI
    (fun v => KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)) v ∧
      v.madeFor = w.madeFor)
    (fun s f x v hJ' hx => writerWP_mono (writerWP_and
      (kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ'.1 hx)
      (writerWP_descendLte_madeFor s _ f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ'.2⟩))
    (fun s fd L n v hJ' hL hlk hleaf hfd =>
      ⟨kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ'.1 hL hlk hleaf hfd, hJ'.2⟩)
    ⟨kdhtJ_start _ top hB _ tx.base hv hvo w ⟨hbook, hb0, hi0⟩ hhi hwfw hub, rfl⟩ _ _ key ?_ _ he
  intro pre' cv rk L n P w3 hkey hrk hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  subst hkey
  refine rwp_trans (rwp_deleteUpwardP2_keeps afterDelete (afterDeleteJ (fun _ => True)) afterDelete (ctxOf p ts)
    L n P.length cv _ w3 hlk3 (DelHoleJ p ts tx top w (pre' ++ [cv])) ?_
    (fun g h v' hQ => hmu _ g h v' hQ.1 hQ.2)) ?_
  · have hJ3k := hJ3.1
    intro hne hkeep
    have hLV := leafVals_all hSV hkey' hrk
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre' cv _ rk hrk _ hL)
    have hJ23 : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJw hr03
    by_cases hroom : DelRoom (ctxOf p ts) cv n
    · obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
      refine writerWP_mono (writerWP_and (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3k.1.1))
        (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3k.1.2.1 hJ3k.1.2.2 a hpx)) ?_
      rintro _ v ⟨⟨⟨h1, h2, h3, _, h5, _, h7⟩, hbv⟩, hkv⟩
      refine ⟨⟨⟨delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v pre' cv rk L n hI hRO hICE hF
        hkey' hrk hL hn hnl hr03 hLt h1 h2 h3 h7 hbv, hkv.1, hkv.2.1⟩, ?_, ?_⟩, hbv⟩
      · exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base w3 v cv L n hpos hJ23 hlk3
          (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
          (by rw [hr03.1, hr03.2.1]; exact keyLeaf_reached hI hrk L hL)
          (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
          (fun y hy => by rw [hr03.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
      · rw [h5, hr03.2.2.2.2]; exact hSB
    · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
      have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
        (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
        (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
        (by rw [hr03.1, hr03.2.1]; exact hRO) hJ23 (by rw [hr03.2.2.2.2]; exact hSB) hsa2
        P.length _ _ _ hPOK cv n
        (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
        hnl hne hroom (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
      simp only [hXD] at hJ2
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_appendDeleteKlong_full_delH (ctxOf p ts) _
        (viewCoherent_ctxOf p ts) _ tx.base (delFullRootStepOK_ctx p ts) _
        (delFullFitsOKR_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr))
        hsa2 hv hk hICEk w pre' cv rk tx.base top hB hI hRO hF
        hkey' hrk L n P w3 hL hn hnl hne hroom hr03 hJ3k.1 hJ3k.2 hp3' hlinkP hXD hlkX) hJ2)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3k.1.1)) ?_
      rintro _ v ⟨⟨hv', hj⟩, hbv⟩
      exact ⟨⟨hv', hj.1, hj.2⟩, hbv⟩
  · by_cases hnc : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap ∨
        n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false
    · exact rwp_deleteUpwardP2_noClimb _ _ _ _ L n _ cv _ w3 hlk3 hnc
    have hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap := fun h => hnc (Or.inl h)
    have hall : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true := by
      cases h : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) with
      | true => rfl
      | false => exact absurd (Or.inr h) hnc
    by_cases hLr : L = w.top.rootKey
    · have hP0 := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
      subst hP0
      exact rwp_deleteUpwardP2_root _ _ _ _ L n cv _ w3 hlk3 (by rw [hp3', ← hXD]; rfl)
    have hLV := leafVals_all hSV hkey' hrk
    exact rwp_climb_of_J _ _ _ (ctxOf p ts) _ pre' cv rk w tx.base top hB _ tx.base hv hk
      hI hRO hF hICE hkey' hrk _ hC hLC hsa2 hICEk hm hpos hJw hMF
      (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1)
      (fun g h v hJv hbv => hmu _ g h v hJv hbv)
      L n P w3 hL hn hnl hr03 hJ3 hp3' hlinkP hXD hlkX hne hall hLr

/-- `OpDelChk8OKR` holds: at the deletes of the runs of R, at each call of
`afterDelete`, the state has `DelHoleJ` (the leaf's call as in
`opDelChk6OKR_of_chk7`, the upward delete's call as in `opDelChk7OKR_of_chk8`),
where the merges' loop runs as its checked copy (`rwp_mergeUp_of_J`). -/
theorem opDelChk8OKR_holds (p : Params) (R : Struct BVal → Time → Prop) (hM4 : 4 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hm : p.merges = true)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (htb : TakeBelowFuelDelOK p)
    (hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) : OpDelChk8OKR p R := by
  refine opDelChk8OKR_of_mergeChk p R hM4 hsa2 hm hRL hRP hRK hRH htb ?_
  intro ts tx hw hr top w _ _ k g h v' hJv hbv
  have hM : 2 ≤ p.M := by omega
  have hfR : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) (hRK _ _ hr)
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  exact rwp_mergeUp_of_J k g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (p.fuel + 1) hfR (hMS ts) _ tx.base hv hk
    hICEk (by simpa [ctxOf] using hsa2) (by simpa [ctxOf] using hcap) (by simp [ctxOf]) hB.good hB.wf top hB w k
    _ h false v' hJv hbv
/-! ## The top theorem without `hchk` -/

/-- `invGetScanOK_merges_noU` without `hchk5`: every check of the checked
delete holds (`opDelChk8OKR_holds`, then `opDelChk7OKR_of_chk8`,
`opDelChk6OKR_of_chk7`, `opDelChk5OKR_of_chk6`). -/
theorem invGetScanOK_merges_free (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM4 := four_le_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => mergeStepOK_of_segFits (ctxOf p ts) _ _ (Nat.succ_pos _) hcap hsa (hMSF ts)
  exact invGetScanOK_merges_noU p hp hth
    (opDelChk5OKR_of_chk6 p _ (by omega) hsa hcap (fun _ _ h => h.1) (fun _ _ h => h.1.1)
      (fun _ _ h => h.2.2.1.2.2.1) hMS hCoF
      (opDelChk6OKR_of_chk7 p _ (by omega) hsa (fun _ _ h => h.1) (fun _ _ h => h.1.1)
        (fun _ _ h => h.2.2.1.2.2.1) (fun _ _ h => h.2.2.1.2.2.2.1) htb
        (opDelChk7OKR_of_chk8 p _ hM4 hsa hm (fun _ _ h => h.1) (fun _ _ h => h.1.1)
          (fun _ _ h => h.2.2.1.2.2.1) (fun _ _ h => h.2.2.1.2.2.2.1) htb
          (opDelChk8OKR_holds p _ hM4 hsa hcap hm (fun _ _ h => h.1) (fun _ _ h => h.1.1)
            (fun _ _ h => h.2.2.1.2.2.1) (fun _ _ h => h.2.2.1.2.2.2.1) htb hMS))))
    htb d4 l4 hMSF hCoF

end SIS.Tree
