/-
`htb`'s sites (bergdb 025-05, step 8): the merges' loop keeps the tall nodes' frame. Its
k-th iteration merges the node of height k on the key's path, k below the fuel (the
loop throws when its counter runs out); the parent, one height up, is a tall node only
at the last iteration, and the parent's live children, at height k, are none.
-/
import SIS.Tree.HtbWalk
import SIS.Tree.HtbPrefix

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `ghOf` reads the entry it returns. -/
theorem writerWP_ghOf_mem (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (ghOf x) c w (fun r v => v.path = w.path ∧ (x, r.1, r.2) ∈ v.gh) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_cache x c w) ?_
  rintro _ v ⟨-, -, hp⟩
  simp only [writerWP_get]
  split
  · rename_i r hr
    rw [writerWP_pure]
    exact ⟨hp, bk_mem_of_lookup _ _ _ hr⟩
  · exact writerWP_throw _ _ _ _

/-- The merge's descent ends at a node of the height it looks for. -/
theorem writerWP_descendHeight_last (cv h : Nat) :
    ∀ (fuel : Nat) (x : NodeId) (c : Ctx) (w : W), HtPathLast w x →
      WriterWP (descendHeight cv h fuel x) c w (fun _ v => ∃ y g, HtPathLast v y ∧ (y, g, h) ∈ v.gh) := by
  intro fuel
  induction fuel with
  | zero => intro x c w _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hx
    unfold descendHeight
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_ghOf_mem x c w) ?_
    rintro ⟨gx, hx'⟩ v ⟨hp, hm⟩
    simp only
    split
    · rename_i heq
      rw [writerWP_pure]
      have : hx' = h := by simpa using heq
      subst this
      obtain ⟨a, ha⟩ := hx
      exact ⟨x, gx, ⟨a, by rw [hp]; exact ha⟩, hm⟩
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_getNode_cache x c v) ?_
      rintro n u ⟨-, -, hpu⟩
      split
      · exact writerWP_throw _ _ _ _
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd _
          simp only [writerWP_bind]
          unfold pathAdd
          simp only [writerWP_modify]
          refine ih fd.y c _ ⟨some fd.c, ?_⟩
          simp

section Loop

variable {H : NodeId → Nat → Prop} {base : View BVal} {T : NodeId → Prop}

/-- The node that `descendToHeight` finds has the height it looks for. -/
theorem writerWP_descendToHeight_last (B : NodeId) (key : Key) (g h : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hkw : ViewKlongsWf c.p c.view) (hwf : WriterKlongsWf w) :
    WriterWP (descendToHeight key g h) c w (fun d v => ∃ a y g', v.path[d]? = some (a, y) ∧
      (y, g', h) ∈ v.gh) := by
  unfold descendToHeight
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (ht_descendToSegmentRoot B key g c w hvo hb hi hkw hwf) ?_
  rintro root w1 ⟨-, -, -, hl1, -⟩
  split
  · exact writerWP_throw _ _ _ _
  · rename_i cv _
    rw [writerWP_bind]
    refine writerWP_mono (writerWP_descendHeight_last cv h c.p.fuel root c w1 hl1) ?_
    rintro _ w2 ⟨y, g', ⟨a, ha⟩, hm⟩
    rw [writerWP_bind]
    refine writerWP_mono (kd_pathSize c w2) ?_
    rintro sz w3 ⟨hw3, hsz⟩
    subst hw3 hsz
    rw [writerWP_pure]
    exact ⟨a, y, g', ha, hm⟩

/-- A node of height h below the fuel is no tall node, the tall nodes being nodes of
`gh` at the start with a height at or above the fuel. -/
theorem not_tall_of_hasHt {B : NodeId} {c : Ctx} {w0 v : W} (hb : Book B c v)
    (hvh : ViewHeights H B c) (hk : Kept w0 v)
    (hTdef : ∀ y, T y → ∃ g hy, (y, g, hy) ∈ w0.gh ∧ c.p.fuel ≤ hy)
    {y : NodeId} {h : Nat} (hy : HasHt H v y h) (hlt : h < c.p.fuel) : ¬ T y := by
  intro hT
  obtain ⟨g, hy', hm, hle⟩ := hTdef y hT
  have := hasHt_tag hb hvh (hk.2 _ hm) hy
  omega

theorem kd_checkFree (K : KindOracle) (B : NodeId) (o : NodeId) : KdKeepsP K B (checkFree o) := by
  intro c w hv hk hb hi
  exact writerWP_mono (writerWP_checkFree o c w) (fun _ v h => by
    rw [h.1]; exact ⟨hb, hi, KdLe.refl w, rfl⟩)

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 20000 in
/-- `kd_merge` for the merge with the checks. -/
theorem kd_mergeChk (K : KindOracle) (B : NodeId) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KdInv K B w)
    (hd : d ≠ 0) (ax : Option Nat) (hpx : w.path[d]? = some (ax, x))
    (hpq : ∀ a q, w.path[d - 1]? = some (a, q) →
      ∃ nq, w.nodes.lookup q = some nq ∧ nq.leaf = false) :
    WriterWP (mergeChk x d) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold mergeChk mergeTailChk
  kdSimp
  refine writerWP_mono (kd_pathNode (e + 1 - 1) c w) ?_
  rintro p w0 ⟨hw0, ap, hpp⟩
  rw [hw0]
  clear hw0
  simp only [Nat.add_sub_cancel] at hpp hpq
  obtain ⟨nq, hnq, hnql⟩ := hpq ap p hpp
  have hpg : p ∈ w.gh.map (·.1) := hi.pathGh e ap p hpp (List.getElem?_eq_some_iff.mp hpx).1
  obtain ⟨⟨p', gp, hp⟩, hpt, hpe⟩ := List.mem_map.mp hpg
  simp only at hpe
  subst hpe
  have hh : hp ≠ 0 := by
    intro h0; subst h0
    have := kd_leaf hb hnq hpt
    rw [hnql] at this; simp at this
  obtain ⟨k, hak⟩ : ∃ k, ax = some k := by
    cases ax with
    | none => exact absurd rfl (hi.pathSome e none x hpx)
    | some k => exact ⟨k, rfl⟩
  subst hak
  have hxs : IsKeySeg K w x gp := (hi.path e ap p' k x hpp hpx gp hp hpt).1 hh
  refine writerWP_mono (kd_getNode K B p' c w hv hk hb hi) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hpt1 := KdLe.gh' hpt hle1
  refine writerWP_mono (kd_getNode K B x c w1 hv hk hb1 hi1) ?_
  rintro xn w2 ⟨hb2, hi2, hle2, hl2, hp2, -⟩
  obtain ⟨gx, hx, hxt⟩ := kd_tag_of_lookup hb2 hl2
  have := kd_seg_unique hb2 hk hxt (hxs.kdMono (hle1.trans hle2))
  subst this
  have hxl : xn.leaf = (hx == 0) := kd_leaf hb2 hl2 hxt
  have hpp2 : w.path[e]? = some (ap, p') := hpp
  clear hpq hnq hnql hpx hxs
  repeat' first
    | kdSimp
    | simp only [List.forIn_cons, List.forIn_nil]
    | kdSibM hl1 hpt1 hh hxl
    | kdGhX hxt
    | kdCreateM
    | kdMPm hpp2 hpt hh
    | kdRet
    | kdTake
    | kdUseP (kd_unlink _ _ _)
    | ((with_unfolding_none guard_target = WriterWP (checkFree _) _ _ _)
       kdUseP (kd_checkFree _ _ _))
    | kdCore
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 6400000 in
/-- The merges' loop keeps the walk and the frame; at its last iteration, a merge whose
parent is tall ends in E, if it is a merge into two (`hexc`; after a merge into one the
loop throws). -/
theorem tk_mergeUpChk (B : NodeId) (key : Key) (g : Nat) (c : Ctx) (hvo : ViewHtOK H B c)
    (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (K : KindOracle) (hvB : ViewIdsBelow B c.view) (hkK : ViewKinds K B c)
    (w0 : W) (hTdef : ∀ y, T y → ∃ g hy, (y, g, hy) ∈ w0.gh ∧ c.p.fuel ≤ hy)
    (E : W → Prop)
    (hexc : ∀ x d v, Book B c v → HtInv H B c v → WriterKlongsWf v → Kept w0 v → TallOK base T c v →
      KdInv K B v → d ≠ 0 → (∃ a, v.path[d]? = some (a, x)) → d + 1 = v.path.length →
      PathFreeTo v v.path.length →
      (∀ a q, v.path[d - 1]? = some (a, q) → v.taken.contains q = false ∧ T q ∧
        ∀ qn, wNode c.p base v q = some qn → ∀ cv y, (cv, y) ∈ qn.live → ¬ T y) →
      WriterWP (mergeChk x d) c v (fun r v' => r = 2 → E v')) :
    ∀ (fuel h : Nat) (merged : Bool) (v : W), h + fuel = c.p.fuel → Book B c v → HtInv H B c v →
      WriterKlongsWf v → Kept w0 v → TallOK base T c v → KdInv K B v →
      WriterWP (mergeUpChk key g fuel h merged) c v (fun _ v' => Book B c v' ∧ HtInv H B c v' ∧
        Kept v v' ∧ WriterKlongsWf v' ∧ (TallOK base T c v' ∨ E v')) := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _ _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v hfuel hb hi hwf hk0 hT hki
    unfold mergeUpChk
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (ht_descendToHeight B key g h c v hvo hb hi hkw hwf)
      (klongsWf_descendToHeight key g h c v hkw hwf))
      (writerWP_descendToHeight_last B key g h c v hvo hb hi hkw hwf))
      (writerWP_descendToHeight_readsU key g h c base hvc v))
      (kd_descendToHeight K B key g h c v hvB hkK hb hki)) ?_
    rintro d w1 ⟨⟨⟨⟨⟨hb1, hi1, hle1, hpf1, hd1⟩, hwf1⟩, ax0, x0, gx, hx0, hmx⟩, hr1⟩, -, hki1, -⟩
    have hT1 := hT.of_reads hr1
    split
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1.1, hwf1, Or.inl hT1⟩
    · rename_i hd0
      have hd : d ≠ 0 := by intro h0; subst h0; exact hd0 rfl
      simp only [writerWP_bind]
      refine writerWP_mono (kd_pathNode d c w1) ?_
      rintro x w2 ⟨hw, ax, hpx⟩
      rw [hw]
      rw [hx0] at hpx
      simp only [Option.some.injEq, Prod.mk.injEq] at hpx
      obtain ⟨rfl, rfl⟩ := hpx
      refine writerWP_mono (kd_pathNode (d - 1) c w1) ?_
      rintro q w3 ⟨hw3, aq, hpq⟩
      rw [hw3]
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (hw_getNode B q c w1 hvo hb1 hi1)
        (klongsWf_getNode q c w1 hkw hwf1)) (tk_getNodeI q c w1 hvc hT1))
        (kd_getNode K B q c w1 hvB hkK hb1 hki1)) ?_
      rintro nq w4 ⟨⟨⟨⟨hb4, hi4, hle4, hl4, hp4⟩, hwf4, -⟩, hT4, hwq4, hta4, -, -, hwn4⟩, -, hki4, -⟩
      split
      · rw [writerWP_pure]; exact ⟨hb4, hi4, (hle1.trans hle4).1, hwf4, Or.inl hT4⟩
      · rename_i hql
        have hql' : nq.leaf = false := by simpa using hql
        simp only [writerWP_bind]
        refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (hw_getNode B x0 c w4 hvo hb4 hi4)
          (klongsWf_getNode x0 c w4 hkw hwf4)) (tk_getNodeI x0 c w4 hvc hT4))
          (kd_getNode K B x0 c w4 hvB hkK hb4 hki4)) ?_
        rintro nx w5 ⟨⟨⟨⟨hb5, hi5, hle5, hl5, hp5⟩, hwf5, -⟩, hT5, -, hta5, -, -, hwn5⟩, -, hki5, -⟩
        split
        · rw [writerWP_pure]; exact ⟨hb5, hi5, (hle1.trans (hle4.trans hle5)).1, hwf5, Or.inl hT5⟩
        · simp only [writerWP_bind]
          have hpw : w5.path = w1.path := hp5.trans hp4
          have hlen : d + 1 = w1.path.length := by
            have := (List.getElem?_eq_some_iff.mp hx0).1; omega
          -- the heights of q and x
          have hqg : q ∈ w1.gh.map (·.1) := hi1.pathGh (d - 1) aq q hpq (by omega)
          obtain ⟨⟨q', gq, hq⟩, hqm, hqe⟩ := List.mem_map.mp hqg
          simp only at hqe
          subst hqe
          have hqf : w1.taken.contains q' = false := hpf1 (d - 1) aq q' (by omega) hpq
          have hq0 : hq ≠ 0 := by
            intro h0; subst h0
            have := kd_leaf hb4 hl4 (HtLe.gh' hqm hle4)
            rw [hql'] at this; simp at this
          obtain ⟨k, hak⟩ : ∃ k, ax0 = some k := by
            cases ax0 with
            | none => exact absurd rfl (hi1.pathSome (d - 1) none x0 (by rw [show d - 1 + 1 = d by omega]; exact hx0))
            | some k => exact ⟨k, rfl⟩
          have hxh : HasHt H w1 x0 (hq - 1) :=
            hi1.path (d - 1) aq q' k x0 hpq (by rw [show d - 1 + 1 = d by omega, hx0, hak]) gq hq hqm hqf hq0
          have hhq : h = hq - 1 := hasHt_tag hb1 hvo.heights hmx hxh
          have hNq : NodeHt c H w4 hq nq := ht_cache_at hl4 hi4 (HtLe.gh' hqm hle4)
            (by rw [hle4.2]; exact hqf) (HtLe.refl _)
          have hk04 : Kept w0 w4 := hk0.trans (hle1.trans hle4).1
          have hchild : ∀ qn, wNode c.p base w5 q' = some qn → ∀ cv y, (cv, y) ∈ qn.live → ¬ T y := by
            intro qn hqn cv y hy
            have hqf5 : w5.taken.contains q' = false := by rw [hle5.2, hle4.2]; exact hqf
            have e1 : wNode c.p base w5 q' = some nq := by
              rw [hwn5]; exact hwq4 (by rw [← hle5.2]; exact hqf5)
            rw [e1] at hqn
            cases hqn
            have hy' := (hNq.1 cv y hy).2 hq0
            exact not_tall_of_hasHt hb4 hvo.heights hk04 hTdef hy' (by omega)
          have hqcond : ∀ a q2, w5.path[d - 1]? = some (a, q2) → w5.taken.contains q2 = false ∧
              (T q2 → T q') ∧ (∀ qn, wNode c.p base w5 q2 = some qn → ∀ cv y, (cv, y) ∈ qn.live → ¬ T y) ∧
              q2 = q' := by
            intro a q2 hq2
            rw [hpw, hpq] at hq2
            simp only [Option.some.injEq, Prod.mk.injEq] at hq2
            obtain ⟨-, rfl⟩ := hq2
            exact ⟨by rw [hle5.2, hle4.2]; exact hqf, id, hchild, rfl⟩
          have hTq : T q' → f = 0 := by
            intro hTq'
            obtain ⟨g0, hq0', hm0, hle0⟩ := hTdef q' hTq'
            have := (kd_tag_eq hb1 hqm (hk0.trans hle1.1 |>.2 _ hm0)).2
            omega
          have hpf5 : PathFreeTo w5 (d + 1) :=
            ht_pf_le hpf1 hpw (hle4.trans hle5) (by omega)
          have hpx5 : w5.path[d]? = some (some k, x0) := by rw [hpw, hx0, hak]
          have hpq5 : ∀ a q2, w5.path[d - 1]? = some (a, q2) →
              ∃ nq, w5.nodes.lookup q2 = some nq ∧ nq.leaf = false := by
            intro a q2 hq2
            obtain ⟨-, -, -, rfl⟩ := hqcond a q2 hq2
            obtain ⟨n', hn', hl'⟩ := hle5.1.lookup hl4
            exact ⟨n', hn', by rw [hl', hql']⟩
          have hht := writerWP_and (writerWP_and (ht_mergeChk B x0 d c w5 hvo hpos hb5 hi5 hd (some k) hpx5 hpf5 hpq5)
            (klongsWf_mergeChk x0 d c w5 hkw hwf5))
            (kd_mergeChk K B x0 d c w5 hvB hkK hb5 hki5 hd (some k) hpx5 hpq5)
          have hpfAll5 : PathFreeTo w5 w5.path.length :=
            ht_pf_le hpf1 hpw (hle4.trans hle5) (by rw [hpw]; exact Nat.le_refl _)
          by_cases hTq' : T q'
          · obtain rfl := hTq hTq'
            refine writerWP_mono (writerWP_and hht (hexc x0 d w5 hb5 hi5 hwf5
              (hk04.trans hle5.1) hT5 hki5 hd ⟨_, hpx5⟩ (by rw [hpw]; exact hlen) hpfAll5 (fun a q2 hq2 => by
                obtain ⟨h1, -, h3, rfl⟩ := hqcond a q2 hq2
                exact ⟨h1, hTq', h3⟩))) ?_
            rintro r w6 ⟨⟨⟨⟨hb6, hi6, hk6, -⟩, hwf6⟩, -⟩, hE⟩
            have hk := (hle1.trans (hle4.trans hle5)).1.trans hk6
            split
            · rename_i hr2
              rw [writerWP_pure]; exact ⟨hb6, hi6, hk, hwf6, Or.inr (hE (by simpa using hr2))⟩
            · exact writerWP_throw _ _ _ _
          · refine writerWP_mono (writerWP_and hht (tk_mergeChk x0 d c w5 hmp hvc hT5 (fun a q2 hq2 => by
                obtain ⟨h1, h2, h3, rfl⟩ := hqcond a q2 hq2
                exact ⟨h1, hTq', h3⟩))) ?_
            rintro r w6 ⟨⟨⟨⟨hb6, hi6, hk6, -⟩, hwf6⟩, -, hki6, -, -⟩, hT6⟩
            have hk := (hle1.trans (hle4.trans hle5)).1.trans hk6
            split
            · rw [writerWP_pure]; exact ⟨hb6, hi6, hk, hwf6, Or.inl hT6⟩
            · exact writerWP_mono (ih (h + 1) true w6 (by omega) hb6 hi6 hwf6 (hk04.trans (hle5.1.trans hk6)) hT6 hki6)
                (fun _ u hu => ⟨hu.1, hu.2.1, hk.trans hu.2.2.1, hu.2.2.2⟩)

end Loop

open Classical in
/-- `afterDeleteChk` with a check, after the merges' loop, of Tc. -/
noncomputable def afterDeleteChkT (Tc : W → Prop) (key : Key) (g h : Nat) : M Unit := do
  let c ← read
  if c.p.merges then
    let merged ← mergeUpChk key g c.p.fuel h false
    let v' ← (MonadState.get : M W)
    if Tc v' then
      if merged then collapseRootChk key g c.p.fuel
    else throw "check: the state after the merges' loop"

open Classical in
/-- `afterDeleteChkT` with a check of J at its call. -/
noncomputable def afterDeleteH (J Tc : W → Prop) (key : Key) (g h : Nat) : M Unit := do
  let v ← (MonadState.get : M W)
  if J v then afterDeleteChkT Tc key g h
  else throw "check: the state at a call of afterDelete"

section After

variable {H : NodeId → Nat → Prop} {base : View BVal} {T : NodeId → Prop}

set_option maxHeartbeats 3200000 in
/-- `afterDeleteH` keeps the walk and the frame at a segment leaf's call, given the
last merge's case (`hexc`) and how the check after the loop restores the frame then
(`hconv`). -/
theorem tk_afterDeleteH (B : NodeId) (J Tc : W → Prop) (c : Ctx) (hvo : ViewHtOK H B c)
    (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (K : KindOracle) (hvB : ViewIdsBelow B c.view) (hkK : ViewKinds K B c)
    (hJK : ∀ v, J v → KdInv K B v)
    (w0 : W) (hTdef : ∀ y, T y → ∃ g hy, (y, g, hy) ∈ w0.gh ∧ c.p.fuel ≤ hy)
    (E : W → Prop)
    (hexc : ∀ x d v, Book B c v → HtInv H B c v → WriterKlongsWf v → Kept w0 v → TallOK base T c v →
      KdInv K B v → d ≠ 0 → (∃ a, v.path[d]? = some (a, x)) → d + 1 = v.path.length →
      PathFreeTo v v.path.length →
      (∀ a q, v.path[d - 1]? = some (a, q) → v.taken.contains q = false ∧ T q ∧
        ∀ qn, wNode c.p base v q = some qn → ∀ cv y, (cv, y) ∈ qn.live → ¬ T y) →
      WriterWP (mergeChk x d) c v (fun r v' => r = 2 → E v'))
    (hconv : ∀ v, Book B c v → HtInv H B c v → Kept w0 v → E v → Tc v → TallOK base T c v) :
    AdOK H B base T (afterDeleteH J Tc) c w0 := by
  intro key g v ⟨hb, hi, hk0, hwf, hT⟩
  unfold afterDeleteH afterDeleteChkT
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split
  · rename_i hJv
    simp only [writerWP_bind, writerWP_read]
    split
    · simp only [writerWP_bind]
      refine writerWP_mono (tk_mergeUpChk B key g c hvo hpos hkw hmp hvc K hvB hkK w0 hTdef E hexc c.p.fuel 0 false v
        (by omega) hb hi hwf hk0 hT (hJK v hJv)) ?_
      rintro merged v1 ⟨hb1, hi1, hk1, hwf1, hTE⟩
      simp only [writerWP_get]
      split
      · rename_i hTc
        have hT1 : TallOK base T c v1 := by
          rcases hTE with h1 | h1
          · exact h1
          · exact hconv v1 hb1 hi1 (hk0.trans hk1) h1 hTc
        split
        · refine writerWP_mono (writerWP_and (ht_collapseRootChk B key g c hvo hpos hkw c.p.fuel v1 hb1 hi1 hwf1)
            (tk_collapseRootChk key g c hmp hvc c.p.fuel v1 hT1)) ?_
          rintro _ v2 ⟨⟨hb2, hi2, hk2, hwf2⟩, hT2⟩
          exact ⟨hb2, hi2, hk1.trans hk2, hwf2, hT2⟩
        · rw [writerWP_pure]; exact ⟨hb1, hi1, hk1, hwf1, hT1⟩
      · exact writerWP_throw _ _ _ _
    · rw [writerWP_pure]; exact ⟨hb, hi, Kept.refl _, hwf, hT⟩
  · exact writerWP_throw _ _ _ _

end After

end SIS.Tree
