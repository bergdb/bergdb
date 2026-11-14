/-
The delete's checks without `checkPathFree` (bergdb 024-22, step 4; one check
of `OpDelChkOK` proved): after the upward delete's loop, the nodes of the key
access path at the stop node and above are not taken back. The loop takes back
nodes below the stop node only, and the path's nodes are pairwise distinct
(`ht_path_ne`, HeightsPathNodup.lean, from the kinds' walk `KdInv` beside the
heights' at the upward delete's start).

`putKvDelChk2` is `putKvDelChk` (DelChk.lean) without that check; the walk of
the heights through it (`ht_putKvDelChk2`) carries the kinds' books as far as
the upward delete. `OpDelChk2OK`, a delete runs as `putKvDelChk2`, is the named
premise with one check fewer than `OpDelChkOK`: `treeRun_heightLiveOK_chk2`,
`invPreserved_of_open_chk2`, and TP10's fuel premise with `TakeBelowFuelDelOK`
(`txSegFitsOK_of_takeBelowDelR2`, through `OpHtDelOK` versions of
HeightsFit.lean's theorems).
-/
import SIS.Tree.HeightsChkRun
import SIS.Tree.HeightsPathNodup
import SIS.Tree.DelStepsF3
import SIS.Tree.HeightsFit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The copy without the path's check -/

/-- `deleteUpwardChk` without `checkPathFree`. -/
def deleteUpwardChk2 (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let (g, h) ← ghOf leaf
    let _ ← appendDeleteKlong leaf depth cv
    afterDeleteChk key g h
    return false
  let stop ← climb depth
  if stop == depth then
    note "up.root-kept-empty"
    let _ ← appendDeleteKlong leaf depth cv
    return false
  note "up.climb"
  let path := (← (MonadState.get : M W)).path
  let _segment ← (path.take stop).foldlM (fun s (e : Option Nat × NodeId) => do
    pure (if (← getNode e.2).leaf then s + 1 else s)) 0
  for j in List.range (depth - stop) do
    let k := depth - j
    let x ← pathNode k
    let xn ← getNode x
    if xn.firstTime == some tt then takeBackChk x (← pathNode (k - 1)) (← klongAt k)
    else
      note "up.unlink"
      unlink x
  let s ← pathNode stop
  let cs ← klongAt (stop + 1)
  let sn ← getNode s
  let (gs, hs) ← ghOf s
  if !sn.leaf then throw "check: the upward delete's stop node is no segment leaf"
  note "up.stop-at-segment-leaf"
  let _ ← appendDeleteKlong s stop cs
  afterDeleteChk key gs hs
  return false

/-- `setValueDelChk` without the path's check. -/
def setValueDelChk2 (segRoot : NodeId) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← deleteUpwardChk2 leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegsDelChk` without the path's check. -/
def putSegsDelChk2 (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueDelChk2 segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsDelChk2 key rest next

/-- `putKvDelChk` without the path's check. -/
def putKvDelChk2 (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsDelChk2 key key root

/-! ## The walk -/

section Walk

variable {H : NodeId → Nat → Prop} {K : KindOracle}

/-- A loop over a list whose every step keeps I, the step's element in the
list. -/
theorem ht_forIn_inv_mem {α : Type} (c : Ctx) (f : α → PUnit → M (ForInStep PUnit))
    (I : W → Prop) (l : List α)
    (hstep : ∀ j ∈ l, ∀ v, I v → WriterWP (f j PUnit.unit) c v
      (fun r v' => r = ForInStep.yield PUnit.unit ∧ I v')) :
    ∀ (v : W), I v → WriterWP (forIn l PUnit.unit f) c v (fun _ v' => I v') := by
  induction l with
  | nil => intro v hv; simp only [List.forIn_nil, writerWP_pure]; exact hv
  | cons a l ih =>
    intro v hv
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hstep a List.mem_cons_self v hv) ?_
    rintro r v' ⟨hr, hv'⟩
    subst hr
    exact ih (fun j hj => hstep j (List.mem_cons_of_mem _ hj)) v' hv'

set_option maxHeartbeats 3200000 in
/-- The delete of compare value cv in the segment leaf, the path's check
proved: the loop takes back nodes below the stop node, which are no nodes at
the stop node or above (`ht_path_ne` at the start). -/
theorem ht_deleteUpwardChk2 (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) (c : Ctx)
    (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view)
    (hb : Book B c w) (hi : HtInv H B c w) (hwf : WriterKlongsWf w)
    (hpf : PathFreeTo w w.path.length) (hdepth : depth = w.path.length - 1)
    (hlast : HtPathLast w leaf) (n : KNode) (hn : w.nodes.lookup leaf = some n)
    (hk : ViewKinds K B c) (hki : KdInv K B w) :
    WriterWP (deleteUpwardChk2 leaf depth cv key) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
      Kept w v ∧ WriterKlongsWf v) := by
  obtain ⟨a, ha⟩ := hlast
  rw [← hdepth] at ha
  have hlen : depth + 1 = w.path.length := by
    have := (List.getElem?_eq_some_iff.mp ha).1; omega
  -- every node of the path is cached, so its nodes are distinct
  have hall : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
      q ∈ w.gh.map (·.1) := by
    intro d a' q hq
    by_cases hd : d + 1 < w.path.length
    · exact hi.pathGh d a' q hq hd
    · have hdd : d = depth := by have := (List.getElem?_eq_some_iff.mp hq).1; omega
      subst hdd
      rw [ha] at hq
      cases hq
      obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb hn
      exact List.mem_map.mpr ⟨_, hm, rfl⟩
  have hne : ∀ {j k : Nat}, j ≠ k → ∀ {a b : Option Nat} {q q' : NodeId},
      w.path[j]? = some (a, q) → w.path[k]? = some (b, q') → q ≠ q' :=
    fun hjk _ _ _ _ hq hq' => ht_path_ne hb hvo hi hk hki hpf hall hjk hq hq'
  unfold deleteUpwardChk2
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_getNode_hit leaf n c w hn) ?_
  rintro n' w' ⟨hn', hw'⟩
  subst n' w'
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · rw [writerWP_pure]; exact ⟨hb, hi, Kept.refl w, hwf⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (hw_ghOf B leaf c w hvo hb hi)
      (klongsWf_ghOf leaf c w hkw hwf)) ?_
    rintro ⟨g, h⟩ w1 ⟨⟨hb1, hi1, hle1, hp1, hm1, -⟩, hwf1⟩
    refine writerWP_mono (writerWP_and (ht_appendDeleteKlong B leaf depth cv c w1 hvo
      hpos hb1 hi1 g h hm1 a (by rw [hp1]; exact ha) (ht_pf_le hpf hp1 hle1 (by omega)))
      (klongsWf_appendDeleteKlong leaf depth cv c w1 hkw hwf1)) ?_
    rintro _ w2 ⟨⟨hb2, hi2, hle2, -⟩, hwf2⟩
    refine writerWP_mono (ht_afterDeleteChk B key g h c w2 hvo hpos hkw hb2 hi2 hwf2) ?_
    rintro _ w3 ⟨hb3, hi3, hk3, hwf3⟩
    rw [writerWP_pure]
    exact ⟨hb3, hi3, (hle1.trans hle2).1.trans hk3, hwf3⟩
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (ht_climb B depth c w hvo hb hi)
    (klongsWf_climb depth c w hkw hwf)) ?_
  rintro stop w1 ⟨⟨hb1, hi1, hle1, hp1, hstop⟩, hwf1⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hne' => ?_)
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (hw_keeps B (ht_note B _) c w1 hvo hb1 hi1)
      (klongsWf_note _ c w1 hkw hwf1)) ?_
    rintro _ w2 ⟨⟨hb2, hi2, hle2, hp2⟩, hwf2⟩
    refine writerWP_mono (writerWP_and (ht_appendDeleteKlong B leaf depth cv c w2 hvo
      hpos hb2 hi2 _ _ (HtLe.gh' (kd_tag_of_lookup hb hn).choose_spec.choose_spec (hle1.trans hle2))
      a (by rw [hp2, hp1]; exact ha) (ht_pf_le hpf (hp2.trans hp1) (hle1.trans hle2) (by omega)))
      (klongsWf_appendDeleteKlong leaf depth cv c w2 hkw hwf2)) ?_
    rintro _ w3 ⟨⟨hb3, hi3, hle3, -⟩, hwf3⟩
    rw [writerWP_pure]
    exact ⟨hb3, hi3, (hle1.trans (hle2.trans hle3)).1, hwf3⟩
  have hsd : stop < depth := by
    have : stop ≠ depth := fun h => hne' (by simp [h])
    omega
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (hw_keeps B (ht_note B _) c w1 hvo hb1 hi1)
    (klongsWf_note _ c w1 hkw hwf1)) ?_
  rintro _ w2 ⟨⟨hb2, hi2, hle2, hp2⟩, hwf2⟩
  simp only [writerWP_get]
  -- the segment's fold reads
  refine writerWP_mono (ht_foldlM _ _ c (fun _ v => Book B c v ∧ HtInv H B c v ∧ v.path = w2.path ∧
      WriterKlongsWf v) (fun b e v hv => ?_) 0 w2 ⟨hb2, hi2, rfl, hwf2⟩) ?_
  · obtain ⟨hbv, hiv, hpv, hwfv⟩ := hv
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (hw_getNode B e.2 c v hvo hbv hiv)
      (klongsWf_getNode e.2 c v hkw hwfv)) ?_
    rintro m u ⟨⟨hbu, hiu, hleu, -, hpu⟩, hwfu, -⟩
    rw [writerWP_pure]
    exact ⟨⟨hbu, hiu, hpu.trans hpv, hwfu⟩, hleu⟩
  rintro _ w3 ⟨⟨hb3, hi3, hp3, hwf3⟩, hle3⟩
  have hle03 : HtLe w w3 := hle1.trans (hle2.trans hle3)
  have hk03 : Kept w w3 := hle03.1
  have hp03 : w3.path = w.path := hp3.trans (hp2.trans hp1)
  -- the loop: the nodes at the stop node and above stay not taken back
  refine writerWP_mono (ht_forIn_inv_mem c _ (fun v => Book B c v ∧ HtInv H B c v ∧ Kept w3 v ∧
      v.path = w3.path ∧ WriterKlongsWf v ∧ PathFreeTo v (stop + 1)) (List.range (depth - stop))
      (fun j hj v hv => ?_) w3
      ⟨hb3, hi3, Kept.refl _, rfl, hwf3, ht_pf_le hpf hp03 hle03 (by omega)⟩) ?_
  · obtain ⟨hbv, hiv, hkv, hpv, hwfv, hpfv⟩ := hv
    have hj' : j < depth - stop := List.mem_range.mp hj
    simp only [writerWP_bind]
    refine writerWP_mono (kd_pathNode _ c v) ?_
    rintro x v1 ⟨hv1, ax, hxp⟩
    subst v1
    refine writerWP_mono (writerWP_and (hw_getNode B x c v hvo hbv hiv)
      (klongsWf_getNode x c v hkw hwfv)) ?_
    rintro xn u1 ⟨⟨hbu, hiu, hleu, hlx, hpu⟩, hwfu, -⟩
    split
    · simp only [writerWP_bind]
      refine writerWP_mono (kd_pathNode _ c u1) ?_
      rintro par u2 ⟨hu2, -⟩
      subst u2
      refine writerWP_mono (kd_klongAt _ c u1) ?_
      rintro k u3 ⟨hu3, -⟩
      subst u3
      refine writerWP_mono (writerWP_and (ht_takeBackChk B x par k c u1 hvo hbu hiu u1 xn hlx
        (Kept.refl _)) (klongsWf_takeBackChk x par k c u1 hkw hwfu)) ?_
      rintro _ u4 ⟨⟨hb4, hi4, hk4, hp4, htk4⟩, hwf4⟩
      rw [writerWP_pure]
      refine ⟨by first | rfl | trivial, hb4, hi4, (hkv.trans hleu.1).trans hk4,
        by rw [hp4, hpu, hpv], hwf4, ?_⟩
      intro d a' q hd hq
      have hqv : v.path[d]? = some (a', q) := by rw [hp4, hpu] at hq; exact hq
      have hqw : w.path[d]? = some (a', q) := by rw [hpv, hp03] at hqv; exact hqv
      have hxw : w.path[depth - j]? = some (ax, x) := by rw [hpv, hp03] at hxp; exact hxp
      refine htk4 q (by rw [hleu.2]; exact hpfv d a' q hd hqv) ?_
      exact hne (by omega) hqw hxw
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (hw_keeps B (ht_note B _) c u1 hvo hbu hiu)
        (klongsWf_note _ c u1 hkw hwfu)) ?_
      rintro _ u2 ⟨⟨hb2', hi2', hle2', hp2'⟩, hwf2'⟩
      refine writerWP_mono (writerWP_and (ht_unlink B x c u2 hvo hb2' hi2')
        (klongsWf_unlink x c u2 hkw hwf2')) ?_
      rintro _ u3 ⟨⟨hb3', hi3', hle3', hp3'⟩, hwf3'⟩
      rw [writerWP_pure]
      exact ⟨by first | rfl | trivial, hb3', hi3', (hkv.trans hleu.1).trans (hle2'.1.trans hle3'.1),
        by rw [hp3', hp2', hpu, hpv], hwf3',
        ht_pf_le hpfv (hp3'.trans (hp2'.trans hpu)) (hleu.trans (hle2'.trans hle3'))
          (Nat.le_refl _)⟩
  rintro _ w4 ⟨hb4, hi4, hk4, hp4, hwf4, hpf4⟩
  refine writerWP_mono (kd_pathNode stop c w4) ?_
  rintro sNode w5 ⟨hw5, as, hps⟩
  subst w5
  refine writerWP_mono (kd_klongAt (stop + 1) c w4) ?_
  rintro cs w5 ⟨hw5, -⟩
  subst w5
  refine writerWP_mono (writerWP_and (hw_getNode B sNode c w4 hvo hb4 hi4)
    (klongsWf_getNode sNode c w4 hkw hwf4)) ?_
  rintro sn w5 ⟨⟨hb5, hi5, hle5, hl5, hp5⟩, hwf5, -⟩
  refine writerWP_mono (writerWP_and (hw_ghOf B sNode c w5 hvo hb5 hi5)
    (klongsWf_ghOf sNode c w5 hkw hwf5)) ?_
  rintro ⟨gs, hs⟩ w6 ⟨⟨hb6, hi6, hle6, hp6, hm6, -⟩, hwf6⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (hw_keeps B (ht_note B _) c w6 hvo hb6 hi6)
    (klongsWf_note _ c w6 hkw hwf6)) ?_
  rintro _ w7 ⟨⟨hb7, hi7, hle7, hp7⟩, hwf7⟩
  have hp74 : w7.path = w4.path := hp7.trans (hp6.trans hp5)
  have hle47 : HtLe w4 w7 := hle5.trans (hle6.trans hle7)
  refine writerWP_mono (writerWP_and (ht_appendDeleteKlong B sNode stop cs c w7 hvo hpos hb7 hi7
    gs hs (HtLe.gh' hm6 hle7) as (by rw [hp74]; exact hps) (ht_pf_le hpf4 hp74 hle47 (Nat.le_refl _)))
    (klongsWf_appendDeleteKlong sNode stop cs c w7 hkw hwf7)) ?_
  rintro _ w8 ⟨⟨hb8, hi8, hle8, -⟩, hwf8⟩
  refine writerWP_mono (ht_afterDeleteChk B key gs hs c w8 hvo hpos hkw hb8 hi8 hwf8) ?_
  rintro _ w9 ⟨hb9, hi9, hk9, hwf9⟩
  rw [writerWP_pure]
  exact ⟨hb9, hi9, (hk03.trans hk4).trans ((hle47.trans hle8).1.trans hk9), hwf9⟩

/-- The last segment of a delete, without the path's check. -/
theorem ht_setValueDelChk2 (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (c : Ctx)
    (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view)
    (hb : Book B c w) (hi : HtInv H B c w) (hwf : WriterKlongsWf w)
    (hpf : PathFreeTo w w.path.length) (hr : HtPathLast w segRoot)
    (hk : ViewKinds K B c) (hki : KdInv K B w) :
    WriterWP (setValueDelChk2 segRoot cv key) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
      Kept w v ∧ WriterKlongsWf v) := by
  unfold setValueDelChk2
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and
    (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf (Or.inl hr))
    (klongsWf_descendLte cv c.p.fuel segRoot c w hkw hwf))
    (kd_descendLte K B cv c.p.fuel segRoot c w hvo.ids hk hb hki (Or.inl hr))) ?_
  rintro leaf w1 ⟨⟨⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, -⟩, hpf1⟩, hwf1⟩, -, hki1, -⟩
  have hlast1 : HtPathLast w1 leaf := by
    rcases hlast with h | ⟨rfl, hp, -⟩
    · exact h
    · obtain ⟨a, ha⟩ := hr; exact ⟨a, by rw [hp]; exact ha⟩
  refine writerWP_mono (kd_pathSize c w1) ?_
  rintro ln w2 ⟨hw2, hln⟩
  subst w2
  subst ln
  refine writerWP_mono (ht_deleteUpwardChk2 B leaf (w1.path.length - 1) cv key c w1 hvo hpos hkw
    hb1 hi1 hwf1 hpf1 rfl hlast1 n0 hl0 hk hki1) ?_
  rintro noop w3 ⟨hb3, hi3, hk3, hwf3⟩
  have hk13 := hle1.1.trans hk3
  split
  · try simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (hw_keeps B (ht_fresh B) c w3 hvo hb3 hi3)
      (klongsWf_fresh c w3 hkw hwf3)) ?_
    rintro _ w4 ⟨⟨hb4, hi4, hle4, -⟩, hwf4⟩
    rw [writerWP_pure]
    exact ⟨hb4, hi4, hk13.trans hle4.1, hwf4⟩
  · rw [writerWP_pure]
    exact ⟨hb3, hi3, hk13, hwf3⟩

/-- The segments of a delete's key, without the path's check. -/
theorem ht_putSegsDelChk2 (B : NodeId) (key : Key) (segs : List Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i → ViewKlongsWf c.p c.view →
      Book B c w → HtInv H B c w → WriterKlongsWf w → PathFreeTo w w.path.length →
      HtPathLast w r → ViewKinds K B c → KdInv K B w → 2 ≤ c.p.M →
      WriterWP (putSegsDelChk2 key segs r) c w
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ WriterKlongsWf v) := by
  induction segs with
  | nil => intro r c w _ _ _ _ _ _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    intro r c w hvo hpos hkw hb hi hwf hpf hr hk hki hM
    cases rest with
    | nil =>
      unfold putSegsDelChk2
      exact ht_setValueDelChk2 B r cv key c w hvo hpos hkw hb hi hwf hpf hr hk hki
    | cons d rest' =>
      unfold putSegsDelChk2
      simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_and
        (ht_setNode_del B r cv c w hvo hb hi hkw hwf hpf hr)
        (klongsWf_setNode r cv false c w hkw hwf))
        (kd_setNode K B (appendFrameOK B) r cv false c w hvo.ids hk hb hki hM (Or.inl hr)
          (fun h => by cases h))) ?_
      rintro res w1 ⟨⟨⟨hb1, hi1, hle1, hpf1, hres⟩, hwf1⟩, -, hki1, -⟩
      split
      · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1.1, hwf1⟩
      · rename_i next
        exact writerWP_mono (ih next c w1 hvo hpos hkw hb1 hi1 hwf1 hpf1 (hres next rfl) hk hki1 hM)
          (fun _ u hu => ⟨hu.1, hu.2.1, hle1.1.trans hu.2.2.1, hu.2.2.2⟩)

/-- A delete without the path's check keeps the walk. -/
theorem ht_putKvDelChk2 (B : NodeId) (key : Key) (c : Ctx) (w : W) (hvo : ViewHtOK H B c)
    (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) (hb : Book B c w) (hi : HtInv H B c w)
    (hwf : WriterKlongsWf w) (hk : ViewKinds K B c) (hki : KdInv K B w) (hM : 2 ≤ c.p.M) :
    WriterWP (putKvDelChk2 key) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧
      WriterKlongsWf v) := by
  unfold putKvDelChk2
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (writerWP_and (ht_pathClear B c w hvo hb hi)
    (klongsWf_pathClear c w hkw hwf)) (kd_pathClear K B c w hvo.ids hb hki)) ?_
  rintro _ w1 ⟨⟨⟨hb1, hi1, hk1, hp1, -⟩, hwf1⟩, -, hki1, -, hp1', -⟩
  refine writerWP_mono (writerWP_and (writerWP_and (ht_findRoot B c w1 hvo hb1 hi1 hp1)
    (klongsWf_findRoot c w1 hkw hwf1)) (kd_findRoot K B c w1 hvo.ids hb1 hki1 hp1')) ?_
  rintro root w2 ⟨⟨⟨hb2, hi2, hk2, hp2, -, hpf2⟩, hwf2⟩, -, hki2, -⟩
  exact writerWP_mono (ht_putSegsDelChk2 B key key root c w2 hvo hpos hkw hb2 hi2 hwf2
    (by rw [hp2]; exact hpf2) ⟨none, by rw [hp2]; rfl⟩ hk hki2 hM)
    (fun _ u hu => ⟨hu.1, hu.2.1, hk1.trans (hk2.trans hu.2.2.1), hu.2.2.2⟩)

end Walk

/-! ## The run -/

/-- The delete's checks but the path's hold (named premise): a delete, from a
state that the transaction's earlier operations reach, runs as its copy with
the checks of `OpDelChkOK` but `checkPathFree`. -/
def OpDelChk2OK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk2 key (ctxOf p ts) w = .ok (r', v)

/-- The delete side of the walk from the delete's checks but the path's. -/
theorem opHtDelOK_of_chk2 (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (h : OpDelChk2OK p) : OpHtDelOK p := by
  intro ts tx hw z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
  obtain ⟨-, hk, -, hki⟩ := kd_context p hM hP ts tx hw top pre (Op.del key :: post) hsplit r w hpre
  exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
    (by simpa [ctxOf] using hM) r' v
    (h ts tx hw z top hz htop pre key post hsplit r w hpre r' v he)).2.1

/-- TP7's (b) after every run within reach, given the delete's checks but the
path's. -/
theorem treeRun_heightLiveOK_chk2 (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hchk : OpDelChk2OK p)
    (ts : List Tx) (hw : Within p ts) :
    HeightLiveOK p (treeRun p ts) ts.length :=
  treeRun_heightLiveOK p hM hP (opHtDelOK_of_chk2 p hM hP hchk) ts hw

/-- latest's `invPreserved_of_open` with the live heights from the walk, given
the delete's checks but the path's. -/
theorem invPreserved_of_open_chk2 (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hchk : OpDelChk2OK p)
    (hNE : ∀ ts, Within p ts → NonEmptyOK p (treeRun p ts) ts.length)
    (hRT : ∀ ts, Within p ts → RootsOK p (treeRun p ts) ts.length)
    (hF : ∀ ts, Within p ts → FillOK p (treeRun p ts) ts.length)
    (hO : ∀ ts, Within p ts → RangeAtOK p (treeRun p ts) ts.length) : InvPreserved p :=
  invPreserved_of_open_htDel p hp hP hD
    (opHtDelOK_of_chk2 p (by have := mergeParamsOK_M p hp; omega) hP hchk) hNE hRT hF hO

/-! ## TP10's fuel premise -/

/-- `takeBelowFuelOK_of_del` from the delete side of the heights' walk
(`OpHtDelOK`) in place of `OpDelChkOK`: a put takes nothing back (`ht_putKv_put`'s `HtLe`). -/
theorem takeBelowFuelOK_of_delH (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOK p)
    (hdel : TakeBelowFuelDelOK p) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      ∀ a v, putKv op (ctxOf p ts) w = .ok (a, v) →
      ∀ x g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → v.taken.contains x = true →
        h < p.fuel := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre a v he x g h hm hx hv
  cases op with
  | del key => exact hdel ts tx hw z top hz htop pre key post hsplit r w hpre a v he x g h hm hx hv
  | put key hv0 =>
    exfalso
    have hR := hRL _ _ hr
    have hvo := viewHtOK_of_run p ts tx hw hR (hRK _ _ hr) (hRH _ _ hr)
    have hi := ht_reached p hM (hht) ts tx hw hR hvo z top hz htop pre
      (Op.put key hv0 :: post) hsplit r w hpre
    have hbk := putBook_reached p ts tx hw hR z top htop pre r w hpre
    have hB := putBase_of_run p ts tx hw hR
    have := (ht_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w hvo
      (by simp [ctxOf]) hbk.book hi hM hB.wf hbk.klongs a v he).2.2.2
    rw [this, hx] at hv
    cases hv

set_option maxHeartbeats 1600000 in
/-- `txSegFitsOK_of_takeBelowDelR` from the delete side of the heights' walk
(`OpHtDelOK`) in place of `OpDelChkOK`. -/
theorem txSegFitsOK_of_takeBelowDelRH (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOK p)
    (hdel : TakeBelowFuelDelOK p) : TxSegFitsOK p R := by
  intro ts tx hw hr z top hz htop pre post hsplit r w hpre
  have htb := takeBelowFuelOK_of_delH p hM R hRL hRK hRH hht hdel ts tx hw hr z top hz htop
  have hR := hRL _ _ hr
  have hK := hRK _ _ hr
  have hA := hRH _ _ hr
  have hvo := viewHtOK_of_run p ts tx hw hR hK hA
  have hi := ht_reached p hM (hht) ts tx hw hR hvo z top hz htop pre post
    hsplit r w hpre
  have hbk := putBook_reached p ts tx hw hR z top htop pre r w hpre
  have hub : ∀ x g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → h < p.fuel := by
    intro x g h hm hx
    rcases Nat.lt_or_ge h p.fuel with hlt | hge
    · exact hlt
    exfalso
    have hHh : p.H < h := by have := fuel_gt_H p; omega
    have hmk : HeightMarkedPred p w.gh w.outside := by
      letI := heightMarkedFields
      exact fields_ops pre (ctxOf p ts) (wInit tx top)
        (by change HeightMarkedPred p [] []; simp [HeightMarkedPred]) r w hpre
    have hout := hmk x g h hm hHh
    obtain ⟨bs, wE, he⟩ := execW_success_of_within_snoc p ts tx hw
    unfold execW runOps runOpsFrom at he
    rw [hz] at he
    simp only at he
    have htop' : topOf p (rootless (view (treeSpec p) (treeRun p ts) ts.length)) z = .ok top := htop
    rw [htop'] at he
    simp only at he
    have hrun := boundsOK_ok p _ bs wE he
    have hbnd : ∀ q ∈ wE.outside, wE.taken.contains q.1 = true := by
      unfold boundsOK at he
      rw [hrun] at he
      simp only at he
      split at he
      · cases he
      · rename_i hf
        intro q hq
        have := List.find?_eq_none.mp hf q hq
        simpa using this
    have hrun' : ((pre ++ post).mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (bs, wE) := by
      rw [← hsplit]; exact hrun
    obtain ⟨r2, hpost⟩ := mapM_split_run (ctxOf p ts) (wInit tx top) pre post r w bs wE hpre hrun'
    have houtE : (x, g, h) ∈ wE.outside := by
      letI := outsideHasFields (x, g, h)
      exact fields_ops post (ctxOf p ts) w hout r2 wE hpost
    have htE := hbnd _ houtE
    obtain ⟨pre', op, post', r', u, a, v, hs', hp', ho', hu, hv, rest, r3, hrest⟩ :=
      taken_by_op (ctxOf p ts) (wInit tx top) tx.ops x post pre hsplit r w r2 wE hpre hpost hx htE
    have hmu : (x, g, h) ∈ u.gh := by
      letI := ghHasFields (x, g, h)
      exact fields_ops rest (ctxOf p ts) w hm r3 u hrest
    have := htb pre' op post' hs' r' u hp' a v ho' x g h hmu hu hv
    omega
  have htimes : StructTimesLE (treeRun p ts) ts.length := treeRun_timesLE p ts
  have hbase := baseHeights_of p (treeRun p ts) ts.length (ctxOf p ts) rfl
    (by simp [ctxOf]) htimes hR.1 hK hA
  refine segFits_of_heightsU hbk.book hi.cache hvo.heights _ hbase (p.fuel - 1) _ ?_
  intro x n hn h hh
  rcases hh with ⟨g, hm⟩ | ⟨ny, _, _, _, hny⟩
  · have := hub x g h hm (ht_wNode_cases hn).1
    omega
  · have := heightOf_le p ny.level
    have := fuel_gt_H p
    omega

/-- TP10's fuel premise between operations (`TxSegFitsOK`, latest's `hfit`),
from the delete's checks but the path's and the deletes' take-backs below the
fuel. -/
theorem txSegFitsOK_of_takeBelowDelR2 (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hchk : OpDelChk2OK p)
    (hdel : TakeBelowFuelDelOK p) : TxSegFitsOK p R :=
  txSegFitsOK_of_takeBelowDelRH p hM R hRL hRK hRH (opHtDelOK_of_chk2 p hM hP hchk) hdel

end SIS.Tree
