/-
The heights' walk through a merge (bergdb 024-22, step 4; TP7's (b)). A merge
takes back the nodes merged that the transaction made: no kept node may hold
one then. Where the merge takes a node back, no fact of the take-back's walk
holds (putinv, 23:45), so the holder is a named premise: `MergeTailHoldOK J`,
the merge's tail from a state that meets J runs as its copy with a check
before each take-back (`mergeTailChk`, `checkFree`). J is the take-back's
invariant at the tail's start (putinv's TakeJ2 and TreeOK).
-/
import SIS.Tree.WriterHeightsCollapse
import SIS.Tree.WriterTreeMergeOp

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The check before a take-back -/

/-- No kept node holds o now or before the transaction; o is not the space root
and no node of the view. -/
def holderFree (c : Ctx) (w : W) (o : NodeId) : Bool :=
  w.nodes.all (fun q => w.taken.contains q.1 ||
    (!(q.2.live.any (fun e => e.2 == o)) &&
      !((q.2.toPrev (c.i - 1)).live.any (fun e => e.2 == o)))) &&
  (w.top.rootKey != o) && (c.view o).isNone

/-- The check: `holderFree`, else an error. -/
def checkFree (o : NodeId) : M Unit := do
  let c ← read
  let w ← (MonadState.get : M W)
  if holderFree c w o then pure () else throw "check: a kept node holds the node taken back"

theorem writerWP_checkFree (o : NodeId) (c : Ctx) (w : W) :
    WriterWP (checkFree o) c w (fun _ v => v = w ∧ NoLiveHolder c w o ∧ w.top.rootKey ≠ o ∧
      c.view o = none) := by
  unfold checkFree
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split
  · rename_i hf
    rw [writerWP_pure]
    unfold holderFree at hf
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      Option.isNone_iff_eq_none] at hf
    obtain ⟨⟨hall, hroot⟩, hview⟩ := hf
    refine ⟨rfl, ?_, hroot, hview⟩
    intro q n hq htk
    rcases hall (q, n) hq with h | h
    · simp only at h; rw [htk] at h; cases h
    · simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h
      exact ⟨fun cv hcv => h.1 (cv, o) hcv rfl, fun cv hcv => h.2 (cv, o) hcv rfl⟩
  · exact writerWP_throw _ _ _ _

theorem ht_B_le_of_view_none {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) {o : NodeId}
    {g h : Nat} (hm : (o, g, h) ∈ w.gh) (hv : c.view o = none) : B ≤ o := by
  rcases hb.tag o g h hm with ⟨nd, hnd, _⟩ | ⟨hB, _⟩
  · rw [hv] at hnd; cases hnd
  · exact hB

/-! ## The merge's tail with the check -/

/-- `mergeTail` with `checkFree` before each take-back. -/
def mergeTailChk (c : Ctx) (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode) (leftSome : Bool)
    (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir : Nat) : M Nat := do
  let tt := c.i
  let inner := !xn.leaf
  note (if leftSome then "merge.left" else "merge.right")
  let cL ← match pn.cv? il with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {il} in {p}"
  let cR ← match pn.cv? ir with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {ir} in {p}"
  let lvL := ln.live
  let lvR := rn.live
  if lvL.isEmpty || lvR.isEmpty then
    throw s!"Bug: merge at {tt}: key node {l} or {r} has no live klong"
  if inner && ((lvL.head?.map (·.1)) != some 0 || (lvR.head?.map (·.1)) != some 0) then
    throw s!"Bug: merge at {tt}: inner node {l} or {r} has no live klong of the empty key first"
  let (first, second) := mergeKlongs inner c.p.mergeMax cR lvL lvR
  modify (fun w => { w with merges := w.merges + 1 })
  note (if second.isSome then "merge.two" else "merge.one")
  note (if inner then "merge.inner" else "merge.leaf")
  let (g, h) ← ghOf x
  let lMade := ln.firstTime == some tt
  let rMade := rn.firstTime == some tt
  if lMade then note "merge.made.left"
  if rMade then note "merge.made.right"
  let m1 ← newKey g h (!inner) (newKlongs tt first)
  setMadeFor m1 (← if lMade then replacedBy l else pure (some l))
  let m2 ← match second with
    | some (ks2, g2) => do
      let y ← newKey g h (!inner) (newKlongs tt ks2)
      setMadeFor y (← if rMade then replacedBy r else pure (some r))
      pure (some (y, g2))
    | none => pure none
  mergeParent p (d - 1) il cL m1 ir cR m2
  for (o, made) in [(l, lMade), (r, rMade)] do
    if made then
      retarget p o m1
      checkFree o
      takenBack o
      note "merge.takeback"
    else unlink o
  pure (if second.isSome then 2 else 1)

/-- The merge's holder (named premise): from a state that meets J, the merge's
tail runs as its copy with the check before each take-back. -/
def MergeTailHoldOK (J : Ctx → W → Prop) : Prop :=
  ∀ (c : Ctx) (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode) (leftSome : Bool)
    (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir : Nat) (w v : W) (k : Nat),
    J c w → mergeTail c x d p pn xn leftSome l ln il r rn ir c w = .ok (k, v) →
    mergeTailChk c x d p pn xn leftSome l ln il r rn ir c w = .ok (k, v)

section Tail

variable {H : NodeId → Nat → Prop}

/-- A new node of the merge: the live klongs of l and r, one height below. -/
theorem nodeHt_merged {c : Ctx} {w : W} {h : Nat} (hpos : 0 < c.i) (leaf : Bool)
    (l : List (Nat × NodeId)) (hl : kdPairs (HtP c H w h) l) :
    NodeHt c H w h ⟨leaf, newKlongs c.i l⟩ := by
  refine nodeHt_of_ks hpos ⟨_, rfl⟩ (kdKs_newKlongs c.i hl) ?_
  intro t ht
  simp only [newKlongs, List.mem_cons, List.mem_map] at ht
  rcases ht with ht | ⟨⟨cv, y⟩, _, hk⟩
  · cases ht; exact Nat.le_refl _
  · cases hk

theorem ht_free_HtP {c : Ctx} {H : NodeId → Nat → Prop} {w : W} {h : Nat} :
    kdFree (HtP c H w h) := fun _ _ _ hy => hy

theorem ht_live_pairs {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n) :
    kdPairs (HtP c H w h) n.live := fun q hq => hn.1 q.1 q.2 hq

/-- One step of the merge's last loop with the check: o taken back (its parent
retargeted to m1) or unlinked. -/
theorem ht_mergeStepChk (B p m1 : NodeId) (q : NodeId × Bool) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hpg : p ∈ w.gh.map (·.1)) (hm1 : ∀ g h, (p, g, h) ∈ w.gh → ∀ cv, HtP c H w h cv m1)
    (vr : W) (qn : KNode) (hq : vr.nodes.lookup q.1 = some qn) (hk : Kept vr w) :
    WriterWP ((if q.2 = true then (do
        retarget p q.1 m1
        checkFree q.1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit))) : M (ForInStep PUnit)) c w (fun s v =>
      s = ForInStep.yield PUnit.unit ∧ Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ v.path = w.path ∧
      ∀ y, w.taken.contains y = false → y ≠ q.1 → v.taken.contains y = false) := by
  split
  · simp only [writerWP_bind]
    refine writerWP_mono (ht_retarget B p q.1 m1 c w hvo hb hi hpg
      (fun g h hm _ cv => hm1 g h hm cv)) ?_
    rintro _ w1 ⟨hb1, hi1, hle1, hp1⟩
    refine writerWP_mono (writerWP_checkFree q.1 c w1) ?_
    rintro _ w2 ⟨hw2, hno, hroot, hview⟩
    subst w2
    obtain ⟨qn1, hq1, _⟩ := (hk.trans hle1.1).lookup hq
    obtain ⟨gq, hq', hmq⟩ := kd_tag_of_lookup hb1 hq1
    refine writerWP_mono (ht_takenBack B q.1 c vr w1 qn hq (hk.trans hle1.1) hb1 hi1 hno hroot
      (ht_B_le_of_view_none hb1 hmq hview)) ?_
    rintro _ w3 ⟨hb3, hi3, hk3, hp3, ht3⟩
    refine writerWP_mono (hw_keeps B (ht_note B _) c w3 hvo hb3 hi3) ?_
    rintro _ w4 ⟨hb4, hi4, hle4, hp4⟩
    simp only [writerWP_pure]
    refine ⟨by first | rfl | trivial, hb4, hi4, hle1.1.trans (hk3.trans hle4.1),
      by rw [hp4, hp3, hp1], ?_⟩
    intro y hy hyq
    rw [hle4.2, ht3]
    simp only [List.contains_cons, Bool.or_eq_false_iff]
    refine ⟨by simpa using hyq, ?_⟩
    rw [hle1.2]; exact hy
  · simp only [writerWP_bind]
    refine writerWP_mono (ht_unlink B q.1 c w hvo hb hi) ?_
    rintro _ w1 ⟨hb1, hi1, hle1, hp1⟩
    simp only [writerWP_pure]
    exact ⟨by first | rfl | trivial, hb1, hi1, hle1.1, hp1, fun y hy _ => by rw [hle1.2]; exact hy⟩

/-- The merge's last loop with the check. -/
theorem ht_mergeLoopChk (B p m1 l r : NodeId) (bl br : Bool) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hpg : p ∈ w.gh.map (·.1)) (hm1 : ∀ g h, (p, g, h) ∈ w.gh → ∀ cv, HtP c H w h cv m1)
    (hm1l : m1 ≠ l) (ln rn : KNode)
    (hl : w.nodes.lookup l = some ln) (hr : w.nodes.lookup r = some rn) :
    WriterWP (forIn [(l, bl), (r, br)] PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        checkFree q.1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ v.path = w.path) := by
  rw [List.forIn_cons, writerWP_bind]
  refine writerWP_mono (ht_mergeStepChk B p m1 (l, bl) c w hvo hb hi hpg hm1 w ln hl
    (Kept.refl w)) ?_
  rintro s w1 ⟨hs, hb1, hi1, hk1, hp1, ht1⟩
  subst hs
  simp only
  rw [List.forIn_cons, writerWP_bind]
  have hpg1 : p ∈ w1.gh.map (·.1) := by
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hpg
    exact List.mem_map.mpr ⟨e, hk1.2 e he, hee⟩
  have hm1' : ∀ g h, (p, g, h) ∈ w1.gh → ∀ cv, HtP c H w1 h cv m1 := by
    intro g h hm cv
    obtain ⟨⟨p', g0, h0⟩, he, hee⟩ := List.mem_map.mp hpg
    simp only at hee
    subst hee
    obtain ⟨rfl, rfl⟩ := kd_tag_eq hb1 (hk1.2 _ he) hm
    have h0 := hm1 _ _ he cv
    exact ⟨ht1 m1 h0.1 hm1l, fun hh => (h0.2 hh).mono (fun e he => hk1.2 e he)⟩
  refine writerWP_mono (ht_mergeStepChk B p m1 (r, br) c w1 hvo hb1 hi1 hpg1 hm1' w rn hr hk1) ?_
  rintro s w2 ⟨hs, hb2, hi2, hk2, hp2, _⟩
  subst hs
  simp only [List.forIn_nil, writerWP_pure]
  exact ⟨hb2, hi2, hk1.trans hk2, by rw [hp2, hp1]⟩

/-- ghOf x, x of height hp - 1: its height known. -/
macro "htGhM " hvo:term:max hxH:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  (refine writerWP_mono (hw_ghOf (H := ?htO) ?htB _ _ _ ?htView ?htBook ?htInv) ?htPost)
  case htView => assumption
  case htBook => htState
  case htInv => assumption
  rintro ⟨_, hmgH⟩ _ ⟨hmgB, _, _, _, hmgT, _⟩
  have hmgE := hasHt_tag hmgB ($hvo).heights hmgT (($hxH).mono (fun e he => HtLe.gh' he (by htChain)))
  subst hmgE))

/-- A new node of the merge. -/
macro "htCreateM " hpos:term:max hxleaf:term:max hNl:term:max hNr:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ (newKlongs _ _)) _ _ _)
  (refine writerWP_mono (hw_newKey (H := ?htO) ?htB _ _ _ _ _ _ ?htBook ?htInv ?htLf ?htKs) ?htPost)
  case htBook => htState
  case htInv => assumption
  case htLf => (rw [Bool.not_not]; exact $hxleaf)
  case htKs => (first
    | exact nodeHt_merged $hpos _ _ (kdPairs_mergeKlongs _ _ _ (fun _ => ht_free_HtP)
        (htPairs_mono (ht_live_pairs $hNl) (by htChain)) (htPairs_mono (ht_live_pairs $hNr) (by htChain))).1
    | exact nodeHt_merged $hpos _ _ (kd_merge_snd' (by assumption) (fun _ => ht_free_HtP)
        (htPairs_mono (ht_live_pairs $hNl) (by htChain)) (htPairs_mono (ht_live_pairs $hNr) (by htChain))))
  rintro _ _ ⟨_, _, _, _, _, _, _, _⟩))

theorem ht_P_new {c : Ctx} {w : W} {m : NodeId} {g hp cv : Nat} (hf : w.taken.contains m = false)
    (hm : (m, g, hp - 1) ∈ w.gh) : HtP c H w hp cv m := ⟨hf, fun _ => Or.inl ⟨g, hm⟩⟩

theorem ht_ne_of_not_mem {w : W} {m o : NodeId} (hm : m ∉ w.gh.map (·.1)) {g h : Nat}
    (ho : (o, g, h) ∈ w.gh) : m ≠ o := by
  rintro rfl; exact hm (ht_mem_ids ho)

/-- The merge's parent change and its last loop: m1 and m2 of the height below
p's. -/
theorem ht_mergeFinish (B : NodeId) (c : Ctx) (d : Nat) (p : NodeId) (il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (l r : NodeId) (bl br : Bool) (w v : W)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c v) (hi : HtInv H B c v)
    (hle : HtLe w v) (hpv : v.path = w.path)
    (a : Option Nat) (hpx : w.path[d - 1]? = some (a, p)) (hpf : PathFreeTo w (d - 1 + 1))
    (gp hp : Nat) (hpt : (p, gp, hp) ∈ w.gh) (ln rn : KNode) (hln : w.nodes.lookup l = some ln)
    (hrn : w.nodes.lookup r = some rn) (gm : Nat) (hm1 : (m1, gm, hp - 1) ∈ v.gh)
    (hm1f : v.taken.contains m1 = false) (hm1l : m1 ≠ l)
    (hm2 : ∀ y g, m2 = some (y, g) → ∃ gy, (y, gy, hp - 1) ∈ v.gh ∧ v.taken.contains y = false) :
    WriterWP (mergeParent p (d - 1) il cL m1 ir cR m2) c v (fun _ w' =>
      WriterWP (forIn [(l, bl), (r, br)] PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        checkFree q.1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w'
      (fun _ u => Book B c u ∧ HtInv H B c u ∧ Kept w u ∧ u.path = w.path)) := by
  have hpt1 := HtLe.gh' hpt hle
  refine writerWP_mono (ht_mergeParent B p (d - 1) il cL m1 ir cR m2 c v hvo hpos hb hi a
    (kd_path_at hpx hpv) (ht_pf_le hpf hpv hle (Nat.le_refl _)) gp hp hpt1
    (fun cv => ht_P_new hm1f hm1) (fun y g he cv => ?_)) ?_
  · obtain ⟨gy, hy, hyf⟩ := hm2 y g he
    exact ht_P_new hyf hy
  rintro _ v1 ⟨hb1, hi1, hle1, hp1⟩
  obtain ⟨ln1, hln1, _⟩ := (hle.1.trans hle1.1).lookup hln
  obtain ⟨rn1, hrn1, _⟩ := (hle.1.trans hle1.1).lookup hrn
  have hpt2 := HtLe.gh' hpt1 hle1
  have hm1' : ∀ g h, (p, g, h) ∈ v1.gh → ∀ cv, HtP c H v1 h cv m1 := by
    intro g h hm cv
    obtain ⟨rfl, rfl⟩ := kd_tag_eq hb1 hpt2 hm
    exact ht_P_new (ht_free_le hm1f hle1) (HtLe.gh' hm1 hle1)
  refine writerWP_mono (ht_mergeLoopChk B p m1 l r bl br c v1 hvo hb1 hi1 (ht_mem_ids hpt2) hm1'
    hm1l ln1 rn1 hln1 hrn1) ?_
  rintro _ u ⟨hbu, hiu, hku, hpu⟩
  exact ⟨hbu, hiu, (hle.1.trans hle1.1).trans hku, by rw [hpu, hp1, hpv]⟩

set_option maxHeartbeats 3200000 in
/-- The merge's tail with the check keeps the walk: l and r, live children of
the path's node p at depth d - 1, of the height below p's; x one of them. -/
theorem ht_mergeTailChk (B : NodeId) (c : Ctx) (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir : Nat)
    (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w) (hi : HtInv H B c w)
    (a : Option Nat) (hpx : w.path[d - 1]? = some (a, p)) (hpf : PathFreeTo w (d - 1 + 1))
    (gp hp : Nat) (hpt : (p, gp, hp) ∈ w.gh) (hp0 : hp ≠ 0)
    (hxn : w.nodes.lookup x = some xn) (hln : w.nodes.lookup l = some ln)
    (hrn : w.nodes.lookup r = some rn) (hxlr : x = l ∨ x = r)
    (hlh : HtP c H w hp 0 l) (hrh : HtP c H w hp 0 r) :
    WriterWP (mergeTailChk c x d p pn xn leftSome l ln il r rn ir) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ v.path = w.path) := by
  have hvh := hvo.heights
  have hNode : ∀ o on, w.nodes.lookup o = some on → HtP c H w hp 0 o →
      ∃ go, (o, go, hp - 1) ∈ w.gh ∧ NodeHt c H w (hp - 1) on := by
    intro o on hl ho
    obtain ⟨go, ho', hm⟩ := kd_tag_of_lookup hb hl
    have := hasHt_tag hb hvh hm (ho.2 hp0)
    subst this
    exact ⟨go, hm, hi.cache o on go _ (bk_mem_of_lookup _ _ _ hl) hm ho.1⟩
  obtain ⟨gl, hlt, hNl⟩ := hNode l ln hln hlh
  obtain ⟨gr, hrt, hNr⟩ := hNode r rn hrn hrh
  have hxh : HtP c H w hp 0 x := by rcases hxlr with rfl | rfl <;> assumption
  obtain ⟨gx, hxt, -⟩ := hNode x xn hxn hxh
  have hxleaf : xn.leaf = (hp - 1 == 0) := kd_leaf hb hxn hxt
  have hpg : p ∈ w.gh.map (·.1) := ht_mem_ids hpt
  have hxH : HasHt H w x (hp - 1) := hxh.2 hp0
  clear hNode
  unfold mergeTailChk
  repeat' first
    | htSimp
    | htGhM hvo hxH
    | htCreateM hpos hxleaf hNl hNr
    | htCore
    | htRead
    | wpSplit
    | split
    | contradiction
  all_goals
    exact (ht_mergeFinish B c d p _ _ _ _ _ _ l r _ _ w _ hvo hpos (by htState) (by assumption)
      (by htChain) (by htPathEq) a hpx hpf gp hp hpt ln rn hln hrn _ (by htTag) (by htFree)
      (ht_ne_of_not_mem (by assumption) (HtLe.gh' hlt (by htChain)))
      (fun _ _ he => by cases he <;> exact ⟨_, by htTag, by htFree⟩))

/-- getNode with the walk, the lookups kept, and J. -/
theorem ht_getNodeJ (B : NodeId) (J : Ctx → W → Prop)
    (hJn : ∀ c v y, J c v → WriterWP (getNode y) c v (fun _ v' => J c v'))
    (y : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hJ : J c w) :
    WriterWP (getNode y) c w (fun n v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.nodes.lookup y = some n ∧ v.path = w.path ∧
      (∀ z m, w.nodes.lookup z = some m → v.nodes.lookup z = some m) ∧ J c v) := by
  refine writerWP_mono (writerWP_and (writerWP_and (hw_getNode B y c w hvo hb hi)
    (writerWP_getNode_cache2 y c w)) (hJn c w y hJ)) ?_
  rintro n v ⟨⟨⟨hb1, hi1, hle1, hl1, hp1⟩, hpre, -⟩, hJ1⟩
  exact ⟨hb1, hi1, hle1, hl1, hp1, fun z m hz => lookup_of_prefix _ _ hpre z m hz, hJ1⟩

/-- The sibling with the walk, the lookups kept, and J. -/
theorem ht_siblingJ (B : NodeId) (J : Ctx → W → Prop)
    (hJn : ∀ c v y, J c v → WriterWP (getNode y) c v (fun _ v' => J c v'))
    (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w) (hJ : J c w) :
    WriterWP (sibling p pn i inner) c w (fun r v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path ∧ pn.ptr? i = some r.1 ∧ v.nodes.lookup r.1 = some r.2 ∧
      (∀ z m, w.nodes.lookup z = some m → v.nodes.lookup z = some m) ∧ J c v) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    simp only [writerWP_bind]
    refine writerWP_mono (ht_getNodeJ B J hJn s c w hvo hb hi hJ) ?_
    rintro sn w1 ⟨hb1, hi1, hle1, hl1, hp1, hpre1, hJ1⟩
    split
    · exact writerWP_throw _ _ _ _
    · rw [writerWP_pure]
      exact ⟨hb1, hi1, hle1, hp1, hs, hl1, hpre1, hJ1⟩

/-- The tail by the premise and its copy with the check. -/
theorem ht_mergeTail_of (J : Ctx → W → Prop) (hhold : MergeTailHoldOK J) (c : Ctx) (x : NodeId)
    (d : Nat) (p : NodeId) (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat)
    (r : NodeId) (rn : KNode) (ir : Nat) (w : W) (post : Nat → W → Prop) (hJ : J c w)
    (h : WriterWP (mergeTailChk c x d p pn xn leftSome l ln il r rn ir) c w post) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w post :=
  fun k v he => h k v (hhold c x d p pn xn leftSome l ln il r rn ir w v k hJ he)

/-- A live klong of p by its index. -/
theorem ht_live_of_last {pn : KNode} {i cv : Nat} {y : NodeId}
    (hl : LastLive pn.ks pn.lastBitmap i cv) (hy : pn.ptr? i = some y) :
    pn.ks[i]? = some (.key cv y) ∧ (cv, y) ∈ pn.live := by
  have hk : pn.ks[i]? = some (.key cv y) := by
    obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
    simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
    rw [hy0, hy]
  refine ⟨hk, ?_⟩
  apply mem_of_lookup_nodup
  rw [KNode.live_lookup]
  exact keyLookup_of_last _ _ _ i y hk hl

set_option maxHeartbeats 3200000 in
/-- A merge of x, the path's node at depth d, below an inner node, from a state
that meets J: the walk is kept, given the merge's holder (`MergeTailHoldOK`). -/
theorem ht_merge (B : NodeId) (J : Ctx → W → Prop)
    (hJn : ∀ c v y, J c v → WriterWP (getNode y) c v (fun _ v' => J c v'))
    (hhold : MergeTailHoldOK J) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w) (hi : HtInv H B c w)
    (hd : d ≠ 0) (ax : Option Nat) (hpx : w.path[d]? = some (ax, x)) (hpf : PathFreeTo w (d + 1))
    (hpq : ∀ a q, w.path[d - 1]? = some (a, q) →
      ∃ nq, w.nodes.lookup q = some nq ∧ nq.leaf = false) (hJ : J c w) :
    WriterWP (merge x d) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ v.path = w.path) := by
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_pathNode (d - 1) c w) ?_
  rintro p w0 ⟨hw0, ap, hpp⟩
  subst hw0
  obtain ⟨nq, hnq, hnql⟩ := hpq ap p hpp
  have hlen : d - 1 + 1 < w0.path.length := by
    have := (List.getElem?_eq_some_iff.mp hpx).1; omega
  have hpg : p ∈ w0.gh.map (·.1) := hi.pathGh (d - 1) ap p hpp hlen
  obtain ⟨⟨p', gp, hp⟩, hpt, hpe⟩ := List.mem_map.mp hpg
  simp only at hpe
  subst hpe
  have hpfree : w0.taken.contains p' = false := hpf (d - 1) ap p' (by omega) hpp
  have hh : hp ≠ 0 := by
    intro h0; subst h0
    have := kd_leaf hb hnq hpt
    rw [hnql] at this; simp at this
  refine writerWP_mono (ht_getNodeJ B J hJn p' c w0 hvo hb hi hJ) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1, hpre1, hJ1⟩
  have hNp : NodeHt c H w1 hp pn := ht_cache_at hl1 hi1 (HtLe.gh' hpt hle1) (ht_free_le hpfree hle1)
    (HtLe.refl _)
  refine writerWP_mono (ht_getNodeJ B J hJn x c w1 hvo hb1 hi1 hJ1) ?_
  rintro xn w2 ⟨hb2, hi2, hle2, hl2, hp2, hpre2, hJ2⟩
  have hl12 := hpre2 _ _ hl1
  refine writerWP_mono (kd_klongAt d c w2) ?_
  rintro cx w2' ⟨hw2, -, -⟩
  subst hw2
  generalize hmi : mergeIdx pn cx = mi
  obtain ⟨ixo, ia, ib⟩ := mi
  have hML := mergeIdx_last pn cx
  rw [hmi] at hML
  obtain ⟨hMx, hMa, hMb⟩ := hML
  have hpf2 : PathFreeTo w2' (d - 1 + 1) := ht_pf_le hpf (by rw [hp2, hp1]) (hle1.trans hle2)
    (by omega)
  have hpx2 : w2'.path[d - 1]? = some (ap, p') := by rw [hp2, hp1]; exact hpp
  have hpt2 : (p', gp, hp) ∈ w2'.gh := HtLe.gh' hpt (hle1.trans hle2)
  -- the tail from any later state, with its nodes known
  have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
      (rn : KNode) (ir : Nat) (w3 : W), Book B c w3 → HtInv H B c w3 → HtLe w2' w3 →
      w3.path = w2'.path → J c w3 →
      (∀ z m, w2'.nodes.lookup z = some m → w3.nodes.lookup z = some m) →
      w3.nodes.lookup l = some ln → w3.nodes.lookup r = some rn → (x = l ∨ x = r) →
      HtP c H w2' hp 0 l → HtP c H w2' hp 0 r →
      WriterWP (mergeTail c x d p' pn xn leftSome l ln il r rn ir) c w3
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w0 v ∧ v.path = w0.path) := by
    intro leftSome l ln il r rn ir w3 hb3 hi3 hle3 hp3 hJ3 hpre3 hln3 hrn3 hxlr hlh hrh
    refine ht_mergeTail_of J hhold c x d p' pn xn leftSome l ln il r rn ir w3 _ hJ3 ?_
    refine writerWP_mono (ht_mergeTailChk B c x d p' pn xn leftSome l ln il r rn ir w3 hvo hpos
      hb3 hi3 ap (kd_path_at hpx2 hp3) (ht_pf_le hpf2 hp3 hle3 (Nat.le_refl _)) gp hp
      (HtLe.gh' hpt2 hle3) hh (hpre3 _ _ hl2) hln3 hrn3 hxlr (hlh.mono hle3) (hrh.mono hle3)) ?_
    rintro _ v ⟨hbv, hiv, hkv, hpv⟩
    exact ⟨hbv, hiv, ((hle1.trans hle2).trans hle3).1.trans hkv, by rw [hpv, hp3, hp2, hp1]⟩
  have hchild : ∀ i cv y, LastLive pn.ks pn.lastBitmap i cv → pn.ptr? i = some y →
      HtP c H w2' hp 0 y := by
    intro i cv y hl hy
    obtain ⟨_, hm⟩ := ht_live_of_last hl hy
    exact HtP.mono (show HtP c H w1 hp cv y from hNp.1 cv y hm) hle2
  split
  · rename_i ix hix
    simp only [writerWP_bind, writerWP_pure]
    have hLx := hMx ix hix
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    have hpx' : pn.ptr? ix = some x := by simpa using hptr
    have hxh := hchild ix cx x hLx hpx'
    -- the right sibling, read from a state wb
    have hright : ∀ (wb : W) (ia0 cva : Nat), Book B c wb → HtInv H B c wb → HtLe w2' wb →
        wb.path = w2'.path → J c wb →
        (∀ z m, w2'.nodes.lookup z = some m → wb.nodes.lookup z = some m) →
        LastLive pn.ks pn.lastBitmap ia0 cva →
        WriterWP (do
          let __x ← sibling p' pn ia0 !xn.leaf
          mergeTail c x d p' pn xn false x xn ix __x.1 __x.2 ia0) c wb
          (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w0 v ∧ v.path = w0.path) := by
      intro wb ia0 cva hbb hib hleb hpb hJb hpreb hLa
      rw [writerWP_bind]
      refine writerWP_mono (ht_siblingJ B J hJn p' pn ia0 (!xn.leaf) c wb hvo hbb hib hJb) ?_
      rintro ⟨rs, rsn⟩ w4 ⟨hb4, hi4, hle4, hp4, hs4, hl4, hpre4, hJ4⟩
      exact tailOK false x xn ix rs rsn ia0 w4 hb4 hi4 (hleb.trans hle4) (by rw [hp4, hpb]) hJ4
        (fun z m hz => hpre4 z m (hpreb z m hz)) (hpre4 _ _ (hpreb _ _ hl2)) hl4 (Or.inl rfl)
        hxh (hchild ia0 cva rs hLa hs4)
    split
    · rename_i ib0 cvb
      obtain ⟨hLb, _⟩ := hMb ib0 cvb rfl
      simp only [writerWP_bind]
      refine writerWP_mono (ht_siblingJ B J hJn p' pn ib0 (!xn.leaf) c w2' hvo hb2 hi2 hJ2) ?_
      rintro ⟨ls, lsn⟩ w3 ⟨hb3, hi3, hle3, hp3, hs3, hl3, hpre3, hJ3⟩
      refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · show WriterWP (mergeTail c x d p' pn xn true ls lsn ib0 x xn ix) c w3 _
        exact tailOK true ls lsn ib0 x xn ix w3 hb3 hi3 hle3 hp3 hJ3 hpre3 hl3 (hpre3 _ _ hl2)
          (Or.inr rfl) (hchild ib0 cvb ls hLb hs3) hxh
      · rw [writerWP_bind, writerWP_pure]
        dsimp only
        split
        · rename_i ia0 cva _
          obtain ⟨hLa, _⟩ := hMa ia0 cva rfl
          exact hright w3 ia0 cva hb3 hi3 hle3 hp3 hJ3 hpre3 hLa
        · exact writerWP_throw _ _ _ _
    · rw [writerWP_bind, writerWP_pure]
      dsimp only
      split
      · rename_i ia0 cva
        obtain ⟨hLa, _⟩ := hMa ia0 cva rfl
        exact hright w2' ia0 cva hb2 hi2 (HtLe.refl _) rfl hJ2 (fun _ _ h => h) hLa
      · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end Tail

end SIS.Tree
