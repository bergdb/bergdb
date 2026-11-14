/-
The heights' walk through the delete with the checks (bergdb 024-22, step 4;
TP7's (b); SIS/Tree/DelChk.lean): every take-back the writer's delete makes
keeps the walk when its check holds, so the walk needs no other premise.
-/
import SIS.Tree.DelChk
import SIS.Tree.WriterHeightsDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The checks -/

theorem writerWP_checkRoot (x : NodeId) (depth : Nat) (c : Ctx) (w : W) :
    WriterWP (checkRoot x depth) c w (fun _ v => v = w ∧ HolderAt c w x depth ∧
      (depth ≠ 0 → w.top.rootKey ≠ x) ∧ c.view x = none) := by
  unfold checkRoot
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split
  · rename_i hf
    rw [writerWP_pure]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Option.isNone_iff_eq_none] at hf
    obtain ⟨⟨hall, hroot⟩, hview⟩ := hf
    refine ⟨rfl, ⟨?_, ?_⟩, ?_, hview⟩
    · intro q n hq htk cv hcv
      unfold holderAtB at hall
      simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hall
      rcases hall (q, n) hq with h | ⟨h1, _⟩
      · simp only at h; rw [htk] at h; cases h
      · have := h1 (cv, x) hcv
        simp only [bne_self_eq_false, bne_iff_ne, ne_eq, beq_iff_eq] at this
        rcases this with hf | ⟨⟨hd, hq'⟩, hp⟩
        · cases hf
        refine ⟨hd, ?_, hp⟩
        rcases hpe : w.path[depth - 1]? with _ | ⟨a, q'⟩
        · rw [hpe] at hq'; cases hq'
        · rw [hpe] at hq'
          simp only [Option.map_some, Option.some.injEq] at hq'
          exact ⟨a, by rw [hq']⟩
    · intro q n hq htk cv hcv
      unfold holderAtB at hall
      simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        List.any_eq_false, beq_iff_eq] at hall
      rcases hall (q, n) hq with h | ⟨_, h2⟩
      · simp only at h; rw [htk] at h; cases h
      · exact h2 (cv, x) hcv rfl
    · intro hd
      rcases hroot with h | h
      · exact absurd h hd
      · exact h
  · exact writerWP_throw _ _ _ _

theorem writerWP_checkOld (pn : KNode) (old : NodeId) (c : Ctx) (w : W) :
    WriterWP (checkOld pn old) c w (fun _ v => v = w ∧ pn.leaf = true ∧ (c.view old).isSome = true) := by
  unfold checkOld
  simp only [writerWP_bind, writerWP_read]
  split
  · rename_i hf
    rw [writerWP_pure]
    simp only [Bool.and_eq_true] at hf
    exact ⟨rfl, hf.1, hf.2⟩
  · exact writerWP_throw _ _ _ _

section Walk

variable {H : NodeId → Nat → Prop}

theorem ht_free_of_view {B : NodeId} {c : Ctx} {w : W} (hvo : ViewHtOK H B c) (hi : HtInv H B c w)
    {y : NodeId} (hy : (c.view y).isSome = true) : w.taken.contains y = false := by
  cases hv : c.view y with
  | none => rw [hv] at hy; cases hy
  | some nd =>
    have hlt := hvo.ids y nd hv
    cases ht : w.taken.contains y with
    | false => rfl
    | true => have := hi.takenAbove y ht; omega

/-- The upward delete's take-back with the checks. -/
theorem ht_takeBackChk (B : NodeId) (x parent : NodeId) (cv : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w) (vr : W) (xn : KNode)
    (hx : vr.nodes.lookup x = some xn) (hk : Kept vr w) :
    WriterWP (takeBackChk x parent cv) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧
      v.path = w.path ∧ ∀ y, w.taken.contains y = false → y ≠ x → v.taken.contains y = false) := by
  unfold takeBackChk
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (hw_getNode B parent c w hvo hb hi) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
  refine writerWP_mono (kd_replacedBy x c w1) ?_
  rintro ro w2 ⟨hw2, -⟩
  subst w2
  split
  · rename_i old _ _
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_checkOld pn old c w1) ?_
    rintro _ w3 ⟨hw3, hleaf, hview⟩
    subst w3
    obtain ⟨gp, hp', hmp⟩ := kd_tag_of_lookup hb1 hl1
    have hp0 : hp' = 0 := by
      have := kd_leaf hb1 hl1 hmp
      rw [hleaf] at this
      cases hp' with
      | zero => rfl
      | succ k => simp at this
    have hof := ht_free_of_view hvo hi1 hview
    refine writerWP_mono (ht_retarget B parent x old c w1 hvo hb1 hi1 (ht_mem_ids hmp)
      (fun g h hm _ cv => ?_)) ?_
    · obtain ⟨rfl, rfl⟩ := kd_tag_eq hb1 hmp hm
      exact ⟨hof, fun h0 => absurd hp0 h0⟩
    rintro _ w4 ⟨hb4, hi4, hle4, hp4⟩
    refine writerWP_mono (writerWP_checkFree x c w4) ?_
    rintro _ w5 ⟨hw5, hno, hroot, hviewx⟩
    subst w5
    have hk4 : Kept vr w4 := hk.trans (hle1.trans hle4).1
    obtain ⟨xn4, hx4, _⟩ := hk4.lookup hx
    obtain ⟨gx, hx', hmx⟩ := kd_tag_of_lookup hb4 hx4
    refine writerWP_mono (ht_takenBack B x c vr w4 xn hx hk4 hb4 hi4 hno hroot
      (ht_B_le_of_view_none hb4 hmx hviewx)) ?_
    rintro _ w6 ⟨hb6, hi6, hk6, hp6, ht6⟩
    refine writerWP_mono (hw_keeps B (ht_note B _) c w6 hvo hb6 hi6) ?_
    rintro _ w7 ⟨hb7, hi7, hle7, hp7⟩
    refine ⟨hb7, hi7, (hle1.trans hle4).1.trans (hk6.trans hle7.1), by rw [hp7, hp6, hp4, hp1], ?_⟩
    intro y hy hyx
    rw [hle7.2, ht6]
    simp only [List.contains_cons, Bool.or_eq_false_iff]
    refine ⟨by simpa using hyx, ?_⟩
    rw [hle4.2, hle1.2]; exact hy
  · exact writerWP_throw _ _ _ _

set_option maxHeartbeats 3200000 in
/-- Root collapse with the check before a take-back. -/
theorem ht_collapseRootChk (B : NodeId) (key : Key) (segment : Nat) (c : Ctx)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) :
    ∀ fuel w, Book B c w → HtInv H B c w → WriterKlongsWf w →
      WriterWP (collapseRootChk key segment fuel) c w
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ WriterKlongsWf v) := by
  intro fuel
  induction fuel with
  | zero => intro w _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro w hb hi hwf
    unfold collapseRootChk
    htSimp
    refine writerWP_mono (ht_descendToSegmentRoot B key segment c w hvo hb hi hkw hwf) ?_
    rintro root w1 ⟨hb1, hi1, hle1, hl1, hpf1, hwf1, hsg1⟩
    refine writerWP_mono (writerWP_and (hw_getNode B root c w1 hvo hb1 hi1)
      (klongsWf_getNode root c w1 hkw hwf1)) ?_
    rintro n w2 ⟨⟨hb2, hi2, hle2, hl2, hp2⟩, hwf2, -⟩
    have hdone : Book B c w2 ∧ HtInv H B c w2 ∧ Kept w w2 ∧ WriterKlongsWf w2 :=
      ⟨hb2, hi2, (hle1.trans hle2).1, hwf2⟩
    split
    · rw [writerWP_pure]; exact hdone
    · rename_i hnl
      have hnl' : n.leaf = false := by simpa using hnl
      obtain ⟨a, ha⟩ := hl1
      have ha2 : w2.path[w2.path.length - 1]? = some (a, root) := by rw [hp2]; exact ha
      have hL : 0 < w2.path.length := by
        have := (List.getElem?_eq_some_iff.mp ha2).1; omega
      have hpf2 : PathFreeTo w2 w2.path.length := by
        rw [hp2]; exact ht_pf_le hpf1 hp2 hle2 (Nat.le_refl _)
      obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb2 hl2
      have hseg2 : ∀ a' q, w2.path.length - 1 ≠ 0 → w2.path[w2.path.length - 1 - 1]? = some (a', q) →
          ∃ g', (q, g', 0) ∈ w2.gh := by
        intro a' q hd hq
        rw [hp2] at hq hd
        have : w1.path.length - 1 - 1 = w1.path.length - 2 := by omega
        rw [this] at hq
        obtain ⟨g', hg'⟩ := hsg1 a' q (by omega) hq
        exact ⟨g', HtLe.gh' hg' hle2⟩
      have hk : ∀ v, Book B c v → HtInv H B c v → Kept w2 v → WriterKlongsWf v →
          WriterWP (collapseRootChk key segment f) c v
            (fun _ v' => Book B c v' ∧ HtInv H B c v' ∧ Kept w v' ∧ WriterKlongsWf v') := by
        intro v hbv hiv hkv hwfv
        refine writerWP_mono (ih v hbv hiv hwfv) ?_
        rintro _ u ⟨hbu, hiu, hku, hwfu⟩
        exact ⟨hbu, hiu, ((hle1.trans hle2).1.trans hkv).trans hku, hwfu⟩
      htSimp
      refine writerWP_mono (kd_replacedBy root c w2) ?_
      rintro r w3 ⟨hw3, -⟩
      rw [hw3]
      wpSplit
      · rw [writerWP_pure]; exact hdone
      · split
        · rw [writerWP_pure]; exact hdone
        · rename_i only honly
          wpSplit
          · exact writerWP_throw _ _ _ _
          · rename_i hcvne
            have hcv0 : n.cv? only = some 0 := by simpa using hcvne
            htSimp
            refine writerWP_mono (kd_pathSize c w2) ?_
            rintro sz w4 ⟨hw4, hsz⟩
            rw [hw4, hsz]
            split
            · rename_i hmade
              htSimp
              refine writerWP_mono (writerWP_checkRoot root _ c w2) ?_
              rintro _ w5 ⟨hw5, hhd, hroot, hview⟩
              subst w5
              refine writerWP_mono (writerWP_and (ht_takeBackRoot B root _ only c w2 hvo hpos
                hb2 hi2 g h hm n hl2 hnl' honly hcv0 a ha2
                (by rw [show w2.path.length - 1 + 1 = w2.path.length by omega]; exact hpf2)
                hhd hroot (ht_B_le_of_view_none hb2 hm hview) hseg2)
                (klongsWf_takeBackRoot root _ only c w2 hkw hwf2)) ?_
              rintro _ v ⟨⟨hbv, hiv, hkv⟩, hwfv⟩
              exact hk v hbv hiv hkv hwfv
            · htSimp
              refine writerWP_mono (writerWP_and (ht_replaceRoot B root _ only c w2 hvo hpos
                hb2 hi2 g h hm n hl2 hnl' honly hcv0 a ha2
                (by rw [show w2.path.length - 1 + 1 = w2.path.length by omega]; exact hpf2) hseg2)
                (klongsWf_replaceRoot root _ only c w2 hkw hwf2)) ?_
              rintro _ v ⟨⟨hbv, hiv, hlev⟩, hwfv⟩
              exact hk v hbv hiv hlev.1 hwfv

set_option maxHeartbeats 3200000 in
/-- The merge with the checks of x, the path's node at depth d, below an inner
node: the walk is kept. -/
theorem ht_mergeChk (B : NodeId) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w) (hi : HtInv H B c w)
    (hd : d ≠ 0) (ax : Option Nat) (hpx : w.path[d]? = some (ax, x)) (hpf : PathFreeTo w (d + 1))
    (hpq : ∀ a q, w.path[d - 1]? = some (a, q) →
      ∃ nq, w.nodes.lookup q = some nq ∧ nq.leaf = false) :
    WriterWP (mergeChk x d) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ v.path = w.path) := by
  have hJ : (fun (_ : Ctx) (_ : W) => True) c w := trivial
  have hJn : ∀ c v y, (fun (_ : Ctx) (_ : W) => True) c v →
      WriterWP (getNode y) c v (fun _ v' => (fun (_ : Ctx) (_ : W) => True) c v') :=
    fun _ _ _ _ _ _ _ => trivial
  unfold mergeChk
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
  refine writerWP_mono (ht_getNodeJ B (fun _ _ => True) hJn p' c w0 hvo hb hi hJ) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1, hpre1, hJ1⟩
  have hNp : NodeHt c H w1 hp pn := ht_cache_at hl1 hi1 (HtLe.gh' hpt hle1) (ht_free_le hpfree hle1)
    (HtLe.refl _)
  refine writerWP_mono (ht_getNodeJ B (fun _ _ => True) hJn x c w1 hvo hb1 hi1 hJ1) ?_
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
      w3.path = w2'.path → True →
      (∀ z m, w2'.nodes.lookup z = some m → w3.nodes.lookup z = some m) →
      w3.nodes.lookup l = some ln → w3.nodes.lookup r = some rn → (x = l ∨ x = r) →
      HtP c H w2' hp 0 l → HtP c H w2' hp 0 r →
      WriterWP (mergeTailChk c x d p' pn xn leftSome l ln il r rn ir) c w3
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w0 v ∧ v.path = w0.path) := by
    intro leftSome l ln il r rn ir w3 hb3 hi3 hle3 hp3 _ hpre3 hln3 hrn3 hxlr hlh hrh
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
        wb.path = w2'.path → True →
        (∀ z m, w2'.nodes.lookup z = some m → wb.nodes.lookup z = some m) →
        LastLive pn.ks pn.lastBitmap ia0 cva →
        WriterWP (do
          let __x ← sibling p' pn ia0 !xn.leaf
          mergeTailChk c x d p' pn xn false x xn ix __x.1 __x.2 ia0) c wb
          (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w0 v ∧ v.path = w0.path) := by
      intro wb ia0 cva hbb hib hleb hpb hJb hpreb hLa
      rw [writerWP_bind]
      refine writerWP_mono (ht_siblingJ B (fun _ _ => True) hJn p' pn ia0 (!xn.leaf) c wb hvo hbb hib hJb) ?_
      rintro ⟨rs, rsn⟩ w4 ⟨hb4, hi4, hle4, hp4, hs4, hl4, hpre4, hJ4⟩
      exact tailOK false x xn ix rs rsn ia0 w4 hb4 hi4 (hleb.trans hle4) (by rw [hp4, hpb]) hJ4
        (fun z m hz => hpre4 z m (hpreb z m hz)) (hpre4 _ _ (hpreb _ _ hl2)) hl4 (Or.inl rfl)
        hxh (hchild ia0 cva rs hLa hs4)
    split
    · rename_i ib0 cvb
      obtain ⟨hLb, _⟩ := hMb ib0 cvb rfl
      simp only [writerWP_bind]
      refine writerWP_mono (ht_siblingJ B (fun _ _ => True) hJn p' pn ib0 (!xn.leaf) c w2' hvo hb2 hi2 hJ2) ?_
      rintro ⟨ls, lsn⟩ w3 ⟨hb3, hi3, hle3, hp3, hs3, hl3, hpre3, hJ3⟩
      refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · show WriterWP (mergeTailChk c x d p' pn xn true ls lsn ib0 x xn ix) c w3 _
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

/-! ## Well-formed klongs through the copies -/

theorem klongsWf_checkFree (o : NodeId) : KeepsKlongsWf (checkFree o) := by
  unfold checkFree; kwNeutral

theorem klongsWf_checkOld (pn : KNode) (old : NodeId) : KeepsKlongsWf (checkOld pn old) := by
  unfold checkOld; kwNeutral

theorem klongsWf_mergeCleanupChk (parent m1 : NodeId) (xs : List (NodeId × Bool)) :
    KeepsKlongsWf (forIn xs PUnit.unit (fun q _ => do
      if q.2 then
        retarget parent q.1 m1
        checkFree q.1
        takenBack q.1
        note "merge.takeback"
      else unlink q.1
      pure (ForInStep.yield PUnit.unit))) := by
  apply klongsWf_forIn
  intro q stateToken c w hv hw
  repeat' first
    | contradiction
    | wpSimplify
    | kwCore
    | kwUse (klongsWf_unlink _)
    | kwUse (klongsWf_retarget _ _ _)
    | kwUse (klongsWf_checkFree _)
    | wpSplit
    | split

set_option maxHeartbeats 1800000 in
theorem klongsWf_mergeChk (x : NodeId) (d : Nat) : KeepsKlongsWf (mergeChk x d) := by
  intro c w hv hw
  unfold mergeChk mergeTailChk
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (klongsWf_pathNode (d - 1) c w hv hw) ?_
  intro parent state hstate
  refine writerWP_mono (klongsWf_getNode_caches parent c state hv hstate) ?_
  rintro pn state ⟨hstate, hpn, hcache⟩
  repeat' first
    | contradiction
    | wpSimplify
    | kwCachedCore parent with pn
    | kwMergeParentDone parent with pn
    | kwUse (klongsWf_mergeCleanupChk _ _ _)
    | assumption
    | wpSplit
    | split
    | contradiction

theorem klongsWf_takeBackChk (x parent : NodeId) (cv : Nat) :
    KeepsKlongsWf (takeBackChk x parent cv) := by
  intro c w hv hw
  unfold takeBackChk
  repeat' first
    | wpSimplify
    | kwCore
    | kwUse (klongsWf_retarget _ _ _)
    | kwUse (klongsWf_checkOld _ _)
    | kwUse (klongsWf_checkFree _)
    | wpSplit
    | split
    | contradiction

theorem writerWP_checkPathFree (n : Nat) (c : Ctx) (w : W) :
    WriterWP (checkPathFree n) c w (fun _ v => v = w ∧ PathFreeTo w n) := by
  unfold checkPathFree
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i hf
    rw [writerWP_pure]
    refine ⟨rfl, ?_⟩
    intro d a q hd hq
    simp only [List.all_eq_true, Bool.not_eq_true'] at hf
    have hm : (a, q) ∈ w.path.take n := by
      rw [List.mem_iff_getElem?]
      exact ⟨d, by rw [List.getElem?_take]; simp [hd, hq]⟩
    exact hf (a, q) hm
  · exact writerWP_throw _ _ _ _

/-- The climb of the upward delete reads only. -/
theorem ht_climb (B : NodeId) : ∀ (t : Nat) (c : Ctx) (w : W), ViewHtOK H B c → Book B c w →
    HtInv H B c w →
    WriterWP (climb t) c w (fun r v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path ∧ r ≤ t) := by
  intro t
  induction t with
  | zero =>
    intro c w hvo hb hi
    unfold climb
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (kd_pathNode 0 c w) ?_
    rintro x w1 ⟨hw1, -⟩
    subst w1
    refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
    rintro n w2 ⟨hb2, hi2, hle2, -, hp2⟩
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · first | exact writerWP_throw _ _ _ _ | (simp only [writerWP_bind]; exact writerWP_throw _ _ _ _)
    · first
        | (rw [writerWP_pure]; exact ⟨hb2, hi2, hle2, hp2, Nat.le_refl _⟩)
        | (simp only [writerWP_bind, writerWP_pure]; exact ⟨hb2, hi2, hle2, hp2, Nat.le_refl _⟩)
  | succ t ih =>
    intro c w hvo hb hi
    unfold climb
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (kd_pathNode (t + 1) c w) ?_
    rintro x w1 ⟨hw1, -⟩
    subst w1
    refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
    rintro n w2 ⟨hb2, hi2, hle2, -, hp2⟩
    refine writerWP_mono (kd_pathNode t c w2) ?_
    rintro q w3 ⟨hw3, -⟩
    subst w3
    refine writerWP_mono (kd_klongAt (t + 1) c w2) ?_
    rintro k w4 ⟨hw4, -⟩
    subst w4
    unfold canTakeBack
    simp only [writerWP_bind]
    refine writerWP_mono (hw_getNode B q c w2 hvo hb2 hi2) ?_
    rintro pn w5 ⟨hb5, hi5, hle5, -, hp5⟩
    refine writerWP_mono (kd_replacedBy x c w5) ?_
    rintro ro w6 ⟨hw6, -⟩
    subst w6
    simp only [writerWP_pure]
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · first | exact writerWP_throw _ _ _ _ | (simp only [writerWP_bind]; exact writerWP_throw _ _ _ _)
    · simp only [writerWP_bind]
      refine writerWP_mono (hw_getNode B q c w5 hvo hb5 hi5) ?_
      rintro pn' w7 ⟨hb7, hi7, hle7, -, hp7⟩
      have hle := hle2.trans (hle5.trans hle7)
      have hp : w7.path = w.path := hp7.trans (hp5.trans hp2)
      split
      · refine writerWP_mono (ih c w7 hvo hb7 hi7) ?_
        rintro r v ⟨hbv, hiv, hlev, hpv, hr⟩
        exact ⟨hbv, hiv, hle.trans hlev, hpv.trans hp, by omega⟩
      · rw [writerWP_pure]
        exact ⟨hb7, hi7, hle, hp, by omega⟩

/-- The merges after a delete, with the checks. -/
theorem ht_mergeUpChk (B : NodeId) (key : Key) (g fuel : Nat) :
    ∀ (h : Nat) (merged : Bool) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i →
      ViewKlongsWf c.p c.view → Book B c w → HtInv H B c w → WriterKlongsWf w →
      WriterWP (mergeUpChk key g fuel h merged) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
        Kept w v ∧ WriterKlongsWf v) := by
  induction fuel with
  | zero => intro h merged c w _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged c w hvo hpos hkw hb hi hwf
    unfold mergeUpChk
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and
      (ht_descendToHeight B key g h c w hvo hb hi hkw hwf)
      (klongsWf_descendToHeight key g h c w hkw hwf)) ?_
    rintro d w1 ⟨⟨hb1, hi1, hle1, hpf1, hd1⟩, hwf1⟩
    split
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1.1, hwf1⟩
    · rename_i hd0
      have hd : d ≠ 0 := by intro h0; subst h0; exact hd0 rfl
      simp only [writerWP_bind]
      refine writerWP_mono (kd_pathNode d c w1) ?_
      rintro x w2 ⟨hw, ax, hpx⟩
      rw [hw]
      refine writerWP_mono (kd_pathNode (d - 1) c w1) ?_
      rintro q w3 ⟨hw3, aq, hpq⟩
      rw [hw3]
      refine writerWP_mono (writerWP_and (hw_getNode B q c w1 hvo hb1 hi1)
        (klongsWf_getNode q c w1 hkw hwf1)) ?_
      rintro nq w4 ⟨⟨hb4, hi4, hle4, hl4, hp4⟩, hwf4, -⟩
      split
      · rw [writerWP_pure]; exact ⟨hb4, hi4, (hle1.trans hle4).1, hwf4⟩
      · rename_i hql
        simp only [writerWP_bind]
        refine writerWP_mono (writerWP_and (hw_getNode B x c w4 hvo hb4 hi4)
          (klongsWf_getNode x c w4 hkw hwf4)) ?_
        rintro nx w5 ⟨⟨hb5, hi5, hle5, hl5, hp5⟩, hwf5, -⟩
        split
        · rw [writerWP_pure]; exact ⟨hb5, hi5, (hle1.trans (hle4.trans hle5)).1, hwf5⟩
        · simp only [writerWP_bind]
          have hpw : w5.path = w1.path := hp5.trans hp4
          have hlen : d + 1 = w1.path.length := by
            have := (List.getElem?_eq_some_iff.mp hpx).1; omega
          refine writerWP_mono (writerWP_and
            (ht_mergeChk B x d c w5 hvo hpos hb5 hi5 hd ax
              (by rw [hpw]; exact hpx) (ht_pf_le hpf1 hpw (hle4.trans hle5) (by omega)) ?_)
            (klongsWf_mergeChk x d c w5 hkw hwf5)) ?_
          · intro a q' hq'
            rw [hpw, hpq] at hq'
            simp only [Option.some.injEq, Prod.mk.injEq] at hq'
            obtain ⟨-, rfl⟩ := hq'
            obtain ⟨n', hn', hl'⟩ := hle5.1.lookup hl4
            refine ⟨n', hn', ?_⟩
            rw [hl']
            cases hnl : nq.leaf
            · rfl
            · exact absurd hnl hql
          · rintro r w6 ⟨⟨hb6, hi6, hk6, -⟩, hwf6⟩
            have hk := (hle1.trans (hle4.trans hle5)).1.trans hk6
            split
            · rw [writerWP_pure]; exact ⟨hb6, hi6, hk, hwf6⟩
            · exact writerWP_mono (ih (h + 1) true c w6 hvo hpos hkw hb6 hi6 hwf6)
                (fun _ u hu => ⟨hu.1, hu.2.1, hk.trans hu.2.2.1, hu.2.2.2⟩)

/-- After a delete, with the checks. -/
theorem ht_afterDeleteChk (B : NodeId) (key : Key) (g h : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) (hb : Book B c w)
    (hi : HtInv H B c w) (hwf : WriterKlongsWf w) :
    WriterWP (afterDeleteChk key g h) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧
      WriterKlongsWf v) := by
  unfold afterDeleteChk
  simp only [writerWP_bind, writerWP_read]
  split
  · simp only [writerWP_bind]
    refine writerWP_mono (ht_mergeUpChk B key g c.p.fuel h false c w hvo hpos hkw hb hi hwf) ?_
    rintro r w1 ⟨hb1, hi1, hk1, hwf1⟩
    split
    · refine writerWP_mono (ht_collapseRootChk B key g c hvo hpos hkw c.p.fuel w1 hb1 hi1 hwf1) ?_
      rintro _ u ⟨hbu, hiu, hku, hwfu⟩
      exact ⟨hbu, hiu, hk1.trans hku, hwfu⟩
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hk1, hwf1⟩
  · rw [writerWP_pure]; exact ⟨hb, hi, Kept.refl w, hwf⟩

end Walk

end SIS.Tree
