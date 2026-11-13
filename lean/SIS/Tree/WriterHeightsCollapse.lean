/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)): root
collapse (`replaceRoot`, `collapseRoot`).
-/
import SIS.Tree.HeightsHolder

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

variable {H : NodeId → Nat → Prop}

set_option maxHeartbeats 1600000 in
/-- `replaceRoot` of the inner root x, the path's node at depth, which existed
before the transaction: its one live child takes its place, and x loses its
klongs of the transaction. -/
theorem ht_replaceRoot (B : NodeId) (x : NodeId) (depth only : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w) (hi : HtInv H B c w)
    (g h : Nat) (hx : (x, g, h) ∈ w.gh) (n : KNode) (hn : w.nodes.lookup x = some n)
    (hnl : n.leaf = false) (honly : n.onlyLiveKlong = some only) (hcv0 : n.cv? only = some 0)
    (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (hpf : PathFreeTo w (depth + 1))
    (hseg : ∀ a' q, depth ≠ 0 → w.path[depth - 1]? = some (a', q) → ∃ g', (q, g', 0) ∈ w.gh) :
    WriterWP (replaceRoot x depth only) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v) := by
  have hxf : w.taken.contains x = false := hpf depth a x (by omega) hpx
  have hN := hi.cache x n g h (bk_mem_of_lookup _ _ _ hn) hx hxf
  have hh0 : h ≠ 0 := by
    have := kd_leaf hb hn hx
    rw [hnl] at this
    intro h0; subst h0; simp at this
  unfold replaceRoot
  htSimp
  refine writerWP_mono (kd_getNode_hit x n c w hn) ?_
  rintro n' w1 ⟨hnn, hww⟩
  rw [hnn, hww]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i child hchild
    have hlive : (0, child) ∈ n.live := by
      have := (onlyLiveKlong_liveAt n c.i only child hN.3 honly hchild hcv0).1
      rw [KNode.liveAt_of_times n c.i hN.3] at this
      exact this
    have hcf : w.taken.contains child = false := (hN.1 0 child hlive).1
    cases depth with
    | zero =>
      htSimp
      refine writerWP_mono (hw_keeps B (ht_note B _) c w hvo hb hi) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2⟩
      try rw [writerWP_bind]
      refine writerWP_mono (ht_unlink B x c w2 hvo hb2 hi2) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3⟩
      refine writerWP_mono (hw_newSuperRoot B child c w3 hvo hb3 hi3
        (ht_free_le hcf (hle2.trans hle3))) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, -⟩
      exact ⟨hb4, hi4, hle2.trans (hle3.trans hle4)⟩
    | succ d =>
      htSimp
      refine writerWP_mono (hw_keeps B (ht_note B _) c w hvo hb hi) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2⟩
      refine writerWP_mono (kd_pathNode d c w2) ?_
      rintro leaf w2a ⟨hw2a, a', hpl⟩
      rw [hw2a]
      refine writerWP_mono (kd_klongAt (d + 1) c w2) ?_
      rintro k w2b ⟨hw2b, y, hpk⟩
      rw [hw2b]
      have hpl0 : w.path[d]? = some (a', leaf) := by rw [← hp2]; exact hpl
      obtain ⟨gq, hq0⟩ := hseg a' leaf (by omega) (by simpa using hpl0)
      try rw [writerWP_bind]
      refine writerWP_mono (ht_unlink B x c w2 hvo hb2 hi2) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3⟩
      have hle13 := hle2.trans hle3
      refine writerWP_mono (ht_appendKlongs B d leaf [(k, child)] c w3 hvo hpos hb3 hi3
        ⟨gq, 0, HtLe.gh' hq0 hle13, kdPairs_cons (ht_P_val (ht_free_le hcf hle13)) kdPairs_nil'⟩
        ⟨a', by rw [hp3, hp2]; exact hpl0⟩
        (ht_pf_le hpf (hp3.trans hp2) hle13 (by omega))) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, -⟩
      exact ⟨hb4, hi4, hle13.trans hle4⟩

set_option maxHeartbeats 3200000 in
/-- Root collapse: its loop keeps the walk, given an invariant J of the
take-back's that each step keeps and that gives a root's one holder where the
loop takes it back (`HolderAt`). -/
theorem ht_collapseRoot (B : NodeId) (J : W → Prop) (key : Key) (segment : Nat) (c : Ctx)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view)
    (hJd : ∀ v, J v → WriterWP (descendToSegmentRoot key segment) c v (fun _ v' => J v'))
    (hJn : ∀ v x, J v → WriterWP (getNode x) c v (fun _ v' => J v'))
    (hJt : ∀ v x d o, J v → WriterWP (takeBackRoot x d o) c v (fun _ v' => J v'))
    (hJr : ∀ v x d o, J v → WriterWP (replaceRoot x d o) c v (fun _ v' => J v'))
    (hhold : ∀ v x n o, J v → Book B c v → HtInv H B c v → HtPathLast v x →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime = some c.i →
      n.onlyLiveKlong = some o →
      HolderAt c v x (v.path.length - 1) ∧ (v.path.length - 1 ≠ 0 → v.top.rootKey ≠ x) ∧ B ≤ x) :
    ∀ fuel w, Book B c w → HtInv H B c w → WriterKlongsWf w → J w →
      WriterWP (collapseRoot key segment fuel) c w
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ J v) := by
  intro fuel
  induction fuel with
  | zero => intro w _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro w hb hi hwf hJ
    unfold collapseRoot
    htSimp
    refine writerWP_mono (writerWP_and (ht_descendToSegmentRoot B key segment c w hvo hb hi hkw hwf)
      (hJd w hJ)) ?_
    rintro root w1 ⟨⟨hb1, hi1, hle1, hl1, hpf1, hwf1, hsg1⟩, hJ1⟩
    refine writerWP_mono (writerWP_and (writerWP_and (hw_getNode B root c w1 hvo hb1 hi1)
      (klongsWf_getNode root c w1 hkw hwf1)) (hJn w1 root hJ1)) ?_
    rintro n w2 ⟨⟨⟨hb2, hi2, hle2, hl2, hp2⟩, hwf2, -⟩, hJ2⟩
    have hdone : ∀ (u : W), Book B c u → HtInv H B c u → HtLe w u → J u →
        (Book B c u ∧ HtInv H B c u ∧ Kept w u ∧ J u) :=
      fun u h1 h2 h3 h4 => ⟨h1, h2, h3.1, h4⟩
    split
    · rw [writerWP_pure]; exact hdone w2 hb2 hi2 (hle1.trans hle2) hJ2
    · rename_i hnl
      have hnl' : n.leaf = false := by simpa using hnl
      obtain ⟨a, ha⟩ := hl1
      have ha2 : w2.path[w2.path.length - 1]? = some (a, root) := by rw [hp2]; exact ha
      have hL : 0 < w2.path.length := by
        have := (List.getElem?_eq_some_iff.mp ha2).1; omega
      have hpf2 : PathFreeTo w2 w2.path.length := by
        rw [hp2]; exact ht_pf_le hpf1 hp2 hle2 (Nat.le_refl _)
      have hrf : w2.taken.contains root = false := hpf2 _ a root (by omega) ha2
      obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb2 hl2
      have hseg2 : ∀ a' q, w2.path.length - 1 ≠ 0 → w2.path[w2.path.length - 1 - 1]? = some (a', q) →
          ∃ g', (q, g', 0) ∈ w2.gh := by
        intro a' q hd hq
        rw [hp2] at hq hd
        have : w1.path.length - 1 - 1 = w1.path.length - 2 := by omega
        rw [this] at hq
        obtain ⟨g', hg'⟩ := hsg1 a' q (by omega) hq
        exact ⟨g', HtLe.gh' hg' hle2⟩
      -- the steps after the checks, at w2
      have hstep : ∀ (only : Nat), n.onlyLiveKlong = some only → n.cv? only = some 0 →
          WriterWP (if (n.firstTime == some c.i) = true then
              (takeBackRoot root (w2.path.length - 1) only >>= fun _ => collapseRoot key segment f)
            else (replaceRoot root (w2.path.length - 1) only >>= fun _ =>
              collapseRoot key segment f)) c w2
            (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ J v) := by
        intro only honly hcv0
        have hk : ∀ v, Book B c v → HtInv H B c v → Kept w2 v → WriterKlongsWf v → J v →
            WriterWP (collapseRoot key segment f) c v
              (fun _ v' => Book B c v' ∧ HtInv H B c v' ∧ Kept w v' ∧ J v') := by
          intro v hbv hiv hkv hwfv hJv
          refine writerWP_mono (ih v hbv hiv hwfv hJv) ?_
          rintro _ u ⟨hbu, hiu, hku, hJu⟩
          exact ⟨hbu, hiu, ((hle1.trans hle2).1.trans hkv).trans hku, hJu⟩
        split
        · rename_i hmade
          rw [writerWP_bind]
          have hft : n.firstTime = some c.i := by simpa using hmade
          obtain ⟨hhd, hroot, hB⟩ := hhold w2 root n only hJ2 hb2 hi2 ⟨a, ha2⟩ hl2 hnl' hft honly
          refine writerWP_mono (writerWP_and (writerWP_and (ht_takeBackRoot B root _ only c w2 hvo hpos
            hb2 hi2 g h hm n hl2 hnl' honly hcv0 a (by
              rw [show w2.path.length - 1 = w2.path.length - 1 from rfl]; exact ha2)
            (by rw [show w2.path.length - 1 + 1 = w2.path.length by omega]; exact hpf2)
            hhd hroot hB hseg2) (klongsWf_takeBackRoot root _ only c w2 hkw hwf2))
            (hJt w2 root _ only hJ2)) ?_
          rintro _ v ⟨⟨⟨hbv, hiv, hkv⟩, hwfv⟩, hJv⟩
          exact hk v hbv hiv hkv hwfv hJv
        · rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_and (ht_replaceRoot B root _ only c w2 hvo hpos
            hb2 hi2 g h hm n hl2 hnl' honly hcv0 a ha2
            (by rw [show w2.path.length - 1 + 1 = w2.path.length by omega]; exact hpf2) hseg2)
            (klongsWf_replaceRoot root _ only c w2 hkw hwf2))
            (hJr w2 root _ only hJ2)) ?_
          rintro _ v ⟨⟨⟨hbv, hiv, hlev⟩, hwfv⟩, hJv⟩
          exact hk v hbv hiv hlev.1 hwfv hJv
      htSimp
      refine writerWP_mono (kd_replacedBy root c w2) ?_
      rintro r w3 ⟨hw3, -⟩
      rw [hw3]
      wpSplit
      · rw [writerWP_pure]; exact hdone w2 hb2 hi2 (hle1.trans hle2) hJ2
      · split
        · rw [writerWP_pure]; exact hdone w2 hb2 hi2 (hle1.trans hle2) hJ2
        · rename_i only honly
          wpSplit
          · exact writerWP_throw _ _ _ _
          · rename_i hcvne
            have hcv0 : n.cv? only = some 0 := by simpa using hcvne
            htSimp
            refine writerWP_mono (kd_pathSize c w2) ?_
            rintro sz w4 ⟨hw4, hsz⟩
            rw [hw4, hsz]
            exact hstep only honly hcv0

end SIS.Tree
