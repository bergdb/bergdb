/-
The heights' walk through the merges after a delete and the upward delete
(bergdb 024-22, step 4; TP7's (b)). The take-backs need the holder facts that
TP4's walk gives, here named premises (Option 1, coordinator 23:40): an
invariant J of the take-back's (putinv's TakeJ2 with TreeOK) that the delete's
steps keep, the merge's holder (`MergeTailHoldOK`) and the root's
(`ht_collapseRoot`'s `HolderAt`). `HtDelFamily` collects them.
-/
import SIS.Tree.WriterHeightsMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The named premises of the delete side of the heights' walk (the holder
family): J, the take-back's invariant, is kept by the steps between the
take-backs, and gives the holders where the writer takes a node back. -/
structure HtDelFamily (B : NodeId) (H : NodeId → Nat → Prop) (J : Ctx → W → Prop) : Prop where
  getNode : ∀ c v y, J c v → WriterWP (getNode y) c v (fun _ v' => J c v')
  descendToHeight : ∀ c v key g h, J c v →
    WriterWP (descendToHeight key g h) c v (fun _ v' => J c v')
  descendToSegmentRoot : ∀ c v key s, J c v →
    WriterWP (descendToSegmentRoot key s) c v (fun _ v' => J c v')
  merge : ∀ c v x d, J c v → WriterWP (merge x d) c v (fun _ v' => J c v')
  takeBackRoot : ∀ c v x d o, J c v → WriterWP (takeBackRoot x d o) c v (fun _ v' => J c v')
  replaceRoot : ∀ c v x d o, J c v → WriterWP (replaceRoot x d o) c v (fun _ v' => J c v')
  mergeHold : MergeTailHoldOK J
  rootHold : ∀ c v x n o, J c v → Book B c v → HtInv H B c v → HtPathLast v x →
    v.nodes.lookup x = some n → n.leaf = false → n.firstTime = some c.i →
    n.onlyLiveKlong = some o →
    HolderAt c v x (v.path.length - 1) ∧ (v.path.length - 1 ≠ 0 → v.top.rootKey ≠ x) ∧ B ≤ x
  pathClear : ∀ c v, J c v → WriterWP pathClear c v (fun _ v' => J c v')
  findRoot : ∀ c v, J c v → WriterWP findRoot c v (fun _ v' => J c v')
  descendLte : ∀ c v cv f x, J c v → WriterWP (descendLte cv f x) c v (fun _ v' => J c v')
  setNode : ∀ c v r cv, J c v → WriterWP (setNode r cv false) c v (fun _ v' => J c v')
  appendDeleteKlong : ∀ c v x d cv, J c v →
    WriterWP (appendDeleteKlong x d cv) c v (fun _ v' => J c v')
  /-- The upward delete that empties its leaf (the climb, the take-back loop, the
  stop node) keeps the walk. -/
  upEmpty : ∀ c w leaf depth cv key n, J c w → ViewHtOK H B c → 0 < c.i →
    ViewKlongsWf c.p c.view → Book B c w → HtInv H B c w → WriterKlongsWf w →
    PathFreeTo w w.path.length → depth = w.path.length - 1 → HtPathLast w leaf →
    w.nodes.lookup leaf = some n → n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true →
    WriterWP (deleteUpward leaf depth cv key) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
      Kept w v ∧ WriterKlongsWf v)

section Del

variable {H : NodeId → Nat → Prop}

/-- The merges after a delete keep the walk. -/
theorem ht_mergeUp (B : NodeId) (J : Ctx → W → Prop) (hF : HtDelFamily B H J) (key : Key)
    (g fuel : Nat) :
    ∀ (h : Nat) (merged : Bool) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i →
      ViewKlongsWf c.p c.view → Book B c w → HtInv H B c w → WriterKlongsWf w → J c w →
      WriterWP (mergeUp key g fuel h merged) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
        Kept w v ∧ WriterKlongsWf v ∧ J c v) := by
  induction fuel with
  | zero => intro h merged c w _ _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged c w hvo hpos hkw hb hi hwf hJ
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and
      (ht_descendToHeight B key g h c w hvo hb hi hkw hwf)
      (klongsWf_descendToHeight key g h c w hkw hwf)) (hF.descendToHeight c w key g h hJ)) ?_
    rintro d w1 ⟨⟨⟨hb1, hi1, hle1, hpf1, hd1⟩, hwf1⟩, hJ1⟩
    split
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1.1, hwf1, hJ1⟩
    · rename_i hd0
      have hd : d ≠ 0 := by intro h0; subst h0; exact hd0 rfl
      simp only [writerWP_bind]
      refine writerWP_mono (kd_pathNode d c w1) ?_
      rintro x w2 ⟨hw, ax, hpx⟩
      rw [hw]
      refine writerWP_mono (kd_pathNode (d - 1) c w1) ?_
      rintro q w3 ⟨hw3, aq, hpq⟩
      rw [hw3]
      refine writerWP_mono (writerWP_and (writerWP_and (hw_getNode B q c w1 hvo hb1 hi1)
        (klongsWf_getNode q c w1 hkw hwf1)) (hF.getNode c w1 q hJ1)) ?_
      rintro nq w4 ⟨⟨⟨hb4, hi4, hle4, hl4, hp4⟩, hwf4, -⟩, hJ4⟩
      split
      · rw [writerWP_pure]; exact ⟨hb4, hi4, (hle1.trans hle4).1, hwf4, hJ4⟩
      · rename_i hql
        simp only [writerWP_bind]
        refine writerWP_mono (writerWP_and (writerWP_and (hw_getNode B x c w4 hvo hb4 hi4)
          (klongsWf_getNode x c w4 hkw hwf4)) (hF.getNode c w4 x hJ4)) ?_
        rintro nx w5 ⟨⟨⟨hb5, hi5, hle5, hl5, hp5⟩, hwf5, -⟩, hJ5⟩
        split
        · rw [writerWP_pure]; exact ⟨hb5, hi5, (hle1.trans (hle4.trans hle5)).1, hwf5, hJ5⟩
        · simp only [writerWP_bind]
          have hpw : w5.path = w1.path := hp5.trans hp4
          have hlen : d + 1 = w1.path.length := by
            have := (List.getElem?_eq_some_iff.mp hpx).1; omega
          refine writerWP_mono (writerWP_and (writerWP_and
            (ht_merge B J hF.getNode hF.mergeHold x d c w5 hvo hpos hb5 hi5 hd ax
              (by rw [hpw]; exact hpx) (ht_pf_le hpf1 hpw (hle4.trans hle5) (by omega)) ?_ hJ5)
            (klongsWf_merge x d c w5 hkw hwf5)) (hF.merge c w5 x d hJ5)) ?_
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
          · rintro r w6 ⟨⟨⟨hb6, hi6, hk6, -⟩, hwf6⟩, hJ6⟩
            have hk := (hle1.trans (hle4.trans hle5)).1.trans hk6
            split
            · rw [writerWP_pure]; exact ⟨hb6, hi6, hk, hwf6, hJ6⟩
            · exact writerWP_mono (ih (h + 1) true c w6 hvo hpos hkw hb6 hi6 hwf6 hJ6)
                (fun _ u hu => ⟨hu.1, hu.2.1, hk.trans hu.2.2.1, hu.2.2.2⟩)

/-- After a delete: the merges, and root collapse after a merge. -/
theorem ht_afterDelete (B : NodeId) (J : Ctx → W → Prop) (hF : HtDelFamily B H J) (key : Key)
    (g h : Nat) (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i)
    (hkw : ViewKlongsWf c.p c.view) (hb : Book B c w) (hi : HtInv H B c w)
    (hwf : WriterKlongsWf w) (hJ : J c w) :
    WriterWP (afterDelete key g h) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧
      WriterKlongsWf v ∧ J c v) := by
  unfold afterDelete
  simp only [writerWP_bind, writerWP_read]
  split
  · simp only [writerWP_bind]
    refine writerWP_mono (ht_mergeUp B J hF key g c.p.fuel h false c w hvo hpos hkw hb hi hwf hJ) ?_
    rintro r w1 ⟨hb1, hi1, hk1, hwf1, hJ1⟩
    split
    · refine writerWP_mono (writerWP_and (ht_collapseRoot B (J c) key g c hvo hpos hkw
        (fun v hv => hF.descendToSegmentRoot c v key g hv) (fun v x hv => hF.getNode c v x hv)
        (fun v x d o hv => hF.takeBackRoot c v x d o hv) (fun v x d o hv => hF.replaceRoot c v x d o hv)
        (fun v x n o hv => hF.rootHold c v x n o hv) c.p.fuel w1 hb1 hi1 hwf1 hJ1)
        (klongsWf_collapseRoot key g c.p.fuel c w1 hkw hwf1)) ?_
      rintro _ u ⟨⟨hbu, hiu, hku, hJu⟩, hwfu⟩
      exact ⟨hbu, hiu, hk1.trans hku, hwfu, hJu⟩
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hk1, hwf1, hJ1⟩
  · rw [writerWP_pure]; exact ⟨hb, hi, Kept.refl w, hwf, hJ⟩

theorem ht_J_ghOf (J : Ctx → W → Prop) {B : NodeId} (hF : HtDelFamily B H J) (x : NodeId) (c : Ctx)
    (w : W) (hJ : J c w) : WriterWP (ghOf x) c w (fun _ v => J c v) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (hF.getNode c w x hJ) ?_
  intro _ w1 hJ1
  simp only [writerWP_get]
  split
  · rw [writerWP_pure]; exact hJ1
  · exact writerWP_throw _ _ _ _

/-- The delete of compare value cv in the segment leaf, the path's last node. -/
theorem ht_deleteUpward (B : NodeId) (J : Ctx → W → Prop) (hF : HtDelFamily B H J)
    (leaf : NodeId) (depth cv : Nat) (key : Key) (c : Ctx) (w : W) (hvo : ViewHtOK H B c)
    (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) (hb : Book B c w) (hi : HtInv H B c w)
    (hwf : WriterKlongsWf w) (hJ : J c w) (hpf : PathFreeTo w w.path.length)
    (hdepth : depth = w.path.length - 1) (hlast : HtPathLast w leaf) (n : KNode)
    (hn : w.nodes.lookup leaf = some n) :
    WriterWP (deleteUpward leaf depth cv key) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
      Kept w v ∧ WriterKlongsWf v) := by
  by_cases hall : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true
  · exact hF.upEmpty c w leaf depth cv key n hJ hvo hpos hkw hb hi hwf hpf hdepth hlast hn hall
  obtain ⟨a, ha⟩ := hlast
  rw [← hdepth] at ha
  have hlen : depth + 1 = w.path.length := by
    have := (List.getElem?_eq_some_iff.mp ha).1; omega
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_getNode_hit leaf n c w hn) ?_
  rintro n' w' ⟨hn', hw'⟩
  subst n' w'
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · rw [writerWP_pure]; exact ⟨hb, hi, Kept.refl w, hwf⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hne => ?_)
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (writerWP_and (hw_ghOf B leaf c w hvo hb hi)
      (klongsWf_ghOf leaf c w hkw hwf)) (ht_J_ghOf J hF leaf c w hJ)) ?_
    rintro ⟨g, h⟩ w1 ⟨⟨⟨hb1, hi1, hle1, hp1, hm1, -⟩, hwf1⟩, hJ1⟩
    refine writerWP_mono (writerWP_and (writerWP_and (ht_appendDeleteKlong B leaf depth cv c w1 hvo
      hpos hb1 hi1 g h hm1 a (by rw [hp1]; exact ha) (ht_pf_le hpf hp1 hle1 (by omega)))
      (klongsWf_appendDeleteKlong leaf depth cv c w1 hkw hwf1))
      (hF.appendDeleteKlong c w1 leaf depth cv hJ1)) ?_
    rintro _ w2 ⟨⟨⟨hb2, hi2, hle2, -⟩, hwf2⟩, hJ2⟩
    refine writerWP_mono (ht_afterDelete B J hF key g h c w2 hvo hpos hkw hb2 hi2 hwf2 hJ2) ?_
    rintro _ w3 ⟨hb3, hi3, hk3, hwf3, -⟩
    rw [writerWP_pure]
    exact ⟨hb3, hi3, (hle1.trans hle2).1.trans hk3, hwf3⟩
  · exact absurd (by simpa using hne) hall

/-- The last segment of a delete: down to its leaf, then the delete. -/
theorem ht_setValue_del (B : NodeId) (J : Ctx → W → Prop) (hF : HtDelFamily B H J)
    (segRoot : NodeId) (cv : Nat) (key : Key) (c : Ctx) (w : W) (hvo : ViewHtOK H B c)
    (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) (hb : Book B c w) (hi : HtInv H B c w)
    (hwf : WriterKlongsWf w) (hJ : J c w) (hpf : PathFreeTo w w.path.length)
    (hr : HtPathLast w segRoot) :
    WriterWP (setValue segRoot cv key none) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
      Kept w v ∧ WriterKlongsWf v) := by
  unfold setValue
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and
    (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf (Or.inl hr))
    (klongsWf_descendLte cv c.p.fuel segRoot c w hkw hwf))
    (hF.descendLte c w cv c.p.fuel segRoot hJ)) ?_
  rintro leaf w1 ⟨⟨⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, -⟩, hpf1⟩, hwf1⟩, hJ1⟩
  have hlast1 : HtPathLast w1 leaf := by
    rcases hlast with h | ⟨rfl, hp, -⟩
    · exact h
    · obtain ⟨a, ha⟩ := hr; exact ⟨a, by rw [hp]; exact ha⟩
  refine writerWP_mono (kd_pathSize c w1) ?_
  rintro ln w2 ⟨hw2, hln⟩
  subst w2
  subst ln
  refine writerWP_mono (ht_deleteUpward B J hF leaf (w1.path.length - 1) cv key c w1 hvo hpos hkw
    hb1 hi1 hwf1 hJ1 hpf1 rfl hlast1 n0 hl0) ?_
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

/-- The tree of the next segment, for a delete: found or none. -/
theorem ht_setNode_del (B : NodeId) (segRoot : NodeId) (cv : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hkw : ViewKlongsWf c.p c.view) (hwf : WriterKlongsWf w)
    (hpf : PathFreeTo w w.path.length) (hr : HtPathLast w segRoot) :
    WriterWP (setNode segRoot cv false) c w (fun r v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      PathFreeTo v v.path.length ∧ ∀ y, r = some y → HtPathLast v y) := by
  unfold setNode
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf
    (Or.inl hr)) (klongsWf_descendLte cv c.p.fuel segRoot c w hkw hwf)) ?_
  rintro cur w1 ⟨⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, hleaf0⟩, hpf1⟩, hwf1⟩
  obtain ⟨g, hh, hm⟩ := kd_tag_of_lookup hb1 hl0
  have hh0 : hh = 0 := kd_h0 hb1 hl0 hm hleaf0
  subst hh0
  obtain ⟨a, ha⟩ : HtPathLast w1 cur := by
    rcases hlast with h1 | ⟨hcr, hp, -⟩
    · exact h1
    · subst hcr
      obtain ⟨a, ha⟩ := hr
      exact ⟨a, by rw [hp]; exact ha⟩
  have hcf : w1.taken.contains cur = false := by
    have := (List.getElem?_eq_some_iff.mp ha).1
    exact hpf1 _ a cur (by omega) ha
  have hN0 : NodeHt c H w1 0 n0 := ht_cache_at hl0 hi1 hm hcf (HtLe.refl _)
  refine writerWP_mono (kd_getNode_hit cur n0 c w1 hl0) ?_
  rintro n w2 ⟨hn, hw⟩
  rw [hn, hw]
  split
  · rename_i fd hfd
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (ht_pathAdd B fd.c fd.y c w1 hvo hb1 hi1 a cur n0 (ht_getLast_of ha) hl0
      cv (ht_searchEq_live (writerKlongsWf_lookup w1 hwf1 cur n0 hl0) hN0.3 hfd) hcf) ?_
    rintro _ w3 ⟨hb3, hi3, hk3, hp3, ht3, hyf⟩
    refine ⟨hb3, hi3, hle1.trans ⟨hk3, ht3⟩, PathFreeTo.append hpf1 _ hp3 ht3 hyf, ?_⟩
    intro y hy
    cases hy
    exact ⟨some fd.c, by rw [hp3]; exact kd_pathLast_append _ _⟩
  · simp only [Bool.not_false, ↓reduceIte, writerWP_pure]
    exact ⟨hb1, hi1, hle1, hpf1, fun y hy => by cases hy⟩

/-- The segments of a delete's key. -/
theorem ht_putSegs_del (B : NodeId) (J : Ctx → W → Prop) (hF : HtDelFamily B H J) (key : Key)
    (segs : List Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i → ViewKlongsWf c.p c.view →
      Book B c w → HtInv H B c w → WriterKlongsWf w → J c w → PathFreeTo w w.path.length →
      HtPathLast w r →
      WriterWP (putSegs key none segs r) c w
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ WriterKlongsWf v) := by
  induction segs with
  | nil => intro r c w _ _ _ _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    intro r c w hvo hpos hkw hb hi hwf hJ hpf hr
    cases rest with
    | nil =>
      unfold putSegs
      exact ht_setValue_del B J hF r cv key c w hvo hpos hkw hb hi hwf hJ hpf hr
    | cons d rest' =>
      unfold putSegs
      simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_and
        (ht_setNode_del B r cv c w hvo hb hi hkw hwf hpf hr)
        (klongsWf_setNode r cv false c w hkw hwf)) (hF.setNode c w r cv hJ)) ?_
      rintro res w1 ⟨⟨⟨hb1, hi1, hle1, hpf1, hres⟩, hwf1⟩, hJ1⟩
      split
      · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1.1, hwf1⟩
      · rename_i next
        exact writerWP_mono (ih next c w1 hvo hpos hkw hb1 hi1 hwf1 hJ1 hpf1 (hres next rfl))
          (fun _ u hu => ⟨hu.1, hu.2.1, hle1.1.trans hu.2.2.1, hu.2.2.2⟩)

/-- A delete keeps the walk, given the holder family. -/
theorem ht_putKv_del (B : NodeId) (J : Ctx → W → Prop) (hF : HtDelFamily B H J) (key : Key)
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view)
    (hb : Book B c w) (hi : HtInv H B c w) (hwf : WriterKlongsWf w) (hJ : J c w) :
    WriterWP (putKv (.del key)) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧
      WriterKlongsWf v) := by
  unfold putKv
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (writerWP_and (ht_pathClear B c w hvo hb hi)
    (klongsWf_pathClear c w hkw hwf)) (hF.pathClear c w hJ)) ?_
  rintro _ w1 ⟨⟨⟨hb1, hi1, hk1, hp1, -⟩, hwf1⟩, hJ1⟩
  refine writerWP_mono (writerWP_and (writerWP_and (ht_findRoot B c w1 hvo hb1 hi1 hp1)
    (klongsWf_findRoot c w1 hkw hwf1)) (hF.findRoot c w1 hJ1)) ?_
  rintro root w2 ⟨⟨⟨hb2, hi2, hk2, hp2, -, hpf2⟩, hwf2⟩, hJ2⟩
  exact writerWP_mono (ht_putSegs_del B J hF key key root c w2 hvo hpos hkw hb2 hi2 hwf2 hJ2
    (by rw [hp2]; exact hpf2) ⟨none, by rw [hp2]; rfl⟩)
    (fun _ u hu => ⟨hu.1, hu.2.1, hk1.trans (hk2.trans hu.2.2.1), hu.2.2.2⟩)

end Del

end SIS.Tree
