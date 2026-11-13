/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)), the
delete's steps that take nothing back: a full node given its last version
(`handleFull`), a bitmap (`appendDeleteKlong`), `unlink`, `retarget`.
-/
import SIS.Tree.WriterHeightsDelNode

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

variable {H : NodeId → Nat → Prop}

/-- A full node x, the path's node at depth, replaced by a last version of the
right height. -/
theorem ht_handleFull (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (g h : Nat) (hx : (x, g, h) ∈ w.gh) (a : Option Nat)
    (hpx : w.path[depth]? = some (a, x)) (hpf : PathFreeTo w (depth + 1))
    (hflat : FlatAt c.i last.ks) (hlast : kdKs (HtP c H w h) last.ks) :
    WriterWP (handleFull depth x last compact) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
  unfold handleFull
  cases depth with
  | zero =>
    exact ht_handleFullWith B _ 0 x [] last compact c w hvo hpos hb hi g h hx a hpx hpf hflat hlast
      kdPairs_nil' (fun e he => by cases he)
  | succ d =>
    refine ht_handleFullWith B _ (d + 1) x [] last compact c w hvo hpos hb hi g h hx a hpx hpf hflat
      hlast kdPairs_nil' ?_
    intro e he
    cases he
    intro q more c' w' hvo' hpos' hb' hi' hpf' hpq hmore
    exact ht_appendKlongs B d q more c' w' hvo' hpos' hb' hi' hmore hpq hpf'

/-- A store of an overlay node read at state vr, meeting `NodeHt` when it is
not taken back. -/
theorem ht_putNode_if (B x : NodeId) (n' : KNode) (c : Ctx) (vr w : W) (n0 : KNode)
    (hb : Book B c w) (hi : HtInv H B c w) (hl : vr.nodes.lookup x = some n0) (hkr : HtLe vr w)
    (hleaf : n'.leaf = n0.leaf)
    (hks : ∀ g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → NodeHt c H w h n') :
    WriterWP (putNode x n') c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path) := by
  obtain ⟨n1, hn1, hl1⟩ := hkr.1.1 x n0 hl
  refine writerWP_mono (ht_putNode B x n' c w hb hi n1 hn1 (hleaf.trans hl1.symm) hks) ?_
  rintro _ v ⟨hb', hi', hk', hp, ht, -⟩
  exact ⟨hb', hi', ⟨hk', ht⟩, hp⟩

/-- `unlink`: a node that loses its klongs of the transaction. -/
theorem ht_unlink (B : NodeId) (x : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK H B c)
    (hb : Book B c w) (hi : HtInv H B c w) :
    WriterWP (unlink x) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path) := by
  unfold unlink
  htSimp
  refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
  split
  · refine writerWP_mono (ht_putNode_if B x _ c w1 w1 n hb1 hi1 hl1 (HtLe.refl _)
      (bk_toPrev_leaf _ _) ?_) ?_
    · intro g h hm hf
      exact nodeHt_toPrev (ht_cache_at hl1 hi1 hm hf (HtLe.refl _))
    · rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
  · rw [writerWP_pure]
    exact ⟨hb1, hi1, hle1, hp1⟩

/-- `retarget`: the transaction's klongs of p that name src name dst, a node of
the right height for p. -/
theorem ht_retarget (B : NodeId) (p src dst : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK H B c)
    (hb : Book B c w) (hi : HtInv H B c w) (hpg : p ∈ w.gh.map (·.1))
    (hd : ∀ g h, (p, g, h) ∈ w.gh → w.taken.contains p = false → ∀ cv, HtP c H w h cv dst) :
    WriterWP (retarget p src dst) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path) := by
  unfold retarget
  htSimp
  refine writerWP_mono (hw_getNode B p c w hvo hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
  split
  · refine writerWP_mono (ht_putNode_if B p _ c w1 w1 n hb1 hi1 hl1 (HtLe.refl _) rfl ?_) ?_
    · intro g h hm hf
      have hm0 : (p, g, h) ∈ w.gh := by
        obtain ⟨⟨p', g0, h0⟩, hq, hqe⟩ := List.mem_map.mp hpg
        simp only at hqe
        subst hqe
        obtain ⟨rfl, rfl⟩ := kd_tag_eq hb1 (HtLe.gh' hq hle1) hm
        exact hq
      have hN := ht_cache_at hl1 hi1 hm hf (HtLe.refl _)
      refine nodeHt_retarget hN _ src dst ?_
      intro cv
      exact (hd g h hm0 (by rw [← hle1.2]; exact hf) cv).mono hle1
    · rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
  · rw [writerWP_pure]
    exact ⟨hb1, hi1, hle1, hp1⟩

/-- A note, then f. -/
theorem ht_seq_note (B : NodeId) {α : Type} (s : String) (f : M α) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w) (post : α → W → Prop)
    (hf : ∀ v, Book B c v → HtInv H B c v → HtLe w v → v.path = w.path → WriterWP f c v post) :
    WriterWP (do note s; f) c w post := by
  rw [writerWP_bind]
  refine writerWP_mono (hw_keeps B (ht_note B s) c w hvo hb hi) ?_
  rintro _ v ⟨hb2, hi2, hle2, hp2⟩
  exact hf v hb2 hi2 hle2 hp2

theorem ht_hasTransDel {n : KNode} {t : Time}
    (h : ((match n.ks.getLast? with
      | some (.del _) => true
      | _ => false) && n.lastTime == some t) = true) :
    ∃ old, n.ks.getLast? = some (.del old) ∧ n.lastTime = some t := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  cases hg : n.ks.getLast? with
  | none => rw [hg] at h1; simp at h1
  | some k =>
    rw [hg] at h1
    cases k with
    | del b => exact ⟨b, rfl, h2⟩
    | time u => simp at h1
    | key a y => simp at h1

/-- `appendDeleteKlong` at x, the path's node at depth: a bitmap, in place or
new, or the node replaced by its last version without cv. -/
theorem ht_appendDeleteKlong (B : NodeId) (x : NodeId) (depth cv : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w) (hi : HtInv H B c w)
    (g h : Nat) (hx : (x, g, h) ∈ w.gh) (a : Option Nat) (hpx : w.path[depth]? = some (a, x))
    (hpf : PathFreeTo w (depth + 1)) :
    WriterWP (appendDeleteKlong x depth cv) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
  have hxf : w.taken.contains x = false := hpf depth a x (by omega) hpx
  unfold appendDeleteKlong
  htSimp
  refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
  have hx1 := HtLe.gh' hx hle1
  have hN := ht_cache_at hl1 hi1 hx1 (ht_free_le hxf hle1) (HtLe.refl _)
  -- every step from a state v after w1 (a note changes nothing the walk reads)
  have hfull : ∀ v cp, Book B c v → HtInv H B c v → HtLe w1 v → v.path = w1.path →
      WriterWP (handleFull depth x
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) cp >>= fun _ =>
        pure (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap)) c v
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
    intro v cp hbv hiv hlev hpv
    rw [writerWP_bind]
    have hpxv : v.path[depth]? = some (a, x) := by rw [hpv, hp1]; exact hpx
    refine writerWP_mono (ht_handleFull B depth x _ cp c v hvo hpos hbv hiv g h (HtLe.gh' hx1 hlev) a
      hpxv (ht_pf_le hpf (hpv.trans hp1) (hle1.trans hlev) (Nat.le_refl _))
      (KNode.lastVersionGivenDel_flatAt n c.i _) (htKs_mono (htKs_lastVersion_del hN c.i cv) hlev)) ?_
    rintro _ u ⟨hb2, hi2, hle2, hp2⟩
    rw [writerWP_pure]
    exact ⟨hb2, hi2, hle1.trans (hlev.trans hle2), hp2.trans (hpv.trans hp1)⟩
  have hput : ∀ v n', Book B c v → HtInv H B c v → HtLe w1 v → v.path = w1.path →
      n'.leaf = n.leaf → NodeHt c H w1 h n' →
      WriterWP (putNode x n' >>= fun _ =>
        pure (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap)) c v
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
    intro v n' hbv hiv hlev hpv hlf hN'
    rw [writerWP_bind]
    refine writerWP_mono (ht_putNode_of B x n' c w1 w1 v n hbv hiv hl1 hlev hlf g h hx1 hlev
      (hN'.htMono hlev)) ?_
    rintro _ u ⟨hb2, hi2, hle2, hp2, -⟩
    rw [writerWP_pure]
    exact ⟨hb2, hi2, hle1.trans (hlev.trans hle2), hp2.trans (hpv.trans hp1)⟩
  split
  · exact writerWP_throw _ _ _ _
  · wpSplit
    · wpSplit
      · rename_i htd
        have hTD : ∃ old, n.ks.getLast? = some (.del old) ∧ n.lastTime = some c.i := by
          revert htd
          cases hg : n.ks.getLast? with
          | none => simp
          | some k =>
            cases k with
            | del b =>
              simp only [Bool.true_and, beq_iff_eq]
              exact fun h => ⟨b, rfl, h⟩
            | time u => simp
            | key a y => simp
        obtain ⟨old, hlast, hlt⟩ := hTD
        wpSplit
        · exact ht_seq_note B _ _ c w1 hvo hb1 hi1 _ (fun v hbv hiv hlev hpv => hfull v true hbv hiv hlev hpv)
        · exact ht_seq_note B _ _ c w1 hvo hb1 hi1 _ (fun v hbv hiv hlev hpv =>
            hput v _ hbv hiv hlev hpv (bk_setAt_leaf _ _ _) (nodeHt_setAt_del hpos hN old hlast hlt cv))
      · wpSplit
        · wpSplit
          · exact ht_seq_note B _ _ c w1 hvo hb1 hi1 _ (fun v hbv hiv hlev hpv => hfull v true hbv hiv hlev hpv)
          · exact ht_seq_note B _ _ c w1 hvo hb1 hi1 _ (fun v hbv hiv hlev hpv =>
              hput v _ hbv hiv hlev hpv (KNode.add_leaf _ _ _) (nodeHt_add_del hpos hN cv))
        · exact ht_seq_note B _ _ c w1 hvo hb1 hi1 _ (fun v hbv hiv hlev hpv => hfull v false hbv hiv hlev hpv)
    · rw [writerWP_pure]
      exact ⟨hb1, hi1, hle1, hp1⟩

/-! ## The descents -/

/-- A fold of steps that keep an invariant. -/
theorem ht_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (c : Ctx) (Inv : β → W → Prop)
    (hf : ∀ b a w, Inv b w → WriterWP (f b a) c w (fun r v => Inv r v ∧ HtLe w v)) :
    ∀ (init : β) (w : W), Inv init w → WriterWP (xs.foldlM f init) c w (fun r v => Inv r v ∧ HtLe w v) := by
  induction xs with
  | nil =>
    intro init w h0
    simp only [List.foldlM_nil, writerWP_pure]
    exact ⟨h0, HtLe.refl w⟩
  | cons a xs ih =>
    intro init w h0
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a w h0) ?_
    rintro b v ⟨hb, hle⟩
    exact writerWP_mono (ih b v hb) (fun r u h => ⟨h.1, hle.trans h.2⟩)

/-- The descent to the root of the tree of segment `segment` on the key's path:
it ends at the path's last node, and the path's nodes are not taken back. -/
theorem ht_descendToSegmentRoot (B : NodeId) (key : Key) (segment : Nat)
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hkw : ViewKlongsWf c.p c.view) (hwf : WriterKlongsWf w) :
    WriterWP (descendToSegmentRoot key segment) c w (fun r v => Book B c v ∧ HtInv H B c v ∧
      HtLe w v ∧ HtPathLast v r ∧ PathFreeTo v v.path.length ∧ WriterKlongsWf v) := by
  unfold descendToSegmentRoot
  htSimp
  refine writerWP_mono (writerWP_and (ht_pathClear B c w hvo hb hi) (klongsWf_pathClear c w hkw hwf)) ?_
  rintro _ w1 ⟨⟨hb1, hi1, hk1, hp1, ht1⟩, hwf1⟩
  refine writerWP_mono (writerWP_and (ht_findRoot B c w1 hvo hb1 hi1 hp1)
    (klongsWf_findRoot c w1 hkw hwf1)) ?_
  rintro root w2 ⟨⟨hb2, hi2, hk2, hp2, ht2, hpf2⟩, hwf2⟩
  refine writerWP_mono (ht_foldlM _ _ c (fun node v => Book B c v ∧ HtInv H B c v ∧
      HtPathLast v node ∧ PathFreeTo v v.path.length ∧ WriterKlongsWf v)
    ?_ root w2 ⟨hb2, hi2, ⟨none, by rw [hp2]; rfl⟩, by rw [hp2]; exact hpf2, hwf2⟩) ?_
  · intro node cv u ⟨hbu, hiu, hlu, hpfu, hwfu⟩
    htSimp
    refine writerWP_mono (writerWP_and (ht_descendLte B cv c.p.fuel node c u hvo hbu hiu hpfu
      (Or.inl hlu)) (klongsWf_descendLte cv c.p.fuel node c u hkw hwfu)) ?_
    rintro leaf u1 ⟨⟨hb3, hi3, hle3, hlast, -, hpf3⟩, hwf3⟩
    have hl3 : HtPathLast u1 leaf := by
      rcases hlast with h | ⟨rfl, hp, -⟩
      · exact h
      · obtain ⟨a, ha⟩ := hlu
        exact ⟨a, by rw [hp]; exact ha⟩
    refine writerWP_mono (writerWP_and (hw_getNode B leaf c u1 hvo hb3 hi3)
      (klongsWf_getNode leaf c u1 hkw hwf3)) ?_
    rintro n u2 ⟨⟨hb4, hi4, hle4, hl4, hp4⟩, hwf4, hnwf⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i fd hfd
      obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb4 hl4
      obtain ⟨a, ha⟩ := hl3
      have ha4 : u2.path[u2.path.length - 1]? = some (a, leaf) := by rw [hp4]; exact ha
      have hL : 0 < u2.path.length := by
        have := (List.getElem?_eq_some_iff.mp ha4).1; omega
      have hpf4 : PathFreeTo u2 u2.path.length := by
        rw [hp4]; exact ht_pf_le hpf3 hp4 hle4 (Nat.le_refl _)
      have hlf : u2.taken.contains leaf = false := hpf4 _ a leaf (by omega) ha4
      have hN := ht_cache_at hl4 hi4 hm hlf (HtLe.refl _)
      htSimp
      refine writerWP_mono (writerWP_and (ht_pathAdd B fd.c fd.y c u2 hvo hb4 hi4 a leaf n
        (ht_getLast_of ha4) hl4 cv (ht_searchEq_live hnwf hN.3 hfd) hlf)
        (klongsWf_pathAdd (some fd.c) fd.y c u2 hkw hwf4)) ?_
      rintro _ u3 ⟨⟨hb5, hi5, hk5, hp5, ht5, hyf⟩, hwf5⟩
      exact ⟨⟨hb5, hi5, ⟨some fd.c, by rw [hp5]; exact kd_pathLast_append _ _⟩,
        PathFreeTo.append hpf4 _ hp5 ht5 hyf, hwf5⟩,
        hle3.trans (hle4.trans ⟨hk5, ht5⟩)⟩
  · rintro r v ⟨⟨hb3, hi3, hl3, hpf3, hwf3⟩, hle3⟩
    exact ⟨hb3, hi3, HtLe.trans ⟨hk1, ht1⟩ (HtLe.trans ⟨hk2, ht2⟩ hle3), hl3, hpf3, hwf3⟩

/-- The descent by height from x, the path's last node. -/
theorem ht_descendHeight (B : NodeId) (cv h fuel : Nat) :
    ∀ (x : NodeId) (c : Ctx) (w : W), ViewHtOK H B c → Book B c w → HtInv H B c w →
      HtPathLast w x → PathFreeTo w w.path.length →
      WriterWP (descendHeight cv h fuel x) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧
        HtLe w v ∧ PathFreeTo v v.path.length) := by
  induction fuel with
  | zero => intro x c w _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hvo hb hi ⟨a, ha⟩ hpf
    unfold descendHeight
    htSimp
    refine writerWP_mono (hw_ghOf B x c w hvo hb hi) ?_
    rintro ⟨gx, hx⟩ w1 ⟨hb1, hi1, hle1, hp1, hm1, -⟩
    have hpf1 : PathFreeTo w1 w1.path.length := by
      rw [hp1]; exact ht_pf_le hpf hp1 hle1 (Nat.le_refl _)
    split
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1, hpf1⟩
    · htSimp
      refine writerWP_mono (hw_getNode B x c w1 hvo hb1 hi1) ?_
      rintro n w2 ⟨hb2, hi2, hle2, hl2, hp2⟩
      have hm2 := HtLe.gh' hm1 hle2
      have ha2 : w2.path[w2.path.length - 1]? = some (a, x) := by rw [hp2, hp1]; exact ha
      have hL : 0 < w2.path.length := by
        have := (List.getElem?_eq_some_iff.mp ha2).1; omega
      have hpf2 : PathFreeTo w2 w2.path.length := by
        rw [hp2]; exact ht_pf_le hpf1 hp2 hle2 (Nat.le_refl _)
      have hxf : w2.taken.contains x = false := hpf2 _ a x (by omega) ha2
      have hN := ht_cache_at hl2 hi2 hm2 hxf (HtLe.refl _)
      split
      · exact writerWP_throw _ _ _ _
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          htSimp
          refine writerWP_mono (ht_pathAdd B fd.c fd.y c w2 hvo hb2 hi2 a x n (ht_getLast_of ha2) hl2
            fd.c (ht_live_of_liveAt hN (KNode.searchLte_mem n c.i cv fd hfd)) hxf) ?_
          rintro _ w3 ⟨hb3, hi3, hk3, hp3, ht3, hyf⟩
          refine writerWP_mono (ih fd.y c w3 hvo hb3 hi3 ⟨some fd.c, by rw [hp3]; simp⟩
            (PathFreeTo.append hpf2 _ hp3 ht3 hyf)) ?_
          rintro _ v ⟨hb4, hi4, hle4, hpf4⟩
          exact ⟨hb4, hi4, hle1.trans (hle2.trans (HtLe.trans ⟨hk3, ht3⟩ hle4)), hpf4⟩

/-- The descent of the merges' loop: the path rebuilt, its nodes not taken back. -/
theorem ht_descendToHeight (B : NodeId) (key : Key) (g h : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w)
    (hkw : ViewKlongsWf c.p c.view) (hwf : WriterKlongsWf w) :
    WriterWP (descendToHeight key g h) c w (fun d v => Book B c v ∧ HtInv H B c v ∧
      HtLe w v ∧ PathFreeTo v v.path.length ∧ d = v.path.length - 1) := by
  unfold descendToHeight
  htSimp
  refine writerWP_mono (ht_descendToSegmentRoot B key g c w hvo hb hi hkw hwf) ?_
  rintro root w1 ⟨hb1, hi1, hle1, hl1, hpf1, -⟩
  split
  · exact writerWP_throw _ _ _ _
  · rename_i cv _
    rw [writerWP_bind]
    refine writerWP_mono (ht_descendHeight B cv h c.p.fuel root c w1 hvo hb1 hi1 hl1 hpf1) ?_
    rintro _ w2 ⟨hb2, hi2, hle2, hpf2⟩
    htSimp
    refine writerWP_mono (kd_pathSize c w2) ?_
    rintro sz w3 ⟨rfl, rfl⟩
    exact ⟨hb2, hi2, hle1.trans hle2, hpf2, rfl⟩

/-! ## The merge's parent -/

theorem ht_htd_facts {n : KNode} {t : Time}
    (htd : ((match n.ks.getLast? with
      | some (.del _) => true
      | _ => false) && n.lastTime == some t) = true) :
    ∃ old, n.ks.getLast? = some (.del old) ∧ n.lastTime = some t := ht_hasTransDel htd

theorem ht_flatAt_replaceKlong' {i : Time} {ks out : List Klong} {t cv : Nat} {y : NodeId}
    (hr : replaceKlong ks t cv y = .ok (some out)) (h : FlatAt i ks) : FlatAt i out :=
  flatAt_replaceKlong i ks out t cv y h hr

theorem ht_kdKs_replaceKlong' {P : Nat → NodeId → Prop} {ks out : List Klong} {t cv : Nat}
    {y : NodeId} (hr : replaceKlong ks t cv y = .ok (some out)) (hk : kdKs P ks) (hy : P cv y) :
    kdKs P out := kdKs_replaceKlong hr hk hy

/-- A last version given the delete of cR, or of nothing. -/
theorem htKs_lastVersion_ite {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n)
    (t : Time) (cR : Nat) (b : Prop) [Decidable b] :
    kdKs (HtP c H w h)
      (n.lastVersionGivenDel t (if b then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap)).ks := by
  by_cases hb : b
  · rw [if_pos hb]; exact htKs_lastVersion_del hn t cR
  · rw [if_neg hb]; exact htKs_lastVersion hn t

syntax "htFlatMP" : tactic
macro_rules
  | `(tactic| htFlatMP) => `(tactic| first
    | ((with_unfolding_none guard_target = FlatAt _ (KNode.lastVersionGivenDel _ _ _).ks)
       exact KNode.lastVersionGivenDel_flatAt _ _ _)
    | ((with_unfolding_none guard_target = FlatAt _ (insertSorted _ _ _))
       exact flatAt_insertSorted _ _ _ _ (by htFlatMP))
    | exact ht_flatAt_replaceKlong' (by assumption) (by htFlatMP))

/-- Klongs of the right height for a last version of the merge's parent, with
the pointers m1 and m2's of the right height. -/
syntax "htKsMP " term:max term:max : tactic
macro_rules
  | `(tactic| htKsMP $h1 $h2) => `(tactic| first
    | ((with_unfolding_none guard_target = kdKs _ (KNode.lastVersionGivenDel _ _ (bitsUnion _ _)).ks)
       exact htKs_mono (htKs_lastVersion_del (by assumption) _ _) (by htChain))
    | ((with_unfolding_none guard_target = kdKs _ (KNode.lastVersionGivenDel _ _ (ite _ _ _)).ks)
       exact htKs_mono (htKs_lastVersion_ite (by assumption) _ _ _) (by htChain))
    | ((with_unfolding_none guard_target = kdKs _ (KNode.lastVersionGivenDel _ _ (KNode.lastBitmap _)).ks)
       exact htKs_mono (htKs_lastVersion (by assumption) _) (by htChain))
    | ((with_unfolding_none guard_target = kdKs _ (insertSorted _ _ _))
       exact kdKs_insertSorted _ (by htKsMP $h1 $h2) ($h2 _ _ (by first | assumption | rfl) _))
    | exact ht_kdKs_replaceKlong' (by assumption) (by htKsMP $h1 $h2) ($h1 _)
    | exact ht_kdKs_replaceKlong' (by assumption) (by htKsMP $h1 $h2) ($h2 _ _ (by first | assumption | rfl) _))

/-- The klongs of the parent's last version in the merge: from the last version
given the right child's delete or not, the left klong replaced, the right one
inserted or replaced. -/
syntax "htKsBase" : tactic
macro_rules
  | `(tactic| htKsBase) => `(tactic| first
    | exact htKs_mono (htKs_lastVersion_ite (by assumption) _ _ _) (by htChain)
    | exact htKs_mono (htKs_lastVersion_del (by assumption) _ _) (by htChain)
    | exact htKs_mono (htKs_lastVersion (by assumption) _) (by htChain))

syntax "htKsMP2 " term:max term:max : tactic
macro_rules
  | `(tactic| htKsMP2 $h1 $h2) => `(tactic| first
    | exact kdKs_insertSorted _ (ht_kdKs_replaceKlong' (by assumption) (by htKsBase) ($h1 _))
        ($h2 _ _ rfl _)
    | exact ht_kdKs_replaceKlong' (by assumption)
        (ht_kdKs_replaceKlong' (by assumption) (by htKsBase) ($h1 _)) ($h2 _ _ rfl _)
    | exact ht_kdKs_replaceKlong' (by assumption) (by htKsBase) ($h1 _))

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 20000 in
/-- The parent p of a merge, the path's node at depth, gets klongs that name m1
and m2, nodes of the right height for it. -/
theorem ht_mergeParent (B : NodeId) (p : NodeId) (depth il cL : Nat)
    (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat))
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (a : Option Nat) (hpx : w.path[depth]? = some (a, p))
    (hpf : PathFreeTo w (depth + 1)) (gp hp : Nat) (hx : (p, gp, hp) ∈ w.gh)
    (hm1 : ∀ cv, HtP c H w hp cv m1) (hm2 : ∀ y g, m2 = some (y, g) → ∀ cv, HtP c H w hp cv y) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
  have hxf : w.taken.contains p = false := hpf depth a p (by omega) hpx
  unfold mergeParent
  htSimp
  refine writerWP_mono (hw_getNode B p c w hvo hb hi) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
  have hx1 := HtLe.gh' hx hle1
  have hN := ht_cache_at hl1 hi1 hx1 (ht_free_le hxf hle1) (HtLe.refl _)
  have hm1' : ∀ cv, HtP c H w1 hp cv m1 := fun cv => (hm1 cv).mono hle1
  have hm2' : ∀ y g, m2 = some (y, g) → ∀ cv, HtP c H w1 hp cv y :=
    fun y g h cv => (hm2 y g h cv).mono hle1
  have hpx1 : w1.path[depth]? = some (a, p) := by rw [hp1]; exact hpx
  have hpf1 : PathFreeTo w1 (depth + 1) := ht_pf_le hpf hp1 hle1 (Nat.le_refl _)
  have hNmp : ∀ htd lip rip, (htd = true → ∃ old, pn.ks.getLast? = some (.del old) ∧
      pn.lastTime = some c.i) →
      NodeHt c H w1 hp (mpNode pn c.i il cL m1 ir cR m2 htd lip rip) :=
    fun htd lip rip h => nodeHt_mpNode hpos hN il cL m1 ir cR m2 htd lip rip h hm1' hm2'
  have hfullP : ∀ (v : W) (last : KNode) (cp : Bool), Book B c v → HtInv H B c v → HtLe w1 v →
      v.path = w1.path → FlatAt c.i last.ks → kdKs (HtP c H v hp) last.ks →
      WriterWP (handleFull depth p last cp) c v
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
    intro v last cp hbv hiv hlev hpv hfl hks
    refine writerWP_mono (ht_handleFull B depth p last cp c v hvo hpos hbv hiv gp hp
      (HtLe.gh' hx1 hlev) a (by rw [hpv]; exact hpx1) (ht_pf_le hpf1 hpv hlev (Nat.le_refl _))
      hfl hks) ?_
    rintro _ u ⟨hb2, hi2, hle2, hp2⟩
    exact ⟨hb2, hi2, hle1.trans (hlev.trans hle2), hp2.trans (hpv.trans hp1)⟩
  have hm1v : ∀ v, HtLe w1 v → ∀ cv, HtP c H v hp cv m1 := fun v h cv => (hm1' cv).mono h
  have hm2v : ∀ v, HtLe w1 v → ∀ y g, m2 = some (y, g) → ∀ cv, HtP c H v hp cv y :=
    fun v h y g hy cv => (hm2' y g hy cv).mono h
  have hleafP : ∀ (last : KNode) (cp : Bool) (s : String), FlatAt c.i last.ks →
      (∀ v, HtLe w1 v → kdKs (HtP c H v hp) last.ks) →
      WriterWP (note s) c w1 (fun _ w' => WriterWP (handleFull depth p last cp) c w'
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path)) := by
    intro last cp s hfl hks
    refine writerWP_mono (hw_keeps B (ht_note B s) c w1 hvo hb1 hi1) ?_
    rintro _ v ⟨hbv, hiv, hlev, hpv⟩
    exact hfullP v last cp hbv hiv hlev hpv hfl (hks v hlev)
  wpSplit
  · rename_i hsz
    clear hsz
    wpSplit
    · rename_i hdead
      clear hdead
      repeat' first
        | htSimp
        | exact writerWP_throw _ _ _ _
        | ((with_unfolding_none guard_target = WriterWP (note _) _ _ _)
           refine writerWP_mono (hw_keeps B (ht_note B _) c w1 hvo hb1 hi1) ?_
           rintro _ v ⟨hbv, hiv, hlev, hpv⟩)
        | ((with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
           refine hfullP _ _ _ (by assumption) (by assumption) (by assumption) (by assumption) ?_ ?_
           · dsimp only
             htFlatMP
           · dsimp only
             htKsMP2 (hm1v _ (by assumption)) (hm2v _ (by assumption)))
        | split
        | contradiction
    · refine ht_seq_note B _ _ c w1 hvo hb1 hi1 _ (fun v hbv hiv hlev hpv => ?_)
      refine writerWP_mono (ht_putNode_of B p _ c w1 w1 v pn hbv hiv hl1 hlev ?_ gp hp hx1 hlev
        ((hNmp _ _ _ ?_).htMono hlev)) ?_
      · first | bkLeaf | (repeat' split) <;> bkLeaf
      · intro htd
        revert htd
        cases hg : pn.ks.getLast? with
        | none => simp
        | some k =>
          cases k with
          | del b =>
            simp only [Bool.true_and, beq_iff_eq]
            exact fun h => ⟨b, rfl, h⟩
          | time u => simp
          | key a y => simp
      · rintro _ u ⟨hb2, hi2, hle2, hp2, -⟩
        exact ⟨hb2, hi2, hle1.trans (hlev.trans hle2), hp2.trans (hpv.trans hp1)⟩
  · rename_i hsz
    clear hsz
    repeat' first
      | htSimp
      | exact writerWP_throw _ _ _ _
      | ((with_unfolding_none guard_target = WriterWP (note _) _ _ _)
         refine writerWP_mono (hw_keeps B (ht_note B _) c w1 hvo hb1 hi1) ?_
         rintro _ v ⟨hbv, hiv, hlev, hpv⟩)
      | ((with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
         refine hfullP _ _ _ (by assumption) (by assumption) (by assumption) (by assumption) ?_ ?_
         · dsimp only
           htFlatMP
         · dsimp only
           htKsMP2 (hm1v _ (by assumption)) (hm2v _ (by assumption)))
      | split
      | contradiction

end SIS.Tree
