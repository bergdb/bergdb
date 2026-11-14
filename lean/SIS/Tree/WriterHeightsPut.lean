/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)),
continued: the descent and a put (`descendLte`, `setValue`, `setNode`,
`putSegs`, `putKv` of a put).
-/
import SIS.Tree.WriterHeightsFull
import SIS.Tree.WriterKindsRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

variable {H : NodeId → Nat → Prop}

/-- x is the key access path's last node. -/
def HtPathLast (w : W) (x : NodeId) : Prop := ∃ a, w.path[w.path.length - 1]? = some (a, x)

theorem ht_getLast_of {w : W} {a : Option Nat} {x : NodeId}
    (h : w.path[w.path.length - 1]? = some (a, x)) : w.path.getLast? = some (a, x) := by
  rw [List.getLast?_eq_getElem?]; exact h

/-- A live klong at the transaction's time of a node of the right times. -/
theorem ht_live_of_liveAt {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n)
    {cv : Nat} {y : NodeId} (hy : (cv, y) ∈ n.liveAt c.i) : (cv, y) ∈ n.live := by
  rw [KNode.liveAt_of_times n c.i hn.3] at hy
  exact hy

/-- The descent by `searchLte` from x, the path's last node or an empty
segment leaf off the path: it stops at a segment leaf, the path's last node
(or x itself, the empty leaf, with the path as it was). -/
theorem ht_descendLte (B : NodeId) (cv fuel : Nat) :
    ∀ (x : NodeId) (c : Ctx) (w : W), ViewHtOK H B c → Book B c w → HtInv H B c w →
      PathFreeTo w w.path.length →
      (HtPathLast w x ∨ w.nodes.lookup x = some ⟨true, []⟩) →
      WriterWP (descendLte cv fuel x) c w (fun r v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
        (HtPathLast v r ∨ (r = x ∧ v.path = w.path ∧ v.nodes.lookup r = some ⟨true, []⟩)) ∧
        (∃ n, v.nodes.lookup r = some n ∧ n.leaf = true) ∧ PathFreeTo v v.path.length) := by
  induction fuel with
  | zero => intro x c w _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hvo hb hi hpf hx
    unfold descendLte
    htSimp
    rcases hx with ⟨a, ha⟩ | he
    · have hL : 0 < w.path.length := by
        have := (List.getElem?_eq_some_iff.mp ha).1; omega
      have hxf : w.taken.contains x = false := hpf _ a x (by omega) ha
      refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
      rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
      split
      · rename_i hleaf
        rw [writerWP_pure]
        exact ⟨hb1, hi1, hle1, Or.inl ⟨a, by rw [hp1]; exact ha⟩, ⟨n, hl1, hleaf⟩,
          by rw [hp1]; exact ht_pf_le hpf hp1 hle1 (Nat.le_refl _)⟩
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb1 hl1
          have hN := ht_cache_at hl1 hi1 hm (ht_free_le hxf hle1) (HtLe.refl _)
          have ha1 : w1.path.getLast? = some (a, x) := by
            rw [hp1]; exact ht_getLast_of ha
          htSimp
          have hpf1 : PathFreeTo w1 w1.path.length := by
            rw [hp1]; exact ht_pf_le hpf hp1 hle1 (Nat.le_refl _)
          refine writerWP_mono (ht_pathAdd B fd.c fd.y c w1 hvo hb1 hi1 a x n ha1 hl1 fd.c
            (ht_live_of_liveAt hN (KNode.searchLte_mem n c.i cv fd hfd))
            (ht_free_le hxf hle1)) ?_
          rintro _ w2 ⟨hb2, hi2, hk2, hp2, ht2, hyf⟩
          refine writerWP_mono (ih fd.y c w2 hvo hb2 hi2
            (PathFreeTo.append hpf1 _ hp2 ht2 hyf) (Or.inl ⟨some fd.c, ?_⟩)) ?_
          · rw [hp2]
            simp
          · rintro r v ⟨hb3, hi3, hle3, hlast, hleaf3, hpf3⟩
            refine ⟨hb3, hi3, hle1.trans (HtLe.trans ⟨hk2, ht2⟩ hle3), ?_, hleaf3, hpf3⟩
            rcases hlast with hlast | ⟨rfl, hp3, -⟩
            · exact Or.inl hlast
            · left
              refine ⟨some fd.c, ?_⟩
              rw [hp3, hp2]
              simp
    · refine writerWP_mono (kd_getNode_hit x _ c w he) ?_
      rintro n w1 ⟨rfl, rfl⟩
      simp only [↓reduceIte, writerWP_pure]
      exact ⟨hb, hi, HtLe.refl _, Or.inr ⟨by trivial, by trivial, he⟩, ⟨_, he, rfl⟩, hpf⟩

/-- A node's last stored version with a key klong added at the transaction's time. -/
theorem nodeHt_add {c : Ctx} {w : W} {h : Nat} {n : KNode} (hpos : 0 < c.i)
    (hn : NodeHt c H w h n) {cv : Nat} {y : NodeId} (hy : HtP c H w h cv y) :
    NodeHt c H w h (n.add c.i (.key cv y)) :=
  nodeHt_addFold hpos hn [(cv, y)] (kdPairs_cons hy kdPairs_nil')

theorem ht_P_val {c : Ctx} {w : W} {y : NodeId} {cv : Nat} (hy : w.taken.contains y = false) :
    HtP c H w 0 cv y := ⟨hy, fun h0 => absurd rfl h0⟩

set_option maxHeartbeats 1600000 in
/-- `setValue` of a put from segRoot, the path's last node, or an empty
segment leaf off the path. -/
theorem ht_setValue_put (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (hv0 : Nat)
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (hM : 2 ≤ c.p.M) (hpf : PathFreeTo w w.path.length)
    (hr : HtPathLast w segRoot ∨ w.nodes.lookup segRoot = some ⟨true, []⟩) :
    WriterWP (setValue segRoot cv key (some hv0)) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v) := by
  unfold setValue
  htSimp
  refine writerWP_mono (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf hr) ?_
  rintro leaf w1 ⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, hleaf0⟩, hpf1⟩
  obtain ⟨g, hh, hm⟩ := kd_tag_of_lookup hb1 hl0
  have hh0 : hh = 0 := kd_h0 hb1 hl0 hm hleaf0
  subst hh0
  try htSimp
  refine writerWP_mono (writerWP_and (ht_newValue B hv0 c w1 hvo hb1 hi1)
    (kd_newValue_nodes hv0 c w1)) ?_
  rintro y w2 ⟨⟨hb2, hi2, hk2, hp2, ht2, hy2⟩, hn2, -⟩
  have hle2 : HtLe w1 w2 := ⟨hk2, ht2⟩
  have hyf : w2.taken.contains y = false := by
    rw [ht2, hy2]; exact ht_free_of_fresh B hb1 (kd_next_not hb1)
  have hm2 := HtLe.gh' hm hle2
  rcases hlast with ⟨a, ha⟩ | ⟨rfl, hp1, he⟩
  · have hxf : w1.taken.contains leaf = false := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      exact hpf1 _ a leaf (by omega) ha
    refine writerWP_mono (hw_getNode B leaf c w2 hvo hb2 hi2) ?_
    rintro n w3 ⟨hb3, hi3, hle3, hl3, hp3⟩
    have hm3 := HtLe.gh' hm2 hle3
    have hN := ht_cache_at hl3 hi3 hm3 (ht_free_le (ht_free_le hxf hle2) hle3) (HtLe.refl _)
    have hyf3 := ht_free_le hyf hle3
    split
    · htSimp
      refine writerWP_mono (ht_putNode_of B leaf _ c w3 w3 w3 n hb3 hi3 hl3 (HtLe.refl _)
        (KNode.add_leaf _ _ _) g 0 hm3 (HtLe.refl _) (nodeHt_add hpos hN (ht_P_val hyf3))) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, -⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4))⟩
    · htSimp
      refine writerWP_mono (kd_pathSize c w3) ?_
      rintro sz w4 ⟨hw, hsz⟩
      rw [hw, hsz]
      have hL3 : 0 < w3.path.length := by
        rw [hp3, hp2]; have := (List.getElem?_eq_some_iff.mp ha).1; omega
      refine writerWP_mono (ht_appendKlongs B _ leaf [(cv, y)] c w3 hvo hpos hb3 hi3
        ⟨g, 0, hm3, kdPairs_cons (ht_P_val hyf3) kdPairs_nil'⟩ ⟨a, by rw [hp3, hp2]; exact ha⟩
        (by
          rw [hp3, hp2] at hL3 ⊢
          rw [show w1.path.length - 1 + 1 = w1.path.length by omega]
          exact ht_pf_le hpf1 (hp3.trans hp2) (hle2.trans hle3) (Nat.le_refl _))) ?_
      rintro _ w5 ⟨hb5, hi5, hle5, -⟩
      exact ⟨hb5, hi5, hle1.trans (hle2.trans (hle3.trans hle5))⟩
  · have he2 : w2.nodes.lookup leaf = some ⟨true, []⟩ := by rw [hn2]; exact he
    refine writerWP_mono (kd_getNode_hit leaf _ c w2 he2) ?_
    rintro n w3 ⟨hn3, hw3⟩
    rw [hn3, hw3]
    split
    · htSimp
      refine writerWP_mono (ht_putNode_of B leaf _ c w2 w2 w2 _ hb2 hi2 he2 (HtLe.refl _)
        (KNode.add_leaf _ _ _) g 0 hm2 (HtLe.refl _)
        (nodeHt_add hpos (nodeHt_nil c w2 0 true) (ht_P_val hyf))) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, -⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans hle4)⟩
    · rename_i hfull
      exact absurd (kd_empty_ok c.p hM c.i cv y) hfull

/-- Every node of the key access path is a key node of the overlay when its
last node is. -/
theorem ht_path_in_gh {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W} (hi : HtInv H B c w) {x : NodeId}
    (hpl : HtPathLast w x) (hx : x ∈ w.gh.map (·.1)) : ∀ e ∈ w.path, e.2 ∈ w.gh.map (·.1) := by
  intro e he
  obtain ⟨d, hd⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨a, ha⟩ := hpl
  have hlt := (List.getElem?_eq_some_iff.mp hd).1
  by_cases hd1 : d + 1 < w.path.length
  · obtain ⟨a', q⟩ := e
    exact hi.pathGh d a' q hd hd1
  · have : d = w.path.length - 1 := by omega
    subst this
    rw [ha] at hd
    cases hd
    exact hx

/-- A search for a compare value finds a live klong of a well formed node. -/
theorem ht_searchEq_live {n : KNode} {t : Time} {cv : Nat} {fd : Found}
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (h : n.searchEq t cv = some fd) : (cv, fd.y) ∈ n.live := by
  have := KNode.searchEq_live n t hw ht cv
  rw [h] at this
  exact bk_mem_of_lookup _ cv fd.y this.symm

set_option maxHeartbeats 1600000 in
/-- `setNode` of a put from segRoot, the path's last node, or an empty segment
leaf off the path: the tree of the next segment, the path's last node, or a new
empty segment leaf off the path. -/
theorem ht_setNode_put (B : NodeId) (hframe : AppendFrameOK B) (segRoot : NodeId)
    (cv : Nat) (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (hM : 2 ≤ c.p.M) (hkw : ViewKlongsWf c.p c.view) (hwf : WriterKlongsWf w)
    (hpf : PathFreeTo w w.path.length)
    (hr : HtPathLast w segRoot ∨ w.nodes.lookup segRoot = some ⟨true, []⟩) :
    WriterWP (setNode segRoot cv true) c w (fun r v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      PathFreeTo v v.path.length ∧
      ∀ y, r = some y → HtPathLast v y ∨ v.nodes.lookup y = some ⟨true, []⟩) := by
  unfold setNode
  htSimp
  refine writerWP_mono (writerWP_and (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf hr)
    (klongsWf_descendLte cv c.p.fuel segRoot c w hkw hwf)) ?_
  rintro cur w1 ⟨⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, hleaf0⟩, hpf1⟩, hwf1⟩
  obtain ⟨g, hh, hm⟩ := kd_tag_of_lookup hb1 hl0
  have hh0 : hh = 0 := kd_h0 hb1 hl0 hm hleaf0
  subst hh0
  have hcase : HtPathLast w1 cur ∨ n0 = ⟨true, []⟩ := by
    rcases hlast with h1 | ⟨hcr, hp, he⟩
    · exact Or.inl h1
    · subst hcr
      rcases hr with ⟨a, ha⟩ | -
      · exact Or.inl ⟨a, by rw [hp]; exact ha⟩
      · right
        rw [hl0] at he
        exact Option.some.inj he
  have hN0 : NodeHt c H w1 0 n0 := by
    rcases hcase with ⟨a, ha⟩ | rfl
    · have := (List.getElem?_eq_some_iff.mp ha).1
      exact ht_cache_at hl0 hi1 hm (hpf1 _ a cur (by omega) ha) (HtLe.refl _)
    · exact nodeHt_nil c w1 0 true
  refine writerWP_mono (kd_getNode_hit cur n0 c w1 hl0) ?_
  rintro n w2 ⟨hn, hw⟩
  rw [hn, hw]
  split
  · rename_i fd hfd
    rcases hcase with ⟨a, ha⟩ | hn0
    · htSimp
      have hcf : w1.taken.contains cur = false := by
        have := (List.getElem?_eq_some_iff.mp ha).1
        exact hpf1 _ a cur (by omega) ha
      refine writerWP_mono (ht_pathAdd B fd.c fd.y c w1 hvo hb1 hi1 a cur n0 (ht_getLast_of ha) hl0
        cv (ht_searchEq_live (writerKlongsWf_lookup w1 hwf1 cur n0 hl0) hN0.3 hfd) hcf) ?_
      rintro _ w3 ⟨hb3, hi3, hk3, hp3, ht3, hyf⟩
      refine ⟨hb3, hi3, hle1.trans ⟨hk3, ht3⟩, PathFreeTo.append hpf1 _ hp3 ht3 hyf, ?_⟩
      intro y hy
      cases hy
      left
      exact ⟨some fd.c, by rw [hp3]; exact kd_pathLast_append _ _⟩
    · subst hn0
      rw [nex_run_searchEq_nil _ _ _ rfl] at hfd
      cases hfd
  · split
    · rename_i hcr
      simp at hcr
    · htSimp
      refine writerWP_mono (hw_ghOf B cur c w1 hvo hb1 hi1) ?_
      rintro ⟨g', h'⟩ w3 ⟨hb3, hi3, hle3, hp3, hm3, -⟩
      obtain ⟨hg', hh'⟩ := kd_tag_eq hb3 (HtLe.gh' hm hle3) hm3
      subst hg'
      subst hh'
      htSimp
      refine writerWP_mono (hw_keeps B (ht_note B _) c w3 hvo hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4⟩
      have hcg4 : cur ∈ w4.gh.map (·.1) := kd_mem_ids (HtLe.gh' hm (hle3.trans hle4))
      refine writerWP_mono (hw_newKey B (g + 1) 0 true [] c w4 hb4 hi4 rfl
        (nodeHt_nil c w4 0 true)) ?_
      rintro child w5 ⟨hb5, hi5, hle5, hp5, hlc, hmc, hcf, hcx⟩
      have hcur : cur ≠ child := fun h => hcx (h ▸ hcg4)
      have hle15 : HtLe w1 w5 := hle3.trans (hle4.trans hle5)
      obtain ⟨n5, hl5, hlf5⟩ := hle15.1.1 cur n0 hl0
      have hm5 := HtLe.gh' hm hle15
      have hcf5 : HtP c H w5 0 cv child := ht_P_val hcf
      split
      · htSimp
        refine writerWP_mono (writerWP_and (ht_putNode_of B cur _ c w1 w1 w5 n0 hb5 hi5 hl0 hle15
          (KNode.add_leaf _ _ _) g 0 hm hle15 (nodeHt_add hpos (hN0.htMono hle15) hcf5))
          (kd_putNode_other cur _ n5 c w5 hl5)) ?_
        rintro _ w6 ⟨⟨hb6, hi6, hle6, hp6, -⟩, hoth⟩
        refine ⟨hb6, hi6, hle1.trans (hle15.trans hle6), ?_, ?_⟩
        · have hp61 : w6.path = w1.path := hp6.trans (hp5.trans (hp4.trans hp3))
          rw [hp61]
          exact ht_pf_le hpf1 hp61 (hle15.trans hle6) (Nat.le_refl _)
        intro y hy
        cases hy
        right
        rw [hoth child (Ne.symm hcur)]
        exact hlc
      · rename_i hfull
        have hpl : HtPathLast w1 cur := by
          rcases hcase with h1 | hn0
          · exact h1
          · subst hn0
            exact absurd (kd_empty_lt c.p hM) hfull
        obtain ⟨a, ha⟩ := hpl
        have hpw : w5.path = w1.path := hp5.trans (hp4.trans hp3)
        have hpath : ∀ e ∈ w5.path, e.2 ≠ child := by
          intro e he
          rw [hpw] at he
          have := ht_path_in_gh hi1 ⟨a, ha⟩ (kd_mem_ids hm) e he
          intro hce
          apply hcx
          rw [← hce]
          obtain ⟨q, hq, hqe⟩ := List.mem_map.mp this
          exact List.mem_map.mpr ⟨q, HtLe.gh' hq (hle3.trans hle4), hqe⟩
        htSimp
        refine writerWP_mono (kd_pathSize c w5) ?_
        rintro sz w6 ⟨hw6, hsz⟩
        rw [hw6, hsz]
        have hL1 : 0 < w1.path.length := by
          have := (List.getElem?_eq_some_iff.mp ha).1; omega
        have hpf5 : PathFreeTo w5 (w1.path.length - 1 + 1) := by
          rw [show w1.path.length - 1 + 1 = w1.path.length by omega]
          exact ht_pf_le hpf1 hpw hle15 (Nat.le_refl _)
        refine writerWP_mono (writerWP_and (ht_appendKlongs B _ cur [(cv, child)] c w5 hvo hpos hb5 hi5
          ⟨g, 0, hm5, kdPairs_cons hcf5 kdPairs_nil'⟩ ⟨a, by rw [hpw]; exact ha⟩
          (by rw [hpw]; exact hpf5))
          (hframe _ cur [(cv, child)] c w5 child hvo.ids hb5 hlc (Ne.symm hcur) hpath)) ?_
        rintro _ w7 ⟨⟨hb7, hi7, hle7, hp7⟩, hlc7⟩
        have hp71 : w7.path = w1.path := hp7.trans hpw
        refine ⟨hb7, hi7, hle1.trans (hle15.trans hle7), ?_, fun y hy => by
          cases hy; exact Or.inr hlc7⟩
        rw [hp71]
        exact ht_pf_le hpf1 hp71 (hle15.trans hle7) (Nat.le_refl _)

/-- The loop of a put over the key's segments. -/
theorem ht_putSegs_put (B : NodeId) (hframe : AppendFrameOK B) (key : Key) (hv0 : Nat)
    (segs : List Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i → Book B c w → HtInv H B c w →
      2 ≤ c.p.M → ViewKlongsWf c.p c.view → WriterKlongsWf w → PathFreeTo w w.path.length →
      (HtPathLast w r ∨ w.nodes.lookup r = some ⟨true, []⟩) →
      WriterWP (putSegs key (some hv0) segs r) c w
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v) := by
  induction segs with
  | nil => intro r c w _ _ _ _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    intro r c w hvo hpos hb hi hM hkw hwf hpf hr
    cases rest with
    | nil =>
      unfold putSegs
      exact ht_setValue_put B r cv key hv0 c w hvo hpos hb hi hM hpf hr
    | cons d rest' =>
      unfold putSegs
      htSimp
      refine writerWP_mono (writerWP_and (ht_setNode_put B hframe r cv c w hvo hpos hb hi hM hkw hwf hpf hr)
        (klongsWf_setNode r cv true c w hkw hwf)) ?_
      rintro res w1 ⟨⟨hb1, hi1, hle1, hpf1, hres⟩, hwf1⟩
      split
      · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1⟩
      · rename_i next
        exact writerWP_mono (ih next c w1 hvo hpos hb1 hi1 hM hkw hwf1 hpf1 (hres next rfl))
          (fun _ u hu => ⟨hu.1, hu.2.1, hle1.trans hu.2.2⟩)

/-- A put keeps the heights. -/
theorem ht_putKv_put (B : NodeId) (hframe : AppendFrameOK B) (key : Key) (hv0 : Nat) (c : Ctx)
    (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w) (hi : HtInv H B c w)
    (hM : 2 ≤ c.p.M) (hkw : ViewKlongsWf c.p c.view) (hwf : WriterKlongsWf w) :
    WriterWP (putKv (.put key hv0)) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v) := by
  unfold putKv
  htSimp
  refine writerWP_mono (writerWP_and (ht_pathClear B c w hvo hb hi) (klongsWf_pathClear c w hkw hwf)) ?_
  rintro _ w1 ⟨⟨hb1, hi1, hk1, hp1, ht1⟩, hwf1⟩
  refine writerWP_mono (writerWP_and (ht_findRoot B c w1 hvo hb1 hi1 hp1)
    (klongsWf_findRoot c w1 hkw hwf1)) ?_
  rintro root w2 ⟨⟨hb2, hi2, hk2, hp2, ht2, hpf2⟩, hwf2⟩
  have hl : HtPathLast w2 root := ⟨none, by rw [hp2]; rfl⟩
  exact writerWP_mono (ht_putSegs_put B hframe key hv0 key root c w2 hvo hpos hb2 hi2 hM hkw hwf2
    (by rw [hp2]; exact hpf2) (Or.inl hl))
    (fun _ u hu => ⟨hu.1, hu.2.1, HtLe.trans ⟨hk1, ht1⟩ (HtLe.trans ⟨hk2, ht2⟩ hu.2.2)⟩)

end SIS.Tree
