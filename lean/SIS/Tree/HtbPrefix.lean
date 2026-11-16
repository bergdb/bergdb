/-
`htb`'s sites (bergdb 025-05, step 8): the delete's checked copy with any `afterDelete`
(`putKvDelChk2G`) keeps the heights' walk and the tall nodes' frame (`TallOK`), given
that its `afterDelete` does at a segment leaf. The upward loop takes back the emptied
nodes below the stop node: each has one live klong at the climb, or is the leaf, so
none is tall.
-/
import SIS.Tree.HtbFrame
import SIS.Tree.HtbDefs

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node all of whose key klongs a delete of compare value c deletes has at most one
live klong. -/
theorem KNode.cnt_le_one_of_allKeysIn (n : KNode) (c : Nat)
    (h : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf c)) = true) : n.cnt ≤ 1 := by
  have hs : ∀ a ∈ n.live.map Prod.fst, a ∈ [c] := by
    intro a ha
    obtain ⟨y, i, hm, hi⟩ := (n.live_has_key a).mp ha
    by_cases hac : a = c
    · simp [hac]
    · exfalso
      have h1 := KNode.not_mem_bitsOf_of_key_ne n a c y i hm hac
      have h2 : i ∉ bitsUnion n.lastBitmap (n.bitsOf c) := by
        rw [mem_bitsUnion_iff]; rintro (h3 | h3)
        · exact hi h3
        · exact h1 h3
      rw [KNode.allKeysIn_false_of_live_key n _ a y i hm h2] at h
      cases h
  have := n.live_keys_nodup.length_le_of_subset hs
  simpa [KNode.cnt] using this

theorem lookup_isSome_of_mem' {β : Type} (l : List (NodeId × β)) (a : NodeId) (b : β)
    (h : (a, b) ∈ l) : (l.lookup a).isSome = true := by
  induction l with
  | nil => cases h
  | cons q r ih =>
    rcases q with ⟨q1, q2⟩
    simp only [List.lookup]
    by_cases hq : a = q1
    · subst hq; simp
    · have : (a == q1) = false := by simpa using hq
      simp only [this]
      rcases List.mem_cons.mp h with h1 | h1
      · cases h1; exact absurd rfl hq
      · exact ih h1

section Prefix

variable {H : NodeId → Nat → Prop} {K : KindOracle} {base : View BVal} {T : NodeId → Prop}

/-- What the walk carries: the heights' walk, the books' relation to the start, and
the frame. -/
def HtbState (H : NodeId → Nat → Prop) (B : NodeId) (base : View BVal) (T : NodeId → Prop)
    (c : Ctx) (w v : W) : Prop :=
  Book B c v ∧ HtInv H B c v ∧ Kept w v ∧ WriterKlongsWf v ∧ TallOK base T c v

/-- `afterDelete`'s obligation: from a state of the walk, it keeps the walk. -/
def AdOK (H : NodeId → Nat → Prop) (B : NodeId) (base : View BVal) (T : NodeId → Prop)
    (ad : Key → Nat → Nat → M Unit) (c : Ctx) (w0 : W) : Prop :=
  ∀ key g v, HtbState H B base T c w0 v →
    WriterWP (ad key g 0) c v (fun _ v' => HtbState H B base T c v v')

theorem AdOK.mono {B : NodeId} {ad : Key → Nat → Nat → M Unit} {c : Ctx} {w0 w : W}
    (h : AdOK H B base T ad c w0) (hk : Kept w0 w) : AdOK H B base T ad c w := by
  intro key g v hv
  exact h key g v ⟨hv.1, hv.2.1, hk.trans hv.2.2.1, hv.2.2.2⟩

set_option maxHeartbeats 6400000 in
/-- The upward delete with any `afterDelete`. -/
theorem tk_deleteUpwardChk2G (B : NodeId) (ad : Key → Nat → Nat → M Unit) (leaf : NodeId)
    (depth cv : Nat) (key : Key) (c : Ctx)
    (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view)
    (hb : Book B c w) (hi : HtInv H B c w) (hwf : WriterKlongsWf w)
    (hpf : PathFreeTo w w.path.length) (hdepth : depth = w.path.length - 1)
    (hlast : HtPathLast w leaf) (n : KNode) (hn : w.nodes.lookup leaf = some n) (hleaf : n.leaf = true)
    (hk : ViewKinds K B c) (hki : KdInv K B w)
    (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base) (hT : TallOK base T c w)
    (hAd : AdOK H B base T ad c w) :
    WriterWP (deleteUpwardChk2G ad leaf depth cv key) c w (fun _ v => HtbState H B base T c w v) := by
  obtain ⟨a, ha⟩ := hlast
  rw [← hdepth] at ha
  have hlen : depth + 1 = w.path.length := by
    have := (List.getElem?_eq_some_iff.mp ha).1; omega
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
  -- the leaf is no tall node
  have hleafT : ¬ T leaf := by
    intro hTl
    obtain ⟨_, hun, m, hm, hml, _⟩ := hT leaf hTl
    have : wNode c.p base w leaf = some n := by
      unfold wNode; simp only [hun, Bool.false_eq_true, ↓reduceIte, hn]
    rw [this] at hm
    cases hm
    rw [hleaf] at hml
    cases hml
  -- the path's nodes, as the climb's facts take them
  let X : Nat → NodeId := fun i => ((w.path[i]?).map (·.2)).getD 0
  let Kc : Nat → Nat := fun i => match w.path[i]? with
    | some (some k, _) => k
    | _ => 0
  let Nn : Nat → KNode := fun i => (w.nodes.lookup (X i)).getD default
  have hX : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i) := by
    intro i hi'
    have hlt : i < w.path.length := by omega
    obtain ⟨e, he⟩ : ∃ e, w.path[i]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp [X, he]
  have hKc : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (Kc i), X i) := by
    intro i h0 hi'
    have hlt : i < w.path.length := by omega
    obtain ⟨⟨a', q⟩, he⟩ : ∃ e, w.path[i]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hsome := hi.pathSome (i - 1) a' q (by rw [show i - 1 + 1 = i by omega]; exact he)
    cases a' with
    | none => exact absurd rfl hsome
    | some k => simp [Kc, X, he]
  have hNn : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i) := by
    intro i hi'
    have hlt : i < w.path.length := by omega
    obtain ⟨⟨a', q⟩, he⟩ : ∃ e, w.path[i]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hq : X i = q := by simp [X, he]
    have hmem' : q ∈ w.nodes.map (·.1) := by
      rw [hb.ids]; exact List.mem_reverse.mpr (hall i a' q he)
    obtain ⟨⟨q', n'⟩, hq', he'⟩ := List.mem_map.mp hmem'
    simp only at he'
    subst he'
    have hsome : (w.nodes.lookup (X i)).isSome = true := by
      rw [hq]; exact lookup_isSome_of_mem' _ _ _ hq'
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
    simp [Nn, hm]
  have hwX : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := by
    intro i hi'
    have hfree : w.taken.contains (X i) = false := by
      obtain ⟨⟨a', q⟩, he⟩ : ∃ e, w.path[i]? = some e :=
        ⟨_, List.getElem?_eq_getElem (show i < w.path.length by omega)⟩
      have hq : X i = q := by simp [X, he]
      rw [hq]; exact hpf i a' q (by omega) he
    unfold wNode; simp only [hfree, Bool.false_eq_true, ↓reduceIte, hNn i hi']
  unfold deleteUpwardChk2G
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_getNode_hit leaf n c w hn) ?_
  rintro n' w' ⟨hn', hw'⟩
  subst n' w'
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · rw [writerWP_pure]; exact ⟨hb, hi, Kept.refl w, hwf, hT⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (writerWP_and (hw_ghOf B leaf c w hvo hb hi)
      (klongsWf_ghOf leaf c w hkw hwf)) (tk_ghOf leaf c w hmp hvc hT)) ?_
    rintro ⟨g, h⟩ w1 ⟨⟨⟨hb1, hi1, hle1, hp1, hm1, n1, hl1, hnl1⟩, hwf1⟩, hT1⟩
    have hh0 : h = 0 := by
      obtain ⟨n2, hl2, hl2'⟩ := hle1.1.lookup hn
      rw [hl1] at hl2
      cases hl2
      rw [hl2', hleaf] at hnl1
      cases h with
      | zero => rfl
      | succ k => simp at hnl1
    subst hh0
    refine writerWP_mono (writerWP_and (writerWP_and (ht_appendDeleteKlong B leaf depth cv c w1 hvo
      hpos hb1 hi1 g 0 hm1 a (by rw [hp1]; exact ha) (ht_pf_le hpf hp1 hle1 (by omega)))
      (klongsWf_appendDeleteKlong leaf depth cv c w1 hkw hwf1))
      (tk_appendDeleteKlong leaf depth cv c w1 hmp hvc hT1 hleafT)) ?_
    rintro _ w2 ⟨⟨⟨hb2, hi2, hle2, -⟩, hwf2⟩, hT2⟩
    refine writerWP_mono (hAd key g w2 ⟨hb2, hi2, (hle1.trans hle2).1, hwf2, hT2⟩) ?_
    rintro _ w3 ⟨hb3, hi3, hk3, hwf3, hT3⟩
    rw [writerWP_pure]
    exact ⟨hb3, hi3, (hle1.trans hle2).1.trans hk3, hwf3, hT3⟩
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (writerWP_and (ht_climb B depth c w hvo hb hi)
    (klongsWf_climb depth c w hkw hwf)) (writerWP_climb c X Nn Kc depth w hX hKc hNn)) ?_
  rintro stop w1 ⟨⟨⟨hb1, hi1, hle1, hp1, hstop⟩, hwf1⟩, hw1, -, hbetween, -, -, -⟩
  subst w1
  -- the nodes strictly between the stop node and the leaf have one live klong
  have hmidT : ∀ k, stop < k → k < depth → ¬ T (X k) := by
    intro k h1 h2
    exact hT.not_of (X k) (Nn k) (hwX k (by omega))
      (Or.inl (KNode.cnt_le_one_of_allKeysIn _ _ (hbetween k h1 h2)))
  have hXdepth : X depth = leaf := by
    have := hX depth (Nat.le_refl _); rw [ha] at this; exact (Option.some.inj this).symm
  have hchainT : ∀ k, stop < k → k ≤ depth → ¬ T (X k) := by
    intro k h1 h2
    by_cases hk' : k = depth
    · subst hk'; rw [hXdepth]; exact hleafT
    · exact hmidT k h1 (by omega)
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hne' => ?_)
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (writerWP_and (hw_keeps B (ht_note B _) c w hvo hb1 hi1)
      (klongsWf_note _ c w hkw hwf1)) (tk_note _ c w hmp hvc hT)) ?_
    rintro _ w2 ⟨⟨⟨hb2, hi2, hle2, hp2⟩, hwf2⟩, hT2⟩
    refine writerWP_mono (writerWP_and (writerWP_and (ht_appendDeleteKlong B leaf depth cv c w2 hvo
      hpos hb2 hi2 _ _ (HtLe.gh' (kd_tag_of_lookup hb hn).choose_spec.choose_spec (hle1.trans hle2))
      a (by rw [hp2, hp1]; exact ha) (ht_pf_le hpf (hp2.trans hp1) (hle1.trans hle2) (by omega)))
      (klongsWf_appendDeleteKlong leaf depth cv c w2 hkw hwf2))
      (tk_appendDeleteKlong leaf depth cv c w2 hmp hvc hT2 hleafT)) ?_
    rintro _ w3 ⟨⟨⟨hb3, hi3, hle3, -⟩, hwf3⟩, hT3⟩
    rw [writerWP_pure]
    exact ⟨hb3, hi3, (hle1.trans (hle2.trans hle3)).1, hwf3, hT3⟩
  have hsd : stop < depth := by
    have : stop ≠ depth := fun h => hne' (by simp [h])
    omega
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (writerWP_and (hw_keeps B (ht_note B _) c w hvo hb1 hi1)
    (klongsWf_note _ c w hkw hwf1)) (tk_note _ c w hmp hvc hT)) ?_
  rintro _ w2 ⟨⟨⟨hb2, hi2, hle2, hp2⟩, hwf2⟩, hT2⟩
  simp only [writerWP_get]
  refine writerWP_mono (ht_foldlM _ _ c (fun _ v => Book B c v ∧ HtInv H B c v ∧ v.path = w2.path ∧
      WriterKlongsWf v ∧ TallOK base T c v) (fun b e v hv => ?_) 0 w2 ⟨hb2, hi2, rfl, hwf2, hT2⟩) ?_
  · obtain ⟨hbv, hiv, hpv, hwfv, hTv⟩ := hv
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (writerWP_and (hw_getNode B e.2 c v hvo hbv hiv)
      (klongsWf_getNode e.2 c v hkw hwfv)) (tk_getNode e.2 c v hmp hvc hTv)) ?_
    rintro m u ⟨⟨⟨hbu, hiu, hleu, -, hpu⟩, hwfu, -⟩, hTu⟩
    rw [writerWP_pure]
    exact ⟨⟨hbu, hiu, hpu.trans hpv, hwfu, hTu⟩, hleu⟩
  rintro _ w3 ⟨⟨hb3, hi3, hp3, hwf3, hT3⟩, hle3⟩
  have hle03 : HtLe w w3 := hle1.trans (hle2.trans hle3)
  have hk03 : Kept w w3 := hle03.1
  have hp03 : w3.path = w.path := hp3.trans (hp2.trans hp1)
  refine writerWP_mono (ht_forIn_inv_mem c _ (fun v => Book B c v ∧ HtInv H B c v ∧ Kept w3 v ∧
      v.path = w3.path ∧ WriterKlongsWf v ∧ PathFreeTo v (stop + 1) ∧ TallOK base T c v)
      (List.range (depth - stop))
      (fun j hj v hv => ?_) w3
      ⟨hb3, hi3, Kept.refl _, rfl, hwf3, ht_pf_le hpf hp03 hle03 (by omega), hT3⟩) ?_
  · obtain ⟨hbv, hiv, hkv, hpv, hwfv, hpfv, hTv⟩ := hv
    have hj' : j < depth - stop := List.mem_range.mp hj
    simp only [writerWP_bind]
    refine writerWP_mono (kd_pathNode _ c v) ?_
    rintro x v1 ⟨hv1, ax, hxp⟩
    subst v1
    have hxT : ¬ T x := by
      have hxw : w.path[depth - j]? = some (ax, x) := by rw [hpv, hp03] at hxp; exact hxp
      have hXx : X (depth - j) = x := by
        have := hX (depth - j) (by omega); rw [hxw] at this; exact (Option.some.inj this).symm
      rw [← hXx]; exact hchainT (depth - j) (by omega) (by omega)
    refine writerWP_mono (writerWP_and (writerWP_and (hw_getNode B x c v hvo hbv hiv)
      (klongsWf_getNode x c v hkw hwfv)) (tk_getNode x c v hmp hvc hTv)) ?_
    rintro xn u1 ⟨⟨⟨hbu, hiu, hleu, hlx, hpu⟩, hwfu, -⟩, hTu⟩
    split
    · simp only [writerWP_bind]
      refine writerWP_mono (kd_pathNode _ c u1) ?_
      rintro par u2 ⟨hu2, -⟩
      subst u2
      refine writerWP_mono (kd_klongAt _ c u1) ?_
      rintro k u3 ⟨hu3, -⟩
      subst u3
      refine writerWP_mono (writerWP_and (writerWP_and (ht_takeBackChk B x par k c u1 hvo hbu hiu u1 xn hlx
        (Kept.refl _)) (klongsWf_takeBackChk x par k c u1 hkw hwfu))
        (tk_takeBackChk x par k c u1 hmp hvc hTu hxT)) ?_
      rintro _ u4 ⟨⟨⟨hb4, hi4, hk4, hp4, htk4⟩, hwf4⟩, hT4⟩
      rw [writerWP_pure]
      refine ⟨by first | rfl | trivial, hb4, hi4, (hkv.trans hleu.1).trans hk4,
        by rw [hp4, hpu, hpv], hwf4, ?_, hT4⟩
      intro d a' q hd hq
      have hqv : v.path[d]? = some (a', q) := by rw [hp4, hpu] at hq; exact hq
      have hqw : w.path[d]? = some (a', q) := by rw [hpv, hp03] at hqv; exact hqv
      have hxw : w.path[depth - j]? = some (ax, x) := by rw [hpv, hp03] at hxp; exact hxp
      refine htk4 q (by rw [hleu.2]; exact hpfv d a' q hd hqv) ?_
      exact hne (by omega) hqw hxw
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_and (hw_keeps B (ht_note B _) c u1 hvo hbu hiu)
        (klongsWf_note _ c u1 hkw hwfu)) (tk_note _ c u1 hmp hvc hTu)) ?_
      rintro _ u2 ⟨⟨⟨hb2', hi2', hle2', hp2'⟩, hwf2'⟩, hT2'⟩
      refine writerWP_mono (writerWP_and (writerWP_and (ht_unlink B x c u2 hvo hb2' hi2')
        (klongsWf_unlink x c u2 hkw hwf2')) (tk_unlink x c u2 hvc hT2' hxT)) ?_
      rintro _ u3 ⟨⟨⟨hb3', hi3', hle3', hp3'⟩, hwf3'⟩, hT3'⟩
      rw [writerWP_pure]
      exact ⟨by first | rfl | trivial, hb3', hi3', (hkv.trans hleu.1).trans (hle2'.1.trans hle3'.1),
        by rw [hp3', hp2', hpu, hpv], hwf3',
        ht_pf_le hpfv (hp3'.trans (hp2'.trans hpu)) (hleu.trans (hle2'.trans hle3'))
          (Nat.le_refl _), hT3'⟩
  rintro _ w4 ⟨hb4, hi4, hk4, hp4, hwf4, hpf4, hT4⟩
  refine writerWP_mono (kd_pathNode stop c w4) ?_
  rintro sNode w5 ⟨hw5, as, hps⟩
  subst w5
  refine writerWP_mono (kd_klongAt (stop + 1) c w4) ?_
  rintro cs w5 ⟨hw5, -⟩
  subst w5
  refine writerWP_mono (writerWP_and (writerWP_and (hw_getNode B sNode c w4 hvo hb4 hi4)
    (klongsWf_getNode sNode c w4 hkw hwf4)) (tk_getNodeI sNode c w4 hvc hT4)) ?_
  rintro sn w5 ⟨⟨⟨hb5, hi5, hle5, hl5, hp5⟩, hwf5, -⟩, hT5, hsn5, -⟩
  refine writerWP_mono (writerWP_and (writerWP_and (hw_ghOf B sNode c w5 hvo hb5 hi5)
    (klongsWf_ghOf sNode c w5 hkw hwf5)) (tk_ghOf sNode c w5 hmp hvc hT5)) ?_
  rintro ⟨gs, hs⟩ w6 ⟨⟨⟨hb6, hi6, hle6, hp6, hm6, n6, hl6, hnl6⟩, hwf6⟩, hT6⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hsl => ?_)
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  have hsl' : sn.leaf = true := by simpa using hsl
  have hs0 : hs = 0 := by
    obtain ⟨n7, hl7, hl7'⟩ := hle6.1.lookup hl5
    rw [hl6] at hl7
    cases hl7
    rw [hl7', hsl'] at hnl6
    cases hs with
    | zero => rfl
    | succ k => simp at hnl6
  subst hs0
  have hp74 : w6.path = w4.path := hp6.trans hp5
  have hsT : ¬ T sNode := by
    intro hTs
    obtain ⟨_, hun, m, hm, hml, _⟩ := hT6 sNode hTs
    have hun5 : w5.taken.contains sNode = false := by rw [← hle6.2]; exact hun
    have e1 : wNode c.p base w5 sNode = some sn := hsn5 hun5
    have e2 : wNode c.p base w6 sNode = some n6 := by
      unfold wNode; simp only [hun, Bool.false_eq_true, ↓reduceIte, hl6]
    obtain ⟨n7, hl7, hl7'⟩ := hle6.1.lookup hl5
    rw [hl6] at hl7
    cases hl7
    rw [e2] at hm
    cases hm
    rw [hl7', hsl'] at hml
    cases hml
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (writerWP_and (hw_keeps B (ht_note B _) c w6 hvo hb6 hi6)
    (klongsWf_note _ c w6 hkw hwf6)) (tk_note _ c w6 hmp hvc hT6)) ?_
  rintro _ w7 ⟨⟨⟨hb7, hi7, hle7, hp7⟩, hwf7⟩, hT7⟩
  have hp74' : w7.path = w4.path := hp7.trans hp74
  have hle47 : HtLe w4 w7 := hle5.trans (hle6.trans hle7)
  refine writerWP_mono (writerWP_and (writerWP_and (ht_appendDeleteKlong B sNode stop cs c w7 hvo hpos hb7 hi7
    gs 0 (HtLe.gh' hm6 hle7) as (by rw [hp74']; exact hps) (ht_pf_le hpf4 hp74' hle47 (Nat.le_refl _)))
    (klongsWf_appendDeleteKlong sNode stop cs c w7 hkw hwf7))
    (tk_appendDeleteKlong sNode stop cs c w7 hmp hvc hT7 hsT)) ?_
  rintro _ w8 ⟨⟨⟨hb8, hi8, hle8, -⟩, hwf8⟩, hT8⟩
  refine writerWP_mono (hAd key gs w8 ⟨hb8, hi8, (hk03.trans hk4).trans ((hle47.trans hle8).1), hwf8, hT8⟩) ?_
  rintro _ w9 ⟨hb9, hi9, hk9, hwf9, hT9⟩
  rw [writerWP_pure]
  exact ⟨hb9, hi9, (hk03.trans hk4).trans ((hle47.trans hle8).1.trans hk9), hwf9, hT9⟩

theorem tk_descendLte (cv f : Nat) (x : NodeId) : TallKeeps base T (descendLte cv f x) :=
  tk_reads _ (fun c w hvc => writerWP_descendLte_readsU cv c base hvc f x w)

theorem tk_setNode_false (segRoot : NodeId) (cv : Nat) : TallKeeps base T (setNode segRoot cv false) := by
  intro c w hmp hvc h
  unfold setNode
  simp only [Bool.not_false, ↓reduceIte]
  repeat' first
    | assumption
    | contradiction
    | wpSimplify
    | tkUse (tk_descendLte _ _ _)
    | tkMore
    | wpSplit
    | split

set_option maxHeartbeats 3200000 in
/-- The last segment of a delete. -/
theorem tk_setValueDelChk2G (B : NodeId) (ad : Key → Nat → Nat → M Unit) (segRoot : NodeId) (cv : Nat)
    (key : Key) (c : Ctx)
    (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view)
    (hb : Book B c w) (hi : HtInv H B c w) (hwf : WriterKlongsWf w)
    (hpf : PathFreeTo w w.path.length) (hr : HtPathLast w segRoot)
    (hk : ViewKinds K B c) (hki : KdInv K B w)
    (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base) (hT : TallOK base T c w)
    (hAd : AdOK H B base T ad c w) :
    WriterWP (setValueDelChk2G ad segRoot cv key) c w (fun _ v => HtbState H B base T c w v) := by
  unfold setValueDelChk2G
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
    (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf (Or.inl hr))
    (klongsWf_descendLte cv c.p.fuel segRoot c w hkw hwf))
    (kd_descendLte K B cv c.p.fuel segRoot c w hvo.ids hk hb hki (Or.inl hr)))
    (tk_descendLte cv c.p.fuel segRoot c w hmp hvc hT)) ?_
  rintro leaf w1 ⟨⟨⟨⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, hlf0⟩, hpf1⟩, hwf1⟩, -, hki1, -⟩, hT1⟩
  have hlast1 : HtPathLast w1 leaf := by
    rcases hlast with h | ⟨rfl, hp, -⟩
    · exact h
    · obtain ⟨a, ha⟩ := hr; exact ⟨a, by rw [hp]; exact ha⟩
  refine writerWP_mono (kd_pathSize c w1) ?_
  rintro ln w2 ⟨hw2, hln⟩
  subst w2
  subst ln
  refine writerWP_mono (tk_deleteUpwardChk2G B ad leaf (w1.path.length - 1) cv key c w1 hvo hpos hkw
    hb1 hi1 hwf1 hpf1 rfl hlast1 n0 hl0 hlf0 hk hki1 hmp hvc hT1 (hAd.mono hle1.1)) ?_
  rintro noop w3 ⟨hb3, hi3, hk3, hwf3, hT3⟩
  have hk13 := hle1.1.trans hk3
  split
  · try simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (writerWP_and (hw_keeps B (ht_fresh B) c w3 hvo hb3 hi3)
      (klongsWf_fresh c w3 hkw hwf3)) (tk_fresh c w3 hmp hvc hT3)) ?_
    rintro _ w4 ⟨⟨⟨hb4, hi4, hle4, -⟩, hwf4⟩, hT4⟩
    rw [writerWP_pure]
    exact ⟨hb4, hi4, hk13.trans hle4.1, hwf4, hT4⟩
  · rw [writerWP_pure]
    exact ⟨hb3, hi3, hk13, hwf3, hT3⟩

set_option maxHeartbeats 3200000 in
/-- The segments of a delete's key. -/
theorem tk_putSegsDelChk2G (B : NodeId) (ad : Key → Nat → Nat → M Unit) (key : Key) (segs : List Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i → ViewKlongsWf c.p c.view →
      Book B c w → HtInv H B c w → WriterKlongsWf w → PathFreeTo w w.path.length →
      HtPathLast w r → ViewKinds K B c → KdInv K B w → 2 ≤ c.p.M →
      MergeParamsOK c.p → ViewCoherent c base → TallOK base T c w → AdOK H B base T ad c w →
      WriterWP (putSegsDelChk2G ad key segs r) c w (fun _ v => HtbState H B base T c w v) := by
  induction segs with
  | nil => intro r c w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    intro r c w hvo hpos hkw hb hi hwf hpf hr hk hki hM hmp hvc hT hAd
    cases rest with
    | nil =>
      unfold putSegsDelChk2G
      exact tk_setValueDelChk2G B ad r cv key c w hvo hpos hkw hb hi hwf hpf hr hk hki hmp hvc hT hAd
    | cons d rest' =>
      unfold putSegsDelChk2G
      simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
        (ht_setNode_del B r cv c w hvo hb hi hkw hwf hpf hr)
        (klongsWf_setNode r cv false c w hkw hwf))
        (kd_setNode K B (appendFrameOK B) r cv false c w hvo.ids hk hb hki hM (Or.inl hr)
          (fun h => by cases h))) (tk_setNode_false r cv c w hmp hvc hT)) ?_
      rintro res w1 ⟨⟨⟨⟨hb1, hi1, hle1, hpf1, hres⟩, hwf1⟩, -, hki1, -⟩, hT1⟩
      split
      · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1.1, hwf1, hT1⟩
      · rename_i next
        exact writerWP_mono (ih next c w1 hvo hpos hkw hb1 hi1 hwf1 hpf1 (hres next rfl) hk hki1 hM
            hmp hvc hT1 (hAd.mono hle1.1))
          (fun _ u hu => ⟨hu.1, hu.2.1, hle1.1.trans hu.2.2.1, hu.2.2.2⟩)

/-- A delete keeps the walk and the frame. -/
theorem tk_putKvDelChk2G (B : NodeId) (ad : Key → Nat → Nat → M Unit) (key : Key) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c)
    (hpos : 0 < c.i) (hkw : ViewKlongsWf c.p c.view) (hb : Book B c w) (hi : HtInv H B c w)
    (hwf : WriterKlongsWf w) (hk : ViewKinds K B c) (hki : KdInv K B w) (hM : 2 ≤ c.p.M)
    (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base) (hT : TallOK base T c w)
    (hAd : AdOK H B base T ad c w) :
    WriterWP (putKvDelChk2G ad key) c w (fun _ v => HtbState H B base T c w v) := by
  unfold putKvDelChk2G
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (ht_pathClear B c w hvo hb hi)
    (klongsWf_pathClear c w hkw hwf)) (kd_pathClear K B c w hvo.ids hb hki))
    (tk_pathClear c w hmp hvc hT)) ?_
  rintro _ w1 ⟨⟨⟨⟨hb1, hi1, hk1, hp1, -⟩, hwf1⟩, -, hki1, -, hp1', -⟩, hT1⟩
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (ht_findRoot B c w1 hvo hb1 hi1 hp1)
    (klongsWf_findRoot c w1 hkw hwf1)) (kd_findRoot K B c w1 hvo.ids hb1 hki1 hp1'))
    (tk_findRoot c w1 hmp hvc hT1)) ?_
  rintro root w2 ⟨⟨⟨⟨hb2, hi2, hk2, hp2, -, hpf2⟩, hwf2⟩, -, hki2, -⟩, hT2⟩
  exact writerWP_mono (tk_putSegsDelChk2G B ad key key root c w2 hvo hpos hkw hb2 hi2 hwf2
    (by rw [hp2]; exact hpf2) ⟨none, by rw [hp2]; rfl⟩ hk hki2 hM hmp hvc hT2 (hAd.mono (hk1.trans hk2)))
    (fun _ u hu => ⟨hu.1, hu.2.1, hk1.trans (hk2.trans hu.2.2.1), hu.2.2.2⟩)

end Prefix

end SIS.Tree
