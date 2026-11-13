/-
The writer's tree kept by a merge into two nodes (bergdb 024-22, `OpTreeOK`;
024-11, M3): two siblings l and r under p, both reached, are replaced by new
nodes m1 and m2 whose live klongs are among the two parts of their merged
klongs (`splitMerged`), which name the nodes that l and r named, each once; p
names m1 with l's compare value and m2 with one of its own, and no longer names
l or r (`treeOK_mergeTwoAfter`). The merged klongs name what l and r name
(`splitMerged_map_snd`, `mergeList_map_snd`).
-/
import SIS.Tree.WriterTreeMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem renameHead_map_snd (c : Nat) (l : List (Nat × NodeId)) :
    (renameHead c l).map Prod.snd = l.map Prod.snd := by
  cases l with
  | nil => rfl
  | cons a rest => rcases a with ⟨a1, a2⟩; rfl

/-- A merge's klongs name what the left node's and the right one's name. -/
theorem mergeList_map_snd (inner : Bool) (cR : Nat) (lvL lvR : List (Nat × NodeId)) :
    (mergeList inner cR lvL lvR).map Prod.snd = lvL.map Prod.snd ++ lvR.map Prod.snd := by
  unfold mergeList
  cases inner with
  | true => simp only [↓reduceIte, List.map_append, renameHead_map_snd]
  | false => simp only [Bool.false_eq_true, ↓reduceIte, List.map_append]

/-- A merge into two nodes: their klongs name what the merged klongs name. -/
theorem splitMerged_map_snd (inner : Bool) (cap : Nat) (e E1 E2 : List (Nat × NodeId)) (g : Nat)
    (h : splitMerged inner cap e = (E1, some (E2, g))) :
    (E1 ++ E2).map Prod.snd = e.map Prod.snd := by
  unfold splitMerged at h
  split at h
  · cases h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2, _⟩ := h
    subst h1 h2
    rw [List.map_append]
    cases inner with
    | true =>
      simp only [↓reduceIte, renameHead_map_snd]
      rw [← List.map_append, List.take_append_drop]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← List.map_append, List.take_append_drop]

/-- A merge into one node: its klongs are the merged klongs. -/
theorem splitMerged_one (inner : Bool) (cap : Nat) (e E1 : List (Nat × NodeId))
    (h : splitMerged inner cap e = (E1, none)) : E1 = e := by
  unfold splitMerged at h
  split at h
  · simp only [Prod.mk.injEq] at h; exact h.1.symm
  · simp at h

/-- In a list whose targets differ, a target has one compare value. -/
theorem snd_unique_of_nodup (l : List (Nat × NodeId)) (hn : (l.map Prod.snd).Nodup)
    (a b : Nat) (y : NodeId) (ha : (a, y) ∈ l) (hb : (b, y) ∈ l) : a = b := by
  induction l with
  | nil => cases ha
  | cons q rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · rw [← ha] at hb; simp only [Prod.mk.injEq] at hb; exact hb.1.symm
    · exact absurd (List.mem_map.mpr ⟨(b, y), hb, by rw [← ha]⟩) hn.1
    · exact absurd (List.mem_map.mpr ⟨(a, y), ha, by rw [← hb]⟩) hn.1
    · exact ih hn.2 ha hb

/-- Keys that differ, each target named under one compare value: the targets
differ. -/
theorem targets_nodup (l : List (Nat × NodeId)) (hk : (l.map Prod.fst).Nodup)
    (hone : ∀ c c' y, (c, y) ∈ l → (c', y) ∈ l → c = c') : (l.map Prod.snd).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons q rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hk ⊢
    refine ⟨fun hm => ?_, ih hk.2 (fun c c' y h1 h2 =>
      hone c c' y (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2))⟩
    obtain ⟨⟨c', y'⟩, hmem, hy⟩ := List.mem_map.mp hm
    simp only at hy
    have := hone q.1 c' q.2 (by simp) (by rw [← hy]; exact List.mem_cons_of_mem _ hmem)
    exact hk.1 (List.mem_map.mpr ⟨(c', y'), hmem, by rw [this]⟩)

/-- The tree after a merge into two nodes: siblings l and rr under p, named by
p's live klongs cL and cR, replaced by new nodes m1 and m2 whose live klongs are
among E1 and E2, which together name what l and rr name; p's live klongs after
are cL naming m1, g naming m2, and its others but cL's and cR's; nothing else
changes but l and rr, which are left behind. -/
theorem treeOK_mergeTwoAfter (N N' : NodeId → Option KNode) (t : Time) (r p l rr m1 m2 : NodeId)
    (pn ln rn pn' mn1 mn2 : KNode) (cL cR g : Nat) (E1 E2 : List (Nat × NodeId))
    (hT : TreeOK N t r) (hp : TReach N t r p) (hpn : N p = some pn)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t) (hc : cL ≠ cR)
    (hln : N l = some ln) (hrn : N rr = some rn)
    (hlt : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hrt : ∀ s, Klong.time s ∈ rn.ks → s ≤ t)
    (hm1 : N m1 = none) (hm1f : ∀ u c, TReach N t r u → ¬ TLink N t u c m1)
    (hm2 : N m2 = none) (hm2f : ∀ u c, TReach N t r u → ¬ TLink N t u c m2) (h12 : m1 ≠ m2)
    (hE : (E1 ++ E2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd)
    (hN'm1 : N' m1 = some mn1) (hmn1 : ∀ c z, (c, z) ∈ mn1.liveAt t → (c, z) ∈ E1)
    (hN'm2 : N' m2 = some mn2) (hmn2 : ∀ c z, (c, z) ∈ mn2.liveAt t → (c, z) ∈ E2)
    (hN'p : N' p = some pn')
    (hpn' : ∀ c z, (c, z) ∈ pn'.liveAt t →
      (c = cL ∧ z = m1) ∨ (c = g ∧ z = m2) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → y ≠ m2 → N' y = N y) :
    TreeOK N' t r := by
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hlink_l
  have hrR : TReach N t r rr := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hlr : l ≠ rr := fun h => hc (hT.oneLink p cL p cR l hp hp hlink_l (by rw [h]; exact hlink_r)).2
  have hm1R : ¬ TReach N t r m1 := not_reach_fresh N t r m1 hT hm1 hm1f
  have hm2R : ¬ TReach N t r m2 := not_reach_fresh N t r m2 hT hm2 hm2f
  have hlL : ln.liveAt t = ln.live := KNode.liveAt_of_times ln t hlt
  have hrL : rn.liveAt t = rn.live := KNode.liveAt_of_times rn t hrt
  -- the targets of l and rr differ
  have hnd : ((ln.live ++ rn.live).map Prod.snd).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨targets_nodup _ (KNode.live_keys_nodup ln) (fun c c' y h1 h2 => ?_),
      targets_nodup _ (KNode.live_keys_nodup rn) (fun c c' y h1 h2 => ?_), ?_⟩
    · exact (hT.oneLink l c l c' y hlR hlR ⟨ln, hln, by rw [hlL]; exact h1⟩
        ⟨ln, hln, by rw [hlL]; exact h2⟩).2
    · exact (hT.oneLink rr c rr c' y hrR hrR ⟨rn, hrn, by rw [hrL]; exact h1⟩
        ⟨rn, hrn, by rw [hrL]; exact h2⟩).2
    · intro a ha b hb hab
      obtain ⟨⟨c1, y1⟩, h1, rfl⟩ := List.mem_map.mp ha
      obtain ⟨⟨c2, y2⟩, h2, rfl⟩ := List.mem_map.mp hb
      simp only at hab
      subst hab
      exact hlr (hT.oneLink l c1 rr c2 y1 hlR hrR ⟨ln, hln, by rw [hlL]; exact h1⟩
        ⟨rn, hrn, by rw [hrL]; exact h2⟩).1
  have hndE : ((E1 ++ E2).map Prod.snd).Nodup := by rw [hE]; exact hnd
  -- a target of the new nodes is a target of l or rr
  have hsrc : ∀ c y, (c, y) ∈ E1 ++ E2 →
      ∃ o c0, (o = l ∨ o = rr) ∧ TLink N t o c0 y := by
    intro c y hm
    have : y ∈ (ln.live ++ rn.live).map Prod.snd := by
      rw [← hE]; exact List.mem_map.mpr ⟨(c, y), hm, rfl⟩
    obtain ⟨⟨c0, y0⟩, h0, hy0⟩ := List.mem_map.mp this
    simp only at hy0
    subst hy0
    rcases List.mem_append.mp h0 with h0 | h0
    · exact ⟨l, c0, Or.inl rfl, ln, hln, by rw [hlL]; exact h0⟩
    · exact ⟨rr, c0, Or.inr rfl, rn, hrn, by rw [hrL]; exact h0⟩
  -- the links of the new nodes
  have hnewl : ∀ z c y, (z = m1 ∨ z = m2) → TLink N' t z c y →
      (c, y) ∈ E1 ∧ z = m1 ∨ (c, y) ∈ E2 ∧ z = m2 := by
    intro z c y hz hlk
    obtain ⟨m, hm, hcm⟩ := hlk
    rcases hz with hz | hz
    · rw [hz, hN'm1] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      exact Or.inl ⟨hmn1 c y hcm, hz⟩
    · rw [hz, hN'm2] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      exact Or.inr ⟨hmn2 c y hcm, hz⟩
  have hnewE : ∀ z c y, (z = m1 ∨ z = m2) → TLink N' t z c y → (c, y) ∈ E1 ++ E2 := by
    intro z c y hz hlk
    rcases hnewl z c y hz hlk with ⟨h, _⟩ | ⟨h, _⟩
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ h
  -- an old target of l or rr is reached, and is neither l nor rr
  have holdT : ∀ o c0 y, (o = l ∨ o = rr) → TLink N t o c0 y →
      TReach N t r y ∧ y ≠ l ∧ y ≠ rr := by
    intro o c0 y ho hlk
    have hoR : TReach N t r o := by rcases ho with h | h <;> rw [h] <;> assumption
    refine ⟨TReach.link hoR hlk, fun hy => ?_, fun hy => ?_⟩
    · rw [hy] at hlk
      have := (hT.oneLink o c0 p cL l hoR hp hlk hlink_l).1
      rcases ho with h | h
      · exact hpl (this.symm.trans h)
      · exact hpr (this.symm.trans h)
    · rw [hy] at hlk
      have := (hT.oneLink o c0 p cR rr hoR hp hlk hlink_r).1
      rcases ho with h | h
      · exact hpl (this.symm.trans h)
      · exact hpr (this.symm.trans h)
  apply treeOK_regroup N N' t r p (fun o => o = l ∨ o = rr) (fun z => z = m1 ∨ z = m2) hT hp
  · rintro (h | h)
    · exact hpl h
    · exact hpr h
  · intro o ho
    rcases ho with h | h
    · rw [h]; exact ⟨hlR, p, cL, Or.inl rfl, hlink_l⟩
    · rw [h]; exact ⟨hrR, p, cR, Or.inl rfl, hlink_r⟩
  · rintro z (h | h)
    · rw [h]; exact hm1R
    · rw [h]; exact hm2R
  · intro y hyp hyN hyO
    exact hother y hyp (fun h => hyO (Or.inl h)) (fun h => hyO (Or.inr h))
      (fun h => hyN (Or.inl h)) (fun h => hyN (Or.inr h))
  · intro c y hlk
    obtain ⟨m, hm, hcm⟩ := hlk
    rw [hN'p] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    rcases hpn' c y hcm with ⟨_, hy⟩ | ⟨_, hy⟩ | ⟨hmem, hcl, hcr⟩
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)
    · have hlk : TLink N t p c y := ⟨pn, hpn, hmem⟩
      refine Or.inl ⟨hlk, ?_⟩
      rintro (hy | hy)
      · rw [hy] at hlk; exact hcl (hT.oneLink p c p cL l hp hp hlk hlink_l).2
      · rw [hy] at hlk; exact hcr (hT.oneLink p c p cR rr hp hp hlk hlink_r).2
  · intro z c y hz hlk
    obtain ⟨o, c0, ho, hlo⟩ := hsrc c y (hnewE z c y hz hlk)
    obtain ⟨_, hyl, hyr⟩ := holdT o c0 y ho hlo
    refine Or.inr ⟨⟨o, c0, ho, hlo⟩, ?_⟩
    rintro (h | h)
    · exact hyl h
    · exact hyr h
  · intro c c' z hz h1 h2
    obtain ⟨m, hm, hcm⟩ := h1
    obtain ⟨m', hm', hcm'⟩ := h2
    rw [hN'p] at hm hm'
    simp only [Option.some.injEq] at hm hm'
    subst hm hm'
    have key : ∀ d, (d, z) ∈ pn'.liveAt t → (z = m1 → d = cL) ∧ (z = m2 → d = g) := by
      intro d hd
      rcases hpn' d z hd with ⟨hd1, hz1⟩ | ⟨hd2, hz2⟩ | ⟨hmem, _, _⟩
      · exact ⟨fun _ => hd1, fun h => absurd (hz1.symm.trans h) h12⟩
      · exact ⟨fun h => absurd (h.symm.trans hz2) h12, fun _ => hd2⟩
      · rcases hz with h | h
        · rw [h] at hmem; exact absurd ⟨pn, hpn, hmem⟩ (hm1f p d hp)
        · rw [h] at hmem; exact absurd ⟨pn, hpn, hmem⟩ (hm2f p d hp)
    rcases hz with h | h
    · rw [(key c hcm).1 h, (key c' hcm').1 h]
    · rw [(key c hcm).2 h, (key c' hcm').2 h]
  · intro z c z' c' y hz hz' h1 h2
    rcases hnewl z c y hz h1 with ⟨e1, hz1⟩ | ⟨e1, hz1⟩ <;>
      rcases hnewl z' c' y hz' h2 with ⟨e2, hz2⟩ | ⟨e2, hz2⟩
    · rw [List.map_append, List.nodup_append] at hndE
      exact ⟨hz1.trans hz2.symm, snd_unique_of_nodup E1 hndE.1 c c' y e1 e2⟩
    · rw [List.map_append, List.nodup_append] at hndE
      exact absurd rfl (hndE.2.2 y (List.mem_map.mpr ⟨_, e1, rfl⟩) y
        (List.mem_map.mpr ⟨_, e2, rfl⟩))
    · rw [List.map_append, List.nodup_append] at hndE
      exact absurd rfl (hndE.2.2 y (List.mem_map.mpr ⟨_, e2, rfl⟩) y
        (List.mem_map.mpr ⟨_, e1, rfl⟩))
    · rw [List.map_append, List.nodup_append] at hndE
      exact ⟨hz1.trans hz2.symm, snd_unique_of_nodup E2 hndE.2.1 c c' y e1 e2⟩
  · intro c z z' c' hz hz' _ hlk
    obtain ⟨o, c0, ho, hlo⟩ := hsrc c' z (hnewE z' c' z hz' hlk)
    obtain ⟨hzR, _, _⟩ := holdT o c0 z ho hlo
    rcases hz with h | h
    · rw [h] at hzR; exact hm1R hzR
    · rw [h] at hzR; exact hm2R hzR
  · by_cases hrp : r = p
    · rw [hrp, hN'p]; exact ⟨_, rfl⟩
    · have hrl : r ≠ l := fun h => hT.rootFree p cL hp (by rw [h]; exact hlink_l)
      have hrr' : r ≠ rr := fun h => hT.rootFree p cR hp (by rw [h]; exact hlink_r)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      have hrm1 : r ≠ m1 := fun h => by rw [h, hm1] at hrm; cases hrm
      have hrm2 : r ≠ m2 := fun h => by rw [h, hm2] at hrm; cases hrm
      rw [hother r hrp hrl hrr' hrm1 hrm2]
      exact ⟨rm, hrm⟩

end SIS.Tree
