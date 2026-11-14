/-
The writer's merge keeps every reading (bergdb 024-12, TP10's `OpGetOK`;
024-22): the merge's last part, `mergeTail`, from the siblings to the parent
with room, keeps `wGet` of every key, the siblings' compare values in their
ranges; and so the whole merge of two nodes the transaction did not make, the
ranges from putinv's `RangeOrder`.
-/
import SIS.Tree.WriterGetMergeOp
import SIS.Tree.WriterGetMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The parent after a merge: its live klongs as the merge leaves them. -/
theorem mrg_parent_liveAt (pn : KNode) (t : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (l r : NodeId) (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ t)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) :
    (∀ cc z, (cc, z) ∈ (mergeParentNode pn t il cL m1 ir cR none).liveAt t ↔
      (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt t ∧ cc ≠ cL ∧ cc ≠ cR)) ∧
    (∀ (m2 : NodeId) (g : Nat) cc z,
      (cc, z) ∈ (mergeParentNode pn t il cL m1 ir cR (some (m2, g))).liveAt t ↔
      (cc = g ∧ z = m2) ∨ (cc ≠ g ∧ cc = cL ∧ z = m1) ∨
        (cc ≠ g ∧ cc ≠ cL ∧ cc ≠ cR ∧ (cc, z) ∈ pn.liveAt t)) := by
  have hhtd := htd_last pn
  have hpn : ∀ cc z, (cc, z) ∈ pn.liveAt t ↔ pn.live.lookup cc = some z := by
    intro cc z
    rw [KNode.liveAt_of_times pn t hpt, mem_iff_lookup _ (KNode.live_keys_nodup pn)]
  refine ⟨?_, ?_⟩
  · intro cc z
    have hmt : ∀ s, Klong.time s ∈ (mergeParentNode pn t il cL m1 ir cR none).ks → s ≤ t := by
      rw [mergeParentNode_eq]
      exact mpNode_times pn t il cL m1 ir cR none _ _ _ (hhtd _) hpt
    rw [KNode.liveAt_of_times _ t hmt, mem_iff_lookup _ (KNode.live_keys_nodup _),
      mergeParentNode_eq, mpNode_live_lookup pn t il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
        hc ?htd (fun _ _ _ h => by cases h) cc, hpn]
    case htd =>
      intro h
      cases hg : pn.ks.getLast? with
      | none => rw [hg] at h; simp at h
      | some k =>
        cases k with
        | del old => exact ⟨old, rfl⟩
        | time t => rw [hg] at h; simp at h
        | key a y => rw [hg] at h; simp at h
    by_cases h1 : cc = cL
    · subst h1
      simp only [↓reduceIte, Option.some.injEq]
      constructor
      · intro h; exact Or.inl ⟨trivial, h.symm⟩
      · rintro (⟨_, h⟩ | ⟨_, h, _⟩)
        · exact h.symm
        · exact absurd rfl h
    · by_cases h2 : cc = cR
      · subst h2
        simp [h1]
      · simp only [h1, h2, ↓reduceIte, false_and, false_or, ne_eq, not_false_eq_true, and_true,
          and_self]
  · intro m2 g cc z
    have hmt : ∀ s, Klong.time s ∈ (mergeParentNode pn t il cL m1 ir cR (some (m2, g))).ks →
        s ≤ t := by
      rw [mergeParentNode_eq]
      exact mpNode_times pn t il cL m1 ir cR (some (m2, g)) _ _ _ (hhtd _) hpt
    rw [KNode.liveAt_of_times _ t hmt, mem_iff_lookup _ (KNode.live_keys_nodup _),
      mergeParentNode_eq, mpNode_live_lookup pn t il cL m1 ir cR (some (m2, g)) _ _ _ l r hpwf hL
        hLL hR hRL hc ?htd ?hrip cc, hpn]
    case htd =>
      intro h
      cases hg : pn.ks.getLast? with
      | none => rw [hg] at h; simp at h
      | some k =>
        cases k with
        | del old => exact ⟨old, rfl⟩
        | time t => rw [hg] at h; simp at h
        | key a y => rw [hg] at h; simp at h
    case hrip =>
      intro h y g' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      simp at h
      exact h.1.1
    simp only
    by_cases h0 : cc = g
    · subst h0
      simp only [↓reduceIte, Option.some.injEq]
      constructor
      · intro h; exact Or.inl ⟨trivial, h.symm⟩
      · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact h.symm
        · exact absurd rfl h
        · exact absurd rfl h
    · by_cases h1 : cc = cL
      · subst h1
        simp only [h0, ↓reduceIte, Option.some.injEq, false_and, ne_eq, not_false_eq_true,
          true_and, false_or, not_true_eq_false, and_false, or_false]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      · by_cases h2 : cc = cR
        · subst h2
          simp [h0, h1]
        · simp only [h0, h1, h2, ↓reduceIte, false_and, ne_eq, not_false_eq_true, true_and,
            false_or]

/-- The second node's first compare value g of a merge into two: above cL and
0, and below every compare value of the parent above cR that is above the right
node's. -/
theorem mrg_two_g (inner : Bool) (cL cR : Nat) (lvL lvR : List (Nat × NodeId)) (h g : Nat)
    (yg : NodeId) (hs : CvSorted (mergeList inner cR lvL lvR)) (hh : 1 ≤ h)
    (hg : ((mergeList inner cR lvL lvR).drop h).head? = some (g, yg)) (hlr : cL < cR)
    (hL : ∀ q ∈ lvL, q.1 < cR ∧ (inner = true → q.1 = 0 ∨ cL < q.1) ∧ (inner = false → cL ≤ q.1))
    (hR : ∀ q ∈ lvR, (inner = true → q.1 = 0 ∨ cR < q.1) ∧ (inner = false → cR ≤ q.1)) :
    cL < g ∧ 0 < g ∧ (∀ k, cR < k → (∀ q ∈ lvR, q.1 < k) → g < k) := by
  have hmemg : (g, yg) ∈ (mergeList inner cR lvL lvR).drop h := List.mem_of_head? hg
  -- the right part's keys
  have hRs : CvSorted (if inner then renameHead cR lvR else lvR) := by
    unfold mergeList at hs
    exact List.Pairwise.sublist (List.sublist_append_right _ _) hs
  have hRge : ∀ q ∈ (if inner then renameHead cR lvR else lvR), cR ≤ q.1 := by
    intro q hq
    cases inner with
    | true =>
      simp only [↓reduceIte] at hq hRs
      cases hl : lvR with
      | nil => rw [hl] at hq; simp [renameHead] at hq
      | cons a rest =>
        rw [hl] at hq hRs
        simp only [renameHead, List.mem_cons] at hq hRs
        rcases hq with rfl | hq
        · exact Nat.le_refl _
        · have := (List.pairwise_cons.mp hRs).1 q hq
          simp at this; omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      exact (hR q hq).2 rfl
  have hRlt : ∀ k, cR < k → (∀ q ∈ lvR, q.1 < k) →
      ∀ q ∈ (if inner then renameHead cR lvR else lvR), q.1 < k := by
    intro k hk hlk q hq
    cases inner with
    | true =>
      simp only [↓reduceIte] at hq
      rcases mem_renameHead cR lvR q hq with h1 | h1
      · omega
      · exact hlk q (List.mem_of_mem_tail h1)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      exact hlk q hq
  have hcls : ∀ q ∈ mergeList inner cR lvL lvR, q ∈ lvL ∨ q ∈ (if inner then renameHead cR lvR else lvR) := by
    intro q hq
    unfold mergeList at hq
    exact List.mem_append.mp hq
  -- a klong before g
  obtain ⟨a, ha, hag⟩ : ∃ a ∈ mergeList inner cR lvL lvR, a.1 < g := by
    have hsplit := List.take_append_drop h (mergeList inner cR lvL lvR)
    have hs' := hs
    rw [← hsplit] at hs'
    have hpa := (List.pairwise_append.mp hs').2.2
    obtain ⟨y, hy⟩ : ∃ y, y ∈ (mergeList inner cR lvL lvR).take h := by
      cases ht : (mergeList inner cR lvL lvR).take h with
      | nil =>
        have hlen := congrArg List.length ht
        simp only [List.length_take, List.length_nil] at hlen
        have hd : (mergeList inner cR lvL lvR).drop h ≠ [] := by
          intro he; rw [he] at hg; simp at hg
        have : h < (mergeList inner cR lvL lvR).length := by
          by_cases hc : h < (mergeList inner cR lvL lvR).length
          · exact hc
          · exact absurd (List.drop_eq_nil_of_le (by omega)) hd
        omega
      | cons y _ => exact ⟨y, by simp⟩
    exact ⟨y, List.mem_of_mem_take hy, hpa y hy (g, yg) hmemg⟩
  have hgE : (g, yg) ∈ mergeList inner cR lvL lvR := List.mem_of_mem_drop hmemg
  refine ⟨?_, by omega, ?_⟩
  · rcases hcls _ hgE with hgl | hgr
    · obtain ⟨hgc, hgi, hgo⟩ := hL _ hgl
      cases inner with
      | true =>
        rcases hgi rfl with h0 | h0
        · simp at h0; omega
        · exact h0
      | false =>
        have hcg : cL ≤ g := hgo rfl
        rcases hcls a ha with hal | har
        · have := (hL a hal).2.2 rfl; omega
        · have := hRge a har; simp at hgc; omega
    · have := hRge _ hgr; omega
  · intro k hk hlk
    rcases hcls _ hgE with hgl | hgr
    · have := (hL _ hgl).1; simp at this; omega
    · exact hRlt k hk hlk _ hgr

/-- `sibling` reads the node that klong i of p names, of the kind asked. -/
theorem writerWP_sibling_leaf (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (base : View BVal) (hvc : ViewCoherent c base) :
    WriterWP (sibling p pn i inner) c w (fun sn v => pn.ptr? i = some sn.1 ∧
      ReadsAs c.p base w v ∧ v.nodes.lookup sn.1 = some sn.2 ∧
      (w.taken.contains sn.1 = false → wNode c.p base w sn.1 = some sn.2) ∧ w.nodes <+: v.nodes ∧
      (∀ z, (v.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
        (c.view z).isSome = true) ∧ sn.2.leaf = !inner) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_getNode_all s c w base hvc) ?_
    intro sn v ⟨h1, h2, h3, h4, h5⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i hne
      simp only [writerWP_pure]
      refine ⟨hs, h1, h2, h3, h4, h5, ?_⟩
      cases hl : sn.leaf <;> cases inner <;> simp_all

end SIS.Tree
