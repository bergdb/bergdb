/-
bergdb 030-29: a segment leaf's groups (`applyGroups`) for a transaction of
puts: the key nodes the next segments' trees write, and what the leaf's list
becomes, compare value by compare value (`ag_loop`), given what each next
segment's tree does (`planTree`); then the leaf's added entries against its
live list (`leaf_counts`).
-/
import Contract.Proof.DnbEmit

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-- The operations of compare value cv at segment g. -/
def grpOf (g : Nat) (ops : List Op) (cv : Nat) : List Op := ops.filter (fun op => segAt g op == cv)

/-- Those that go on to the next segment. -/
def subsOf (g : Nat) (ops : List Op) (cv : Nat) : List Op :=
  (grpOf g ops cv).filter (fun op => !endsAt g op)

/-- The fold of a group's operations that end at the leaf, for puts: each a
new value, so the entry is set (or the list kept if there are none). -/
theorem fold_puts {cv : Nat} : ∀ (L : List Op) (es : List (Nat × NodeId)) (acc : Acc),
    (∀ op ∈ L, opDel op = false) →
    let q := L.foldl (fun (q : List (Nat × NodeId) × Acc) op =>
      match op with
      | .put _ hv =>
        let (y, a) := q.2.fresh
        (setEntry cv y q.1, a.write y (.val hv))
      | .del _ => (removeEntry cv q.1, q.2)) (es, acc)
    kw q.2 = kw acc ∧ (q.1.Pairwise CvLtA ∨ ¬ es.Pairwise CvLtA) ∧
      (∀ c, c ≠ cv → q.1.lookup c = es.lookup c) ∧
      (L = [] → q.1 = es) ∧ (L ≠ [] → ∃ y, q.1.lookup cv = some y)
  | [], es, acc, _ => by
    refine ⟨rfl, ?_, fun _ _ => rfl, fun _ => rfl, fun h => absurd rfl h⟩
    by_cases h : es.Pairwise CvLtA
    · exact Or.inl h
    · exact Or.inr h
  | op :: L, es, acc, hp => by
    simp only [List.foldl_cons]
    cases op with
    | put k hv =>
      simp only
      have ih := fold_puts (cv := cv) L (setEntry cv acc.fresh.1 es) ((acc.fresh.2).write acc.fresh.1 (.val hv))
        (fun o ho => hp o (List.mem_cons_of_mem _ ho))
      simp only at ih
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih
      refine ⟨by rw [i1, kw_write_val, kw_fresh], ?_, ?_, fun h => absurd h (List.cons_ne_nil _ _), fun _ => ?_⟩
      · rcases i2 with i2 | i2
        · exact Or.inl i2
        · by_cases h : es.Pairwise CvLtA
          · exact absurd (setEntry_sorted _ _ h) i2
          · exact Or.inr h
      · intro c hc
        rw [i3 c hc, setEntry_lookup, ite_eq_right hc]
      · by_cases hL : L = []
        · rw [i4 hL, setEntry_lookup, ite_eq_left rfl]
          exact ⟨_, rfl⟩
        · exact i5 hL
    | del k => simp [opDel] at hp

theorem subs_no_end {g : Nat} {ops : List Op} {cv : Nat}
    (hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op)) (hs : subsOf g ops cv ≠ []) :
    (grpOf g ops cv).filter (endsAt g) = [] := by
  obtain ⟨o1, ho1⟩ := List.exists_mem_of_ne_nil _ hs
  unfold subsOf grpOf at ho1
  simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at ho1
  rw [List.filter_eq_nil_iff]
  intro o2 ho2 he2
  unfold grpOf at ho2
  simp only [List.mem_filter, beq_iff_eq] at ho2
  have h1 := hend o1 ho1.1.1
  have h2 := hend o2 ho2.1
  rw [ho1.2, ho1.1.2] at h1
  rw [he2, ho2.2] at h2
  rw [← h1] at h2
  simp at h2

/-- **A leaf's groups, for puts.** Given what each next segment's tree does,
the key nodes written are at most the sum of their bounds, and every compare
value of the groups ends with an entry: its own value, or the tree's root,
with what the tree gives (`Q`). -/
theorem ag_loop {g : Nat} {ops : List Op} {es0 : List (Nat × NodeId)}
    (hputs : ∀ op ∈ ops, opDel op = false)
    (hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op))
    (B : Nat → Nat) (Q : Nat → NodeId → Prop) (F0 : Nat)
    (hT : ∀ f, f < F0 → ∀ cv acc0 res acc1, subsOf g ops cv ≠ [] →
      planTree cf i s f (es0.lookup cv) (g + 1) (subsOf g ops cv) acc0 = some (res, acc1) →
      kw acc1 ≤ kw acc0 + B cv ∧ ∃ y, res = some y ∧ Q cv y) :
    ∀ (cvs : List Nat) (f : Nat) (es1 : List (Nat × NodeId)) (acc : Acc)
      (es : List (Nat × NodeId)) (acc' : Acc), f ≤ F0 → cvs.Nodup →
      (∀ c ∈ cvs, es1.lookup c = es0.lookup c) → es1.Pairwise CvLtA →
      (∀ cv ∈ cvs, grpOf g ops cv ≠ []) →
      applyGroups cf i s f g es1 cvs ops acc = some (es, acc') →
      kw acc' ≤ kw acc + (cvs.map (fun cv => if subsOf g ops cv = [] then 0 else B cv)).sum ∧
      es.Pairwise CvLtA ∧ (∀ c, c ∉ cvs → es.lookup c = es1.lookup c) ∧
      (∀ cv ∈ cvs, ∃ y, es.lookup cv = some y ∧ (subsOf g ops cv = [] ∨ Q cv y))
  | [], f, es1, acc, es, acc', _, _, _, hs1, _, h => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
      cases f with
      | zero => simp [applyGroups] at h
      | succ f' => exact ⟨f', rfl⟩
    simp only [applyGroups, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hs1]
  | cv :: cvs, f, es1, acc, es, acc', hf, hnd, hl1, hs1, hgrp, h => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
      cases f with
      | zero => simp [applyGroups] at h
      | succ f' => exact ⟨f', rfl⟩
    have hnd' := List.nodup_cons.mp hnd
    unfold applyGroups at h
    simp only at h
    have hfp := fold_puts (cv := cv) ((ops.filter (fun op => segAt g op == cv)).filter (endsAt g))
      es1 acc (fun op hop => hputs op (by
        simp only [List.mem_filter] at hop; exact hop.1.1))
    generalize hq : List.foldl _ (es1, acc) _ = q at h hfp
    obtain ⟨es2, acc2⟩ := q
    simp only at hfp h
    obtain ⟨f1, f2, f3, f4, f5⟩ := hfp
    have hs2 : es2.Pairwise CvLtA := by
      rcases f2 with f2 | f2
      · exact f2
      · exact absurd hs1 f2
    have hsubs : ((ops.filter (fun op => segAt g op == cv)).filter (fun op => !endsAt g op)) =
        subsOf g ops cv := rfl
    rw [hsubs] at h
    have hcvs : ∀ c ∈ cvs, c ≠ cv := fun c hc he => hnd'.1 (he ▸ hc)
    split at h
    · rename_i hse
      have hse' : subsOf g ops cv = [] := by simpa using hse
      obtain ⟨i1, i2, i3, i4⟩ := ag_loop hputs hend B Q F0 hT cvs f' es2 acc2 es acc' (by omega)
        hnd'.2 (fun c hc => by rw [f3 c (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)]) hs2
        (fun c hc => hgrp c (List.mem_cons_of_mem _ hc)) h
      refine ⟨?_, i2, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte, zero_add]
        omega
      · intro c hc
        simp only [List.mem_cons, not_or] at hc
        rw [i3 c hc.2, f3 c hc.1]
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · have hL : (ops.filter (fun op => segAt g op == c)).filter (endsAt g) ≠ [] := by
            intro hL
            have hg := hgrp c List.mem_cons_self
            apply hg
            have h2 : (grpOf g ops c).filter (fun op => !endsAt g op) = [] := hse'
            have h1 : (grpOf g ops c).filter (endsAt g) = [] := hL
            rw [List.filter_eq_nil_iff] at h1 h2
            rw [List.eq_nil_iff_forall_not_mem]
            intro o ho
            have a1 := h1 o ho
            have a2 := h2 o ho
            simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at a1 a2
            simp_all
          obtain ⟨y, hy⟩ := f5 hL
          refine ⟨y, ?_, Or.inl hse'⟩
          rw [i3 c hnd'.1, hy]
        · obtain ⟨y, hy, hq⟩ := i4 c hc
          exact ⟨y, hy, hq⟩
    · rename_i hse
      have hse' : subsOf g ops cv ≠ [] := by simpa using hse
      have hL := subs_no_end hend hse'
      have hes2 : es2 = es1 := f4 hL
      subst hes2
      have hacc : acc2 = acc := by
        have hq' := hq
        unfold grpOf at hL
        rw [hL, List.foldl_nil] at hq'
        exact (Prod.mk.inj hq').2.symm
      subst hacc
      rw [hl1 cv List.mem_cons_self] at h
      split at h
      · cases h
      · rename_i y acc3 htr
        obtain ⟨t1, _, ht, hQ⟩ := hT f' (by omega) cv acc2 (some y) acc3 hse' htr
        cases ht
        obtain ⟨i1, i2, i3, i4⟩ := ag_loop hputs hend B Q F0 hT cvs f' (setEntry cv y es2) acc3 es acc'
          (by omega) hnd'.2 (fun c hc => by
            rw [setEntry_lookup, ite_eq_right (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)])
          (setEntry_sorted _ _ hs2) (fun c hc => hgrp c (List.mem_cons_of_mem _ hc)) h
        refine ⟨?_, i2, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte]
          omega
        · intro c hc
          simp only [List.mem_cons, not_or] at hc
          rw [i3 c hc.2, setEntry_lookup, ite_eq_right hc.1]
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · refine ⟨y, ?_, Or.inr hQ⟩
            rw [i3 c hnd'.1, setEntry_lookup, ite_eq_left rfl]
          · exact i4 c hc
      · rename_i acc3 htr
        obtain ⟨_, _, ht, _⟩ := hT f' (by omega) cv acc2 none acc3 hse' htr
        cases ht

theorem lookup_of_mem_sorted {l : List (Nat × NodeId)} (hs : l.Pairwise CvLtA) {c : Nat} {y : NodeId}
    (h : (c, y) ∈ l) : l.lookup c = some y :=
  (lookup_iff_mem (l := l) hs c y).mpr h

/-- The entries of a list in order whose compare values satisfy p are at
most the compare values of a list without duplicates that satisfy p, if each
is one of them. -/
theorem sorted_count_le {l : List (Nat × NodeId)} (hs : l.Pairwise CvLtA) (P : Nat × NodeId → Bool)
    (T : List Nat) (hT : ∀ e ∈ l, P e = true → e.1 ∈ T) :
    (l.filter P).length ≤ T.dedup.length := by
  have hnd : ((l.filter P).map (·.1)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (hs.filter P).imp (fun h => Nat.ne_of_lt h)
  have hsub : (l.filter P).map (·.1) ⊆ T.dedup := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨e, he, rfl⟩ := hc
    rw [List.mem_filter] at he
    exact List.mem_dedup.mpr (hT e he.1 he.2)
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

/-- **A leaf's list against its live list, for puts.** The list after the
groups, es, in order: off the touched compare values as the live list lb; on
each, an entry, the old one or one whose group counts a klong. Then PE removes
no compare value, adds at most the groups' klongs, holds at most lb's entries
and the added, and holds lb itself if it adds none. -/
theorem leaf_counts {lb es : List (Nat × NodeId)} {cvs : List Nat} (kc : Nat → Nat)
    (hlb : lb.Pairwise CvLtA) (hes : es.Pairwise CvLtA) (hnd : cvs.Nodup)
    (hoff : ∀ c, c ∉ cvs → es.lookup c = lb.lookup c)
    (hon : ∀ cv ∈ cvs, ∃ y, es.lookup cv = some y ∧ (lb.lookup cv = some y ∨ 1 ≤ kc cv)) :
    let F := es.map (fun e => (e.1, some e.2))
    (removedCvs lb F).length = 0 ∧
      (F.filter (isAdded lb)).length ≤ (cvs.map kc).sum ∧
      F.length ≤ lb.length + (F.filter (isAdded lb)).length ∧
      ((F.filter (isAdded lb)).length = 0 → lb.map (fun q => (q.1, some q.2)) = F) := by
  intro F
  have hFadd : F.filter (isAdded lb) = (es.filter (fun e => lb.lookup e.1 != some e.2)).map
      (fun e => (e.1, some e.2)) := by
    simp only [F, List.filter_map]
    congr 1
  have hchanged : ∀ e ∈ es, (lb.lookup e.1 != some e.2) = true → e.1 ∈ cvs ∧ 1 ≤ kc e.1 := by
    intro e he hne
    have hel : es.lookup e.1 = some e.2 := lookup_of_mem_sorted hes he
    by_cases hc : e.1 ∈ cvs
    · obtain ⟨y, hy, hor⟩ := hon e.1 hc
      rw [hel] at hy
      cases hy
      rcases hor with hor | hor
      · rw [hor] at hne; simp at hne
      · exact ⟨hc, hor⟩
    · rw [← hoff e.1 hc, hel] at hne; simp at hne
  have hA : (F.filter (isAdded lb)).length ≤ (cvs.filter (fun cv => decide (1 ≤ kc cv))).length := by
    rw [hFadd, List.length_map]
    have := sorted_count_le hes (fun e => lb.lookup e.1 != some e.2)
      (cvs.filter (fun cv => decide (1 ≤ kc cv))) (fun e he hne => by
        obtain ⟨h1, h2⟩ := hchanged e he hne
        exact List.mem_filter.mpr ⟨h1, by simpa using h2⟩)
    rwa [List.Nodup.dedup (hnd.filter _)] at this
  have hsum : (cvs.filter (fun cv => decide (1 ≤ kc cv))).length ≤ (cvs.map kc).sum := by
    clear hon hoff hchanged hA hFadd
    induction cvs with
    | nil => simp
    | cons c r ih =>
      have := ih (List.nodup_cons.mp hnd).2
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      split <;> (simp_all; try omega)
  refine ⟨?_, le_trans hA hsum, ?_, ?_⟩
  · -- every live compare value is in F
    unfold removedCvs
    rw [List.length_map, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro q hq
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false]
    have hql : lb.lookup q.1 = some q.2 := lookup_of_mem_sorted hlb hq
    have : ∃ y, es.lookup q.1 = some y := by
      by_cases hc : q.1 ∈ cvs
      · obtain ⟨y, hy, _⟩ := hon q.1 hc; exact ⟨y, hy⟩
      · exact ⟨q.2, by rw [hoff q.1 hc, hql]⟩
    obtain ⟨y, hy⟩ := this
    rw [List.any_eq_true]
    refine ⟨(q.1, some y), ?_, by simp⟩
    simp only [F, List.mem_map]
    exact ⟨(q.1, y), lookup_mem hy, rfl⟩
  · -- the unchanged entries are live entries
    have hlen : F.length = (es.filter (fun e => !(lb.lookup e.1 != some e.2))).length +
        (es.filter (fun e => lb.lookup e.1 != some e.2)).length := by
      simp only [F, List.length_map]
      have := List.length_eq_length_filter_add (l := es) (fun e => !(lb.lookup e.1 != some e.2))
      simp only [Bool.not_not] at this
      omega
    have hun : (es.filter (fun e => !(lb.lookup e.1 != some e.2))).length ≤ lb.length := by
      have hnd2 : (es.filter (fun e => !(lb.lookup e.1 != some e.2))).Nodup :=
        (hes.filter _).imp (fun {a b} (h : a.1 < b.1) (he : a = b) => by
          subst he; exact lt_irrefl _ h)
      have hsub : es.filter (fun e => !(lb.lookup e.1 != some e.2)) ⊆ lb := by
        intro e he
        rw [List.mem_filter] at he
        have h2 := he.2
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq] at h2
        exact lookup_mem h2
      exact (List.subperm_of_subset hnd2 hsub).length_le
    have hA' : (F.filter (isAdded lb)).length =
        (es.filter (fun e => lb.lookup e.1 != some e.2)).length := by
      rw [hFadd, List.length_map]
    omega
  · intro h0
    have hall : ∀ e ∈ es, lb.lookup e.1 = some e.2 := by
      intro e he
      by_contra hne
      have : e ∈ es.filter (fun e => lb.lookup e.1 != some e.2) := by
        rw [List.mem_filter]; exact ⟨he, by simpa using hne⟩
      rw [hFadd, List.length_map, List.length_eq_zero_iff] at h0
      rw [h0] at this; simp at this
    have heq : lb = es := eq_of_lookup lb es hlb hes (fun c => by
      by_cases hc : c ∈ cvs
      · obtain ⟨y, hy, _⟩ := hon c hc
        rw [hy]
        exact hall (c, y) (lookup_mem hy)
      · exact (hoff c hc).symm)
    subst heq
    rfl

end Contract.PE
