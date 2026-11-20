/-
bergdb 030-36: PE's plan of a transaction of puts and deletes against Java's
count at a segment leaf (`leaf_stepD`): a segment leaf planned into v meets
`PlanSpecD` against Java's count of it (`sbPlan`), given what the next
segments' trees do (`TreePPD` at lower fuels).

A compare value's operations that end at the leaf set a new value or remove
the entry, the last one wins (`agl_loop`); the keys that go on plan the next
segment's tree, which may be emptied (the entry removed) or new
(`fresh_le_del_ftb`). For each compare value PE adds or removes at most one
entry; Java counts at least one klong for it when PE adds (a put, the tree's
klong in the leaf, a new tree's pointer) and at least four when PE removes (a
delete that ends here, or one through the emptied tree). So PE's removed
compare values and added entries are at most Java's klongs
(`leaf_countsD`), and a leaf that no delete passes loses no entry.
-/
import Contract.Proof.DnbDelDefs
import Contract.Proof.DnbFreshDel

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## A leaf's groups, puts and deletes -/

/-- The fold of a group's operations that end at the leaf: the entry of cv
ends removed only if it had none or the group has a delete. -/
theorem fold_none {cv : Nat} : ∀ (L : List Op) (es : List (Nat × NodeId)) (acc : Acc),
    (L.foldl (fun (q : List (Nat × NodeId) × Acc) op =>
      match op with
      | .put _ hv =>
        let (y, a) := q.2.fresh
        (setEntry cv y q.1, a.write y (.val hv))
      | .del _ => (removeEntry cv q.1, q.2)) (es, acc)).1.lookup cv = none →
    es.lookup cv = none ∨ ∃ op ∈ L, opDel op = true
  | [], es, acc, h => Or.inl h
  | op :: L, es, acc, h => by
    simp only [List.foldl_cons] at h
    cases op with
    | put k hv =>
      simp only at h
      rcases fold_none L _ _ h with h1 | ⟨op, hop, hp⟩
      · rw [setEntry_lookup, ite_eq_left rfl] at h1; cases h1
      · exact Or.inr ⟨op, List.mem_cons_of_mem _ hop, hp⟩
    | del k => exact Or.inr ⟨.del k, List.mem_cons_self, rfl⟩

/-- **A leaf's groups, puts and deletes.** Given what each next segment's
tree does (at most `B cv` key nodes, and `Q cv` of its root), the key nodes
written are at most the sum of the bounds; a compare value whose operations
all end at the leaf has its entry changed only by a put (an entry) or a
delete (none); one whose operations go on has the tree's root as its
entry. -/
theorem agl_loop {g : Nat} {ops : List Op} {lb : List (Nat × NodeId)}
    (hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op))
    (B : Nat → Nat) (Q : Nat → Option NodeId → Prop) (F0 : Nat)
    (hT : ∀ f, f < F0 → ∀ cv acc0 res acc1, subsOf g ops cv ≠ [] →
      planTree cf i s f (lb.lookup cv) (g + 1) (subsOf g ops cv) acc0 = some (res, acc1) →
      kw acc1 ≤ kw acc0 + B cv ∧ Q cv res) :
    ∀ (cvs : List Nat) (f : Nat) (es1 : List (Nat × NodeId)) (acc : Acc)
      (es : List (Nat × NodeId)) (acc' : Acc), f ≤ F0 → cvs.Nodup →
      (∀ c ∈ cvs, es1.lookup c = lb.lookup c) → es1.Pairwise CvLtA →
      applyGroups cf i s f g es1 cvs ops acc = some (es, acc') →
      kw acc' ≤ kw acc + (cvs.map (fun cv => if subsOf g ops cv = [] then 0 else B cv)).sum ∧
      es.Pairwise CvLtA ∧ (∀ c, c ∉ cvs → es.lookup c = es1.lookup c) ∧
      (∀ cv ∈ cvs, (subsOf g ops cv = [] ∧ (es.lookup cv ≠ lb.lookup cv →
          (es.lookup cv ≠ none → ∃ op ∈ grpOf g ops cv, opDel op = false) ∧
          (es.lookup cv = none → ∃ op ∈ grpOf g ops cv, opDel op = true))) ∨
        (subsOf g ops cv ≠ [] ∧ Q cv (es.lookup cv)))
  | [], f, es1, acc, es, acc', _, _, _, hs1, h => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
      cases f with
      | zero => simp [applyGroups] at h
      | succ f' => exact ⟨f', rfl⟩
    simp only [applyGroups, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hs1]
  | cv :: cvs, f, es1, acc, es, acc', hf, hnd, hl1, hs1, h => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
      cases f with
      | zero => simp [applyGroups] at h
      | succ f' => exact ⟨f', rfl⟩
    have hnd' := List.nodup_cons.mp hnd
    unfold applyGroups at h
    simp only at h
    have hfm := fold_mixed (cv := cv) ((ops.filter (fun op => segAt g op == cv)).filter (endsAt g))
      es1 acc
    have hfn := fold_none (cv := cv) ((ops.filter (fun op => segAt g op == cv)).filter (endsAt g))
      es1 acc
    generalize hq : List.foldl _ (es1, acc) _ = q at h hfm hfn
    obtain ⟨es2, acc2⟩ := q
    simp only at hfm hfn h
    obtain ⟨f1, f2, f3, f4⟩ := hfm
    have hs2 := f2 hs1
    have hsubs : ((ops.filter (fun op => segAt g op == cv)).filter (fun op => !endsAt g op)) =
        subsOf g ops cv := rfl
    rw [hsubs] at h
    have hcvs : ∀ c ∈ cvs, c ≠ cv := fun c hc he => hnd'.1 (he ▸ hc)
    have hcv0 : es1.lookup cv = lb.lookup cv := hl1 cv List.mem_cons_self
    split at h
    · rename_i hse
      have hse' : subsOf g ops cv = [] := by simpa using hse
      obtain ⟨i1, i2, i3, i4⟩ := agl_loop hend B Q F0 hT cvs f' es2 acc2 es acc' (by omega)
        hnd'.2 (fun c hc => by rw [f3 c (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)]) hs2 h
      refine ⟨?_, i2, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte, zero_add]
        omega
      · intro c hc
        simp only [List.mem_cons, not_or] at hc
        rw [i3 c hc.2, f3 c hc.1]
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · left
          rw [i3 c hnd'.1]
          refine ⟨hse', fun hne => ⟨fun hsome => ?_, fun hnone => ?_⟩⟩
          · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hsome
            rcases f4 y hy with h0 | ⟨op, hop, hp⟩
            · rw [hy, ← h0, hcv0] at hne; exact absurd rfl hne
            · exact ⟨op, List.mem_of_mem_filter hop, hp⟩
          · rcases hfn hnone with h0 | ⟨op, hop, hp⟩
            · rw [hnone, ← h0, hcv0] at hne; exact absurd rfl hne
            · exact ⟨op, List.mem_of_mem_filter hop, hp⟩
        · exact i4 c hc
    · rename_i hse
      have hse' : subsOf g ops cv ≠ [] := by simpa using hse
      have hL := subs_no_end hend hse'
      have hq' := hq
      unfold grpOf at hL
      rw [hL, List.foldl_nil] at hq'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq'
      rw [hcv0] at h
      split at h
      · cases h
      · rename_i y acc3 htr
        obtain ⟨t1, t2⟩ := hT f' (by omega) cv acc (some y) acc3 hse' htr
        obtain ⟨i1, i2, i3, i4⟩ := agl_loop hend B Q F0 hT cvs f' (setEntry cv y es1) acc3 es acc'
          (by omega) hnd'.2 (fun c hc => by
            rw [setEntry_lookup, ite_eq_right (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)])
          (setEntry_sorted _ _ hs1) h
        refine ⟨?_, i2, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte]
          omega
        · intro c hc
          simp only [List.mem_cons, not_or] at hc
          rw [i3 c hc.2, setEntry_lookup, ite_eq_right hc.1]
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · right
            rw [i3 c hnd'.1, setEntry_lookup, ite_eq_left rfl]
            exact ⟨hse', t2⟩
          · exact i4 c hc
      · rename_i acc3 htr
        obtain ⟨t1, t2⟩ := hT f' (by omega) cv acc none acc3 hse' htr
        obtain ⟨i1, i2, i3, i4⟩ := agl_loop hend B Q F0 hT cvs f' (removeEntry cv es1) acc3 es acc'
          (by omega) hnd'.2 (fun c hc => by
            rw [removeEntry_lookup, ite_eq_right (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)])
          (hs1.filter _) h
        refine ⟨?_, i2, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte]
          omega
        · intro c hc
          simp only [List.mem_cons, not_or] at hc
          rw [i3 c hc.2, removeEntry_lookup, ite_eq_right hc.1]
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · right
            rw [i3 c hnd'.1, removeEntry_lookup, ite_eq_left rfl]
            exact ⟨hse', t2⟩
          · exact i4 c hc

/-! ## Java's counts of a group -/

/-- A group whose operations all end at the leaf: Java's klongs are its puts,
its deletes are its deletes. -/
theorem sbGroup_end {b g : Nat} {lv : List (Nat × NodeId)} {ops : List Op} {cv : Nat}
    {child : NodeId → List Op → SR} (hs : subsOf g ops cv = []) :
    sbGroup b g lv (grpOf g ops cv) child cv =
      (((grpOf g ops cv).filter (fun op => !opDel op)).length,
        8 * ((grpOf g ops cv).filter opDel).length, ((grpOf g ops cv).filter opDel).length) := by
  have hall : ∀ op ∈ grpOf g ops cv, endsAt g op = true := by
    intro op hop
    by_contra hne
    have : op ∈ subsOf g ops cv := List.mem_filter.mpr ⟨hop, by simpa using hne⟩
    rw [hs] at this; simp at this
  have hP : (grpOf g ops cv).filter (fun op => endsAt g op && !opDel op) =
      (grpOf g ops cv).filter (fun op => !opDel op) :=
    List.filter_congr (fun op hop => by rw [hall op hop]; rfl)
  have hD : (grpOf g ops cv).filter (fun op => endsAt g op && opDel op) =
      (grpOf g ops cv).filter opDel :=
    List.filter_congr (fun op hop => by rw [hall op hop]; rfl)
  have hse : ((grpOf g ops cv).filter (fun op => !endsAt g op)).isEmpty = true := by
    show (subsOf g ops cv).isEmpty = true
    rw [hs]; rfl
  simp only [sbGroup, hse, ↓reduceIte, hP, hD]

/-- A group whose operations go on: Java's count of the next segment's tree,
or of the new tree of its puts. -/
theorem sbGroup_sub {b g : Nat} {lv : List (Nat × NodeId)} {ops : List Op} {cv : Nat}
    {child : NodeId → List Op → SR} (hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op))
    (hs : subsOf g ops cv ≠ []) :
    sbGroup b g lv (grpOf g ops cv) child cv = (match lv.lookup cv with
      | some y => ((child y (subsOf g ops cv)).up, (child y (subsOf g ops cv)).cnt,
          (child y (subsOf g ops cv)).nd)
      | none => if ((subsOf g ops cv).filter (fun op => !opDel op)).isEmpty then (0, 0, 0)
        else (1, ftbOf b (opKeys ((subsOf g ops cv).filter (fun op => !opDel op))) (g + 1), 0)) := by
  have hL := subs_no_end hend hs
  have hP : ((grpOf g ops cv).filter (fun op => endsAt g op && !opDel op)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro op hop he
    have : op ∈ (grpOf g ops cv).filter (endsAt g) := by
      rw [List.mem_filter]; simp only [Bool.and_eq_true] at he; exact ⟨hop, he.1⟩
    rw [hL] at this; simp at this
  have hD : ((grpOf g ops cv).filter (fun op => endsAt g op && opDel op)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro op hop he
    have : op ∈ (grpOf g ops cv).filter (endsAt g) := by
      rw [List.mem_filter]; simp only [Bool.and_eq_true] at he; exact ⟨hop, he.1⟩
    rw [hL] at this; simp at this
  have hse : ((grpOf g ops cv).filter (fun op => !endsAt g op)).isEmpty = false := by
    show (subsOf g ops cv).isEmpty = false
    cases h : subsOf g ops cv with
    | nil => exact absurd h hs
    | cons _ _ => rfl
  have hsubs : (grpOf g ops cv).filter (fun op => !endsAt g op) = subsOf g ops cv := rfl
  have hse' : (subsOf g ops cv).isEmpty = false := hse
  simp only [sbGroup, hP, hD, hsubs, hse', Bool.false_eq_true, ↓reduceIte]
  cases lv.lookup cv <;> simp

/-! ## A leaf's list against its live list -/

theorem filter_len_le_sum (P : Nat → Bool) (kc : Nat → Nat) : ∀ (l : List Nat),
    (∀ c ∈ l, P c = true → 1 ≤ kc c) → (l.filter P).length ≤ (l.map kc).sum
  | [], _ => by simp
  | c :: r, h => by
    have ih := filter_len_le_sum P kc r (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    split
    · rename_i hc
      have := h c List.mem_cons_self hc
      simp only [List.length_cons]
      omega
    · omega

/-- **A leaf's list against its live list, puts and deletes.** The list
after the groups, es, in order: off the touched compare values as the live
list lb; on each, changed only if its group counts a klong at least. Then
PE's removed compare values and added entries are at most the groups'
klongs, it holds at most lb's entries and the added, and holds lb itself if
it removes and adds none. -/
theorem leaf_countsD {lb es : List (Nat × NodeId)} {cvs : List Nat} (kc : Nat → Nat)
    (hlb : lb.Pairwise CvLtA) (hes : es.Pairwise CvLtA)
    (hoff : ∀ c, c ∉ cvs → es.lookup c = lb.lookup c)
    (hon : ∀ cv ∈ cvs, es.lookup cv ≠ lb.lookup cv → 1 ≤ kc cv) :
    let F := es.map (fun e => (e.1, some e.2))
    (removedCvs lb F).length + (F.filter (isAdded lb)).length ≤ (cvs.map kc).sum ∧
      F.length ≤ lb.length + (F.filter (isAdded lb)).length ∧
      ((removedCvs lb F).length + (F.filter (isAdded lb)).length = 0 →
        lb.map (fun q => (q.1, some q.2)) = F) := by
  intro F
  have hFadd : F.filter (isAdded lb) = (es.filter (fun e => lb.lookup e.1 != some e.2)).map
      (fun e => (e.1, some e.2)) := by
    simp only [F, List.filter_map]
    congr 1
  have hAlen : (F.filter (isAdded lb)).length =
      (es.filter (fun e => lb.lookup e.1 != some e.2)).length := by
    rw [hFadd, List.length_map]
  -- an entry of F for c exactly when es has one
  have hFany : ∀ c, F.any (fun e => e.1 == c) = true → ∃ y, es.lookup c = some y := by
    intro c hc
    rw [List.any_eq_true] at hc
    obtain ⟨e, he, hec⟩ := hc
    simp only [F, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    simp only [beq_iff_eq] at hec
    exact ⟨e'.2, hec ▸ lookup_of_mem_sorted hes he'⟩
  -- the compare values that change
  set D := cvs.filter (fun c => es.lookup c != lb.lookup c) with hD
  have hDsum : D.length ≤ (cvs.map kc).sum :=
    filter_len_le_sum _ kc cvs (fun c hc hp => hon c hc (by simpa using hp))
  have hmemD : ∀ c, es.lookup c ≠ lb.lookup c → c ∈ D := by
    intro c hc
    have hcv : c ∈ cvs := by
      by_contra hn; exact hc (hoff c hn)
    exact List.mem_filter.mpr ⟨hcv, by simpa using hc⟩
  set RL := removedCvs lb F with hRL
  set AL := (es.filter (fun e => lb.lookup e.1 != some e.2)).map (·.1) with hAL
  have hRmem : ∀ c ∈ RL, es.lookup c = none ∧ lb.lookup c ≠ none := by
    intro c hc
    simp only [hRL, removedCvs, List.mem_map, List.mem_filter] at hc
    obtain ⟨q, ⟨hq, hqa⟩, rfl⟩ := hc
    refine ⟨?_, by rw [lookup_of_mem_sorted hlb hq]; simp⟩
    cases hy : es.lookup q.1 with
    | none => rfl
    | some y =>
      exfalso
      have : F.any (fun e => e.1 == q.1) = true := by
        rw [List.any_eq_true]
        exact ⟨(q.1, some y), List.mem_map.mpr ⟨(q.1, y), lookup_mem hy, rfl⟩, by simp⟩
      rw [this] at hqa; simp at hqa
  have hAmem : ∀ c ∈ AL, ∃ y, es.lookup c = some y ∧ lb.lookup c ≠ some y := by
    intro c hc
    simp only [hAL, List.mem_map, List.mem_filter] at hc
    obtain ⟨e, ⟨he, hne⟩, rfl⟩ := hc
    exact ⟨e.2, lookup_of_mem_sorted hes he, by simpa using hne⟩
  have hRnd : RL.Nodup := by
    simp only [hRL, removedCvs]
    rw [List.Nodup, List.pairwise_map]
    exact (hlb.filter _).imp (fun h => Nat.ne_of_lt h)
  have hAnd : AL.Nodup := by
    simp only [hAL]
    rw [List.Nodup, List.pairwise_map]
    exact (hes.filter _).imp (fun h => Nat.ne_of_lt h)
  have hnd2 : (RL ++ AL).Nodup := by
    rw [List.nodup_append]
    refine ⟨hRnd, hAnd, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨y, hy, _⟩ := hAmem a hb
    rw [(hRmem a ha).1] at hy; cases hy
  have hsub : RL ++ AL ⊆ D := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨h1, h2⟩ := hRmem c hc
      exact hmemD c (by rw [h1]; exact fun h => h2 h.symm)
    · obtain ⟨y, h1, h2⟩ := hAmem c hc
      exact hmemD c (by rw [h1]; exact fun h => h2 h.symm)
  have hRA := (List.subperm_of_subset hnd2 hsub).length_le
  rw [List.length_append] at hRA
  have hALlen : AL.length = (F.filter (isAdded lb)).length := by
    rw [hAlen, hAL, List.length_map]
  refine ⟨by omega, ?_, ?_⟩
  · -- the unchanged entries are live entries
    have hlen : F.length = (es.filter (fun e => !(lb.lookup e.1 != some e.2))).length +
        (es.filter (fun e => lb.lookup e.1 != some e.2)).length := by
      simp only [F, List.length_map]
      have := List.length_eq_length_filter_add (l := es) (fun e => !(lb.lookup e.1 != some e.2))
      simp only [Bool.not_not] at this
      omega
    have hun : (es.filter (fun e => !(lb.lookup e.1 != some e.2))).length ≤ lb.length := by
      have hnd3 : (es.filter (fun e => !(lb.lookup e.1 != some e.2))).Nodup :=
        (hes.filter _).imp (fun {a b} (h : a.1 < b.1) (he : a = b) => by
          subst he; exact lt_irrefl _ h)
      have hsub3 : es.filter (fun e => !(lb.lookup e.1 != some e.2)) ⊆ lb := by
        intro e he
        rw [List.mem_filter] at he
        have h2 := he.2
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq] at h2
        exact lookup_mem h2
      exact (List.subperm_of_subset hnd3 hsub3).length_le
    omega
  · intro h0
    have hR0 : RL = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hA0 : AL = [] := List.eq_nil_of_length_eq_zero (by omega)
    have heq : lb = es := eq_of_lookup lb es hlb hes (fun c => by
      cases hy : es.lookup c with
      | some y =>
        by_contra hne
        have : c ∈ AL := by
          simp only [hAL, List.mem_map, List.mem_filter]
          exact ⟨(c, y), ⟨lookup_mem hy, by simpa using hne⟩, rfl⟩
        rw [hA0] at this; simp at this
      | none =>
        cases hl : lb.lookup c with
        | none => rfl
        | some y =>
          exfalso
          have : c ∈ RL := by
            simp only [hRL, removedCvs, List.mem_map, List.mem_filter]
            refine ⟨(c, y), ⟨lookup_mem hl, ?_⟩, rfl⟩
            cases ha : F.any (fun e => e.1 == c) with
            | false => rfl
            | true =>
              obtain ⟨y', hy'⟩ := hFany c ha
              rw [hy] at hy'; cases hy'
          rw [hR0] at this; simp at this)
    subst heq
    rfl

/-! ## Sums -/

theorem le_sum_map {l : List Nat} {f : Nat → Nat} {c : Nat} (h : c ∈ l) : f c ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons a r ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem sum_map_four_add (l : List Nat) (f g : Nat → Nat) :
    (l.map (fun c => 4 * f c + g c)).sum = 4 * (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a r ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-! ## A segment leaf -/

/-- Java's count of a node: what `PlanSpecD` asks of `up` and `parts`, with
any deletes. -/
theorem sbNode_factsD (b : Nat) (n : KNode) (isRoot : Bool) (K nd ci below : Nat) :
    let r := sbNode b n isRoot K nd ci below
    r.nd = nd ∧ r.ci = ci ∧
      r.up = (if isRoot = true ∧ 0 < r.nd then r.ci else 0) +
        (if r.ov = 0 then 0 else if isRoot = true then r.ov + 1 else r.parts) ∧
      (r.ov ≠ 0 → r.ov + 1 ≤ r.parts) ∧
      r.ov = overflowsD b K n.ks.length (decide (0 < nd)) (some (deadCount n.ks)) ∧
      r.parts = (if r.ov = 0 then 0 else max (r.ov + 1) (cutPartsBound b (n.ks.length + K))) := by
  intro r
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  intro h; simp only [r, sbNode] at h ⊢; rw [ite_eq_right h]; exact le_max_left _ _

/-- **A segment leaf, puts and deletes**, given the next segments' trees at
lower fuels. -/
theorem leaf_stepD {b G H F : Nat} (hb : 8 ≤ b)
    (IHt : ∀ f < F, TreePPD b (Cfg.java b G H) i s f) :
    ∀ (x : NodeId) (g : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
      (fs : Nat), Shaped (Cfg.java b G H) s g 0 x → (∃ lo hi, Good s x lo hi) →
      Filled (Cfg.java b G H) s isRoot x → OpsD g ops → ops ≠ [] → s.fuel x ≤ fs → NoJoinsAt (Cfg.java b G H) i s fs x g ops →
      plan (Cfg.java b G H) i s (F + 1) x g 0 ops acc = some (v, acc') →
      PlanSpecD b s g 0 x isRoot v acc acc' (sbPlan b s fs x g ops isRoot) := by
  intro x g ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hNo hpl
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s x = some n := hgk
  simp only [beq_self_eq_true] at hleaf
  obtain ⟨lo, hi, hg⟩ := hgood
  obtain ⟨hwf, hkey⟩ := good_key hg hobj
  have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
  obtain ⟨fs', rfl⟩ : ∃ fs', fs = fs' + 1 := ⟨fs - 1, by omega⟩
  simp only [NoJoinsAt, hgkD, hleaf, ↓reduceIte] at hNo
  have hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op) :=
    fun op hop => endsAt_isLong (hops op hop).1 (hops op hop).2
  set lv := live n.ks with hlv
  set child : NodeId → List Op → SR := fun y subs => sbPlan b s fs' y (g + 1) subs true
  set SG := fun cv => sbGroup b g lv (grpOf g ops cv) child cv with hSG
  -- plan's leaf
  rw [plan.eq_def] at hpl
  simp only at hpl
  rw [hgk] at hpl
  simp only [beq_self_eq_true, ↓reduceIte] at hpl
  cases hag : applyGroups (Cfg.java b G H) i s F g lv (List.map (segAt g) ops).eraseDups ops acc with
  | none => rw [hag] at hpl; cases hpl
  | some q =>
    obtain ⟨es, acc1⟩ := q
    rw [hag] at hpl
    simp only at hpl
    unfold mkNode at hpl
    simp only [beq_self_eq_true, ↓reduceIte] at hpl
    rw [hgk] at hpl
    simp only [Option.some.injEq, Prod.mk.injEq] at hpl
    obtain ⟨rfl, rfl⟩ := hpl
    rw [flatMap_ents_old]
    -- the groups
    set Q : Nat → Option NodeId → Prop := fun cv res =>
      (lv.lookup cv ≠ res → 1 ≤ 4 * (SG cv).2.2 + (SG cv).1) ∧
      (res = none → lv.lookup cv ≠ none → 1 ≤ (SG cv).2.2) with hQ
    have hT : ∀ f, f < F → ∀ cv acc0 res acc1', subsOf g ops cv ≠ [] →
        planTree (Cfg.java b G H) i s f (lv.lookup cv) (g + 1) (subsOf g ops cv) acc0 =
          some (res, acc1') →
        kw acc1' ≤ kw acc0 + (SG cv).2.1 ∧ Q cv res := by
      intro f hf cv acc0 res acc1' hsne hpt
      simp only [hQ, hSG]
      have hSGs := sbGroup_sub (b := b) (lv := lv) (cv := cv) (child := child) hend hsne
      obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hsne
      have hop' := hop
      unfold subsOf grpOf at hop'
      simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hop'
      have hlong : isLong cv = true := by
        have := hend op hop'.1.1
        rw [hop'.2, hop'.1.2] at this
        simpa using this.symm
      have hsops : ∀ o ∈ subsOf g ops cv, keyWf o.key = true ∧ g + 1 < o.key.length := by
        intro o ho
        have ho' := ho
        unfold subsOf grpOf at ho'
        simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at ho'
        obtain ⟨h1, h2⟩ := hops o ho'.1.1
        refine ⟨h1, ?_⟩
        have := ho'.2; simp only [endsAt, beq_eq_false_iff_ne] at this; omega
      cases hl : lv.lookup cv with
      | some y =>
        rw [hl] at hpt hSGs
        simp only at hSGs
        have hmem : (cv, y) ∈ lv := lookup_mem hl
        obtain ⟨m, hm, hmlev, hmne⟩ := hkey cv y hmem (fun _ => hlong)
        have hsh' := shaped_kid_leaf hsh hobj (by simpa using hleaf) hmem hlong
        have hgood' : ∃ lo hi, Good s y lo hi := by
          rcases good_kids hg hobj cv y hmem with ⟨m', hm', _, lo', hi', hg'⟩ | ⟨v', hv'⟩
          · exact ⟨lo', hi', hg'⟩
          · rw [hm] at hv'; cases hv'
        have hfill' := (filled_key hfill hobj).2.2.1 cv y hmem (by simpa using hleaf) hlong
        have hfy : s.fuel y ≤ fs' := by simp [Tree.fuel, hm]; omega
        have hlive : ∀ n', DNB.getKey s y = some n' → live n'.ks ≠ [] := by
          intro n' hn'
          have : n' = m := by
            unfold DNB.getKey at hn'; rw [hm] at hn'; simpa using hn'.symm
          rw [this]; exact hmne
        have ht := IHt f hf y (g + 1) _ acc0 res acc1' fs' hsh' hgood' hfill' hlive hsops
          hsne hfy (by
            have hcv : cv ∈ touched g ops := mem_touched.mpr ⟨op, hop'.1.1, hop'.1.2⟩
            have hn := hNo cv hcv
            change (match lv.lookup cv with
              | none => True
              | some y => subsOf g ops cv ≠ [] →
                NoJoinsAt (Cfg.java b G H) i s fs' y (g + 1) (subsOf g ops cv)) at hn
            rw [hl] at hn
            exact hn hsne) hpt
        change TreePD y res acc0 acc1' (child y (subsOf g ops cv)) at ht
        obtain ⟨t1, t2, t3⟩ := ht
        rw [hSGs]
        dsimp only
        refine ⟨t1, fun hne' => ?_, fun hn _ => ?_⟩
        · cases res with
          | none => have := t2 rfl; omega
          | some y' =>
            rcases t3 y' rfl with rfl | h1
            · exact absurd rfl hne'
            · omega
        · have := t2 hn; omega
      | none =>
        rw [hl] at hpt hSGs
        simp only at hSGs
        obtain ⟨t1, t2⟩ := fresh_le_del_ftb (i := i) (s := s) (G := G) (H := H) hb hsops hpt
        rw [hSGs]
        cases hP : ((subsOf g ops cv).filter (fun op => !opDel op)).isEmpty
        · simp only [hP, Bool.false_eq_true, ↓reduceIte] at t1 ⊢
          exact ⟨t1, fun _ => le_refl _, fun _ hn => absurd rfl hn⟩
        · simp only [hP, ↓reduceIte] at t1 t2 ⊢
          refine ⟨by omega, fun hne' => ?_, fun _ hn => absurd rfl hn⟩
          cases res with
          | none => exact absurd rfl hne'
          | some y' => have := t2 (by simp); cases this
    obtain ⟨a1, a2, a3, a4⟩ := agl_loop (cf := Cfg.java b G H) (i := i) (s := s) (lb := lv) hend
      (fun cv => (SG cv).2.1) Q F hT (touched g ops) F lv acc es acc1 le_rfl (nodup_touched g ops)
      (fun _ _ => rfl) (live_sorted n.ks) hag
    -- each compare value
    have hon : ∀ cv ∈ touched g ops,
        (es.lookup cv ≠ lv.lookup cv → 1 ≤ 4 * (SG cv).2.2 + (SG cv).1) ∧
        (es.lookup cv = none → lv.lookup cv ≠ none → 1 ≤ (SG cv).2.2) := by
      intro cv hcv
      rcases a4 cv hcv with ⟨hs, hch⟩ | ⟨_, hq⟩
      · have hSGe := sbGroup_end (b := b) (lv := lv) (child := child) hs
        have hdel : ∀ op ∈ grpOf g ops cv, opDel op = true →
            1 ≤ ((grpOf g ops cv).filter opDel).length :=
          fun op hop hp => List.length_pos_of_mem (List.mem_filter.mpr ⟨hop, hp⟩)
        have hput : ∀ op ∈ grpOf g ops cv, opDel op = false →
            1 ≤ ((grpOf g ops cv).filter (fun op => !opDel op)).length :=
          fun op hop hp => List.length_pos_of_mem (List.mem_filter.mpr ⟨hop, by simp [hp]⟩)
        simp only [SG, hSGe]
        refine ⟨fun hne' => ?_, fun hn hl => ?_⟩
        · obtain ⟨hA, hB⟩ := hch hne'
          by_cases hn : es.lookup cv = none
          · obtain ⟨op, hop, hp⟩ := hB hn
            have := hdel op hop hp; omega
          · obtain ⟨op, hop, hp⟩ := hA hn
            have := hput op hop hp; omega
        · have hne' : es.lookup cv ≠ lv.lookup cv := by rw [hn]; exact fun h => hl h.symm
          obtain ⟨op, hop, hp⟩ := (hch hne').2 hn
          exact hdel op hop hp
      · obtain ⟨q1, q2⟩ := hq
        exact ⟨fun h => q1 (fun h' => h h'.symm), q2⟩
    obtain ⟨l1, l2, l3⟩ := leaf_countsD (fun cv => 4 * (SG cv).2.2 + (SG cv).1) (live_sorted n.ks) a2
      a3 (fun cv hcv => (hon cv hcv).1)
    -- Java's count of the leaf
    have hsb : sbPlan b s (fs' + 1) x g ops isRoot = sbNode b n isRoot
        (4 * ((touched g ops).map (fun cv => (SG cv).2.2)).sum +
          ((touched g ops).map (fun cv => (SG cv).1)).sum)
        ((touched g ops).map (fun cv => (SG cv).2.2)).sum 0
        ((touched g ops).map (fun cv => (SG cv).2.1)).sum := by
      rw [sbPlan.eq_def]
      simp only [hgkD, hleaf, ↓reduceIte, List.map_map]
      rfl
    rw [sum_map_four_add] at l1
    rw [hsb]
    set nd := ((touched g ops).map (fun cv => (SG cv).2.2)).sum with hnd
    set K := 4 * nd + ((touched g ops).map (fun cv => (SG cv).1)).sum with hK
    set below := ((touched g ops).map (fun cv => (SG cv).2.1)).sum with hbelow
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := sbNode_factsD b n isRoot K nd 0 below
    have hlvl : (live n.ks).length ≤ n.ks.length := live_length_le n.ks
    have hdec : ∀ k, decideNode (Cfg.java b G H) i (some n) false (es.map (fun e => (e.1, some e.2))) =
        .parts k → 0 < (sbNode b n isRoot K nd 0 below).ov ∧
          k ≤ (sbNode b n isRoot K nd 0 below).parts := by
      intro k hk
      obtain ⟨d1, d2⟩ := dec_parts_ov (F := es.map (fun e => (e.1, some e.2))) (K := K)
        (merged := decide (0 < nd)) hwf (by omega) l3 (by omega) hk
      rw [f5]
      refine ⟨d1, ?_⟩
      rw [f6, f5, ite_eq_right (by omega)]
      exact d2
    have hbel : kw acc1 ≤ kw acc + below := by
      refine le_trans a1 (Nat.add_le_add_left (sum_map_le_pointwise (fun cv _ => ?_)) _)
      split
      · exact Nat.zero_le _
      · exact le_refl _
    refine ⟨⟨n, _, _, _, hgkD, rfl, hdec, ?_, by simpa using l2⟩,
      ⟨nd, le_refl _, ?_⟩, f3, f4, fun _ h0 => absurd rfl h0⟩
    · -- each live entry lost has a delete
      rw [f1, List.length_map]
      change lv.length ≤ es.length + nd
      have hA : (lv.filter (fun q => (es.lookup q.1).isSome)).length ≤ es.length := by
        apply len_le_of_lookup ((live_sorted n.ks).filter _)
        intro q hq
        rw [List.mem_filter] at hq
        exact Option.isSome_iff_exists.mp hq.2
      have hB : (lv.filter (fun q => !(es.lookup q.1).isSome)).length ≤ nd := by
        have hnd1 : ((lv.filter (fun q => !(es.lookup q.1).isSome)).map (·.1)).Nodup := by
          rw [List.Nodup, List.pairwise_map]
          exact ((live_sorted n.ks).filter _).imp (fun h => Nat.ne_of_lt h)
        have hsub : (lv.filter (fun q => !(es.lookup q.1).isSome)).map (·.1) ⊆
            (touched g ops).filter (fun cv => decide (1 ≤ (SG cv).2.2)) := by
          intro c hc
          rw [List.mem_map] at hc
          obtain ⟨q, hq, rfl⟩ := hc
          rw [List.mem_filter] at hq
          have hy : es.lookup q.1 = none := by simpa using hq.2
          have hct : q.1 ∈ touched g ops := by
            by_contra hn
            rw [a3 q.1 hn, lookup_live hq.1] at hy; cases hy
          refine List.mem_filter.mpr ⟨hct, ?_⟩
          have := (hon q.1 hct).2 hy (by rw [lookup_live hq.1]; simp)
          simpa using this
        have h1 := (List.subperm_of_subset hnd1 hsub).length_le
        rw [List.length_map] at h1
        have h2 := filter_len_le_sum (fun cv => decide (1 ≤ (SG cv).2.2)) (fun cv => (SG cv).2.2)
          (touched g ops) (fun c _ hp => by simpa using hp)
        change (lv.filter (fun q => !(es.lookup q.1).isSome)).length ≤
          ((touched g ops).map (fun cv => (SG cv).2.2)).sum
        exact le_trans h1 h2
      have hsplit : lv.length = (lv.filter (fun q => (es.lookup q.1).isSome)).length +
          (lv.filter (fun q => !(es.lookup q.1).isSome)).length :=
        List.length_eq_length_filter_add _
      omega
    · have hc := dcost_le hdec
      have hcnt := sbNode_cnt b n isRoot K nd 0 below
      simp only [vcost, vcostL_old, add_zero]
      omega

end Contract.PE
