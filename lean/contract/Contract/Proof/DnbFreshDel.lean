/-
bergdb 030-36: a new segment tree for operations that may include deletes.
PE plans a new tree (`planTree` from no root) for the operations of keys
whose segment g is not in the leaf above. It starts from no entries: a put
sets a value, a delete removes the entry, and the operations of longer keys
plan a new tree below, whose root, or none, is the entry. So the leaf's
final entries are only compare values with a put, and a tree of deletes only
is empty and writes no key node. What it writes is at most Java's
`freshTreeBound` of the puts' keys, which is what Java counts
(`fresh_le_del`); in the form of `sbGroup`, with `ftbOf` (`fresh_le_del_ftb`).
-/
import Contract.Proof.DnbFresh

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-- The puts of a list of operations. -/
def putsOf (ops : List Op) : List Op := ops.filter (fun op => !opDel op)

/-- The operations of a new tree at segment g: well-formed keys longer than
g; the puts' keys of at most g + F' segments. -/
def FreshOpsD (g F' : Nat) (ops : List Op) : Prop :=
  ∀ op ∈ ops, keyWf op.key = true ∧ g < op.key.length ∧ (opDel op = false → op.key.length ≤ g + F')

/-- Keys of at most g + F' segments, puts and deletes, are `FreshOpsD`. -/
theorem freshOpsD_of_len {g F' : Nat} {ops : List Op}
    (h : ∀ op ∈ ops, keyWf op.key = true ∧ g < op.key.length ∧ op.key.length ≤ g + F') :
    FreshOpsD g F' ops :=
  fun op hop => ⟨(h op hop).1, (h op hop).2.1, fun _ => (h op hop).2.2⟩

/-! ## A leaf's groups in a new tree -/

/-- The fold of a group's operations that end at the leaf, puts and deletes:
no key node written, the order kept, the other compare values kept, and an
entry for cv only if it had one or the group has a put. -/
theorem fold_mixed {cv : Nat} : ∀ (L : List Op) (es : List (Nat × NodeId)) (acc : Acc),
    let q := L.foldl (fun (q : List (Nat × NodeId) × Acc) op =>
      match op with
      | .put _ hv =>
        let (y, a) := q.2.fresh
        (setEntry cv y q.1, a.write y (.val hv))
      | .del _ => (removeEntry cv q.1, q.2)) (es, acc)
    kw q.2 = kw acc ∧ (es.Pairwise CvLtA → q.1.Pairwise CvLtA) ∧
      (∀ c, c ≠ cv → q.1.lookup c = es.lookup c) ∧
      (∀ y, q.1.lookup cv = some y → es.lookup cv = some y ∨ ∃ op ∈ L, opDel op = false)
  | [], es, acc => by
    refine ⟨rfl, id, fun _ _ => rfl, fun y hy => Or.inl hy⟩
  | op :: L, es, acc => by
    simp only [List.foldl_cons]
    cases op with
    | put k hv =>
      simp only
      have ih := fold_mixed (cv := cv) L (setEntry cv acc.fresh.1 es)
        ((acc.fresh.2).write acc.fresh.1 (.val hv))
      simp only at ih
      obtain ⟨i1, i2, i3, _⟩ := ih
      refine ⟨by rw [i1, kw_write_val, kw_fresh], fun hs => i2 (setEntry_sorted _ _ hs),
        fun c hc => by rw [i3 c hc, setEntry_lookup, ite_eq_right hc],
        fun _ _ => Or.inr ⟨.put k hv, List.mem_cons_self, rfl⟩⟩
    | del k =>
      simp only
      have ih := fold_mixed (cv := cv) L (removeEntry cv es) acc
      simp only at ih
      obtain ⟨i1, i2, i3, i4⟩ := ih
      refine ⟨i1, fun hs => i2 (hs.filter _),
        fun c hc => by rw [i3 c hc, removeEntry_lookup, ite_eq_right hc], fun y hy => ?_⟩
      rcases i4 y hy with h | ⟨op, hop, hp⟩
      · rw [removeEntry_lookup, ite_eq_left rfl] at h; cases h
      · exact Or.inr ⟨op, List.mem_cons_of_mem _ hop, hp⟩

/-- **A leaf's groups in a new tree.** Given what each next segment's new
tree does (at most `B cv` key nodes, a root only if it has a put), the key
nodes written are at most the sum of the bounds, and a compare value of the
groups ends with an entry only if its group has a put. -/
theorem agd_loop {g : Nat} {ops : List Op}
    (hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op))
    (B : Nat → Nat) (F0 : Nat)
    (hT : ∀ f, f < F0 → ∀ cv acc0 res acc1, subsOf g ops cv ≠ [] →
      planTree cf i s f none (g + 1) (subsOf g ops cv) acc0 = some (res, acc1) →
      kw acc1 ≤ kw acc0 + B cv ∧ (res ≠ none → ∃ op ∈ subsOf g ops cv, opDel op = false)) :
    ∀ (cvs : List Nat) (f : Nat) (es1 : List (Nat × NodeId)) (acc : Acc)
      (es : List (Nat × NodeId)) (acc' : Acc), f ≤ F0 → cvs.Nodup →
      (∀ c ∈ cvs, es1.lookup c = none) → es1.Pairwise CvLtA →
      applyGroups cf i s f g es1 cvs ops acc = some (es, acc') →
      kw acc' ≤ kw acc + (cvs.map (fun cv => if subsOf g ops cv = [] then 0 else B cv)).sum ∧
      es.Pairwise CvLtA ∧ (∀ c, c ∉ cvs → es.lookup c = es1.lookup c) ∧
      (∀ cv ∈ cvs, ∀ y, es.lookup cv = some y → ∃ op ∈ grpOf g ops cv, opDel op = false)
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
    generalize hq : List.foldl _ (es1, acc) _ = q at h hfm
    obtain ⟨es2, acc2⟩ := q
    simp only at hfm h
    obtain ⟨f1, f2, f3, f4⟩ := hfm
    have hs2 := f2 hs1
    have hsubs : ((ops.filter (fun op => segAt g op == cv)).filter (fun op => !endsAt g op)) =
        subsOf g ops cv := rfl
    rw [hsubs] at h
    have hcvs : ∀ c ∈ cvs, c ≠ cv := fun c hc he => hnd'.1 (he ▸ hc)
    have hcv0 : es1.lookup cv = none := hl1 cv List.mem_cons_self
    split at h
    · rename_i hse
      have hse' : subsOf g ops cv = [] := by simpa using hse
      obtain ⟨i1, i2, i3, i4⟩ := agd_loop hend B F0 hT cvs f' es2 acc2 es acc' (by omega)
        hnd'.2 (fun c hc => by rw [f3 c (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)]) hs2 h
      refine ⟨?_, i2, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte, zero_add]
        omega
      · intro c hc
        simp only [List.mem_cons, not_or] at hc
        rw [i3 c hc.2, f3 c hc.1]
      · intro c hc y hy
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [i3 c hnd'.1] at hy
          rcases f4 y hy with h0 | ⟨op, hop, hp⟩
          · rw [hcv0] at h0; cases h0
          · exact ⟨op, List.mem_of_mem_filter hop, hp⟩
        · exact i4 c hc y hy
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
        obtain ⟨i1, i2, i3, i4⟩ := agd_loop hend B F0 hT cvs f' (setEntry cv y es1) acc3 es acc'
          (by omega) hnd'.2 (fun c hc => by
            rw [setEntry_lookup, ite_eq_right (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)])
          (setEntry_sorted _ _ hs1) h
        refine ⟨?_, i2, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte]
          omega
        · intro c hc
          simp only [List.mem_cons, not_or] at hc
          rw [i3 c hc.2, setEntry_lookup, ite_eq_right hc.1]
        · intro c hc y' hy'
          rcases List.mem_cons.mp hc with rfl | hc
          · obtain ⟨op, hop, hp⟩ := t2 (by simp)
            exact ⟨op, List.mem_of_mem_filter hop, hp⟩
          · exact i4 c hc y' hy'
      · rename_i acc3 htr
        obtain ⟨t1, _⟩ := hT f' (by omega) cv acc none acc3 hse' htr
        obtain ⟨i1, i2, i3, i4⟩ := agd_loop hend B F0 hT cvs f' (removeEntry cv es1) acc3 es acc'
          (by omega) hnd'.2 (fun c hc => by
            rw [removeEntry_lookup, ite_eq_right (hcvs c hc), hl1 c (List.mem_cons_of_mem _ hc)])
          (hs1.filter _) h
        refine ⟨?_, i2, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hse', ↓reduceIte]
          omega
        · intro c hc
          simp only [List.mem_cons, not_or] at hc
          rw [i3 c hc.2, removeEntry_lookup, ite_eq_right hc.1]
        · intro c hc y' hy'
          rcases List.mem_cons.mp hc with rfl | hc
          · rw [i3 c hnd'.1, removeEntry_lookup, ite_eq_left rfl] at hy'
            cases hy'
          · exact i4 c hc y' hy'

/-! ## Counting -/

theorem sum_map_le_pointwise {T : List Nat} {φ ψ : Nat → Nat} (h : ∀ c ∈ T, φ c ≤ ψ c) :
    (T.map φ).sum ≤ (T.map ψ).sum := by
  induction T with
  | nil => simp
  | cons c r ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h c List.mem_cons_self
    have h2 := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    omega

theorem sum_map_filter_ne (T : List Nat) (φ : Nat → Nat) :
    (T.map φ).sum = ((T.filter (fun c => decide (φ c ≠ 0))).map φ).sum := by
  induction T with
  | nil => rfl
  | cons c r ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases hc : φ c = 0
    · simp [hc, ih]
    · simp [hc, ih]

/-- A sum over a list without duplicates is at most the sum over a list that
holds each of its compare values whose term is not 0. -/
theorem sum_le_of_vanish {T T' : List Nat} (hT : T.Nodup) (φ : Nat → Nat)
    (h : ∀ c ∈ T, φ c ≠ 0 → c ∈ T') : (T.map φ).sum ≤ (T'.map φ).sum := by
  rw [sum_map_filter_ne T φ]
  have hsub : T.filter (fun c => decide (φ c ≠ 0)) ⊆ T' := by
    intro c hc
    rw [List.mem_filter] at hc
    exact h c hc.1 (by simpa using hc.2)
  obtain ⟨l, hp, hs⟩ := List.subperm_of_subset (hT.filter _) hsub
  exact subperm_sum_le ⟨l.map φ, hp.map φ, hs.map φ⟩

/-- The puts of a compare value's operations that go on are those of the
puts. -/
theorem subsOf_putsOf (g : Nat) (ops : List Op) (cv : Nat) :
    putsOf (subsOf g ops cv) = subsOf g (putsOf ops) cv := by
  simp only [putsOf, subsOf, grpOf, List.filter_filter]
  apply List.filter_congr
  intro op _
  cases opDel op <;> simp [Bool.and_comm]

theorem exists_put_iff (ops : List Op) : (∃ op ∈ ops, opDel op = false) ↔ putsOf ops ≠ [] := by
  constructor
  · rintro ⟨op, hop, hp⟩ h
    have : op ∈ putsOf ops := List.mem_filter.mpr ⟨hop, by simp [hp]⟩
    rw [h] at this; simp at this
  · intro h
    obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ h
    rw [putsOf, List.mem_filter] at hop
    exact ⟨op, hop.1, by simpa using hop.2⟩

/-- The leaf of a new tree has an entry only for a compare value whose
group has a put: at most the compare values the puts touch. -/
theorem leaf_len_puts {g : Nat} {ops : List Op} {es : List (Nat × NodeId)}
    (hes : es.Pairwise CvLtA) (hoff : ∀ c, c ∉ touched g ops → es.lookup c = none)
    (hon : ∀ cv ∈ touched g ops, ∀ y, es.lookup cv = some y → ∃ op ∈ grpOf g ops cv, opDel op = false) :
    es.length ≤ (touched g (putsOf ops)).length := by
  have hnd : (es.map (·.1)).Nodup := by
    rw [List.Nodup, List.pairwise_map]; exact hes.imp (fun h => Nat.ne_of_lt h)
  have hsub : es.map (·.1) ⊆ touched g (putsOf ops) := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨e, he, rfl⟩ := hc
    have hel : es.lookup e.1 = some e.2 := lookup_of_mem_sorted hes he
    have hin : e.1 ∈ touched g ops := by
      by_contra hn
      rw [hoff e.1 hn] at hel; cases hel
    obtain ⟨op, hop, hp⟩ := hon e.1 hin e.2 hel
    unfold grpOf at hop
    rw [List.mem_filter, beq_iff_eq] at hop
    exact mem_touched.mpr ⟨op, List.mem_filter.mpr ⟨hop.1, by simp [hp]⟩, hop.2⟩
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

/-- The new trees below a new tree's leaf, each bounded by its puts (nothing
if it has none), are Java's trees below of the puts. -/
theorem subs_sum_del {g : Nat} {ops : List Op} (hg : ∀ op ∈ ops, g < op.key.length)
    (h : List Key → Nat) :
    ((touched g ops).map (fun cv => if subsOf g ops cv = [] then 0 else
      (if ∃ op ∈ subsOf g ops cv, opDel op = false then h (opKeys (putsOf (subsOf g ops cv)))
        else 0))).sum
      ≤ ((freshGroup g (opKeys (putsOf ops))).2.map (fun q => h q.2)).sum := by
  have hgP : ∀ op ∈ putsOf ops, g < op.key.length := fun op hop => hg op (List.mem_of_mem_filter hop)
  calc _ ≤ ((touched g ops).map (fun cv => if subsOf g (putsOf ops) cv = [] then 0
          else h (opKeys (subsOf g (putsOf ops) cv)))).sum := by
        apply sum_map_le_pointwise
        intro cv _
        split
        · exact Nat.zero_le _
        · split
          · rename_i hp
            rw [exists_put_iff, subsOf_putsOf] at hp
            rw [ite_eq_right hp, subsOf_putsOf]
          · exact Nat.zero_le _
    _ ≤ ((touched g (putsOf ops)).map (fun cv => if subsOf g (putsOf ops) cv = [] then 0
          else h (opKeys (subsOf g (putsOf ops) cv)))).sum := by
        apply sum_le_of_vanish (nodup_touched g ops)
        intro c _ hne
        have hs : subsOf g (putsOf ops) c ≠ [] := by
          intro h0; rw [h0] at hne; simp at hne
        obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hs
        unfold subsOf grpOf at hop
        rw [List.mem_filter, List.mem_filter, beq_iff_eq] at hop
        exact mem_touched.mpr ⟨op, hop.1.1, hop.1.2⟩
    _ ≤ _ := subs_sum_le hgP h

/-! ## A new tree -/

/-- **A new segment tree, puts and deletes**, writes at most Java's
`freshTreeBound` of its puts' keys (nothing if it has no put), and has a root
only if it has a put. -/
theorem fresh_le_del {b G H : Nat} (hb : 8 ≤ b) : ∀ (F' f g : Nat) (ops : List Op) (acc : Acc)
    (res : Option NodeId) (acc' : Acc), FreshOpsD g F' ops →
    planTree (Cfg.java b G H) i s f none g ops acc = some (res, acc') →
    kw acc' ≤ kw acc + (if ∃ op ∈ ops, opDel op = false then
      freshTreeBound b F' (opKeys (putsOf ops)) g else 0) ∧
    (res ≠ none → ∃ op ∈ ops, opDel op = false) := by
  intro F' f
  induction f using Nat.strong_induction_on generalizing F' with
  | _ f ih =>
  intro g ops acc res acc' hops hpt
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := by
    cases f with
    | zero => simp [planTree] at hpt
    | succ f' => exact ⟨f', rfl⟩
  rw [planTree.eq_def] at hpt
  simp only at hpt
  have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2.1
  have hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op) :=
    fun op hop => endsAt_isLong (hops op hop).1 (hg op hop)
  -- the groups
  cases hag : applyGroups (Cfg.java b G H) i s f g [] (List.map (segAt g) ops).eraseDups ops acc with
  | none => rw [hag] at hpt; simp at hpt
  | some p =>
    obtain ⟨es, acc1⟩ := p
    rw [hag] at hpt
    simp only at hpt
    set B : Nat → Nat := fun cv => if ∃ op ∈ subsOf g ops cv, opDel op = false then
      freshTreeBound b (F' - 1) (opKeys (putsOf (subsOf g ops cv))) (g + 1) else 0 with hBdef
    have hT : ∀ f', f' < f → ∀ cv acc0 res0 acc1', subsOf g ops cv ≠ [] →
        planTree (Cfg.java b G H) i s f' none (g + 1) (subsOf g ops cv) acc0 = some (res0, acc1') →
        kw acc1' ≤ kw acc0 + B cv ∧ (res0 ≠ none → ∃ op ∈ subsOf g ops cv, opDel op = false) := by
      intro f' hf' cv acc0 res0 acc1' _ hpt'
      have hsops : FreshOpsD (g + 1) (F' - 1) (subsOf g ops cv) := by
        intro op hop
        unfold subsOf grpOf at hop
        simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hop
        obtain ⟨h1, h2, h3⟩ := hops op hop.1.1
        simp only [endsAt, beq_eq_false_iff_ne] at hop
        refine ⟨h1, by omega, fun hp => ?_⟩
        have := h3 hp
        omega
      exact ih f' (by omega) (F' - 1) (g + 1) _ acc0 res0 acc1' hsops hpt'
    obtain ⟨a1, a2, a3, a4⟩ := agd_loop (cf := Cfg.java b G H) (i := i) (s := s) hend B f hT
      (touched g ops) f [] acc es acc1 le_rfl (nodup_touched g ops) (fun _ _ => rfl)
      List.Pairwise.nil hag
    have hlen : es.length ≤ (touched g (putsOf ops)).length :=
      leaf_len_puts a2 (fun c hc => by rw [a3 c hc]; rfl) a4
    have hsum := subs_sum_del hg (fun ks => freshTreeBound b (F' - 1) ks (g + 1))
    have hput_es : es ≠ [] → ∃ op ∈ ops, opDel op = false := by
      intro hne
      rw [exists_put_iff]
      intro h0
      rw [h0, touched_nil] at hlen
      exact hne (List.eq_nil_of_length_eq_zero (by simpa using hlen))
    -- the bound of the trees below
    have hbelow : kw acc1 ≤ kw acc + (if ∃ op ∈ ops, opDel op = false then
        ((freshGroup g (opKeys (putsOf ops))).2.map
          (fun q => freshTreeBound b (F' - 1) q.2 (g + 1))).sum else 0) := by
      split
      · exact le_trans a1 (by simpa [B] using hsum)
      · rename_i hp
        rw [exists_put_iff, not_not] at hp
        have : ((touched g ops).map (fun cv => if subsOf g ops cv = [] then 0 else B cv)).sum = 0 := by
          apply le_antisymm _ (Nat.zero_le _)
          refine le_trans (by simpa [B] using hsum) ?_
          rw [hp]; simp [opKeys, freshGroup]
        omega
    -- the new leaf
    set F0 := List.flatMap (fun e => ents e.1 e.2) (es.map (fun e => (e.1, VN.old e.2)))
    have hmk : mkNode (Cfg.java b G H) i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) =
        if (Cfg.java b G H).G < g ∨ (Cfg.java b G H).H < 0 then none
        else some (.node none g 0 false (es.map (fun e => (e.1, VN.old e.2))) F0
          (decideNode (Cfg.java b G H) i none false F0)) := by
      unfold mkNode; simp only [beq_self_eq_true, ↓reduceIte, F0]
      split <;> simp_all
    rw [hmk] at hpt
    by_cases hgc : (Cfg.java b G H).G < g ∨ (Cfg.java b G H).H < 0
    · rw [ite_eq_left hgc] at hpt; simp at hpt
    · rw [ite_eq_right hgc, Option.map_some] at hpt
      simp only at hpt
      have hF0 : F0.length = es.length := by
        simp only [F0, List.flatMap_map]
        rw [List.length_flatMap]
        simp [ents]
      have hdec : decideNode (Cfg.java b G H) i none false F0 =
          .parts (cutPartsBound b es.length) := by
        simp only [decideNode, Bool.false_eq_true, ↓reduceIte, hF0, cutParts_java]
      rw [hdec] at hpt
      by_cases hes : es = []
      · -- an empty leaf: no tree, and nothing more written
        have hF0e : F0 = [] := by simp [F0, hes]
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
          cases f with
          | zero => simp [settleRoot] at hpt
          | succ f' => exact ⟨f', rfl⟩
        rw [settleRoot.eq_def] at hpt
        simp [hF0e] at hpt
        obtain ⟨rfl, rfl⟩ := hpt
        refine ⟨?_, fun h => absurd rfl h⟩
        by_cases hput : ∃ op ∈ ops, opDel op = false
        · rw [ite_eq_left hput] at hbelow ⊢
          obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := by
            obtain ⟨op, hop, hp⟩ := hput
            have := (hops op hop).2.2 hp
            have := hg op hop
            exact ⟨F' - 1, by omega⟩
          refine hbelow.trans (Nat.add_le_add_left ?_ _)
          simp only [freshTreeBound, Nat.add_sub_cancel]
          omega
        · rw [ite_eq_right hput] at hbelow ⊢
          exact hbelow
      · have hput := hput_es hes
        have hFne : F0 ≠ [] := by
          intro h0; rw [h0] at hF0
          exact hes (List.eq_nil_of_length_eq_zero hF0.symm)
        split at hpt
        · cases hpt
        · rename_i hset
          obtain ⟨v', hv, _⟩ := settle_chain (i := i) (s := s) hb f none 0 false
            (es.map (fun e => (e.1, VN.old e.2))) F0 _ _ hFne (fun h => absurd rfl h) hset
          cases hv
        · rename_i v1 hset
          obtain ⟨v', hv, hv', _⟩ := settle_chain (i := i) (s := s) hb f none 0 false
            (es.map (fun e => (e.1, VN.old e.2))) F0 _ _ hFne (fun h => absurd rfl h) hset
          cases hv
          split at hpt
          · rename_i c y acc2 hem
            simp only [Option.some.injEq, Prod.mk.injEq] at hpt
            obtain ⟨rfl, rfl⟩ := hpt
            refine ⟨?_, fun _ => hput⟩
            rw [ite_eq_left hput] at hbelow ⊢
            have hkw := emit_kw v1 acc1 _ acc2 hem
            simp only [vcost, dcost, vcostL_old] at hv'
            have hra := raOf_le b (cutPartsBound b es.length)
            have hkl := touched_le_klongs (ops := putsOf ops)
              (fun op hop => hg op (List.mem_of_mem_filter hop))
            have hmono := cutPartsBound_mono b (le_trans hlen hkl)
            have hra2 := rootsAbove_mono hb hmono
            obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := by
              obtain ⟨op, hop, hp⟩ := hput
              have := (hops op hop).2.2 hp
              have := hg op hop
              exact ⟨F' - 1, by omega⟩
            simp only [freshTreeBound, Nat.add_sub_cancel] at hbelow ⊢
            set K := (freshGroup g (opKeys (putsOf ops))).1
            have : cutPartsBound b K + rootsAbove b (cutPartsBound b K) ≤
                max (1 + freshSplits b (K + 1) (overflows b K 0 false))
                  (cutPartsBound b K + rootsAbove b (cutPartsBound b K)) :=
              le_max_right _ _
            omega
          · cases hpt

theorem len_le_foldl_max : ∀ (keys : List Key) (m : Nat) (k : Key), k ∈ keys →
    k.length ≤ keys.foldl (fun m (k : Key) => max m k.length) m
  | [], _, _, h => by simp at h
  | k' :: r, m, k, h => by
    simp only [List.foldl_cons]
    have hge : ∀ (l : List Key) (a : Nat), a ≤ l.foldl (fun m (k : Key) => max m k.length) a := by
      intro l; induction l with
      | nil => intro a; exact le_rfl
      | cons x l ih => intro a; simp only [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih _)
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right _ _) (hge r _)
    · exact len_le_foldl_max r _ k h

/-- **A new tree below a segment leaf, in the form of `sbGroup`**: for the
operations subs that go on after segment g, of well-formed keys, the new tree
at segment g + 1 writes at most `ftbOf` of the puts' keys (Java's
`freshTreeBound` with the fuel `countNode` gives it), nothing if there is no
put, and has a root only if there is a put. -/
theorem fresh_le_del_ftb {b G H : Nat} (hb : 8 ≤ b) {f g : Nat} {subs : List Op} {acc : Acc}
    {res : Option NodeId} {acc' : Acc}
    (hwf : ∀ op ∈ subs, keyWf op.key = true ∧ g + 1 < op.key.length)
    (hpt : planTree (Cfg.java b G H) i s f none (g + 1) subs acc = some (res, acc')) :
    kw acc' ≤ kw acc + (if (subs.filter (fun op => !opDel op)).isEmpty then 0
      else ftbOf b (opKeys (subs.filter (fun op => !opDel op))) (g + 1)) ∧
    (res ≠ none → (subs.filter (fun op => !opDel op)).isEmpty = false) := by
  have hops : FreshOpsD (g + 1)
      ((opKeys (subs.filter (fun op => !opDel op))).foldl (fun m (k : Key) => max m k.length) 0 + 1)
      subs := by
    intro op hop
    refine ⟨(hwf op hop).1, by have := (hwf op hop).2; omega, fun hp => ?_⟩
    have hmem : op ∈ subs.filter (fun op => !opDel op) := List.mem_filter.mpr ⟨hop, by simp [hp]⟩
    have := len_le_foldl_max (opKeys (subs.filter (fun op => !opDel op))) 0 op.key
      (List.mem_map_of_mem hmem)
    omega
  obtain ⟨h1, h2⟩ := fresh_le_del (i := i) (s := s) (G := G) (H := H) hb _ f (g + 1) subs acc res
    acc' hops hpt
  have hiff : (∃ op ∈ subs, opDel op = false) ↔ (subs.filter (fun op => !opDel op)).isEmpty = false := by
    rw [exists_put_iff, putsOf, ne_eq, ← List.isEmpty_iff, Bool.not_eq_true]
  refine ⟨?_, fun hr => hiff.mp (h2 hr)⟩
  by_cases hp : ∃ op ∈ subs, opDel op = false
  · rw [ite_eq_left hp] at h1
    rw [hiff.mp hp]
    exact h1
  · rw [ite_eq_right hp] at h1
    have : (subs.filter (fun op => !opDel op)).isEmpty = true := by
      cases hc : (subs.filter (fun op => !opDel op)).isEmpty
      · exact absurd (hiff.mpr hc) hp
      · rfl
    rw [this]
    simpa using h1

end Contract.PE
