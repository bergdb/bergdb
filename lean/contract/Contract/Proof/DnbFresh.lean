/-
bergdb 030-29: a new segment tree. For puts of keys whose segment g is not in
the leaf above, PE plans a new tree (`planTree` from no root): its leaf of one
entry a compare value, cut into parts, the new roots above them, and the trees
below its long entries. It writes at most Java's `freshTreeBound` of the keys
(`fresh_le`): the leaf's entries are at most Java's klongs (a value for each
key that ends, a pointer for each segment that goes on), and the trees below
are Java's trees below.
-/
import Contract.Proof.DnbLeaf

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## Keys -/

/-- A well-formed key goes on after segment g exactly when its segment g is
long. -/
theorem keyWf_isLong : ∀ (k : Key) (g : Nat), keyWf k = true → g < k.length →
    (isLong (k[g]?.getD 0) = true ↔ g + 1 < k.length)
  | [], _, h, _ => by simp [keyWf] at h
  | [c], g, h, hg => by
    simp only [List.length_singleton] at hg
    obtain rfl : g = 0 := by omega
    simp only [keyWf, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp [h]
  | c :: d :: rest, 0, h, _ => by
    simp only [keyWf, Bool.and_eq_true] at h
    simp [h.1]
  | c :: d :: rest, g + 1, h, hg => by
    simp only [keyWf, Bool.and_eq_true] at h
    have := keyWf_isLong (d :: rest) g h.2 (by simp at hg ⊢; omega)
    simp only [List.getElem?_cons_succ, List.length_cons] at this ⊢
    rw [this]
    omega

theorem endsAt_isLong {g : Nat} {op : Op} (hwf : keyWf op.key = true) (hg : g < op.key.length) :
    endsAt g op = !isLong (segAt g op) := by
  have := keyWf_isLong op.key g hwf hg
  unfold endsAt segAt
  cases h : isLong ((op.key[g]?).getD 0)
  · rw [h] at this
    simp only [Bool.false_eq_true, false_iff, not_lt] at this
    simp only [Bool.not_false, beq_iff_eq]
    omega
  · rw [h] at this
    simp only [true_iff] at this
    simp only [Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    omega

/-! ## `freshGroup` -/

/-- What `freshGroup` gives for keys K at level g: each segment that goes on
once, with its keys in order, and a klong for each key that ends and each such
segment. -/
structure FGInv (g : Nat) (K : List Key) (r : Nat × List (Nat × List Key)) : Prop where
  nd : (r.2.map (·.1)).Nodup
  keys : ∀ q ∈ r.2, q.2 = K.filter (fun k => k.length != g + 1 && k[g]? == some q.1)
  mem : ∀ c, c ∈ r.2.map (·.1) ↔ ∃ k ∈ K, k.length ≠ g + 1 ∧ k[g]? = some c
  count : r.1 = (K.filter (fun k => k.length == g + 1)).length + r.2.length

theorem freshGroup_inv (g : Nat) (K : List Key) : FGInv g K (freshGroup g K) := by
  induction K using List.reverseRecOn with
  | nil => exact ⟨by simp [freshGroup], by simp [freshGroup], by simp [freshGroup], by simp [freshGroup]⟩
  | append_singleton K k ih =>
    unfold freshGroup at ih ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize List.foldl _ (0, []) K = r at ih ⊢
    obtain ⟨a, L⟩ := r
    obtain ⟨ind, ikeys, imem, icount⟩ := ih
    simp only at ind ikeys imem icount ⊢
    split
    · rename_i hlen
      simp only [beq_iff_eq] at hlen
      refine ⟨ind, fun q hq => ?_, fun c => ?_, ?_⟩
      · rw [ikeys q hq, List.filter_append]; simp [hlen]
      · rw [imem c]; simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨k', hk', h1, h2⟩; exact ⟨k', Or.inl hk', h1, h2⟩
        · rintro ⟨k', hk' | rfl, h1, h2⟩
          · exact ⟨k', hk', h1, h2⟩
          · exact absurd hlen h1
      · simp only [List.filter_append, List.length_append]; simp [hlen]; omega
    · rename_i hlen
      simp only [beq_iff_eq] at hlen
      split
      · rename_i c hc
        split
        · rename_i hany
          refine ⟨?_, fun q hq => ?_, fun c' => ?_, ?_⟩
          · rw [List.map_map]
            convert ind using 1
            apply List.map_congr_left
            intro q _; simp only [Function.comp_apply]; split <;> rfl
          · rw [List.mem_map] at hq
            obtain ⟨q0, hq0, rfl⟩ := hq
            split
            · rename_i hq1
              simp only [beq_iff_eq] at hq1
              rw [ikeys q0 hq0, List.filter_append]
              simp [hlen, hc, hq1]
            · rename_i hq1
              simp only [beq_iff_eq] at hq1
              rw [ikeys q0 hq0, List.filter_append]
              have : (k[g]? == some q0.1) = false := by
                rw [hc]; simp; exact fun h => hq1 h.symm
              simp [this]
          · have hmap : (L.map (fun q => if q.1 == c then (q.1, q.2 ++ [k]) else q)).map (·.1) =
                L.map (·.1) := by
              rw [List.map_map]; apply List.map_congr_left; intro q _
              simp only [Function.comp_apply]; split <;> rfl
            rw [hmap, imem c']
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · rintro ⟨k', hk', h1, h2⟩; exact ⟨k', Or.inl hk', h1, h2⟩
            · rintro ⟨k', hk' | rfl, h1, h2⟩
              · exact ⟨k', hk', h1, h2⟩
              · rw [List.any_eq_true] at hany
                obtain ⟨q, hq, hqc⟩ := hany
                simp only [beq_iff_eq] at hqc
                rw [hc] at h2
                cases h2
                have : q.1 ∈ L.map (·.1) := List.mem_map_of_mem hq
                rw [hqc] at this
                exact (imem _).mp this
          · simp only [List.length_map, List.filter_append, List.length_append]
            simp [hlen]; omega
        · rename_i hany
          refine ⟨?_, fun q hq => ?_, fun c' => ?_, ?_⟩
          · rw [List.map_append, List.nodup_append]
            refine ⟨ind, by simp, ?_⟩
            intro x hx y hy
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
            subst hy
            intro hxy; subst hxy
            rw [List.any_eq_true] at hany
            apply hany
            rw [List.mem_map] at hx
            obtain ⟨q, hq, hqc⟩ := hx
            exact ⟨q, hq, by simp [hqc]⟩
          · rw [List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | rfl
            · rw [ikeys q hq, List.filter_append]
              have : (k[g]? == some q.1) = false := by
                rw [hc]; simp
                intro he; subst he
                rw [List.any_eq_true] at hany
                exact hany ⟨q, hq, by simp⟩
              simp [this]
            · simp only
              rw [List.filter_append]
              have h0 : K.filter (fun k => k.length != g + 1 && k[g]? == some c) = [] := by
                rw [List.filter_eq_nil_iff]
                intro k' hk' hp
                simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
                have := (imem c).mpr ⟨k', hk', hp.1, hp.2⟩
                rw [List.mem_map] at this
                obtain ⟨q, hq, hqc⟩ := this
                rw [List.any_eq_true] at hany
                exact hany ⟨q, hq, by simp [hqc]⟩
              rw [h0]
              simp [hlen, hc]
          · rw [List.map_append, List.mem_append, imem c']
            simp only [List.map_cons, List.map_nil, List.mem_singleton, List.mem_append]
            constructor
            · rintro (⟨k', hk', h1, h2⟩ | rfl)
              · exact ⟨k', Or.inl hk', h1, h2⟩
              · exact ⟨k, Or.inr rfl, by simpa using hlen, hc⟩
            · rintro ⟨k', hk' | rfl, h1, h2⟩
              · exact Or.inl ⟨k', hk', h1, h2⟩
              · rw [hc] at h2; cases h2; exact Or.inr rfl
          · simp only [List.length_append, List.length_singleton, List.filter_append]
            simp [hlen]; omega
      · rename_i hc
        refine ⟨ind, fun q hq => ?_, fun c => ?_, ?_⟩
        · rw [ikeys q hq, List.filter_append]; simp [hc]
        · rw [imem c]; simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨k', hk', h1, h2⟩; exact ⟨k', Or.inl hk', h1, h2⟩
          · rintro ⟨k', hk' | rfl, h1, h2⟩
            · exact ⟨k', hk', h1, h2⟩
            · rw [hc] at h2; cases h2
        · simp only [List.filter_append, List.length_append]; simp [hlen]; omega

/-! ## Counting -/

theorem subperm_sum_le {l1 l2 : List Nat} (h : l1.Subperm l2) : l1.sum ≤ l2.sum := by
  obtain ⟨l, hp, hs⟩ := h
  rw [← hp.sum_eq]
  exact hs.sum_le_sum (fun _ _ => Nat.zero_le _)

/-- A list in order whose compare values are exactly those of a list without
duplicates has its length. -/
theorem sorted_length_eq {es : List (Nat × NodeId)} {cvs : List Nat} (hes : es.Pairwise CvLtA)
    (hnd : cvs.Nodup) (hoff : ∀ c, c ∉ cvs → es.lookup c = none)
    (hon : ∀ c ∈ cvs, ∃ y, es.lookup c = some y) : es.length = cvs.length := by
  have hnd1 : (es.map (·.1)).Nodup := by
    rw [List.Nodup, List.pairwise_map]; exact hes.imp (fun h => Nat.ne_of_lt h)
  have hperm : (es.map (·.1)).Perm cvs := by
    rw [List.perm_ext_iff_of_nodup hnd1 hnd]
    intro c
    constructor
    · intro hc
      rw [List.mem_map] at hc
      obtain ⟨e, he, rfl⟩ := hc
      by_contra hn
      have := hoff e.1 hn
      rw [lookup_of_mem_sorted hes he] at this
      cases this
    · intro hc
      obtain ⟨y, hy⟩ := hon c hc
      exact List.mem_map.mpr ⟨(c, y), lookup_mem hy, rfl⟩
  have := hperm.length_eq
  rwa [List.length_map] at this

/-- The keys of the operations of compare value cv that go on, at level g. -/
theorem opKeys_subs {g cv : Nat} {ops : List Op} (hg : ∀ op ∈ ops, g < op.key.length) :
    opKeys (subsOf g ops cv) =
      (opKeys ops).filter (fun k => k.length != g + 1 && k[g]? == some cv) := by
  unfold opKeys subsOf grpOf
  rw [List.filter_filter, List.filter_map]
  congr 1
  apply List.filter_congr
  intro op hop
  have h1 := hg op hop
  simp only [Function.comp_apply, endsAt, segAt]
  have h2 : op.key[g]? = some (op.key[g]?.getD 0) := by
    rw [List.getElem?_eq_getElem h1]; rfl
  rw [h2]
  cases hc : (op.key[g]?.getD 0 == cv) <;> cases hl : (op.key.length == g + 1) <;> simp_all

/-- The compare values touched are at most Java's klongs of a new tree. -/
theorem touched_le_klongs {g : Nat} {ops : List Op} (hg : ∀ op ∈ ops, g < op.key.length) :
    (touched g ops).length ≤ (freshGroup g (opKeys ops)).1 := by
  obtain ⟨ind, ikeys, imem, icount⟩ := freshGroup_inv g (opKeys ops)
  rw [icount]
  set endC := (ops.filter (endsAt g)).map (segAt g)
  have hsub : touched g ops ⊆ endC ++ (freshGroup g (opKeys ops)).2.map (·.1) := by
    intro c hc
    obtain ⟨op, hop, rfl⟩ := mem_touched.mp hc
    rw [List.mem_append]
    by_cases he : endsAt g op = true
    · exact Or.inl (List.mem_map.mpr ⟨op, List.mem_filter.mpr ⟨hop, he⟩, rfl⟩)
    · right
      rw [imem]
      refine ⟨op.key, List.mem_map_of_mem hop, by simpa [endsAt] using he, ?_⟩
      unfold segAt
      rw [List.getElem?_eq_getElem (hg op hop)]; rfl
  have := (List.subperm_of_subset (nodup_touched g ops) hsub).length_le
  have hend : endC.length = ((opKeys ops).filter (fun k => k.length == g + 1)).length := by
    simp only [endC, List.length_map, opKeys]
    rw [List.filter_map, List.length_map]
    rfl
  rw [List.length_append, hend, List.length_map] at this
  exact this

/-- The new trees below a new tree's leaf are Java's trees below. -/
theorem subs_sum_le {g : Nat} {ops : List Op} (hg : ∀ op ∈ ops, g < op.key.length)
    (h : List Key → Nat) :
    ((touched g ops).map (fun cv => if subsOf g ops cv = [] then 0 else h (opKeys (subsOf g ops cv)))).sum
      ≤ ((freshGroup g (opKeys ops)).2.map (fun q => h q.2)).sum := by
  obtain ⟨ind, ikeys, imem, _⟩ := freshGroup_inv g (opKeys ops)
  set T := (touched g ops).filter (fun cv => subsOf g ops cv ≠ [])
  have hl : ((touched g ops).map (fun cv => if subsOf g ops cv = [] then 0 else h (opKeys (subsOf g ops cv)))).sum
      = (T.map (fun cv => h (opKeys (subsOf g ops cv)))).sum := by
    simp only [T]
    clear ind ikeys imem T
    induction (touched g ops) with
    | nil => rfl
    | cons c r ih =>
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      split
      · rename_i hc; simp only [hc, zero_add] at ih ⊢
        simp [ih]
      · rename_i hc; simp [hc, ih]
  rw [hl]
  set T' := T.map (fun cv => (cv, opKeys (subsOf g ops cv)))
  have hT' : T.map (fun cv => h (opKeys (subsOf g ops cv))) = T'.map (fun q => h q.2) := by
    simp [T']
  rw [hT']
  apply subperm_sum_le
  have hnd : T'.Nodup :=
    ((nodup_touched g ops).filter _).map (fun a b h => (Prod.mk.inj h).1)
  have hsub : T' ⊆ (freshGroup g (opKeys ops)).2 := by
    intro q hq
    simp only [T', List.mem_map] at hq
    obtain ⟨cv, hcv, rfl⟩ := hq
    simp only [T, List.mem_filter, decide_eq_true_eq] at hcv
    obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hcv.2
    have hop' := hop
    unfold subsOf grpOf at hop'
    simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hop'
    have hmem : cv ∈ (freshGroup g (opKeys ops)).2.map (·.1) := by
      rw [imem]
      refine ⟨op.key, List.mem_map_of_mem hop'.1.1, by simpa [endsAt] using hop'.2, ?_⟩
      rw [← hop'.1.2]; unfold segAt
      rw [List.getElem?_eq_getElem (hg op hop'.1.1)]; rfl
    rw [List.mem_map] at hmem
    obtain ⟨q, hq, hqc⟩ := hmem
    have hq2 := ikeys q hq
    rw [hqc, ← opKeys_subs hg] at hq2
    have : (cv, opKeys (subsOf g ops cv)) = q := Prod.ext hqc.symm hq2.symm
    rw [this]; exact hq
  obtain ⟨l, hp, hs⟩ := List.subperm_of_subset hnd hsub
  exact ⟨l.map (fun q => h q.2), hp.map _, hs.map _⟩

/-- What the operations of a new tree at segment g are: puts of well-formed
keys longer than g, of at most g + F' segments. -/
def FreshOps (g F' : Nat) (ops : List Op) : Prop :=
  ∀ op ∈ ops, opDel op = false ∧ keyWf op.key = true ∧ g < op.key.length ∧ op.key.length ≤ g + F'

/-- **A new segment tree** writes at most Java's `freshTreeBound` of its keys,
and is a tree (a root). -/
theorem fresh_le {b G H : Nat} (hb : 8 ≤ b) : ∀ (F' f g : Nat) (ops : List Op) (acc : Acc)
    (res : Option NodeId) (acc' : Acc), FreshOps g F' ops → ops ≠ [] →
    planTree (Cfg.java b G H) i s f none g ops acc = some (res, acc') →
    kw acc' ≤ kw acc + freshTreeBound b F' (opKeys ops) g ∧ ∃ y, res = some y
  | 0, _, g, ops, _, _, _, hops, hne, _ => by
    obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hne
    have := hops op hop; omega
  | _ + 1, 0, _, _, _, _, _, _, _, hpt => by simp [planTree] at hpt
  | F' + 1, f + 1, g, ops, acc, res, acc', hops, hne, hpt => by
    rw [planTree.eq_def] at hpt
    simp only at hpt
    have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2.2.1
    -- the groups
    cases hag : applyGroups (Cfg.java b G H) i s f g [] (List.map (segAt g) ops).eraseDups ops acc with
    | none => rw [hag] at hpt; simp at hpt
    | some p =>
      obtain ⟨es, acc1⟩ := p
      rw [hag] at hpt
      simp only at hpt
      have hT : ∀ f', f' < f → ∀ cv acc0 res acc1', subsOf g ops cv ≠ [] →
          planTree (Cfg.java b G H) i s f' (([] : List (Nat × NodeId)).lookup cv) (g + 1)
            (subsOf g ops cv) acc0 = some (res, acc1') →
          kw acc1' ≤ kw acc0 + freshTreeBound b F' (opKeys (subsOf g ops cv)) (g + 1) ∧
            ∃ y, res = some y ∧ True := by
        intro f' _ cv acc0 res0 acc1' hsne hpt'
        have hsops : FreshOps (g + 1) F' (subsOf g ops cv) := by
          intro op hop
          unfold subsOf grpOf at hop
          simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hop
          obtain ⟨h1, h2, h3, h4⟩ := hops op hop.1.1
          refine ⟨h1, h2, ?_, by omega⟩
          simp only [endsAt, beq_eq_false_iff_ne] at hop
          omega
        obtain ⟨r1, y, hy⟩ := fresh_le hb F' f' (g + 1) _ acc0 res0 acc1' hsops hsne hpt'
        exact ⟨r1, y, hy, trivial⟩
      have hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op) :=
        fun op hop => endsAt_isLong (hops op hop).2.1 (hg op hop)
      obtain ⟨a1, a2, a3, a4⟩ := ag_loop (cf := Cfg.java b G H) (i := i) (s := s)
        (fun op hop => (hops op hop).1) hend
        (fun cv => freshTreeBound b F' (opKeys (subsOf g ops cv)) (g + 1)) (fun _ _ => True) f hT
        (touched g ops) f [] acc es acc1 le_rfl (nodup_touched g ops) (fun _ _ => rfl)
        List.Pairwise.nil (fun cv hcv => by
          obtain ⟨op, hop, rfl⟩ := mem_touched.mp hcv
          exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hop, by simp⟩)) hag
      have hlen : es.length = (touched g ops).length :=
        sorted_length_eq a2 (nodup_touched g ops) (fun c hc => by rw [a3 c hc]; rfl)
          (fun c hc => by obtain ⟨y, hy, _⟩ := a4 c hc; exact ⟨y, hy⟩)
      have htne : touched g ops ≠ [] := by
        obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hne
        exact List.ne_nil_of_mem (mem_touched.mpr ⟨op, hop, rfl⟩)
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
        have hFne : F0 ≠ [] := by
          intro h0; rw [h0] at hF0
          simp only [List.length_nil] at hF0
          rw [← hF0] at hlen
          exact htne (List.eq_nil_of_length_eq_zero hlen.symm)
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
            refine ⟨?_, y, rfl⟩
            have hkw := emit_kw v1 acc1 _ acc2 hem
            simp only [vcost, dcost, vcostL_old] at hv'
            have hra := raOf_le b (cutPartsBound b es.length)
            -- Java's count of the tree
            have hkl := touched_le_klongs hg
            rw [← hlen] at hkl
            have hsum := subs_sum_le hg (fun ks => freshTreeBound b F' ks (g + 1))
            have hmono := cutPartsBound_mono b hkl
            have hra2 := rootsAbove_mono hb hmono
            simp only [freshTreeBound]
            have : cutPartsBound b (freshGroup g (opKeys ops)).1 +
                rootsAbove b (cutPartsBound b (freshGroup g (opKeys ops)).1) ≤
                max (1 + freshSplits b ((freshGroup g (opKeys ops)).1 + 1)
                  (overflows b (freshGroup g (opKeys ops)).1 0 false))
                  (cutPartsBound b (freshGroup g (opKeys ops)).1 +
                    rootsAbove b (cutPartsBound b (freshGroup g (opKeys ops)).1)) :=
              le_max_right _ _
            omega
          · cases hpt

end Contract.PE
