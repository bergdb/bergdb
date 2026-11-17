/-
The contract package (bergdb 030-08): TP24, Java's search through the skip
pointers (`findTop`, `TopDs.findSuperRootAtTime`) finds the top node of the
lookup time, the last one made at or before it (`topAt`), at a record's time
and between two records.

The route. A top that meets the top's clauses from its start is built one
top node at a time, each with a new id, a later root time, and skip pointers
that meet `skipsOk` (`TopGood`). Then: a skip pointer names an earlier top
node and caches its root time (`TopGood.skip`); the lowest one names the top
node just before (`TopGood.pred`); a top node without skip pointers is the
first (`TopGood.first`). The search's first loop goes down skip pointers
whose cached time is at or after the lookup time, and stops at a node whose
skip pointers are all before it (`skipDown_spec`); that node is the answer if
its time is the lookup time, and else the one just before it is, which its
lowest skip pointer names.
-/
import Mathlib.Tactic
import Contract.Top

namespace Contract

/-! ## Lists -/

theorem lookup_append_some {tp tp' : Top} {z : NodeId} {n : TopNode}
    (h : tp.lookup z = some n) : (tp ++ tp').lookup z = some n := by
  induction tp with
  | nil => simp at h
  | cons a r ih =>
    obtain ⟨k, b⟩ := a
    cases hk : z == k
    · simp only [List.lookup, hk, List.cons_append] at h ⊢
      exact ih h
    · simp only [List.lookup, hk, List.cons_append] at h ⊢
      exact h

theorem lookup_append_none {tp tp' : Top} {z : NodeId} (h : tp.lookup z = none) :
    (tp ++ tp').lookup z = tp'.lookup z := by
  induction tp with
  | nil => rfl
  | cons a r ih =>
    obtain ⟨k, b⟩ := a
    cases hk : z == k
    · simp only [List.lookup, hk, List.cons_append] at h ⊢
      exact ih h
    · simp [List.lookup, hk] at h

theorem mem_of_lookup {tp : Top} {z : NodeId} {n : TopNode} (h : tp.lookup z = some n) :
    (z, n) ∈ tp := by
  obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem last_rel {α : Type} {R : α → α → Prop} {l : List α} {x : α} (hp : l.Pairwise R)
    (hl : l.getLast? = some x) : ∀ y ∈ l, y = x ∨ R y x := by
  intro y hy
  have h := dropLast_append_of_getLast? hl
  rw [← h] at hp hy
  rcases List.mem_append.mp hy with h1 | h1
  · exact Or.inr ((List.pairwise_append.mp hp).2.2 y h1 x (by simp))
  · exact Or.inl (by simpa using h1)

theorem length_filter_le {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => le_refl _
  | a :: r, h => by
    have ih := length_filter_le p q r (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hp : p a = true
    · have hq := h a (List.mem_cons_self) hp
      simp [hp, hq, ih]
    · by_cases hq : q a = true
      · simp only [List.filter_cons, hp, hq]
        simp only [Bool.false_eq_true, ite_false, ite_true, List.length_cons]
        omega
      · simp only [List.filter_cons, hp, hq]
        simpa using ih

theorem length_filter_lt {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) → ∀ x ∈ l, q x = true → p x = false →
      (l.filter p).length < (l.filter q).length
  | [], _, x, hx, _, _ => by simp at hx
  | a :: r, h, x, hx, hqx, hpx => by
    have h' : ∀ y ∈ r, p y = true → q y = true := fun y hy => h y (List.mem_cons_of_mem a hy)
    rcases List.mem_cons.mp hx with rfl | hx
    · have := length_filter_le p q r h'
      simp only [List.filter_cons, hpx, hqx]
      simp only [Bool.false_eq_true, ite_false, ite_true, List.length_cons]
      omega
    · have ih := length_filter_lt p q r h' x hx hqx hpx
      by_cases hp : p a = true
      · have hq := h a (List.mem_cons_self) hp
        simp [hp, hq, ih]
      · by_cases hq : q a = true
        · simp only [List.filter_cons, hp, hq]
          simp only [Bool.false_eq_true, ite_false, ite_true, List.length_cons]
          omega
        · simp only [List.filter_cons, hp, hq]
          simpa using ih

/-! ## A top built by the clauses -/

/-- A top built one top node at a time, each with an id not used before, a
root time after those before it, and skip pointers that meet `skipsOk`. -/
inductive TopGood : Top → Prop where
  | nil : TopGood []
  | snoc (tp : Top) (z : NodeId) (n : TopNode) : TopGood tp → tp.node z = none →
      (∀ zm ∈ tp, zm.2.time < n.time) → skipsOk tp n = true → TopGood (tp ++ [(z, n)])

theorem skipsOk_parts {tp : Top} {n : TopNode} (h : skipsOk tp n = true) :
    (∀ q ∈ n.skips, (tp.node q.2.1).map (·.time) = some q.2.2) ∧
    (∀ w nw, tp.getLast? = some (w, nw) → ∃ j ty r, n.skips = (j, w, ty) :: r) ∧
    (tp = [] → n.skips = []) := by
  unfold skipsOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨_, h2⟩, h3⟩ := h
  refine ⟨h2, ?_, ?_⟩
  · intro w nw hw
    rw [hw] at h3
    cases hs : n.skips with
    | nil => simp [hs] at h3
    | cons q r =>
      obtain ⟨j, y, ty⟩ := q
      simp only [hs, List.head?_cons, beq_iff_eq] at h3
      exact ⟨j, ty, r, by rw [h3]⟩
  · intro htp
    subst htp
    cases hs : n.skips with
    | nil => rfl
    | cons q r => simp [hs] at h3

namespace TopGood

variable {tp : Top}

theorem lookup (hg : TopGood tp) : ∀ {z : NodeId} {n : TopNode}, (z, n) ∈ tp →
    tp.node z = some n := by
  induction hg with
  | nil => intro z n h; simp at h
  | snoc tp z0 n0 _ hz _ _ ih =>
    intro z n h
    unfold Top.node at ih hz ⊢
    rcases List.mem_append.mp h with h | h
    · exact lookup_append_some (ih h)
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [lookup_append_none hz]
      simp [List.lookup]

theorem pairwise (hg : TopGood tp) : tp.Pairwise (fun a b => a.2.time < b.2.time) := by
  induction hg with
  | nil => exact List.Pairwise.nil
  | snoc tp z n _ _ ht _ ih =>
    refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact ht a ha

/-- The super root has the latest root time. -/
theorem last_max (hg : TopGood tp) : ∀ {w : NodeId} {nw : TopNode},
    tp.getLast? = some (w, nw) → ∀ zm ∈ tp, zm.2.time ≤ nw.time := by
  intro w nw hl zm hm
  rcases last_rel hg.pairwise hl zm hm with h | h
  · rw [h]
  · exact Nat.le_of_lt h

/-- A skip pointer names an earlier top node and caches its root time. -/
theorem skip (hg : TopGood tp) : ∀ {z : NodeId} {n : TopNode} {q : Nat × NodeId × Time},
    (z, n) ∈ tp → q ∈ n.skips → ∃ ny, (q.2.1, ny) ∈ tp ∧ ny.time = q.2.2 ∧ ny.time < n.time := by
  induction hg with
  | nil => intro z n q h; simp at h
  | snoc tp z0 n0 _ _ ht hs ih =>
    intro z n q h hq
    rcases List.mem_append.mp h with h | h
    · obtain ⟨ny, h1, h2, h3⟩ := ih h hq
      exact ⟨ny, List.mem_append_left _ h1, h2, h3⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 := (skipsOk_parts hs).1 q hq
      cases hy : tp.node q.2.1 with
      | none => simp [hy] at h1
      | some ny =>
        simp only [hy, Option.map_some, Option.some.injEq] at h1
        have hm := mem_of_lookup hy
        exact ⟨ny, List.mem_append_left _ hm, h1, ht _ hm⟩

/-- The lowest skip pointer names the top node just before: no top node has a
root time between. -/
theorem pred (hg : TopGood tp) : ∀ {z : NodeId} {n : TopNode} {q : Nat × NodeId × Time},
    (z, n) ∈ tp → n.skips.head? = some q →
    ∃ ny, (q.2.1, ny) ∈ tp ∧ ny.time = q.2.2 ∧
      ∀ zm ∈ tp, zm.2.time < n.time → zm.2.time ≤ ny.time := by
  induction hg with
  | nil => intro z n q h; simp at h
  | snoc tp z0 n0 hg0 _ ht hs ih =>
    intro z n q h hq
    rcases List.mem_append.mp h with h | h
    · obtain ⟨ny, h1, h2, h3⟩ := ih h hq
      refine ⟨ny, List.mem_append_left _ h1, h2, ?_⟩
      intro zm hzm hlt
      rcases List.mem_append.mp hzm with hzm | hzm
      · exact h3 zm hzm hlt
      · simp only [List.mem_singleton] at hzm
        subst hzm
        exact absurd (Nat.lt_trans hlt (ht _ h)) (Nat.lt_irrefl _)
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := skipsOk_parts hs
      cases hl : tp.getLast? with
      | none =>
        have := h3 (List.getLast?_eq_none_iff.mp hl)
        simp [this] at hq
      | some wn =>
        obtain ⟨w, nw⟩ := wn
        obtain ⟨j, ty, r, hsk⟩ := h2 w nw hl
        rw [hsk] at hq
        simp only [List.head?_cons, Option.some.injEq] at hq
        subst hq
        have hwm := List.mem_of_getLast? hl
        have hc := h1 (j, w, ty) (by rw [hsk]; exact List.mem_cons_self)
        rw [hg0.lookup hwm] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        refine ⟨nw, List.mem_append_left _ hwm, hc, ?_⟩
        intro zm hzm hlt
        rcases List.mem_append.mp hzm with hzm | hzm
        · exact hg0.last_max hl zm hzm
        · simp only [List.mem_singleton] at hzm
          subst hzm
          exact absurd hlt (Nat.lt_irrefl _)

/-- A top node without skip pointers is the first. -/
theorem first (hg : TopGood tp) : ∀ {z : NodeId} {n : TopNode}, (z, n) ∈ tp → n.skips = [] →
    ∀ zm ∈ tp, n.time ≤ zm.2.time := by
  induction hg with
  | nil => intro z n h; simp at h
  | snoc tp z0 n0 hg0 _ ht hs ih =>
    intro z n h hsk zm hzm
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp hzm with hzm | hzm
      · exact ih h hsk zm hzm
      · simp only [List.mem_singleton] at hzm
        subst hzm
        exact Nat.le_of_lt (ht _ h)
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, h2, _⟩ := skipsOk_parts hs
      cases hl : tp.getLast? with
      | none =>
        have htp := List.getLast?_eq_none_iff.mp hl
        subst htp
        simp only [List.nil_append, List.mem_singleton] at hzm
        subst hzm
        exact le_refl _
      | some wn =>
        obtain ⟨j, ty, r, hsk'⟩ := h2 wn.1 wn.2 hl
        rw [hsk] at hsk'
        simp at hsk'

end TopGood

/-! ## The top node of a time -/

theorem topAt_eq {tp : Top} (hg : TopGood tp) {z : NodeId} {n : TopNode} (hm : (z, n) ∈ tp)
    {t : Time} (ht : n.time ≤ t) (hmax : ∀ zm ∈ tp, zm.2.time ≤ t → zm.2.time ≤ n.time) :
    topAt tp t = some (z, n) := by
  unfold topAt
  have hzL : (z, n) ∈ tp.filter (fun zn => decide (zn.2.time ≤ t)) :=
    List.mem_filter.mpr ⟨hm, by simpa using ht⟩
  have hpw : (tp.filter (fun zn => decide (zn.2.time ≤ t))).Pairwise
      (fun a b => a.2.time < b.2.time) := hg.pairwise.sublist List.filter_sublist
  cases hlast : (tp.filter (fun zn => decide (zn.2.time ≤ t))).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hlast
    rw [hlast] at hzL
    simp at hzL
  | some x =>
    have hx := List.mem_filter.mp (List.mem_of_getLast? hlast)
    have hxle : x.2.time ≤ n.time := hmax x hx.1 (by simpa using hx.2)
    rcases last_rel hpw hlast (z, n) hzL with h | h
    · rw [h]
    · exact absurd hxle (Nat.not_le.mpr h)

theorem topAt_none {tp : Top} {t : Time} (h : ∀ zm ∈ tp, t < zm.2.time) : topAt tp t = none := by
  unfold topAt
  have : tp.filter (fun zn => decide (zn.2.time ≤ t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simpa using h a ha
  rw [this]
  rfl

/-! ## The search -/

theorem rightMostGte_none {n : TopNode} {t : Time} {mid : Bool} (h : rightMostGte n t mid = none) :
    ∀ q ∈ n.skips, atOrAfter q.2.2 t mid = false := by
  intro q hq
  unfold rightMostGte at h
  cases hf : n.skips.reverse.find? (fun q => atOrAfter q.2.2 t mid) with
  | none =>
    have := List.find?_eq_none.mp hf q (List.mem_reverse.mpr hq)
    simpa using this
  | some q' => simp [hf] at h

/-- The search's first loop: from a top node at or after the lookup time, with
enough fuel, it stops at a top node at or after the lookup time whose skip
pointers all cache times before it. -/
theorem skipDown_spec {tp : Top} (hg : TopGood tp) (t : Time) (mid : Bool) :
    ∀ (f : Nat) (z : NodeId) (n : TopNode), tp.node z = some n → atOrAfter n.time t mid = true →
      (tp.filter (fun zm => decide (zm.2.time < n.time))).length < f →
      ∃ nf, tp.node (skipDown tp t mid f z) = some nf ∧ atOrAfter nf.time t mid = true ∧
        rightMostGte nf t mid = none
  | 0, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, z, n, hz, ha, hf => by
    simp only [skipDown, hz]
    cases hr : rightMostGte n t mid with
    | none => exact ⟨n, hz, ha, hr⟩
    | some y =>
      simp only
      unfold rightMostGte at hr
      cases hfd : n.skips.reverse.find? (fun q => atOrAfter q.2.2 t mid) with
      | none => simp [hfd] at hr
      | some q =>
        simp only [hfd, Option.map_some, Option.some.injEq] at hr
        subst hr
        have hqm := List.mem_reverse.mp (List.mem_of_find?_eq_some hfd)
        have hqa := List.find?_some hfd
        obtain ⟨ny, hmy, hty, hlt⟩ := hg.skip (mem_of_lookup hz) hqm
        refine skipDown_spec hg t mid f q.2.1 ny (hg.lookup hmy) (by rw [hty]; exact hqa) ?_
        have := length_filter_lt (fun zm : NodeId × TopNode => decide (zm.2.time < ny.time))
          (fun zm => decide (zm.2.time < n.time)) tp
          (fun x _ hx => by simp only [decide_eq_true_eq] at hx ⊢; exact Nat.lt_trans hx hlt)
          (q.2.1, ny) hmy (by simpa using hlt) (by simp)
        omega

/-- TP24: the search finds the top node of the lookup time, the last one made
at or before it, at a record's time (`mid` false) and between two records
(`mid` true). -/
theorem findTop_right {tp : Top} (hg : TopGood tp) (t : Time) (mid : Bool) :
    findTop tp t mid = (topAt tp t).map (·.1) := by
  unfold findTop
  cases hl : tp.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl
    subst hl
    rfl
  | some wn =>
    obtain ⟨w, nw⟩ := wn
    have hwm := List.mem_of_getLast? hl
    simp only
    by_cases hwt : nw.time ≤ t
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hwt), topAt_eq hg hwm hwt (fun zm hzm _ => hg.last_max hl zm hzm)]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hwt)]
      have hwt' : t < nw.time := Nat.lt_of_not_le hwt
      have hwa : atOrAfter nw.time t mid = true := by
        cases mid <;> simp [atOrAfter, hwt', Nat.le_of_lt hwt']
      have hfuel : (tp.filter (fun zm => decide (zm.2.time < nw.time))).length < tp.length := by
        have := length_filter_lt (fun zm : NodeId × TopNode => decide (zm.2.time < nw.time))
          (fun _ => true) tp (fun _ _ _ => rfl) (w, nw) hwm rfl (by simp)
        simpa using this
      obtain ⟨nf, hzf, hfa, hfr⟩ := skipDown_spec hg t mid tp.length w nw (hg.lookup hwm) hwa hfuel
      simp only [hzf]
      have hfm := mem_of_lookup hzf
      by_cases hft : (!mid && nf.time == t) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hft)]
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hft
        rw [topAt_eq hg hfm (le_of_eq hft.2) (fun zm _ h => by rw [hft.2]; exact h)]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hft)]
        have hlt : t < nf.time := by
          cases mid
          · simp [atOrAfter] at hfa
            simp at hft
            exact Nat.lt_of_le_of_ne hfa (Ne.symm hft)
          · simpa [atOrAfter] using hfa
        cases hh : nf.skips.head? with
        | none =>
          rw [List.head?_eq_none_iff] at hh
          rw [topAt_none (fun zm hzm => Nat.lt_of_lt_of_le hlt (hg.first hfm hh zm hzm))]
          rfl
        | some q =>
          obtain ⟨j, y, ty⟩ := q
          simp only
          have hqm : (j, y, ty) ∈ nf.skips := List.mem_of_mem_head? hh
          have hqa := rightMostGte_none hfr _ hqm
          have hty : ty ≤ t := by
            cases mid
            · simp only [atOrAfter, Bool.false_eq_true, ite_false, decide_eq_false_iff_not] at hqa
              exact Nat.le_of_lt (Nat.lt_of_not_le hqa)
            · simp only [atOrAfter, ite_true, decide_eq_false_iff_not] at hqa
              exact Nat.le_of_not_lt hqa
          rw [ite_eq_left_of_eq_true _ _ (eq_true hty)]
          obtain ⟨ny, hym, hnyt, hmax⟩ := hg.pred hfm hh
          simp only at hym hnyt
          rw [topAt_eq hg hym (by rw [hnyt]; exact hty)
            (fun zm hzm h => hmax zm hzm (Nat.lt_of_le_of_lt h hlt))]
          rfl

/-- The space root that Java's search gives is the root pointer of the top
node of the lookup time. -/
theorem findRoot_right {tp : Top} (hg : TopGood tp) (t : Time) (mid : Bool) :
    findRoot tp t mid = (topAt tp t).map (·.2.root) := by
  unfold findRoot
  rw [findTop_right hg t mid]
  cases h : topAt tp t with
  | none => rfl
  | some zn =>
    obtain ⟨z, n⟩ := zn
    have hm : (z, n) ∈ tp := by
      unfold topAt at h
      exact (List.mem_filter.mp (List.mem_of_getLast? h)).1
    simp [hg.lookup hm]

/-- The tree's space root at time t is the root pointer of the top node of
time t, when the tree's space roots are the top's. -/
theorem root_at_top {s : Tree} {tp : Top} (h : s.roots = rootsOf tp) (t : Time) :
    (s.at t).root = (topAt tp t).map (·.2.root) := by
  simp only [Tree.root, Tree.at, topAt, h, rootsOf, List.filter_map, List.getLast?_map,
    Option.map_map]
  rfl

end Contract
