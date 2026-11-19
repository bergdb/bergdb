/-
bergdb 030-21: the top of PE's writer (`newTopNode`, `startTop`) meets the
top's clauses of the contract (`TopStart`, `TopStep`, Top.lean).

The writer keeps the top in a state with a few plain properties (`TopInv`):
the top is not empty, its ids are distinct and below the next fresh id, its
root times are at most the time of the last transaction, each skip pointer
names a top node of the top and caches that node's root time, and the super
root's skip indexes are set bits of its ordinal, the top's length less one.
The start top has them (`topInv_start`); a new top node made by
`newTopNode`, with a fresh id and a later time, keeps them and is a step of
the contract (`topInv_new`).

The step's skip pointers (`skipsOk`): the indexes are the set bits of the
ordinal o, in increasing order; an inherited skip pointer is one of the old
super root's, which names a top node and caches its time already, and the
others name the old super root w with its time. The first one is at the
lowest set bit j of o. That bit is clear in o - 1, the old super root's
ordinal, so the old super root has no skip pointer of index j, and the first
skip pointer names w.
-/
import Mathlib.Tactic
import Contract.PeWriter

namespace Contract.PE

/-- What the writer keeps of the top between transactions, with `next` its
next fresh id and t the time of the last transaction. -/
structure TopInv (tp : Top) (next : NodeId) (t : Time) : Prop where
  /-- The top has a top node: the super root. -/
  ne : tp ≠ []
  /-- Every id of a top node is below the next fresh id. -/
  ids : ∀ z n, (z, n) ∈ tp → z < next
  /-- Every root time is at most t. -/
  times : ∀ z n, (z, n) ∈ tp → n.time ≤ t
  /-- No two top nodes have the same id. -/
  nodup : (tp.map (·.1)).Nodup
  /-- Each skip pointer names a top node of the top and caches its root
  time. -/
  skips : ∀ z n, (z, n) ∈ tp → ∀ q ∈ n.skips, (tp.node q.2.1).map (·.time) = some q.2.2
  /-- The super root's skip indexes are set bits of its ordinal, the top's
  length less one. -/
  bits : ∀ w nw, tp.getLast? = some (w, nw) → ∀ q ∈ nw.skips, (tp.length - 1).testBit q.1 = true

namespace PeTop

/-! ## Bits -/

/-- The lowest set bit j of o is clear in o - 1. -/
theorem testBit_pred_lowest : ∀ (j o : Nat), o.testBit j = true → (∀ k < j, o.testBit k = false) →
    (o - 1).testBit j = false
  | 0, o, h, _ => by
    rw [Nat.testBit_zero] at h ⊢
    simp only [decide_eq_true_eq] at h
    simp only [decide_eq_false_iff_not]
    omega
  | j + 1, o, h, hk => by
    have h0 := hk 0 (Nat.succ_pos j)
    rw [Nat.testBit_zero] at h0
    simp only [decide_eq_false_iff_not] at h0
    rw [← Nat.testBit_div_two] at h ⊢
    have hd : (o - 1) / 2 = o / 2 - 1 := by omega
    rw [hd]
    refine testBit_pred_lowest j (o / 2) h (fun k hk' => ?_)
    rw [Nat.testBit_div_two]
    exact hk (k + 1) (by omega)

/-- `topHeight o` covers every set bit of o. -/
theorem lt_topHeight {o j : Nat} (h : o.testBit j = true) : j < topHeight o := by
  unfold topHeight
  by_cases ho : o = 0
  · subst ho
    simp at h
  · simp only [ho, beq_iff_eq, ite_false]
    by_contra hj
    have hj := Nat.le_of_not_lt hj
    have h2 : o < 2 ^ j :=
      lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) hj)
    rw [Nat.testBit_lt_two_pow h2] at h
    exact Bool.false_ne_true h

/-! ## Lists -/

theorem strictUp_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → strictUp l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
    simp only [strictUp, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, strictUp_of_pairwise (b :: r) h.of_cons⟩

/-- With distinct ids, a top node of the top is the one its id names. -/
theorem node_of_mem : ∀ {tp : Top} {z : NodeId} {n : TopNode}, (tp.map (·.1)).Nodup →
    (z, n) ∈ tp → tp.node z = some n
  | [], _, _, _, h => by simp at h
  | (k, b) :: r, z, n, hd, h => by
    rw [List.map_cons, List.nodup_cons] at hd
    unfold Top.node
    rw [List.lookup_cons]
    rcases List.mem_cons.mp h with hm | hm
    · simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp
    · have hzk : z ≠ k := by
        rintro rfl
        exact hd.1 (List.mem_map.mpr ⟨(z, n), hm, rfl⟩)
      have hb : (z == k) = false := by simpa using hzk
      rw [hb]
      exact node_of_mem hd.2 hm

/-- A top node of the top is the same in a longer top. -/
theorem node_append {tp : Top} (tp' : Top) {z : NodeId} {n : TopNode} (h : tp.node z = some n) :
    (tp ++ tp').node z = some n := by
  induction tp with
  | nil => simp [Top.node] at h
  | cons a r ih =>
    obtain ⟨k, b⟩ := a
    unfold Top.node at h ih ⊢
    rw [List.cons_append, List.lookup_cons]
    rw [List.lookup_cons] at h
    cases hk : z == k
    · simp only [hk] at h ⊢
      exact ih h
    · simp only [hk] at h ⊢
      exact h

/-- An id that no top node has names none. -/
theorem node_none {tp : Top} {z : NodeId} (h : ∀ y m, (y, m) ∈ tp → y ≠ z) : tp.node z = none := by
  unfold Top.node
  rw [List.lookup_eq_none_iff]
  intro p hp
  have := h p.1 p.2 hp
  simp only [bne_iff_ne, ne_eq]
  exact fun e => this e.symm

/-! ## The new top node -/

/-- The skip pointer of index j of the new top node with ordinal o, after the
super root w with node nw (`newTopNode`'s step). -/
def newSkip (o : Nat) (w : NodeId) (nw : TopNode) (j : Nat) : Option (Nat × NodeId × Time) :=
  if o.testBit j then
    match nw.skips.find? (fun q => q.1 == j) with
    | some q => some q
    | none => some (j, w, nw.time)
  else none

theorem newTopNode_last {tp : Top} {w : NodeId} {nw : TopNode} (i : Time) (r : NodeId)
    (h : tp.getLast? = some (w, nw)) :
    newTopNode tp i r =
      ⟨i, r, (List.range (topHeight tp.length)).filterMap (newSkip tp.length w nw)⟩ := by
  unfold newTopNode
  rw [h]
  rfl

theorem newTopNode_time (tp : Top) (i : Time) (r : NodeId) : (newTopNode tp i r).time = i := by
  unfold newTopNode
  split <;> rfl

/-- The indexes of the new skip pointers: the set bits of the ordinal. -/
theorem map_fst_filterMap (o : Nat) (w : NodeId) (nw : TopNode) : ∀ l : List Nat,
    (l.filterMap (newSkip o w nw)).map (·.1) = l.filter (fun j => o.testBit j)
  | [] => rfl
  | j :: l => by
    have ih := map_fst_filterMap o w nw l
    rw [List.filterMap_cons, List.filter_cons]
    by_cases hb : o.testBit j = true
    · obtain ⟨q, hv, hq⟩ : ∃ q, newSkip o w nw j = some q ∧ q.1 = j := by
        unfold newSkip
        cases hf : nw.skips.find? (fun q => q.1 == j) with
        | none => exact ⟨(j, w, nw.time), by simp [hb], rfl⟩
        | some q => exact ⟨q, by simp [hb], by simpa using List.find?_some hf⟩
      rw [hv]
      simp only [hb, ↓reduceIte, List.map_cons, hq, ih]
    · have hv : newSkip o w nw j = none := by simp [newSkip, hb]
      rw [hv]
      simp only [hb, Bool.false_eq_true, ↓reduceIte, ih]

/-- A new skip pointer: its index is a set bit of the ordinal; it is the
super root's of that index, or names the super root with its root time. -/
theorem mem_newSkips {o : Nat} {w : NodeId} {nw : TopNode} {l : List Nat}
    {q : Nat × NodeId × Time} (h : q ∈ l.filterMap (newSkip o w nw)) :
    o.testBit q.1 = true ∧ (q ∈ nw.skips ∨ q = (q.1, w, nw.time)) := by
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
  unfold newSkip at hj
  by_cases hb : o.testBit j = true
  · simp only [hb, ite_true] at hj
    cases hf : nw.skips.find? (fun q => q.1 == j) with
    | none =>
      rw [hf] at hj
      cases hj
      exact ⟨hb, Or.inr rfl⟩
    | some q' =>
      rw [hf] at hj
      cases hj
      have hq := List.find?_some hf
      simp only [beq_iff_eq] at hq
      exact ⟨hq ▸ hb, Or.inl (List.mem_of_find?_eq_some hf)⟩
  · simp [hb] at hj

/-- T3 for the new top node. -/
theorem skipsOk_new {tp : Top} {next : NodeId} {t : Time} (h : TopInv tp next t) (i : Time)
    (r : NodeId) : skipsOk tp (newTopNode tp i r) = true := by
  obtain ⟨⟨w, nw⟩, hlast⟩ : ∃ a, tp.getLast? = some a := by
    cases hl : tp.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h.ne
    | some a => exact ⟨a, rfl⟩
  have hw : (w, nw) ∈ tp := List.mem_of_getLast? hlast
  have ho : tp.length ≠ 0 := by
    intro h0
    exact h.ne (List.length_eq_zero_iff.mp h0)
  rw [newTopNode_last i r hlast]
  unfold skipsOk
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [map_fst_filterMap]
    exact strictUp_of_pairwise _ (List.pairwise_lt_range.filter _)
  · rw [List.all_eq_true]
    intro q hq
    rw [beq_iff_eq]
    rcases (mem_newSkips hq).2 with hq' | hq'
    · exact h.skips w nw hw q hq'
    · rw [hq']
      simp [node_of_mem h.nodup hw]
  · rw [hlast]
    set L := (List.range (topHeight tp.length)).filterMap (newSkip tp.length w nw) with hL
    have hidx := map_fst_filterMap tp.length w nw (List.range (topHeight tp.length))
    rw [← hL] at hidx
    obtain ⟨j1, hj1⟩ := Nat.exists_testBit_of_ne_zero ho
    have hne : L ≠ [] := by
      intro hL0
      have hm : j1 ∈ L.map (·.1) := by
        rw [hidx, List.mem_filter, List.mem_range]
        exact ⟨lt_topHeight hj1, hj1⟩
      rw [hL0] at hm
      simp at hm
    obtain ⟨q, L', hqL⟩ := List.exists_cons_of_ne_nil hne
    have hq : q ∈ L := by rw [hqL]; exact List.mem_cons_self
    obtain ⟨hbit, hor⟩ := mem_newSkips (hL ▸ hq)
    have hlow : ∀ k < q.1, tp.length.testBit k = false := by
      intro k hk
      by_contra hkb
      rw [Bool.not_eq_false] at hkb
      have hm : k ∈ L.map (·.1) := by
        rw [hidx, List.mem_filter, List.mem_range]
        exact ⟨lt_topHeight hkb, hkb⟩
      have hp : (L.map (·.1)).Pairwise (· < ·) := by
        rw [hidx]
        exact List.pairwise_lt_range.filter _
      rw [hqL, List.map_cons] at hm hp
      rcases List.mem_cons.mp hm with hm | hm
      · omega
      · have := List.rel_of_pairwise_cons hp hm
        omega
    have hclear := testBit_pred_lowest q.1 tp.length hbit hlow
    rcases hor with hor | hor
    · have := h.bits w nw hlast q hor
      rw [hclear] at this
      exact absurd this Bool.false_ne_true
    · rw [hqL, List.head?_cons, hor]
      simp

end PeTop

open PeTop

/-! ## The results -/

/-- The start top is the contract's start and has `TopInv`, with the start's
next fresh id, at time 0. -/
theorem topInv_start : TopStart startTop ∧ TopInv startTop startNext 0 := by
  refine ⟨⟨2, ⟨0, 1, []⟩, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [startTop]
  · intro z n h
    simp only [startTop, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    decide
  · intro z n h
    simp only [startTop, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact le_refl _
  · simp [startTop]
  · intro z n h q hq
    simp only [startTop, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hq
  · intro w nw h q hq
    simp only [startTop, List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hq

/-- A later next fresh id and a later time keep `TopInv`. -/
theorem topInv_mono {tp : Top} {next : NodeId} {t : Time} {next' : NodeId} {t' : Time}
    (h : TopInv tp next t) (h1 : next ≤ next') (h2 : t ≤ t') : TopInv tp next' t' :=
  { ne := h.ne
    ids := fun z n hm => lt_of_lt_of_le (h.ids z n hm) h1
    times := fun z n hm => le_trans (h.times z n hm) h2
    nodup := h.nodup
    skips := h.skips
    bits := h.bits }

/-- The top after a transaction at a time i after t that makes a new top node
with a fresh id z (at least `next`): a step of the contract (`TopStep`), and
`TopInv` holds with the next fresh id z + 1, at time i. -/
theorem topInv_new {tp : Top} {next : NodeId} {t : Time} {z : NodeId} {i : Time} {r : NodeId}
    (h : TopInv tp next t) (hz : next ≤ z) (hi : t < i) :
    TopStep i tp (tp ++ [(z, newTopNode tp i r)]) ∧
      TopInv (tp ++ [(z, newTopNode tp i r)]) (z + 1) i := by
  have hfresh : ∀ y m, (y, m) ∈ tp → y ≠ z := by
    intro y m hm
    exact Nat.ne_of_lt (lt_of_lt_of_le (h.ids y m hm) hz)
  have hnone : tp.node z = none := node_none hfresh
  have hok := skipsOk_new h i r
  refine ⟨Or.inr ⟨z, newTopNode tp i r, rfl, hnone, newTopNode_time tp i r, hok⟩, ?_⟩
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro y m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact lt_of_lt_of_le (h.ids y m hm) (Nat.le_succ_of_le hz)
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, _⟩ := hm
      exact Nat.lt_succ_self _
  · intro y m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact le_of_lt (lt_of_le_of_lt (h.times y m hm) hi)
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨_, rfl⟩ := hm
      exact le_of_eq (newTopNode_time tp i r)
  · rw [List.map_append, List.nodup_append]
    refine ⟨h.nodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    obtain ⟨⟨y, m⟩, hm, rfl⟩ := List.mem_map.mp ha
    exact hfresh y m hm
  · have hall : ∀ q ∈ (newTopNode tp i r).skips, (tp.node q.2.1).map (·.time) = some q.2.2 := by
      unfold skipsOk at hok
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
      exact hok.1.2
    have hext : ∀ q : Nat × NodeId × Time, (tp.node q.2.1).map (·.time) = some q.2.2 →
        ((tp ++ [(z, newTopNode tp i r)]).node q.2.1).map (·.time) = some q.2.2 := by
      intro q hq
      obtain ⟨m, hm, hmt⟩ := Option.map_eq_some_iff.mp hq
      rw [node_append _ hm]
      simp [hmt]
    intro y m hm q hq
    rcases List.mem_append.mp hm with hm | hm
    · exact hext q (h.skips y m hm q hq)
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨_, rfl⟩ := hm
      exact hext q (hall q hq)
  · intro w nw hl q hq
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
      Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    obtain ⟨⟨w0, nw0⟩, hlast⟩ : ∃ a, tp.getLast? = some a := by
      cases hl : tp.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h.ne
      | some a => exact ⟨a, rfl⟩
    rw [newTopNode_last i r hlast] at hq
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    exact (mem_newSkips hq).1

/-- The space roots of a top with a top node added: those before, and the new
node's root with its time. -/
theorem rootsOf_snoc (tp : Top) (z : NodeId) (n : TopNode) :
    rootsOf (tp ++ [(z, n)]) = rootsOf tp ++ [(n.time, n.root)] := by
  simp [rootsOf]

end Contract.PE
