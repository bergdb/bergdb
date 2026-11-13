/-
The tree model (bergdb 024-12, TP7): what the writer may do to a key node it
holds. A node of the writer's overlay is `Good` when

* its klongs before the transaction's time are the node's klongs in P@(i-1)
  (none for a node that the transaction made): the writer changes no klong
  of an earlier time;
* it has no time klong after the transaction's time;
* it is a key node of P@(i-1), or its id is one of the transaction's.

This file has the rules on lists of klongs: each change the writer makes to a
node keeps it `Good` (an appended klong, the transaction's own bitmap set in
place, a klong of the transaction pointed in place, the klongs of the
transaction dropped, a last version in place of a node of the transaction).
SIS/Tree/WriterGood*.lean take them through the writer.
-/
import SIS.Tree.FlatKlongs
import SIS.Tree.FreshCache
import SIS.Tree.HistoricalPrefix

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Prefixes -/

/-- The test of `prefixAt`: not a time klong after t. -/
def atOrBefore (t : Time) (k : Klong) : Bool :=
  match k with
  | .time x => decide (x ≤ t)
  | _ => true

theorem prefixAt_eq_takeWhile (ks : List Klong) (t : Time) :
    prefixAt ks t = ks.takeWhile (atOrBefore t) := rfl

theorem takeWhile_append_of_stop {α : Type} (p : α → Bool) (a b : List α)
    (h : ∃ x ∈ a, p x = false) : (a ++ b).takeWhile p = a.takeWhile p := by
  induction a with
  | nil => obtain ⟨x, hx, _⟩ := h; cases hx
  | cons y a ih =>
    obtain ⟨x, hx, hp⟩ := h
    by_cases hy : p y = true
    · simp only [List.cons_append, List.takeWhile_cons, hy, ↓reduceIte]
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hy] at hp; cases hp
      · rw [ih ⟨x, hx, hp⟩]
    · simp only [List.cons_append, List.takeWhile_cons, hy, Bool.false_eq_true, ↓reduceIte]

/-- Two lists of klongs that agree up to a time klong after t have the same
klongs at t. -/
theorem prefixAt_eq_of_take (ks ks' : List Klong) (t u : Time) (m : Nat) (hu : t < u)
    (hm : ks[m]? = some (.time u)) (h : ks'.take (m + 1) = ks.take (m + 1)) :
    prefixAt ks' t = prefixAt ks t := by
  have hstop : ∃ x ∈ ks.take (m + 1), atOrBefore t x = false := by
    refine ⟨.time u, ?_, by simp [atOrBefore]; omega⟩
    rw [List.mem_iff_getElem?]
    exact ⟨m, by rw [List.getElem?_take]; simp [hm]⟩
  have h1 : prefixAt ks t = (ks.take (m + 1)).takeWhile (atOrBefore t) := by
    rw [prefixAt_eq_takeWhile]
    conv => lhs; rw [← List.take_append_drop (m + 1) ks]
    exact takeWhile_append_of_stop _ _ _ hstop
  have h2 : prefixAt ks' t = (ks'.take (m + 1)).takeWhile (atOrBefore t) := by
    rw [prefixAt_eq_takeWhile]
    conv => lhs; rw [← List.take_append_drop (m + 1) ks']
    exact takeWhile_append_of_stop _ _ _ (by rw [h]; exact hstop)
  rw [h1, h2, h]

/-- The klongs at t are all the klongs, or end before a time klong after t. -/
theorem prefixAt_stop (ks : List Klong) (t : Time) :
    prefixAt ks t = ks ∨ ∃ u, t < u ∧ ks[(prefixAt ks t).length]? = some (.time u) := by
  induction ks with
  | nil => exact Or.inl rfl
  | cons k ks ih =>
    cases k with
    | time x =>
      by_cases hx : x ≤ t
      · have he : prefixAt (.time x :: ks) t = .time x :: prefixAt ks t := by
          simp [prefixAt, hx]
        rw [he]
        rcases ih with h | ⟨u, hu, h⟩
        · exact Or.inl (by rw [h])
        · exact Or.inr ⟨u, hu, by simpa using h⟩
      · have he : prefixAt (.time x :: ks) t = [] := by simp [prefixAt, hx]
        rw [he]
        exact Or.inr ⟨x, by omega, rfl⟩
    | key c y =>
      have he : prefixAt (.key c y :: ks) t = .key c y :: prefixAt ks t := by simp [prefixAt]
      rw [he]
      rcases ih with h | ⟨u, hu, h⟩
      · exact Or.inl (by rw [h])
      · exact Or.inr ⟨u, hu, by simpa using h⟩
    | del b =>
      have he : prefixAt (.del b :: ks) t = .del b :: prefixAt ks t := by simp [prefixAt]
      rw [he]
      rcases ih with h | ⟨u, hu, h⟩
      · exact Or.inl (by rw [h])
      · exact Or.inr ⟨u, hu, by simpa using h⟩

theorem prefixAt_prefix (ks : List Klong) (t : Time) : (prefixAt ks t).IsPrefix ks :=
  List.takeWhile_prefix _

theorem prefixAt_idem (ks : List Klong) (t : Time) : prefixAt (prefixAt ks t) t = prefixAt ks t := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    cases k with
    | time x =>
      by_cases hx : x ≤ t
      · simp only [prefixAt, List.takeWhile_cons, hx, decide_true, ↓reduceIte] at ih ⊢
        rw [ih]
      · simp [prefixAt, hx]
    | key c y =>
      simp only [prefixAt, List.takeWhile_cons, ↓reduceIte] at ih ⊢
      rw [ih]
    | del b =>
      simp only [prefixAt, List.takeWhile_cons, ↓reduceIte] at ih ⊢
      rw [ih]

theorem prefixAt_eq_self (ks : List Klong) (t : Time)
    (h : ∀ u, Klong.time u ∈ ks → u ≤ t) : prefixAt ks t = ks := by
  rcases prefixAt_stop ks t with he | ⟨u, hu, hm⟩
  · exact he
  · have hmem : Klong.time u ∈ ks := List.mem_of_getElem? hm
    have := h u hmem
    omega

/-- Before the first time klong of a node there is no time klong. -/
theorem prefixAt_no_time_of_firstTime (ks : List Klong) (t i : Time) (hi : t < i)
    (hf : (⟨false, ks⟩ : KNode).firstTime = some i) :
    ∀ u, Klong.time u ∉ prefixAt ks t := by
  induction ks with
  | nil => simp [KNode.firstTime] at hf
  | cons k ks ih =>
    cases k with
    | time x =>
      have hx : x = i := by simpa [KNode.firstTime] using hf
      subst x
      have he : prefixAt (.time i :: ks) t = [] := by
        simp [prefixAt, Nat.not_le.mpr hi]
      rw [he]
      intro u hu
      cases hu
    | key c y =>
      have he : prefixAt (.key c y :: ks) t = .key c y :: prefixAt ks t := by simp [prefixAt]
      rw [he]
      intro u hu
      rcases List.mem_cons.mp hu with hu | hu
      · cases hu
      · exact ih (by simpa [KNode.firstTime] using hf) u hu
    | del b =>
      have he : prefixAt (.del b :: ks) t = .del b :: prefixAt ks t := by simp [prefixAt]
      rw [he]
      intro u hu
      rcases List.mem_cons.mp hu with hu | hu
      · cases hu
      · exact ih (by simpa [KNode.firstTime] using hf) u hu

/-! ## The last time klong -/

theorem lastTime_anchor_aux (rest pre : List Klong) (lt : Option Time) (li : Option Nat)
    (h : (lt = none ∧ li = none) ∨
      ∃ u m, lt = some u ∧ li = some m ∧ pre[m]? = some (.time u)) :
    (rest.foldl (fun t k => match k with
        | .time x => some x
        | _ => t) lt = none ∧
      (rest.zipIdx pre.length).foldl (fun t (k, i) => match k with
        | .time _ => some i
        | _ => t) li = none) ∨
    ∃ u m, rest.foldl (fun t k => match k with
        | .time x => some x
        | _ => t) lt = some u ∧
      (rest.zipIdx pre.length).foldl (fun t (k, i) => match k with
        | .time _ => some i
        | _ => t) li = some m ∧ (pre ++ rest)[m]? = some (.time u) := by
  induction rest generalizing pre lt li with
  | nil => simpa using h
  | cons k rest ih =>
    have hlen : (pre ++ [k]).length = pre.length + 1 := by simp
    have hpre : pre ++ k :: rest = (pre ++ [k]) ++ rest := by simp
    simp only [List.zipIdx_cons, List.foldl_cons]
    rw [hpre, ← hlen]
    apply ih
    cases k with
    | time x =>
      refine Or.inr ⟨x, pre.length, rfl, rfl, by simp⟩
    | key c y =>
      rcases h with h | ⟨u, m, h1, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨u, m, h1, h2, ?_⟩
        have hm : m < pre.length := (List.getElem?_eq_some_iff.mp h3).1
        rw [List.getElem?_append_left hm]
        exact h3
    | del b =>
      rcases h with h | ⟨u, m, h1, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨u, m, h1, h2, ?_⟩
        have hm : m < pre.length := (List.getElem?_eq_some_iff.mp h3).1
        rw [List.getElem?_append_left hm]
        exact h3

/-- A node with a last time has its last time klong at `lastTimeIndex`. -/
theorem KNode.lastTime_anchor (n : KNode) (u : Time) (h : n.lastTime = some u) :
    ∃ m, n.lastTimeIndex = some m ∧ n.ks[m]? = some (.time u) := by
  have ha := lastTime_anchor_aux n.ks [] none none (Or.inl ⟨rfl, rfl⟩)
  simp only [List.length_nil, List.nil_append] at ha
  change (n.lastTime = none ∧ n.lastTimeIndex = none) ∨
    ∃ u m, n.lastTime = some u ∧ n.lastTimeIndex = some m ∧ n.ks[m]? = some (.time u) at ha
  rcases ha with ⟨h1, _⟩ | ⟨v, m, h1, h2, h3⟩
  · rw [h] at h1; cases h1
  · rw [h] at h1
    cases h1
    exact ⟨m, h2, h3⟩

/-! ## The klongs of a history -/

theorem parseKlongEntry_time_mem (acc : KlongParseState) (e : Entry BVal) (t : Time)
    (h : Klong.time t ∈ (parseKlongEntry acc e).1) : Klong.time t ∈ acc.1 ∨ t = e.time := by
  have hks : Klong.time t ∈ (if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]) →
      Klong.time t ∈ acc.1 ∨ t = e.time := by
    intro hm
    split at hm
    · exact Or.inl hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (by simpa using hm)
  unfold parseKlongEntry at h
  dsimp only at h
  split at h
  · rcases List.mem_append.mp h with h | h
    · exact hks h
    · simp at h
  · exact hks h
  · rcases List.mem_append.mp h with h | h
    · exact hks h
    · simp at h
  · exact hks h

/-- A time klong of a history's klongs is the time of an entry. -/
theorem klongsOf_time_mem (es : History BVal) (t : Time) (h : Klong.time t ∈ klongsOf es) :
    ∃ e ∈ es, e.time = t := by
  have hf : ∀ (qs : History BVal) (acc : KlongParseState),
      Klong.time t ∈ (qs.foldl parseKlongEntry acc).1 →
        Klong.time t ∈ acc.1 ∨ ∃ e ∈ qs, e.time = t := by
    intro qs
    induction qs with
    | nil => intro acc h; exact Or.inl h
    | cons e qs ih =>
      intro acc h
      rcases ih _ h with h | ⟨e', he', ht⟩
      · rcases parseKlongEntry_time_mem acc e t h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨e, List.mem_cons_self, h.symm⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', ht⟩
  rw [klongsOf_eq_parse] at h
  rcases hf es _ h with h | h
  · cases h
  · exact h

theorem parseKlongEntry_head (acc : KlongParseState) (e : Entry BVal)
    (h : (acc.1 = [] ∧ acc.2.1 = none) ∨ ∃ t r, acc.1 = .time t :: r) :
    ∃ t r, (parseKlongEntry acc e).1 = .time t :: r := by
  have hks : ∃ t r, (if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]) =
      .time t :: r := by
    rcases h with ⟨h1, h2⟩ | ⟨t, r, h1⟩
    · exact ⟨e.time, [], by simp [h1, h2]⟩
    · split
      · exact ⟨t, r, h1⟩
      · exact ⟨t, r ++ [.time e.time], by simp [h1]⟩
  obtain ⟨t, r, hk⟩ := hks
  unfold parseKlongEntry
  dsimp only
  split
  · exact ⟨t, r ++ [_], by rw [hk]; rfl⟩
  · exact ⟨t, r, hk⟩
  · exact ⟨t, r ++ [_], by rw [hk]; rfl⟩
  · exact ⟨t, r, hk⟩

/-- The klongs of a history start with a time klong. -/
theorem klongsOf_head (es : History BVal) : klongsOf es = [] ∨ ∃ t r, klongsOf es = .time t :: r := by
  have hf : ∀ (qs : History BVal) (acc : KlongParseState),
      ((acc.1 = [] ∧ acc.2.1 = none) ∨ ∃ t r, acc.1 = .time t :: r) →
      ((qs.foldl parseKlongEntry acc).1 = [] ∨
        ∃ t r, (qs.foldl parseKlongEntry acc).1 = .time t :: r) := by
    intro qs
    induction qs with
    | nil =>
      intro acc h
      rcases h with ⟨h, _⟩ | h
      · exact Or.inl h
      · exact Or.inr h
    | cons e qs ih =>
      intro acc h
      exact ih _ (Or.inr (parseKlongEntry_head acc e h))
  rw [klongsOf_eq_parse]
  exact hf es _ (Or.inl ⟨rfl, rfl⟩)

/-! ## Good nodes -/

/-- The klongs of node x in the writer's view; none for a node not in it. -/
def baseKlongs (v : View BVal) (x : NodeId) : List Klong :=
  match v x with
  | some nd => klongsOf nd.hist
  | none => []

/-- x is a key node of the view, or one of the transaction's ids. -/
def Origin (B : NodeId) (c : Ctx) (x : NodeId) : Prop :=
  (∃ nd, c.view x = some nd ∧ nd.isData = false ∧ nd.level ≤ c.p.keyMax) ∨ B ≤ x

/-- What the writer's view must meet, with B the transaction's first id: a
time after 0; ids below B; entries before the transaction's time; klongs that
name ids below B; key nodes with a klong. -/
structure ViewGood (B : NodeId) (c : Ctx) : Prop where
  pos : 0 < c.i
  ids : ViewIdsBelow B c.view
  times : ∀ x nd, c.view x = some nd → ∀ e ∈ nd.hist, e.time < c.i
  ptrs : ∀ x nd, c.view x = some nd → ∀ cv y, Klong.key cv y ∈ klongsOf nd.hist → y < B
  nonempty : ∀ x nd, c.view x = some nd → nd.isData = false → nd.level ≤ c.p.keyMax →
    klongsOf nd.hist ≠ []

/-- A node of the writer's overlay that keeps its klongs of earlier times. -/
structure Good (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) : Prop where
  old : prefixAt n.ks (c.i - 1) = baseKlongs c.view x
  times : ∀ t, Klong.time t ∈ n.ks → t ≤ c.i
  origin : Origin B c x

/-- A node without klongs of an earlier time: one that the transaction made. -/
def Blank (B : NodeId) (c : Ctx) (x : NodeId) : Prop :=
  baseKlongs c.view x = [] ∧ Origin B c x

/-- A time klong of i, then key klongs only: a last version at time i. -/
def FlatAt (i : Time) (ks : List Klong) : Prop :=
  ∃ r, ks = .time i :: r ∧ ∀ k ∈ r, ∃ cv y, k = Klong.key cv y

theorem good_load (B : NodeId) (c : Ctx) (hv : ViewGood B c) (x : NodeId) (nd : Node BVal)
    (leaf : Bool) (hx : c.view x = some nd) (hd : nd.isData = false)
    (hl : nd.level ≤ c.p.keyMax) : Good B c x ⟨leaf, klongsOf nd.hist⟩ := by
  have ht : ∀ t, Klong.time t ∈ klongsOf nd.hist → t ≤ c.i - 1 := by
    intro t hm
    obtain ⟨e, he, rfl⟩ := klongsOf_time_mem nd.hist t hm
    have := hv.times x nd hx e he
    omega
  refine ⟨?_, ?_, Or.inl ⟨nd, hx, hd, hl⟩⟩
  · simp only [baseKlongs, hx]
    exact prefixAt_eq_self _ _ ht
  · intro t hm
    have := ht t hm
    omega

theorem KNode.add_ks (n : KNode) (t : Time) (k : Klong) :
    (n.add t k).ks = n.ks ++ [.time t, k] ∨ (n.add t k).ks = n.ks ++ [k] := by
  unfold KNode.add
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

theorem Good.add (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (k : Klong)
    (hpos : 0 < c.i) (hk : ∀ u, k ≠ .time u) (h : Good B c x n) :
    Good B c x (n.add c.i k) := by
  refine ⟨?_, ?_, h.origin⟩
  · rw [KNode.add_prefixAt_past n c.i (c.i - 1) (by omega) k]
    exact h.old
  · intro t hm
    rcases n.add_ks c.i k with he | he <;> rw [he] at hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact h.times t hm
      · simp only [List.mem_cons, Klong.time.injEq, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | hm
        · exact Nat.le_refl _
        · exact (hk t hm.symm).elim
    · rcases List.mem_append.mp hm with hm | hm
      · exact h.times t hm
      · simp only [List.mem_singleton] at hm
        exact (hk t hm.symm).elim

theorem Good.add_key (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (cv : Nat) (y : NodeId)
    (hpos : 0 < c.i) (h : Good B c x n) : Good B c x (n.add c.i (.key cv y)) :=
  Good.add B c x n _ hpos (by intro u hu; cases hu) h

theorem Good.add_del (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (bits : List Nat)
    (hpos : 0 < c.i) (h : Good B c x n) : Good B c x (n.add c.i (.del bits)) :=
  Good.add B c x n _ hpos (by intro u hu; cases hu) h

theorem Good.fold_add (B : NodeId) (c : Ctx) (x : NodeId) (ins : List (Nat × NodeId))
    (hpos : 0 < c.i) (n : KNode) (h : Good B c x n) :
    Good B c x (ins.foldl (fun n (q : Nat × NodeId) => n.add c.i (.key q.1 q.2)) n) := by
  induction ins generalizing n with
  | nil => exact h
  | cons q ins ih => exact ih _ (Good.add_key B c x n q.1 q.2 hpos h)

theorem Good.toPrev (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (h : Good B c x n) :
    Good B c x (n.toPrev (c.i - 1)) := by
  refine ⟨?_, ?_, h.origin⟩
  · show prefixAt (prefixAt n.ks (c.i - 1)) (c.i - 1) = _
    rw [prefixAt_idem]
    exact h.old
  · intro t hm
    exact h.times t ((prefixAt_prefix n.ks (c.i - 1)).subset hm)

/-- A klong that is no time klong, set after a time klong of the
transaction. -/
theorem Good.set (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (m j : Nat) (k : Klong)
    (hpos : 0 < c.i) (hm : n.ks[m]? = some (.time c.i)) (hj : m < j)
    (hk : ∀ u, k ≠ .time u) (h : Good B c x n) : Good B c x (n.setAt j k) := by
  refine ⟨?_, ?_, h.origin⟩
  · rw [← h.old]
    exact prefixAt_eq_of_take n.ks _ (c.i - 1) c.i m (by omega) hm
      (List.take_set_of_le (by omega))
  · intro t ht
    rcases List.mem_or_eq_of_mem_set ht with ht | ht
    · exact h.times t ht
    · exact (hk t ht.symm).elim

theorem Good.repoint_gt (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (m e : Nat) (y : NodeId)
    (hpos : 0 < c.i) (hm : n.ks[m]? = some (.time c.i)) (he : m < e)
    (h : Good B c x n) : Good B c x (n.repoint e y) := by
  unfold KNode.repoint
  split
  · exact Good.set B c x n m e _ hpos hm he (by intro u hu; cases hu) h
  · exact h

/-- The transaction's own bitmap, the node's last klong, set in place. -/
theorem Good.setLastDel (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (bits : List Nat)
    (hpos : 0 < c.i) (h : Good B c x n)
    (hflag : ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
      n.lastTime == some c.i) = true) :
    Good B c x (n.setAt (n.size - 1) (.del bits)) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hflag
  obtain ⟨hlast, hlt⟩ := hflag
  obtain ⟨m, _, hm⟩ := n.lastTime_anchor c.i hlt
  have hml : m < n.ks.length := (List.getElem?_eq_some_iff.mp hm).1
  have hne : m ≠ n.ks.length - 1 := by
    intro he
    rw [List.getLast?_eq_getElem?, ← he, hm] at hlast
    simp at hlast
  exact Good.set B c x n m _ _ hpos hm (by unfold KNode.size; omega) (by intro u hu; cases hu) h

/-- A klong after the transaction's time klong, pointed in place. -/
theorem Good.repointAfter (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (e : Nat) (y : NodeId)
    (hpos : 0 < c.i) (h : Good B c x n)
    (hflag : (n.lastTime == some c.i && (match n.lastTimeIndex with
      | some ti => decide (ti < e)
      | none => false)) = true) :
    Good B c x (n.repoint e y) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hflag
  obtain ⟨hlt, hidx⟩ := hflag
  obtain ⟨m, hmi, hm⟩ := n.lastTime_anchor c.i hlt
  rw [hmi] at hidx
  exact Good.repoint_gt B c x n m e y hpos hm (by simpa using hidx) h

theorem KNode.linkIndex_some (n : KNode) (y : NodeId) (cv j : Nat)
    (h : n.linkIndex y cv = some j) : ∃ c', n.ks[j]? = some (.key c' y) := by
  unfold KNode.linkIndex at h
  dsimp only at h
  split at h
  · rename_i c' y' i hf
    split at h
    · rename_i hc
      have hj : i = j := Option.some.inj h
      subst hj
      have hmem := List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
      have hget := List.mem_zipIdx_iff_getElem?.mp hmem
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rw [hc.2] at hget
      exact ⟨c', hget⟩
    · cases h
  · cases h

/-- The klong that links a node of the transaction, pointed in place: no
klong of an earlier time names a node of the transaction. -/
theorem Good.repointLink (B : NodeId) (c : Ctx) (q : NodeId) (pn : KNode) (x : NodeId)
    (cv j : Nat) (y : NodeId) (hv : ViewGood B c) (h : Good B c q pn)
    (hl : pn.linkIndex x cv = some j) (hx : B ≤ x) : Good B c q (pn.repoint j y) := by
  obtain ⟨c', hj⟩ := pn.linkIndex_some x cv j hl
  have hnot : Klong.key c' x ∉ prefixAt pn.ks (c.i - 1) := by
    intro hm
    rw [h.old] at hm
    unfold baseKlongs at hm
    split at hm
    · rename_i nd hq
      have := hv.ptrs q nd hq c' x hm
      omega
    · cases hm
  rcases prefixAt_stop pn.ks (c.i - 1) with he | ⟨u, hu, hstop⟩
  · rw [he] at hnot
    exact (hnot (List.mem_of_getElem? hj)).elim
  · have hjl : (prefixAt pn.ks (c.i - 1)).length < j := by
      rcases Nat.lt_trichotomy j (prefixAt pn.ks (c.i - 1)).length with hlt | heq | hgt
      · exfalso
        apply hnot
        obtain ⟨rest, hr⟩ := prefixAt_prefix pn.ks (c.i - 1)
        have hget : (prefixAt pn.ks (c.i - 1))[j]? = some (.key c' x) := by
          rw [← hr, List.getElem?_append_left hlt] at hj
          exact hj
        exact List.mem_of_getElem? hget
      · rw [← heq, hj] at hstop
        cases hstop
      · exact hgt
    have hui : u = c.i := by
      have := h.times u (List.mem_of_getElem? hstop)
      omega
    subst hui
    exact Good.repoint_gt B c q pn _ j y hv.pos hstop hjl h

theorem take_zipIdx_map {α : Type} (ks : List α) (F : α × Nat → α) (n : Nat)
    (h : ∀ k i, i < n → F (k, i) = k) : (ks.zipIdx.map F).take n = ks.take n := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add]
  split
  · rename_i hj
    cases hk : ks[j]? with
    | none => rfl
    | some k => simp [h k j hj]
  · rfl

/-- `Dag.retarget`: klongs of the transaction named anew. -/
theorem Good.retarget (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (src dst : NodeId)
    (hpos : 0 < c.i) (h : Good B c x n) (hlt : (n.lastTime == some c.i) = true) :
    Good B c x { n with ks := n.ks.zipIdx.map (fun (k, i) => match k with
      | .key cv y => if n.lastTimeIndex.getD 0 < i && y == src then Klong.key cv dst else k
      | _ => k) } := by
  obtain ⟨m, hmi, hm⟩ := n.lastTime_anchor c.i (by simpa using hlt)
  refine ⟨?_, ?_, h.origin⟩
  · rw [← h.old]
    refine prefixAt_eq_of_take n.ks _ (c.i - 1) c.i m (by omega) hm ?_
    apply take_zipIdx_map
    intro k i hi
    cases k with
    | key cv y =>
      have : ¬ (n.lastTimeIndex.getD 0 < i) := by rw [hmi]; simp; omega
      simp [this]
    | time u => rfl
    | del b => rfl
  · intro t ht
    obtain ⟨⟨k, i⟩, hki, hF⟩ := List.mem_map.mp ht
    have hk : k ∈ n.ks := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hki)
    cases k with
    | key cv y =>
      dsimp only at hF
      split at hF <;> cases hF
    | time u =>
      dsimp only at hF
      cases hF
      exact h.times t hk
    | del b =>
      dsimp only at hF
      cases hF

/-! ## Blank nodes and last versions -/

theorem blank_fresh (B : NodeId) (c : Ctx) (hv : ViewGood B c) (x : NodeId) (hx : B ≤ x) :
    Blank B c x := by
  refine ⟨?_, Or.inr hx⟩
  unfold baseKlongs
  split
  · rename_i nd hn
    have := hv.ids x nd hn
    omega
  · rfl

/-- A node whose first time klong is the transaction's has no klong of an
earlier time. -/
theorem blank_of_firstTime (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hpos : 0 < c.i)
    (h : Good B c x n) (hf : (n.firstTime == some c.i) = true) : Blank B c x := by
  refine ⟨?_, h.origin⟩
  have hno := prefixAt_no_time_of_firstTime n.ks (c.i - 1) c.i (by omega)
    (by simpa [KNode.firstTime] using hf)
  rw [h.old] at hno
  unfold baseKlongs at hno ⊢
  split
  · rename_i nd hn
    simp only [hn] at hno
    rcases klongsOf_head nd.hist with he | ⟨t, r, he⟩
    · exact he
    · exact (hno t (by rw [he]; exact List.mem_cons_self)).elim
  · rfl

/-- A blank node is one of the transaction's: a key node of the view has a
klong. -/
theorem Blank.ge (B : NodeId) (c : Ctx) (x : NodeId) (hv : ViewGood B c) (h : Blank B c x) :
    B ≤ x := by
  rcases h.2 with ⟨nd, hx, hd, hl⟩ | hx
  · have hb := h.1
    simp only [baseKlongs, hx] at hb
    exact (hv.nonempty x nd hx hd hl hb).elim
  · exact hx

theorem Good.ofBlank (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode)
    (hpos : 0 < c.i) (hb : Blank B c x) (hks : n.ks = [] ∨ FlatAt c.i n.ks) :
    Good B c x n := by
  refine ⟨?_, ?_, hb.2⟩
  · rw [hb.1]
    rcases hks with he | ⟨r, he, _⟩
    · rw [he]; rfl
    · rw [he]; simp [prefixAt, show ¬ c.i ≤ c.i - 1 by omega]
  · intro t hm
    rcases hks with he | ⟨r, he, hr⟩
    · rw [he] at hm; cases hm
    · rw [he] at hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm; exact Nat.le_refl _
      · obtain ⟨cv, y, hk⟩ := hr _ hm
        cases hk

/-- Key klongs only. -/
def AllKeys (ks : List Klong) : Prop := ∀ k ∈ ks, ∃ cv y, k = Klong.key cv y

theorem allKeys_map (pairs : List (Nat × NodeId)) :
    AllKeys (pairs.map (fun q => Klong.key q.1 q.2)) := by
  intro k hk
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hk
  exact ⟨q.1, q.2, rfl⟩

theorem flatAt_newKlongs (i : Time) (pairs : List (Nat × NodeId)) : FlatAt i (newKlongs i pairs) :=
  ⟨_, rfl, allKeys_map pairs⟩

theorem flatAt_of_flat (ks : List Klong) (h : FlatKlongs ks) :
    ∃ t r, ks = .time t :: r ∧ AllKeys r := by
  obtain ⟨t, pairs, rfl⟩ := h
  exact ⟨t, _, rfl, allKeys_map pairs⟩

theorem FlatAt.flat (i : Time) (ks : List Klong) (h : FlatAt i ks) : FlatKlongs ks := by
  obtain ⟨r, rfl, hr⟩ := h
  have hp : ∀ r : List Klong, AllKeys r → ∃ pairs : List (Nat × NodeId),
      r = pairs.map (fun q => Klong.key q.1 q.2) := by
    intro r
    induction r with
    | nil => intro _; exact ⟨[], rfl⟩
    | cons k r ih =>
      intro hr
      obtain ⟨pairs, hp⟩ := ih (fun k hk => hr k (List.mem_cons_of_mem _ hk))
      obtain ⟨cv, y, rfl⟩ := hr k List.mem_cons_self
      exact ⟨(cv, y) :: pairs, by simp [hp]⟩
  obtain ⟨pairs, rfl⟩ := hp r hr
  exact ⟨i, pairs, rfl⟩

theorem KNode.lastVersionGivenDel_flatAt (n : KNode) (t : Time) (bits : List Nat) :
    FlatAt t (n.lastVersionGivenDel t bits).ks := by
  obtain ⟨pairs, hp, _⟩ := n.lastVersionGivenDel_order t bits
  rw [hp]
  exact flatAt_newKlongs t pairs

theorem KNode.lastVersion_flatAt (n : KNode) (t : Time) : FlatAt t (n.lastVersion t).ks :=
  n.lastVersionGivenDel_flatAt t _

theorem flatAt_of_shape (i : Time) (ks old : List Klong)
    (he : ks.map klongShape = old.map klongShape) (h : FlatAt i old) : FlatAt i ks := by
  obtain ⟨r, rfl, hr⟩ := h
  cases ks with
  | nil => simp at he
  | cons k ks =>
    simp only [List.map_cons] at he
    have hh := List.cons.inj he
    have hk : k = .time i := by
      cases k <;> simp [klongShape] at hh ⊢
      exact hh.1
    subst hk
    refine ⟨ks, rfl, ?_⟩
    intro k hk
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hk
    have hs : (ks.map klongShape)[j]? = (r.map klongShape)[j]? := by rw [hh.2]
    simp only [List.getElem?_map, hj, Option.map_some] at hs
    cases hrj : r[j]? with
    | none => simp [hrj] at hs
    | some k' =>
      obtain ⟨cv, y, rfl⟩ := hr k' (List.mem_of_getElem? hrj)
      simp only [hrj, Option.map_some, Option.some.injEq] at hs
      cases k <;> simp [klongShape] at hs
      exact ⟨_, _, rfl⟩

theorem flatAt_replaceKlong (i : Time) (ks out : List Klong) (t cv : Nat) (y : NodeId)
    (h : FlatAt i ks) (hr : replaceKlong ks t cv y = .ok (some out)) : FlatAt i out :=
  flatAt_of_shape i _ _ (replaceKlong_shape _ _ _ _ _ hr) h

theorem allKeys_insertSorted (r : List Klong) (cv : Nat) (y : NodeId) (h : AllKeys r) :
    AllKeys (insertSorted r cv y) := by
  induction r with
  | nil =>
    intro k hk
    simp only [insertSorted, List.mem_singleton] at hk
    exact ⟨cv, y, hk⟩
  | cons k r ih =>
    obtain ⟨c', y', rfl⟩ := h k List.mem_cons_self
    have hr : AllKeys r := fun k hk => h k (List.mem_cons_of_mem _ hk)
    by_cases hc : cv < c'
    · simp only [insertSorted, hc, ↓reduceIte]
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨cv, y, rfl⟩
      · exact h k hk
    · simp only [insertSorted, hc, ↓reduceIte]
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨c', y', rfl⟩
      · exact ih hr k hk

theorem flatAt_insertSorted (i : Time) (ks : List Klong) (cv : Nat) (y : NodeId)
    (h : FlatAt i ks) : FlatAt i (insertSorted ks cv y) := by
  obtain ⟨r, rfl, hr⟩ := h
  exact ⟨insertSorted r cv y, rfl, allKeys_insertSorted r cv y hr⟩

theorem flatAt_rename_after_head (i : Time) (old : List Klong) (k : Klong) (cv : Nat)
    (y : NodeId) (rest : List Klong) (newCv : Nat)
    (he : old = k :: .key cv y :: rest) (hf : FlatAt i old) :
    FlatAt i (k :: .key newCv y :: rest) := by
  obtain ⟨r, hr, hk⟩ := hf
  rw [he] at hr
  obtain ⟨rfl, rfl⟩ := List.cons.inj hr
  refine ⟨_, rfl, ?_⟩
  intro k' hk'
  rcases List.mem_cons.mp hk' with rfl | hk'
  · exact ⟨newCv, y, rfl⟩
  · exact hk k' (List.mem_cons_of_mem _ hk')

theorem flatAt_lastTime (i : Time) (n : KNode) (h : FlatAt i n.ks) : n.lastTime = some i := by
  obtain ⟨r, hr, hk⟩ := h
  unfold KNode.lastTime
  rw [hr, List.foldl_cons]
  have hf : ∀ (r : List Klong), AllKeys r → r.foldl (fun t k => match k with
      | .time x => some x
      | _ => t) (some i) = some i := by
    intro r
    induction r with
    | nil => intro _; rfl
    | cons k r ih =>
      intro hr
      obtain ⟨cv, y, rfl⟩ := hr k List.mem_cons_self
      exact ih (fun k hk => hr k (List.mem_cons_of_mem _ hk))
  exact hf r hk

theorem FlatAt.add_key (i : Time) (n : KNode) (cv : Nat) (y : NodeId) (h : FlatAt i n.ks) :
    FlatAt i (n.add i (.key cv y)).ks := by
  have hl := flatAt_lastTime i n h
  obtain ⟨r, hr, hk⟩ := h
  have he : (n.add i (.key cv y)).ks = n.ks ++ [.key cv y] := by
    unfold KNode.add
    rw [hl]
    simp
  rw [he, hr]
  refine ⟨r ++ [.key cv y], rfl, ?_⟩
  intro k hk'
  rcases List.mem_append.mp hk' with hk' | hk'
  · exact hk k hk'
  · exact ⟨cv, y, List.mem_singleton.mp hk'⟩

theorem allKeys_append (a b : List Klong) (ha : AllKeys a) (hb : AllKeys b) : AllKeys (a ++ b) := by
  intro k hk
  rcases List.mem_append.mp hk with hk | hk
  · exact ha k hk
  · exact hb k hk

theorem allKeys_map_of {α : Type} (xs : List α) (F : α → Klong)
    (hF : ∀ q, ∃ cv y, F q = Klong.key cv y) : AllKeys (xs.map F) := by
  intro k hk
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hk
  exact hF q

theorem ite_both {α : Type} (P : α → Prop) (c : Prop) [Decidable c] (a b : α)
    (ha : P a) (hb : P b) : P (if c then a else b) := by
  split <;> assumption

/-- Both halves of a space split are last versions at the split's time. -/
theorem halves_flatAt (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId))
    (h : FlatKlongs last.ks) :
    FlatAt t (halves leaf t last ins).1.ks ∧ FlatAt t (halves leaf t last ins).2.1.ks := by
  obtain ⟨u, r, hr, hk⟩ := flatAt_of_flat _ h
  have hf : AllKeys (r.take ((last.size - 1) / 2 + 1 - 1)) :=
    fun k hk' => hk k (List.mem_of_mem_take hk')
  have hs : AllKeys (r.drop ((last.size - 1) / 2 + 1 - 1)) :=
    fun k hk' => hk k (List.mem_of_mem_drop hk')
  have hs' : AllKeys (if leaf = true then r.drop ((last.size - 1) / 2 + 1 - 1) else
      match r.drop ((last.size - 1) / 2 + 1 - 1) with
      | .key _ y :: r' => .key 0 y :: r'
      | s => s) := by
    split
    · exact hs
    · split
      · rename_i c y r' heq
        rw [heq] at hs
        intro k hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact ⟨0, y, rfl⟩
        · exact hs k (List.mem_cons_of_mem _ hk')
      · exact hs
  have hins : ∀ (b : Bool) (sc : Nat), AllKeys (ins.map (fun (q : Nat × NodeId) =>
      if (!leaf && b && q.1 == sc) = true then Klong.key 0 q.2 else Klong.key q.1 q.2)) := by
    intro b sc
    apply allKeys_map_of
    intro q
    split
    · exact ⟨0, q.2, rfl⟩
    · exact ⟨q.1, q.2, rfl⟩
  unfold halves
  simp only [hr, List.drop_succ_cons, List.drop_zero]
  exact ite_both (fun z : KNode × KNode × Nat => FlatAt t z.1.ks ∧ FlatAt t z.2.1.ks) _ _ _
    ⟨⟨_, rfl, hf⟩, ⟨_, rfl, allKeys_append _ _ hs' (hins _ _)⟩⟩
    ⟨⟨_, rfl, allKeys_append _ _ hf (hins _ _)⟩, ⟨_, rfl, hs'⟩⟩

end SIS.Tree
