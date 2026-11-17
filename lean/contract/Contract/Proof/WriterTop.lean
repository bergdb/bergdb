/-
The contract package (bergdb 030-10): the writer's step `newSuperRoot y`
(Java's `TopDs.newSuperRoot`), which makes y the space root at the
transaction's time: in place in the transaction's own top node, or by a new
top node with the next ordinal and a skip pointer at each bit set in the
ordinal.

* Section 1, the state after the step, in closed form (`MW.afterSuperRoot`),
  and the step as an equation: in place when the transaction made the top
  node, else a new one (`newSuperRoot_eq`, from J5, `WTopInv`).
* Section 2, the top: J5 holds after the step (`topInv_afterSuperRoot`). The
  hard part is T3's last clause, that the lowest skip pointer of a new top
  node names the old super root: the old super root's skip pointers are at
  the bits set in its ordinal, and the lowest bit set in ord + 1 is a bit not
  set in ord (`nsr_lowBit`), so the new top node takes no skip pointer of the
  old one there and names the old super root itself.
* Section 3, the map after the step: the same nodes, the root y, the same D
  (`treeOf_afterSuperRoot`); and the put's books (`putBooks_afterSuperRoot`).
* Section 4, all of it together (`newSuperRoot_spec`, `wp_newSuperRoot`).
-/
import Contract.Proof.WriterState

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. The state after the step -/

/-- The ordinal of the top node made after a super root with ordinal o. -/
def nsrOrd (o : Nat) : Nat := if o == 0 then 1 else o + 1

/-- The skip pointers of the top node with ordinal o made after the super root
t: one at each bit set in o, the old super root's of that index, or else the
old super root. -/
def nsrSkips (t : SIS.Tree.Top) (o : Nat) : List (Nat × NodeId) :=
  (List.range (SIS.Tree.topHeight o)).filterMap (fun j =>
    if o.testBit j then
      match t.skips.lookup j with
      | some u => some (j, u)
      | none => some (j, t.id)
    else none)

/-- The state after `newSuperRoot y` in place: the transaction's own top node
gets the root y. -/
def MW.superRootInPlace (w : MW) (y : NodeId) : MW :=
  { w with top := { w.top with rootKey := y }, trail := "top.inplace" :: w.trail }

/-- The state after `newSuperRoot y` at time i with a new top node: the next
id, the next ordinal, the time i, the root y and its skip pointers. -/
def MW.superRootNew (w : MW) (p : MParams) (i : Time) (y : NodeId) : MW :=
  { w with trail := "top.new" :: w.trail, next := w.next + 2,
           top := ⟨w.next, nsrOrd w.top.ord, i, y, nsrSkips w.top (nsrOrd w.top.ord)⟩,
           newTop := true, made := w.made ++ [⟨w.next, p.topLevel (nsrOrd w.top.ord), false⟩] }

/-- The state after `newSuperRoot y` at time i: in place if the transaction
made the top node, else with a new one. -/
def MW.afterSuperRoot (w : MW) (p : MParams) (i : Time) (y : NodeId) : MW :=
  if w.newTop then MW.superRootInPlace w y else MW.superRootNew w p i y

theorem afterSuperRoot_of_true {w : MW} (h : w.newTop = true) (p : MParams) (i : Time)
    (y : NodeId) : MW.afterSuperRoot w p i y = MW.superRootInPlace w y := by
  simp only [MW.afterSuperRoot, h, ↓reduceIte]

theorem afterSuperRoot_of_false {w : MW} (h : w.newTop = false) (p : MParams) (i : Time)
    (y : NodeId) : MW.afterSuperRoot w p i y = MW.superRootNew w p i y := by
  simp only [MW.afterSuperRoot, h, Bool.false_eq_true, ↓reduceIte]

/-- What the step changes and what it keeps, in both cases. -/
theorem afterSuperRoot_fields (w : MW) (p : MParams) (i : Time) (y : NodeId) :
    (MW.afterSuperRoot w p i y).top.rootKey = y ∧ (MW.afterSuperRoot w p i y).newTop = true ∧
      (MW.afterSuperRoot w p i y).nodes = w.nodes ∧ (MW.afterSuperRoot w p i y).vals = w.vals ∧
      (MW.afterSuperRoot w p i y).taken = w.taken ∧ (MW.afterSuperRoot w p i y).gh = w.gh ∧
      (MW.afterSuperRoot w p i y).madeFor = w.madeFor ∧
      (MW.afterSuperRoot w p i y).path = w.path ∧
      (MW.afterSuperRoot w p i y).outside = w.outside := by
  cases hnt : w.newTop
  · rw [afterSuperRoot_of_false hnt]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [afterSuperRoot_of_true hnt]
    exact ⟨rfl, hnt, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- In place: the same nodes made, the same next id, the same top node. -/
theorem afterSuperRoot_inPlace {w : MW} (h : w.newTop = true) (p : MParams) (i : Time)
    (y : NodeId) : (MW.afterSuperRoot w p i y).made = w.made ∧
      (MW.afterSuperRoot w p i y).next = w.next ∧
      (MW.afterSuperRoot w p i y).top.id = w.top.id := by
  rw [afterSuperRoot_of_true h]
  exact ⟨rfl, rfl, rfl⟩

/-- A new top node: made at the end of the nodes made, with the next id. -/
theorem afterSuperRoot_new {w : MW} (h : w.newTop = false) (p : MParams) (i : Time)
    (y : NodeId) : (MW.afterSuperRoot w p i y).made =
        w.made ++ [⟨w.next, p.topLevel (nsrOrd w.top.ord), false⟩] ∧
      (MW.afterSuperRoot w p i y).next = w.next + 2 ∧
      (MW.afterSuperRoot w p i y).top.id = w.next := by
  rw [afterSuperRoot_of_false h]
  exact ⟨rfl, rfl, rfl⟩

/-- The step at the time of the super root: in place. -/
theorem newSuperRoot_inPlace_eq (c : Ctx) (w : MW) (y : NodeId) (h : c.i = w.top.time) :
    SIS.Tree.newSuperRoot y c w = .ok ((), MW.superRootInPlace w y) := by
  simp only [SIS.Tree.newSuperRoot, SIS.Tree.note, bind, ReaderT.bind, StateT.bind, read, readThe,
    MonadReaderOf.read, ReaderT.read, MonadState.get, getThe, MonadStateOf.get, StateT.get, set,
    MonadStateOf.set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    pure, StateT.pure, Except.pure, liftM, monadLift, MonadLift.monadLift, Except.bind, h,
    beq_self_eq_true, ↓reduceIte]
  rfl

/-- The step at another time: a new top node. -/
theorem newSuperRoot_new_eq (c : Ctx) (w : MW) (y : NodeId) (h : c.i ≠ w.top.time) :
    SIS.Tree.newSuperRoot y c w = .ok ((), MW.superRootNew w c.p c.i y) := by
  have h' : (c.i == w.top.time) = false := by simpa using h
  simp only [SIS.Tree.newSuperRoot, SIS.Tree.note, SIS.Tree.fresh, bind, ReaderT.bind,
    StateT.bind, read, readThe, MonadReaderOf.read, ReaderT.read, MonadState.get, getThe,
    MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, ReaderT.pure, StateT.pure, Except.pure, liftM,
    monadLift, MonadLift.monadLift, Except.bind, h', Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The step, from J5: in place exactly if the transaction made the top node. -/
theorem newSuperRoot_eq {p : MParams} {i : Time} {s : Tree} {tp : Top} (v : View BVal)
    (y : NodeId) {w : MW} (hT : WTopInv i s tp w.top w.newTop) :
    SIS.Tree.newSuperRoot y { p := p, i := i, view := v } w =
      .ok ((), MW.afterSuperRoot w p i y) := by
  obtain ⟨-, hold, hnew⟩ := hT
  cases hnt : w.newTop
  · rw [afterSuperRoot_of_false hnt]
    exact newSuperRoot_new_eq _ w y (Nat.ne_of_gt (hold hnt).1)
  · rw [afterSuperRoot_of_true hnt]
    exact newSuperRoot_inPlace_eq _ w y (hnew hnt).1.symm

/-! ## 2. The top -/

/-- The lowest bit set in ord + 1 is not set in ord. -/
theorem nsr_lowBit : ∀ (k ord : Nat), (ord + 1).testBit k = true →
    (∀ j < k, (ord + 1).testBit j = false) → ord.testBit k = false
  | 0, ord, h, _ => by
    simp only [Nat.testBit_zero, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
    omega
  | k + 1, ord, h, hlt => by
    have h0 := hlt 0 (Nat.succ_pos k)
    simp only [Nat.testBit_zero, decide_eq_false_iff_not] at h0
    have hd : (ord + 1) / 2 = ord / 2 + 1 := by omega
    rw [Nat.testBit_add_one] at h ⊢
    rw [hd] at h
    refine nsr_lowBit k (ord / 2) h (fun j hj => ?_)
    have := hlt (j + 1) (by omega)
    rwa [Nat.testBit_add_one, hd] at this

theorem nsr_strictUp : ∀ l : List Nat, l.Pairwise (· < ·) → strictUp l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
    simp only [strictUp, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, nsr_strictUp (b :: r) h.of_cons⟩

theorem nsr_lookup_some {β : Type} : ∀ {l : List (NodeId × β)} {a : NodeId} {b : β},
    (a, b) ∈ l → (l.lookup a).isSome = true
  | [], _, _, h => by simp at h
  | (k, c) :: r, a, b, h => by
    by_cases hk : a = k
    · subst hk
      simp
    · have hb : (a == k) = false := by simpa using hk
      rw [List.lookup_cons, hb]
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1 hk
      · exact nsr_lookup_some h

theorem nsr_mem_lookup {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β},
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (k, c) :: r, a, b, h => by
    by_cases hk : a = k
    · subst hk
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (a == k) = false := by simpa using hk
      rw [List.lookup_cons, hb] at h
      exact List.mem_cons_of_mem _ (nsr_mem_lookup h)

theorem nsr_lookup_none {β : Type} {l : List (Nat × β)} {a : Nat} (h : a ∉ l.map (·.1)) :
    l.lookup a = none := by
  rw [List.lookup_eq_none_iff]
  intro q hq
  have hm : q.1 ∈ l.map (·.1) := List.mem_map_of_mem hq
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact h hm

/-- The indexes of the new skip pointers: the bits set in the ordinal. -/
theorem nsrSkips_fst (t : SIS.Tree.Top) (o : Nat) :
    (nsrSkips t o).map (·.1) =
      (List.range (SIS.Tree.topHeight o)).filter (fun j => o.testBit j) := by
  unfold nsrSkips
  induction List.range (SIS.Tree.topHeight o) with
  | nil => rfl
  | cons j r ih =>
    by_cases hj : o.testBit j = true
    · cases hl : t.skips.lookup j <;> simp [hj, hl, ih]
    · simp [hj, ih]

/-- A new skip pointer is the old super root's of its index, or names the old
super root. -/
theorem nsrSkips_mem {t : SIS.Tree.Top} {o : Nat} {q : Nat × NodeId} (h : q ∈ nsrSkips t o) :
    t.skips.lookup q.1 = some q.2 ∨ (t.skips.lookup q.1 = none ∧ q.2 = t.id) := by
  unfold nsrSkips at h
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp h
  split at hj
  · cases hl : t.skips.lookup j with
    | none =>
      rw [hl] at hj
      cases hj
      exact Or.inr ⟨hl, rfl⟩
    | some u =>
      rw [hl] at hj
      cases hj
      exact Or.inl hl
  · cases hj

theorem nsr_head_range' {β : Type} (f : Nat → Option β) {k : Nat} {b : β} (hk : f k = some b)
    (hlt : ∀ j < k, f j = none) :
    ∀ n a, a ≤ k → k < a + n → ((List.range' a n).filterMap f).head? = some b
  | 0, a, h1, h2 => by omega
  | n + 1, a, h1, h2 => by
    rw [List.range'_succ, List.filterMap_cons]
    rcases Nat.lt_or_eq_of_le h1 with h | rfl
    · rw [hlt a h]
      exact nsr_head_range' f hk hlt n (a + 1) h (by omega)
    · rw [hk]
      rfl

/-- The lowest new skip pointer names the old super root, if the old super
root's skip pointers are at the bits set in its ordinal. -/
theorem nsrSkips_head (t : SIS.Tree.Top) (hidx : t.skips.map (·.1) =
      (List.range (SIS.Tree.topHeight t.ord)).filter (fun j => t.ord.testBit j)) :
    ∃ k, (nsrSkips t (nsrOrd t.ord)).head? = some (k, t.id) := by
  have ho : nsrOrd t.ord = t.ord + 1 := by
    unfold nsrOrd
    split <;> simp_all
  have hex : ∃ k, (t.ord + 1).testBit k = true := Nat.exists_testBit_of_ne_zero (by omega)
  refine ⟨Nat.find hex, ?_⟩
  have hk := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, (t.ord + 1).testBit j = false := fun j hj => by
    simpa using Nat.find_min hex hj
  have hlow := nsr_lowBit _ _ hk hmin
  have hl : t.skips.lookup (Nat.find hex) = none := by
    apply nsr_lookup_none
    rw [hidx]
    simp [hlow]
  have hH : Nat.find hex < SIS.Tree.topHeight (t.ord + 1) := by
    unfold SIS.Tree.topHeight
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, beq_iff_eq, ↓reduceIte]
    by_contra hc
    have hlt : t.ord + 1 < 2 ^ Nat.find hex :=
      lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hlt] at hk
    cases hk
  rw [ho]
  unfold nsrSkips
  rw [List.range_eq_range']
  exact nsr_head_range' _ (k := Nat.find hex) (by simp [hk, hl]) (fun j hj => by simp [hmin j hj])
    (SIS.Tree.topHeight (t.ord + 1)) 0 (Nat.zero_le _) (by omega)

/-- J5 after a new top node. -/
theorem topInv_superRootNew {i : Time} {base : NodeId} {s : Tree} {tp : Top} (p : MParams)
    (y : NodeId) {w : MW} (hT : WTopInv i s tp w.top false) (hb : Books i base s tp)
    (hbase : base ≤ w.next) : WTopInv i s tp (MW.superRootNew w p i y).top true := by
  obtain ⟨hroots, hold, -⟩ := hT
  obtain ⟨-, zn, hlast, hsk, hidx, hcache⟩ := hold rfl
  unfold WTopInv
  refine ⟨hroots, fun h => absurd h (by simp), fun _ => ⟨rfl, (hb.ids _ hbase).2, ?_⟩⟩
  have hnamed : ∀ q ∈ nsrSkips w.top (nsrOrd w.top.ord), (tp.node q.2).isSome = true := by
    intro q hq
    rcases nsrSkips_mem hq with h | ⟨-, h⟩
    · have hm := nsr_mem_lookup h
      rw [hsk] at hm
      obtain ⟨r, hr, hreq⟩ := List.mem_map.mp hm
      have hc := hcache r hr
      have h2 : r.2.1 = q.2 := congrArg Prod.snd hreq
      rw [← h2]
      revert hc
      cases tp.node r.2.1 <;> simp
    · rw [h]
      exact nsr_lookup_some (List.mem_of_getLast? hlast)
  obtain ⟨k, hk⟩ := nsrSkips_head w.top hidx
  simp only [MW.superRootNew]
  unfold skipsOk
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.map_map]
    have he : ((·.1) ∘
        fun q : Nat × NodeId => (q.1, q.2, ((tp.node q.2).map (·.time)).getD 0)) = (·.1) := rfl
    rw [he, nsrSkips_fst]
    exact nsr_strictUp _ (List.pairwise_lt_range.filter _)
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    have hs := hnamed q0 hq0
    revert hs
    cases tp.node q0.2 <;> simp
  · rw [hlast, List.head?_map, hk]
    simp

/-- J5 after the step. -/
theorem topInv_afterSuperRoot {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (y : NodeId) {w : MW} (hT : WTopInv i s tp w.top w.newTop) (hb : Books i base s tp)
    (hbase : base ≤ w.next) :
    WTopInv i s tp (MW.afterSuperRoot w p i y).top (MW.afterSuperRoot w p i y).newTop := by
  rw [(afterSuperRoot_fields w p i y).2.1]
  cases hnt : w.newTop
  · rw [hnt] at hT
    rw [afterSuperRoot_of_false hnt]
    exact topInv_superRootNew p y hT hb hbase
  · rw [hnt] at hT
    rw [afterSuperRoot_of_true hnt]
    obtain ⟨hroots, -, hnew⟩ := hT
    unfold WTopInv
    exact ⟨hroots, fun h => absurd h (by simp), fun _ => hnew rfl⟩

/-! ## 3. The map and the books -/

/-- The level of a key node other than the new top node is the same. -/
theorem wLevel_afterSuperRoot (s : Tree) (p : MParams) (i : Time) (y : NodeId) {w : MW}
    {x : NodeId} (hx : x ≠ w.next) :
    wLevel s (MW.afterSuperRoot w p i y) x = wLevel s w x := by
  cases hnt : w.newTop
  · rw [afterSuperRoot_of_false hnt]
    have hf : (MW.superRootNew w p i y).made.find? (fun m => m.id == x) =
        w.made.find? (fun m => m.id == x) := by
      simp [MW.superRootNew, List.find?_append, Ne.symm hx]
    unfold wLevel
    rw [hf]
  · rw [afterSuperRoot_of_true hnt]
    rfl

/-- The map after the step: the same nodes, the root y, the same D. -/
theorem treeOf_afterSuperRoot (i : Time) (s : Tree) (p : MParams) (y : NodeId) {w : MW}
    (hn : ∀ x n, w.nodes.lookup x = some n → x < w.next) :
    (treeOf i s (MW.afterSuperRoot w p i y)).obj = (treeOf i s w).obj ∧
      (treeOf i s (MW.afterSuperRoot w p i y)).root = some y ∧
      dirtyOf (MW.afterSuperRoot w p i y) = dirtyOf w := by
  obtain ⟨hr, hnt, h1, h2, h3, -⟩ := afterSuperRoot_fields w p i y
  refine ⟨funext fun x => ?_, ?_, ?_⟩
  · simp only [treeOf, h1, h2, h3]
    cases hl : w.nodes.lookup x with
    | none => rfl
    | some n => simp only [wLevel_afterSuperRoot s p i y (Nat.ne_of_lt (hn x n hl))]
  · simp [Tree.root, treeOf, hnt, hr]
  · simp only [dirtyOf, h1]

/-- The put's books after the step. -/
theorem putBooks_afterSuperRoot {p : MParams} {i : Time} {base : NodeId} {s : Tree} (y : NodeId)
    {w : MW} (hk : PutBooks p i base s w) : PutBooks p i base s (MW.afterSuperRoot w p i y) := by
  obtain ⟨-, -, h1, h2, h3, h4, -, -, h7⟩ := afterSuperRoot_fields w p i y
  have hlev : ∀ x n, w.nodes.lookup x = some n →
      wLevel s (MW.afterSuperRoot w p i y) x = wLevel s w x :=
    fun x n hl => wLevel_afterSuperRoot s p i y (Nat.ne_of_lt (hk.ids.1 x n hl))
  have hmade : ∀ x, x ∈ w.made.map (·.id) →
      x ∈ (MW.afterSuperRoot w p i y).made.map (·.id) := by
    intro x hx
    cases hnt : w.newTop
    · rw [(afterSuperRoot_new hnt p i y).1, List.map_append]
      exact List.mem_append_left _ hx
    · rw [(afterSuperRoot_inPlace hnt p i y).1]
      exact hx
  have hids : ((∀ x n, (MW.afterSuperRoot w p i y).nodes.lookup x = some n →
        x < (MW.afterSuperRoot w p i y).next) ∧
      (∀ x h, (MW.afterSuperRoot w p i y).vals.lookup x = some h →
        x < (MW.afterSuperRoot w p i y).next) ∧
      (∀ m ∈ (MW.afterSuperRoot w p i y).made, m.id < (MW.afterSuperRoot w p i y).next ∧
        base ≤ m.id) ∧
      base ≤ (MW.afterSuperRoot w p i y).next ∧
      ((MW.afterSuperRoot w p i y).newTop = true →
        (MW.afterSuperRoot w p i y).top.id < (MW.afterSuperRoot w p i y).next)) := by
    obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := hk.ids
    cases hnt : w.newTop
    · rw [afterSuperRoot_of_false hnt]
      refine ⟨fun x n hl => Nat.lt_add_right 2 (hi1 x n hl),
        fun x h hl => Nat.lt_add_right 2 (hi2 x h hl), fun m hm => ?_, by
          show base ≤ w.next + 2; omega, fun _ => by show w.next < w.next + 2; omega⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨Nat.lt_add_right 2 (hi3 m hm).1, (hi3 m hm).2⟩
      · simp only [List.mem_singleton] at hm
        subst hm
        exact ⟨by show w.next < w.next + 2; omega, hi4⟩
    · rw [afterSuperRoot_of_true hnt]
      exact ⟨hi1, hi2, hi3, hi4, hi5⟩
  refine ⟨?_, ?_, ?_, hids, ?_, ?_, ?_, ?_⟩
  · rw [h1, h3]
    exact hk.first
  · rw [h1]
    exact hk.times
  · intro x n hl ht
    rw [h1] at hl
    rw [h3] at ht
    obtain ⟨g, h, hg, hG, hH, hL, hleaf⟩ := hk.levels x n hl ht
    exact ⟨g, h, by rw [h4]; exact hg, hG, hH, by rw [hlev x n hl]; exact hL, hleaf⟩
  · rw [h3]
    exact fun x hx => hmade x (hk.taken x hx)
  · rw [h1]
    intro x n hl
    rcases hk.overlay x n hl with h | h
    · exact Or.inl h
    · exact Or.inr (hmade x h)
  · rw [h7]
    exact hk.within
  · rw [h1, h3]
    exact hk.timeFirst

/-- The space roots after the step: those of s, and y at time i. -/
theorem treeOf_afterSuperRoot_roots (i : Time) (s : Tree) (p : MParams) (y : NodeId) (w : MW) :
    (treeOf i s (MW.afterSuperRoot w p i y)).roots = s.roots ++ [(i, y)] := by
  obtain ⟨hr, hnt, -⟩ := afterSuperRoot_fields w p i y
  simp [treeOf, hnt, hr]

/-! ## 4. The step, all together -/

/-- `newSuperRoot y` from a state with J5 and the books of a start: no error;
the state after it is `MW.afterSuperRoot`, with J5, the root y, a top node of
the transaction, and the same overlay, values, nodes taken back, segments and
heights, `madeFor`, path and nodes outside; in place the same nodes made and
next id, else the new top node made at the end, with the next id. -/
theorem newSuperRoot_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (v : View BVal) (y : NodeId) {w : MW} (hT : WTopInv i s tp w.top w.newTop)
    (hb : Books i base s tp) (hbase : base ≤ w.next) :
    ∃ w', SIS.Tree.newSuperRoot y { p := p, i := i, view := v } w = .ok ((), w') ∧
      w' = MW.afterSuperRoot w p i y ∧
      WTopInv i s tp w'.top w'.newTop ∧ w'.top.rootKey = y ∧ w'.newTop = true ∧
      w'.nodes = w.nodes ∧ w'.vals = w.vals ∧ w'.taken = w.taken ∧ w'.gh = w.gh ∧
      w'.madeFor = w.madeFor ∧ w'.path = w.path ∧ w'.outside = w.outside ∧
      (w.newTop = true → w'.made = w.made ∧ w'.next = w.next ∧ w'.top.id = w.top.id) ∧
      (w.newTop = false →
        w'.made = w.made ++ [⟨w.next, p.topLevel (nsrOrd w.top.ord), false⟩] ∧
        w'.next = w.next + 2 ∧ w'.top.id = w.next) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := afterSuperRoot_fields w p i y
  exact ⟨_, newSuperRoot_eq v y hT, rfl, topInv_afterSuperRoot y hT hb hbase, f1, f2, f3, f4,
    f5, f6, f7, f8, f9, fun h => afterSuperRoot_inPlace h p i y,
    fun h => afterSuperRoot_new h p i y⟩

/-- The step for the rules of the writer's steps (`WP`): from J5, every
result is the state `MW.afterSuperRoot`. -/
theorem wp_newSuperRoot {p : MParams} {i : Time} {s : Tree} {tp : Top} (v : View BVal)
    (y : NodeId) {w : MW} (hT : WTopInv i s tp w.top w.newTop) (post : Unit → MW → Prop) :
    WP (SIS.Tree.newSuperRoot y) { p := p, i := i, view := v } w post ↔
      post () (MW.afterSuperRoot w p i y) := by
  constructor
  · intro h
    exact h () _ (newSuperRoot_eq v y hT)
  · intro h r w' he
    rw [newSuperRoot_eq v y hT] at he
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at he
    subst he
    exact h

end Contract
