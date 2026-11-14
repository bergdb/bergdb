/-
The tree model (bergdb 024-12, TP4 and TP7): the writer keeps `PtrsOK`
(SIS/Tree/OverlayPtrs.lean): every pointer it stores names a node of P or a
node that the transaction made. This file: the pointers of the node functions,
the relation `MadeKept` between a state and a later one, the writer's
primitive steps, and the splits.
-/
import SIS.Tree.OverlayPtrs
import SIS.Tree.WriterBook

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Pointers of klongs -/

/-- Every key klong of ks names a node that meets P. -/
def ptrsKs (P : NodeId → Prop) (ks : List Klong) : Prop :=
  ∀ cv y, Klong.key cv y ∈ ks → P y

/-- Every pair (compare value, node) of l names a node that meets P. -/
def ptrsPairs (P : NodeId → Prop) (l : List (Nat × NodeId)) : Prop := ∀ q ∈ l, P q.2

theorem ptrsKs_imp {P Q : NodeId → Prop} {ks : List Klong} (h : ptrsKs P ks)
    (hPQ : ∀ y, P y → Q y) : ptrsKs Q ks := fun cv y hm => hPQ y (h cv y hm)

theorem ptrsPairs_imp {P Q : NodeId → Prop} {l : List (Nat × NodeId)} (h : ptrsPairs P l)
    (hPQ : ∀ y, P y → Q y) : ptrsPairs Q l := fun q hq => hPQ _ (h q hq)

theorem ptrsKs_nil (P : NodeId → Prop) : ptrsKs P [] := by
  intro cv y h; cases h

theorem ptrsKs_of_sub {P : NodeId → Prop} {a b : List Klong} (hs : ∀ k ∈ a, k ∈ b)
    (h : ptrsKs P b) : ptrsKs P a := fun cv y hm => h cv y (hs _ hm)

theorem ptrsKs_append {P : NodeId → Prop} {a b : List Klong} (ha : ptrsKs P a)
    (hb : ptrsKs P b) : ptrsKs P (a ++ b) := by
  intro cv y hm
  rcases List.mem_append.mp hm with hm | hm
  · exact ha cv y hm
  · exact hb cv y hm

theorem ptrsKs_cons_time {P : NodeId → Prop} (t : Time) {r : List Klong} (h : ptrsKs P r) :
    ptrsKs P (.time t :: r) := by
  intro cv y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · exact h cv y hm

theorem ptrsKs_cons_del {P : NodeId → Prop} (b : List Nat) {r : List Klong} (h : ptrsKs P r) :
    ptrsKs P (.del b :: r) := by
  intro cv y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · exact h cv y hm

theorem ptrsKs_cons_key {P : NodeId → Prop} (c : Nat) {y : NodeId} {r : List Klong} (hy : P y)
    (h : ptrsKs P r) : ptrsKs P (.key c y :: r) := by
  intro cv z hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm; exact hy
  · exact h cv z hm

theorem ptrsKs_add_key {P : NodeId → Prop} {n : KNode} (t : Time) (c : Nat) {y : NodeId}
    (hn : ptrsKs P n.ks) (hy : P y) : ptrsKs P (n.add t (.key c y)).ks := by
  have hk : ptrsKs P [.time t, .key c y] :=
    ptrsKs_cons_time t (ptrsKs_cons_key c hy (ptrsKs_nil P))
  have hk1 : ptrsKs P [.key c y] := ptrsKs_cons_key c hy (ptrsKs_nil P)
  unfold KNode.add
  split
  · split
    · exact ptrsKs_append hn hk
    · exact ptrsKs_append hn hk1
  · exact ptrsKs_append hn hk

theorem ptrsKs_add_del {P : NodeId → Prop} {n : KNode} (t : Time) (b : List Nat)
    (hn : ptrsKs P n.ks) : ptrsKs P (n.add t (.del b)).ks := by
  have hk : ptrsKs P [.time t, .del b] :=
    ptrsKs_cons_time t (ptrsKs_cons_del b (ptrsKs_nil P))
  have hk1 : ptrsKs P [.del b] := ptrsKs_cons_del b (ptrsKs_nil P)
  unfold KNode.add
  split
  · split
    · exact ptrsKs_append hn hk
    · exact ptrsKs_append hn hk1
  · exact ptrsKs_append hn hk

theorem ptrsKs_foldl {P : NodeId → Prop} (f : KNode → Nat × NodeId → KNode)
    (hf : ∀ n q, ptrsKs P n.ks → P q.2 → ptrsKs P (f n q).ks)
    {n : KNode} (hn : ptrsKs P n.ks) {ins : List (Nat × NodeId)} (hi : ptrsPairs P ins) :
    ptrsKs P (ins.foldl f n).ks := by
  induction ins generalizing n with
  | nil => exact hn
  | cons q ins ih =>
    rw [List.foldl_cons]
    exact ih (hf n q hn (hi q List.mem_cons_self)) (fun e he => hi e (List.mem_cons_of_mem _ he))

theorem ptrsKs_setAt {P : NodeId → Prop} {n : KNode} (i : Nat) (k : Klong)
    (hn : ptrsKs P n.ks) (hk : ptrsKs P [k]) : ptrsKs P (n.setAt i k).ks := by
  intro cv y hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact hn cv y hm
  · exact hk cv y (by rw [hm]; exact List.mem_singleton_self _)

theorem ptrsKs_setAt_del {P : NodeId → Prop} {n : KNode} (i : Nat) (b : List Nat)
    (hn : ptrsKs P n.ks) : ptrsKs P (n.setAt i (.del b)).ks :=
  ptrsKs_setAt i _ hn (ptrsKs_cons_del b (ptrsKs_nil P))

theorem ptrsKs_toPrev {P : NodeId → Prop} {n : KNode} (t : Time) (hn : ptrsKs P n.ks) :
    ptrsKs P (n.toPrev t).ks :=
  ptrsKs_of_sub (fun _ hk => (List.takeWhile_sublist _).subset hk) hn

theorem ptrsKs_repoint {P : NodeId → Prop} {n : KNode} (i : Nat) {y : NodeId}
    (hn : ptrsKs P n.ks) (hy : P y) : ptrsKs P (n.repoint i y).ks := by
  unfold KNode.repoint
  split
  · exact ptrsKs_setAt i _ hn (ptrsKs_cons_key _ hy (ptrsKs_nil P))
  · exact hn

theorem ptrsId_of_ptr {P : NodeId → Prop} {n : KNode} {i : Nat} {y : NodeId}
    (h : n.ptr? i = some y) (hn : ptrsKs P n.ks) : P y := by
  unfold KNode.ptr? at h
  split at h
  · rename_i c z hz
    cases h
    exact hn c _ (List.mem_of_getElem? hz)
  · cases h

theorem ptrs_setCv {P : NodeId → Prop} (m : List (Nat × NodeId)) (c : Nat) (y : NodeId)
    (hm : ptrsPairs P m) (hy : P y) : ptrsPairs P (setCv m c y) := by
  unfold setCv
  split
  · intro q hq
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · subst he; exact hy
    · subst he; exact hm a ha
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hm q hq
    · rw [List.mem_singleton.mp hq]; exact hy

theorem ptrs_lastVersionFold {P : NodeId → Prop} (del : List Nat) (xs : List (Klong × Nat))
    (hx : ∀ q ∈ xs, ∀ cv y, q.1 = .key cv y → P y) (m : List (Nat × NodeId))
    (hm : ptrsPairs P m) :
    ptrsPairs P (xs.foldl (fun m (q : Klong × Nat) => match q.1 with
      | .key c y => if del.contains q.2 then m else setCv m c y
      | _ => m) m) := by
  induction xs generalizing m with
  | nil => exact hm
  | cons q xs ih =>
    rw [List.foldl_cons]
    apply ih (fun e he => hx e (List.mem_cons_of_mem _ he))
    obtain ⟨k, i⟩ := q
    cases k with
    | key c y =>
      dsimp only
      split
      · exact hm
      · exact ptrs_setCv m c y hm (hx _ List.mem_cons_self c y rfl)
    | time t => exact hm
    | del b => exact hm

theorem ptrsKs_lastVersionGivenDel {P : NodeId → Prop} {n : KNode} (t : Time) (del : List Nat)
    (hn : ptrsKs P n.ks) : ptrsKs P (n.lastVersionGivenDel t del).ks := by
  unfold KNode.lastVersionGivenDel
  dsimp only
  apply ptrsKs_cons_time
  intro cv y hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  cases he
  have hq' := (List.mem_mergeSort).mp hq
  have hf := ptrs_lastVersionFold (P := P) del n.ks.zipIdx ?_ [] (fun q h => by cases h)
  · exact hf _ hq'
  · intro e he cv' y' hk
    have hm' : e.1 ∈ n.ks := List.fst_mem_of_mem_zipIdx (by obtain ⟨a, b⟩ := e; exact he)
    rw [hk] at hm'
    exact hn cv' y' hm'

theorem ptrsKs_lastVersion {P : NodeId → Prop} {n : KNode} (t : Time)
    (hn : ptrsKs P n.ks) : ptrsKs P (n.lastVersion t).ks :=
  ptrsKs_lastVersionGivenDel t _ hn

theorem ptrsPairs_live {P : NodeId → Prop} {n : KNode} (hn : ptrsKs P n.ks) :
    ptrsPairs P n.live := by
  intro q hq
  unfold KNode.live at hq
  obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp hq
  cases k with
  | key c y =>
    cases he
    exact ptrsKs_lastVersion 0 hn c y hk
  | time t => cases he
  | del b => cases he

theorem ptrsKs_of_pairs_map {P : NodeId → Prop} {l : List (Nat × NodeId)}
    (f : Nat × NodeId → Klong) (hf : ∀ q, ∃ c, f q = .key c q.2)
    (h : ptrsPairs P l) : ptrsKs P (l.map f) := by
  intro cv y hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  obtain ⟨c, hc⟩ := hf q
  rw [hc] at he
  cases he
  exact h q hq

theorem ptrs_ite_key (b : Prop) [Decidable b] (a c : Nat) (y : NodeId) :
    ∃ c', (if b then Klong.key a y else Klong.key c y) = Klong.key c' y := by
  by_cases h : b
  · exact ⟨a, by simp [h]⟩
  · exact ⟨c, by simp [h]⟩

theorem ptrs_halves_shape {P : NodeId → Prop} (b leaf : Bool) (t : Time) (f s insK : List Klong)
    (sc : Nat) (hf : ptrsKs P f) (hs : ptrsKs P s) (hi : ptrsKs P insK) :
    ptrsKs P (if b = true then ((⟨leaf, .time t :: f⟩ : KNode), (⟨leaf, .time t :: s ++ insK⟩ : KNode), sc)
      else (⟨leaf, .time t :: f ++ insK⟩, ⟨leaf, .time t :: s⟩, sc)).1.ks ∧
    ptrsKs P (if b = true then ((⟨leaf, .time t :: f⟩ : KNode), (⟨leaf, .time t :: s ++ insK⟩ : KNode), sc)
      else (⟨leaf, .time t :: f ++ insK⟩, ⟨leaf, .time t :: s⟩, sc)).2.1.ks := by
  cases b
  · exact ⟨ptrsKs_cons_time t (ptrsKs_append hf hi), ptrsKs_cons_time t hs⟩
  · exact ⟨ptrsKs_cons_time t hf, ptrsKs_cons_time t (ptrsKs_append hs hi)⟩

theorem ptrsKs_halves {P : NodeId → Prop} (leaf : Bool) (t : Time) {last : KNode}
    {ins : List (Nat × NodeId)} (hl : ptrsKs P last.ks) (hi : ptrsPairs P ins) :
    ptrsKs P (halves leaf t last ins).1.ks ∧ ptrsKs P (halves leaf t last ins).2.1.ks := by
  have hbody : ptrsKs P (last.ks.drop 1) :=
    ptrsKs_of_sub (fun _ hk => List.mem_of_mem_drop hk) hl
  have hf : ∀ j, ptrsKs P ((last.ks.drop 1).take j) :=
    fun j => ptrsKs_of_sub (fun _ hk => List.mem_of_mem_take hk) hbody
  have hs : ∀ j, ptrsKs P ((last.ks.drop 1).drop j) :=
    fun j => ptrsKs_of_sub (fun _ hk => List.mem_of_mem_drop hk) hbody
  have hs' : ∀ (s : List Klong), ptrsKs P s → ptrsKs P (match s with
      | .key _ y :: r => .key 0 y :: r
      | s => s) := by
    intro s h
    split
    · rename_i y r
      exact ptrsKs_cons_key 0 (h _ y List.mem_cons_self)
        (ptrsKs_of_sub (fun _ hk => List.mem_cons_of_mem _ hk) h)
    · exact h
  have hins : ∀ (g : Nat × NodeId → Klong), (∀ q, ∃ c, g q = .key c q.2) →
      ptrsKs P (ins.map g) := fun g hg => ptrsKs_of_pairs_map g hg hi
  unfold halves
  dsimp only
  apply ptrs_halves_shape
  · exact hf _
  · split
    · exact hs _
    · exact hs' _ (hs _)
  · apply hins
    intro q
    exact ptrs_ite_key _ _ _ _

theorem ptrs_replaceKlong_go {P : NodeId → Prop} (t : Time) (c : Nat) {y : NodeId} (hy : P y)
    (rest pre : List Klong) (cur : Option Time) (ks' : List Klong)
    (hp : ptrsKs P pre) (hr : ptrsKs P rest)
    (h : replaceKlong.go t c y pre rest cur = .ok (some ks')) : ptrsKs P ks' := by
  induction rest generalizing pre cur with
  | nil => simp [replaceKlong.go] at h
  | cons k r ih =>
    have hr' : ptrsKs P r := ptrsKs_of_sub (fun _ hk => List.mem_cons_of_mem _ hk) hr
    cases k with
    | time x =>
      simp only [replaceKlong.go] at h
      exact ih _ _ (ptrsKs_append hp (ptrsKs_cons_time x (ptrsKs_nil P))) hr' h
    | key c' y' =>
      simp only [replaceKlong.go] at h
      split at h
      · cases h
        exact ptrsKs_append hp (ptrsKs_cons_key c hy hr')
      · exact ih _ _ (ptrsKs_append hp (ptrsKs_cons_key c' (hr c' y' List.mem_cons_self)
          (ptrsKs_nil P))) hr' h
    | del b => simp [replaceKlong.go] at h

theorem ptrsKs_replaceKlong {P : NodeId → Prop} {ks : List Klong} {t : Time} {c : Nat}
    {y : NodeId} {ks' : List Klong} (h : replaceKlong ks t c y = .ok (some ks'))
    (hk : ptrsKs P ks) (hy : P y) : ptrsKs P ks' :=
  ptrs_replaceKlong_go t c hy ks [] none ks' (ptrsKs_nil P) hk h

theorem ptrsKs_insertSorted {P : NodeId → Prop} {ks : List Klong} (cv : Nat) {y : NodeId}
    (hk : ptrsKs P ks) (hy : P y) : ptrsKs P (insertSorted ks cv y) := by
  induction ks with
  | nil => exact ptrsKs_cons_key cv hy (ptrsKs_nil P)
  | cons k r ih =>
    have hr : ptrsKs P r := ptrsKs_of_sub (fun _ h => List.mem_cons_of_mem _ h) hk
    have hcons : ∀ s, ptrsKs P s → ptrsKs P (k :: s) := by
      intro s hs cv z hm
      rcases List.mem_cons.mp hm with hm | hm
      · rw [← hm] at hk; exact hk cv z List.mem_cons_self
      · exact hs cv z hm
    unfold insertSorted
    split
    · split
      · exact ptrsKs_cons_key cv hy hk
      · exact hcons _ (ih hr)
    · exact hcons _ (ih hr)

theorem ptrsKs_newKlongs {P : NodeId → Prop} (t : Time) {l : List (Nat × NodeId)}
    (h : ptrsPairs P l) : ptrsKs P (newKlongs t l) :=
  ptrsKs_cons_time t (ptrsKs_of_pairs_map _ (fun q => ⟨q.1, rfl⟩) h)

theorem ptrsPairs_append {P : NodeId → Prop} {a b : List (Nat × NodeId)} (ha : ptrsPairs P a)
    (hb : ptrsPairs P b) : ptrsPairs P (a ++ b) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact ha q hq
  · exact hb q hq

theorem ptrsPairs_renameHead {P : NodeId → Prop} (c : Nat) {l : List (Nat × NodeId)}
    (h : ptrsPairs P l) : ptrsPairs P (renameHead c l) := by
  cases l with
  | nil => intro q hq; cases hq
  | cons a r =>
    obtain ⟨a1, y⟩ := a
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact h (a1, y) List.mem_cons_self
    · exact h q (List.mem_cons_of_mem _ hq)

theorem ptrsPairs_mergeKlongs {P : NodeId → Prop} (inner : Bool) (cap cR : Nat)
    {a b : List (Nat × NodeId)} (ha : ptrsPairs P a) (hb : ptrsPairs P b) :
    ptrsPairs P (mergeKlongs inner cap cR a b).1 ∧
      ∀ s, (mergeKlongs inner cap cR a b).2 = some s → ptrsPairs P s.1 := by
  have he : ptrsPairs P (mergeList inner cR a b) := by
    unfold mergeList
    refine ptrsPairs_append ha ?_
    split
    · exact ptrsPairs_renameHead cR hb
    · exact hb
  unfold mergeKlongs splitMerged
  generalize mergeList inner cR a b = e at he
  split
  · exact ⟨he, fun s hs => by cases hs⟩
  · refine ⟨fun q hq => he q (List.mem_of_mem_take hq), ?_⟩
    intro s hs
    cases hs
    have hd : ptrsPairs P (e.drop ((e.length + 1) / 2)) :=
      fun q hq => he q (List.mem_of_mem_drop hq)
    dsimp only
    split
    · exact ptrsPairs_renameHead 0 hd
    · exact hd

theorem ptrsKs_renameKey {P : NodeId → Prop} {ks : List Klong} {t : Klong} {c1 : Nat}
    {y1 : NodeId} {r : List Klong} (c' : Nat) (he : ks = t :: .key c1 y1 :: r)
    (hk : ptrsKs P ks) : ptrsKs P (t :: .key c' y1 :: r) := by
  subst he
  intro cv y hm
  rcases List.mem_cons.mp hm with hm | hm
  · exact hk cv y (hm ▸ List.mem_cons_self)
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact hk c1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact hk cv y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))

/-- LE-b's next live klong (`emptyKeyNext`) names a node of a key klong of
the node. -/
theorem ptrs_emptyKeyFold {P : NodeId → Prop} (del0 : List Nat) {ks : List Klong}
    {i cv : Nat} {y : NodeId}
    (h : ks.zipIdx.foldl (fun (best : Option (Nat × Nat × NodeId)) (k, i) =>
      match k with
      | .key cv y =>
        if del0.contains i then best else
          match best with
          | none => some (i, cv, y)
          | some (_, jcv, _) => if cv ≤ jcv then some (i, cv, y) else best
      | _ => best) none = some (i, cv, y))
    (hk : ptrsKs P ks) : P y := by
  have hgen : ∀ (xs : List (Klong × Nat)) (b : Option (Nat × Nat × NodeId)),
      (∀ q ∈ xs, ∀ cv y, q.1 = .key cv y → P y) →
      (∀ i cv y, b = some (i, cv, y) → P y) →
      ∀ i cv y, xs.foldl (fun (best : Option (Nat × Nat × NodeId)) (k, i) =>
        match k with
        | .key cv y =>
          if del0.contains i then best else
            match best with
            | none => some (i, cv, y)
            | some (_, jcv, _) => if cv ≤ jcv then some (i, cv, y) else best
        | _ => best) b = some (i, cv, y) → P y := by
    intro xs
    induction xs with
    | nil => intro b _ hb i cv y he; exact hb i cv y he
    | cons q xs ih =>
      intro b hx hb i cv y he
      rw [List.foldl_cons] at he
      refine ih _ (fun e he' => hx e (List.mem_cons_of_mem _ he')) ?_ i cv y he
      obtain ⟨k, j⟩ := q
      have hq := hx (k, j) List.mem_cons_self
      intro i' cv' y' hb'
      cases k with
      | key c z =>
        dsimp only at hb'
        split at hb'
        · exact hb _ _ _ hb'
        · split at hb'
          · cases hb'; exact hq _ _ rfl
          · split at hb'
            · cases hb'; exact hq _ _ rfl
            · exact hb _ _ _ hb'
      | time t => exact hb _ _ _ hb'
      | del b' => exact hb _ _ _ hb'
  refine hgen _ none ?_ (fun _ _ _ he => by cases he) i cv y h
  intro q hq cv' y' he
  have hm : q.1 ∈ ks := List.fst_mem_of_mem_zipIdx (by obtain ⟨a, b⟩ := q; exact hq)
  rw [he] at hm
  exact hk cv' y' hm

/-- The klongs of `retarget`: those of the node, some pointed to `dst`. -/
theorem ptrsKs_retargetMap {P : NodeId → Prop} (ti : Nat) (src dst : NodeId) {ks : List Klong}
    (hk : ptrsKs P ks) (hd : P dst) :
    ptrsKs P (ks.zipIdx.map (fun (k, i) => match k with
      | .key cv y => if ti < i && y == src then Klong.key cv dst else k
      | _ => k)) := by
  intro cv y hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  obtain ⟨k, i⟩ := q
  have hkm : k ∈ ks := List.fst_mem_of_mem_zipIdx hq
  cases k with
  | key c z =>
    dsimp only at he
    split at he
    · cases he; exact hd
    · cases he; exact hk _ _ hkm
  | time t => cases he
  | del b => cases he

theorem ptrsPairs_mergeKlongs_eq1 {P : NodeId → Prop} {inner : Bool} {cap cR : Nat}
    {a b f : List (Nat × NodeId)} {s : Option (List (Nat × NodeId) × Nat)}
    (he : mergeKlongs inner cap cR a b = (f, s)) (ha : ptrsPairs P a) (hb : ptrsPairs P b) :
    ptrsPairs P f := by
  have h := (ptrsPairs_mergeKlongs inner cap cR ha hb).1
  rw [he] at h; exact h

theorem ptrsPairs_mergeKlongs_eq2 {P : NodeId → Prop} {inner : Bool} {cap cR : Nat}
    {a b f ks2 : List (Nat × NodeId)} {s : Option (List (Nat × NodeId) × Nat)} {g2 : Nat}
    (he : mergeKlongs inner cap cR a b = (f, s)) (hs : s = some (ks2, g2))
    (ha : ptrsPairs P a) (hb : ptrsPairs P b) : ptrsPairs P ks2 := by
  have h := (ptrsPairs_mergeKlongs inner cap cR ha hb).2
  rw [he] at h; exact h _ hs

theorem ptrsPairs_mergeKlongs_snd {P : NodeId → Prop} {inner : Bool} {cap cR : Nat}
    {a b ks2 : List (Nat × NodeId)} {g2 : Nat}
    (hs : (mergeKlongs inner cap cR a b).2 = some (ks2, g2))
    (ha : ptrsPairs P a) (hb : ptrsPairs P b) : ptrsPairs P ks2 :=
  (ptrsPairs_mergeKlongs inner cap cR ha hb).2 _ hs

/-! ## A state and a later one -/

/-- Node x is a node of P (`Old`) or one that the transaction made by state w. -/
def ptrsId (Old : NodeId → Prop) (w : W) (x : NodeId) : Prop := Old x ∨ x ∈ w.made.map (·.id)

/-- An optional node id, if some, meets `ptrsId`. -/
def ptrsOpt (Old : NodeId → Prop) (w : W) (r : Option NodeId) : Prop :=
  ∀ o, r = some o → ptrsId Old w o

/-- The nodes made stay made. -/
def MadeKept (w v : W) : Prop := ∀ m ∈ w.made, m ∈ v.made

theorem MadeKept.refl (w : W) : MadeKept w w := fun _ h => h

theorem MadeKept.trans {a b d : W} (h1 : MadeKept a b) (h2 : MadeKept b d) : MadeKept a d :=
  fun m h => h2 m (h1 m h)

theorem ptrsId.mono {Old : NodeId → Prop} {a b : W} {x : NodeId} (h : ptrsId Old a x)
    (hk : MadeKept a b) : ptrsId Old b x := by
  rcases h with h | h
  · exact Or.inl h
  · obtain ⟨m, hm, he⟩ := List.mem_map.mp h
    exact Or.inr (List.mem_map.mpr ⟨m, hk m hm, he⟩)

theorem ptrsKs.mono {Old : NodeId → Prop} {a b : W} {ks : List Klong}
    (h : ptrsKs (ptrsId Old a) ks) (hk : MadeKept a b) : ptrsKs (ptrsId Old b) ks :=
  ptrsKs_imp h (fun _ hy => hy.mono hk)

theorem ptrsPairs.mono {Old : NodeId → Prop} {a b : W} {l : List (Nat × NodeId)}
    (h : ptrsPairs (ptrsId Old a) l) (hk : MadeKept a b) : ptrsPairs (ptrsId Old b) l :=
  ptrsPairs_imp h (fun _ hy => hy.mono hk)

theorem ptrsOpt.mono {Old : NodeId → Prop} {a b : W} {r : Option NodeId}
    (h : ptrsOpt Old a r) (hk : MadeKept a b) : ptrsOpt Old b r :=
  fun o ho => (h o ho).mono hk

theorem ptrsOpt_get {Old : NodeId → Prop} {w : W} {r : Option NodeId} {o : NodeId}
    (he : r = some o) (h : ptrsOpt Old w r) : ptrsId Old w o := h o he

theorem ptrsOpt_pair_get {Old : NodeId → Prop} {w : W} {m : Option (NodeId × Nat)} {y : NodeId}
    {g : Nat} (he : m = some (y, g)) (h : ptrsOpt Old w (m.map (·.1))) : ptrsId Old w y :=
  h y (by rw [he]; rfl)

theorem ptrsOpt_some {Old : NodeId → Prop} {w : W} {o : NodeId} (h : ptrsId Old w o) :
    ptrsOpt Old w (some o) := by
  intro o' he; cases he; exact h

theorem ptrsOpt_none (Old : NodeId → Prop) (w : W) : ptrsOpt Old w none := by
  intro o he; cases he

theorem ptrsPairs_nil (P : NodeId → Prop) : ptrsPairs P [] := by
  intro q hq; cases hq

theorem ptrsPairs_cons {P : NodeId → Prop} (c : Nat) {y : NodeId} {r : List (Nat × NodeId)}
    (hy : P y) (h : ptrsPairs P r) : ptrsPairs P ((c, y) :: r) := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst hq; exact hy
  · exact h q hq

theorem ptrsId_made {Old : NodeId → Prop} {w : W} (m : NewNode) (hm : m ∈ w.made) :
    ptrsId Old w m.id := Or.inr (List.mem_map.mpr ⟨m, hm, rfl⟩)

/-- The writer's steps keep `PtrsOK`, and the nodes made stay made. -/
def KeepsPtrs (Old : NodeId → Prop) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewPtrsOld Old c.view → PtrsOK Old c w →
    WriterWP f c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v)

theorem ptrs_writerWP {Old : NodeId → Prop} {α : Type} {f : M α} (hf : KeepsPtrs Old f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewPtrsOld Old c.view)
    (hw : PtrsOK Old c w) (hp : ∀ r v, PtrsOK Old c v → MadeKept w v → post r v) :
    WriterWP f c w post := writerWP_mono (hf c w hv hw) (fun r v h => hp r v h.1 h.2)

theorem ptrs_throw (Old : NodeId → Prop) {α : Type} (e : String) :
    KeepsPtrs Old (throw e : M α) := by
  intro c w _ _
  exact writerWP_throw _ _ _ _

/-- `PtrsOK` of a state with other fields changed. -/
theorem PtrsOK.upd {Old : NodeId → Prop} {c : Ctx} {w : W} (hw : PtrsOK Old c w)
    (gh : List (NodeId × Nat × Nat)) (vals : List (NodeId × Nat)) (taken : List NodeId)
    (next : NodeId) (path : List (Option Nat × NodeId)) (trail : List String)
    (merges spaceSplits : Nat) (outside : List (NodeId × Nat × Nat)) :
    PtrsOK Old c ⟨w.nodes, gh, w.made, vals, taken, w.madeFor, next, path, w.top, w.newTop, trail,
      merges, spaceSplits, outside⟩ :=
  ⟨hw.klongs, hw.ids, hw.rootKey, hw.skips, hw.topId, hw.topTime, hw.madeFor⟩

/-- `PtrsOK` with more nodes made. -/
theorem PtrsOK.grow {Old : NodeId → Prop} {c : Ctx} {w : W} (hw : PtrsOK Old c w) (v : W)
    (hn : v.nodes = w.nodes) (hm : MadeKept w v) (ht : v.top = w.top)
    (hnt : v.newTop = w.newTop) (hf : v.madeFor = w.madeFor) : PtrsOK Old c v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq cv y hk; rw [hn] at hq; exact ptrsId.mono (hw.klongs q hq cv y hk) hm
  · intro q hq; rw [hn] at hq; exact ptrsId.mono (hw.ids q hq) hm
  · rw [ht]; exact ptrsId.mono (hw.rootKey) hm
  · rw [ht]; exact hw.skips
  · rw [ht, hnt]; exact hw.topId
  · rw [ht, hnt]; exact hw.topTime
  · intro q hq; rw [hf] at hq; exact ptrsId.mono (hw.madeFor q hq) hm

/-! ## The primitive steps -/

theorem ptrs_mem_upsert (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (q : NodeId × KNode) (hq : q ∈ upsert ns x n) : q = (x, n) ∨ q ∈ ns := by
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · exact Or.inl he.symm
    · exact Or.inr (he ▸ ha)
  · rcases List.mem_append.mp hq with hq | hq
    · exact Or.inr hq
    · exact Or.inl (List.mem_singleton.mp hq)

/-- A read of key node x: its pointers and its id meet `ptrsId`. -/
theorem ptrs_getNode (Old : NodeId → Prop) (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w) :
    WriterWP (getNode x) c w (fun n v => PtrsOK Old c v ∧ MadeKept w v ∧
      ptrsKs (ptrsId Old v) n.ks ∧ ptrsId Old v x) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    have hm := bk_mem_of_lookup _ _ _ hn
    exact ⟨hw, MadeKept.refl w, fun cv y hk => hw.klongs (x, n) hm cv y hk, hw.ids (x, n) hm⟩
  · simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hnd
      split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨⟨?_, ?_, hw.rootKey, hw.skips, hw.topId, hw.topTime, hw.madeFor⟩,
          MadeKept.refl w, ?_, Or.inl (hv.1 x nd hnd)⟩
        · intro q hq cv y hk
          rcases List.mem_append.mp hq with hq | hq
          · exact hw.klongs q hq cv y hk
          · rw [List.mem_singleton.mp hq] at hk
            exact Or.inl (hv.2 x nd hnd cv y hk)
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hw.ids q hq
          · rw [List.mem_singleton.mp hq]
            exact Or.inl (hv.1 x nd hnd)
        · intro cv y hk
          exact Or.inl (hv.2 x nd hnd cv y hk)
    · exact writerWP_throw _ _ _ _

/-- A store of key node x, with pointers that meet `ptrsId`. -/
theorem ptrs_putNode (Old : NodeId → Prop) (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hw : PtrsOK Old c w) (hn : ptrsKs (ptrsId Old w) n.ks) (hx : ptrsId Old w x) :
    WriterWP (putNode x n) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  simp only [putNode, writerWP_modify]
  refine ⟨⟨?_, ?_, hw.rootKey, hw.skips, hw.topId, hw.topTime, hw.madeFor⟩, MadeKept.refl w⟩
  · intro q hq cv y hk
    rcases ptrs_mem_upsert _ _ _ q hq with rfl | hq
    · exact hn cv y hk
    · exact hw.klongs q hq cv y hk
  · intro q hq
    rcases ptrs_mem_upsert _ _ _ q hq with rfl | hq
    · exact hx
    · exact hw.ids q hq

theorem ptrs_newKey_state (Old : NodeId → Prop) (c : Ctx) (w v : W) (leaf : Bool)
    (ks : List Klong) (l : Nat) (hw : PtrsOK Old c w) (hks : ptrsKs (ptrsId Old w) ks)
    (hn : v.nodes = w.nodes ++ [(w.next, ⟨leaf, ks⟩)])
    (hm : v.made = w.made ++ [⟨w.next, l, false⟩]) (ht : v.top = w.top)
    (hnt : v.newTop = w.newTop) (hf : v.madeFor = w.madeFor) :
    PtrsOK Old c v ∧ MadeKept w v ∧ ptrsId Old v w.next := by
  have hk : MadeKept w v := fun m h => by rw [hm]; exact List.mem_append_left _ h
  have hx : ptrsId Old v w.next := Or.inr (List.mem_map.mpr ⟨_, by
    rw [hm]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hk, hx⟩
  · intro q hq cv y hy
    rw [hn] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ptrsId.mono (hw.klongs q hq cv y hy) hk
    · rw [List.mem_singleton.mp hq] at hy
      exact ptrsId.mono (hks cv y hy) hk
  · intro q hq
    rw [hn] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ptrsId.mono (hw.ids q hq) hk
    · rw [List.mem_singleton.mp hq]; exact hx
  · rw [ht]; exact ptrsId.mono hw.rootKey hk
  · rw [ht]; exact hw.skips
  · rw [ht, hnt]; exact hw.topId
  · rw [ht, hnt]; exact hw.topTime
  · intro q hq; rw [hf] at hq; exact ptrsId.mono (hw.madeFor q hq) hk

/-- A new key node with pointers that meet `ptrsId`: its id is made. -/
theorem ptrs_newKey (Old : NodeId → Prop) (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx)
    (w : W) (hw : PtrsOK Old c w) (hks : ptrsKs (ptrsId Old w) ks) :
    WriterWP (newKey g h leaf ks) c w (fun x v => PtrsOK Old c v ∧ MadeKept w v ∧
      ptrsId Old v x) := by
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  split
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact ptrs_newKey_state Old c w _ leaf ks _ hw hks rfl rfl rfl rfl rfl
  · simp only [writerWP_bind, writerWP_pure, writerWP_modify]
    exact ptrs_newKey_state Old c w _ leaf ks _ hw hks rfl rfl rfl rfl rfl

theorem ptrs_newValue (Old : NodeId → Prop) (h : Nat) (c : Ctx) (w : W)
    (_hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w) :
    WriterWP (newValue h) c w (fun x v => PtrsOK Old c v ∧ MadeKept w v ∧ ptrsId Old v x) := by
  simp only [newValue, fresh, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure,
    writerWP_modify]
  exact ⟨hw.grow _ rfl (fun m hm => List.mem_append_left _ hm) rfl rfl rfl,
    fun m hm => List.mem_append_left _ hm,
    Or.inr (List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩)⟩

theorem ptrs_setMadeFor (Old : NodeId → Prop) (x : NodeId) (old : Option NodeId) (c : Ctx)
    (w : W) (hw : PtrsOK Old c w) (ho : ptrsOpt Old w old) :
    WriterWP (setMadeFor x old) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  unfold setMadeFor
  split
  · rename_i o
    simp only [writerWP_modify]
    refine ⟨⟨hw.klongs, hw.ids, hw.rootKey, hw.skips, hw.topId, hw.topTime, ?_⟩,
      MadeKept.refl w⟩
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact ho o rfl
    · exact hw.madeFor q hq
  · simp only [writerWP_pure]; exact ⟨hw, MadeKept.refl w⟩

theorem ptrs_lookup_madeFor (l : List (NodeId × NodeId)) (x o : NodeId)
    (h : l.lookup x = some o) : (x, o) ∈ l := bk_mem_of_lookup l x o h

theorem ptrs_replacedBy (Old : NodeId → Prop) (x : NodeId) (c : Ctx) (w : W)
    (_hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w) :
    WriterWP (replacedBy x) c w (fun r v => PtrsOK Old c v ∧ MadeKept w v ∧ ptrsOpt Old v r) := by
  simp only [replacedBy, writerWP_bind, writerWP_get, writerWP_pure]
  refine ⟨hw, MadeKept.refl w, ?_⟩
  intro o ho
  exact hw.madeFor _ (ptrs_lookup_madeFor _ _ _ ho)

theorem ptrs_newSuperRoot (Old : NodeId → Prop) (y : NodeId) (c : Ctx) (w : W)
    (hw : PtrsOK Old c w) (hy : ptrsId Old w y) :
    WriterWP (newSuperRoot y) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  unfold newSuperRoot
  simp only [note, fresh, writerWP_bind, writerWP_get, writerWP_read]
  split
  · rename_i ht
    simp only [writerWP_bind, writerWP_set, writerWP_modify]
    exact ⟨⟨hw.klongs, hw.ids, hy, hw.skips, hw.topId, hw.topTime, hw.madeFor⟩, MadeKept.refl w⟩
  · rename_i ht
    simp only [writerWP_bind, writerWP_modify, writerWP_get, writerWP_set, writerWP_pure]
    have hnt : w.newTop = false := by
      cases hn : w.newTop
      · rfl
      · exfalso; apply ht; rw [hw.topTime hn]; simp
    have hid : Old w.top.id := hw.topId hnt
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun m hm => List.mem_append_left _ hm⟩
    · intro q hq cv y' hk
      exact ptrsId.mono (hw.klongs q hq cv y' hk) (fun m hm => List.mem_append_left _ hm)
    · intro q hq
      exact ptrsId.mono (hw.ids q hq) (fun m hm => List.mem_append_left _ hm)
    · exact ptrsId.mono (hy) (fun m hm => List.mem_append_left _ hm)
    · intro q hq
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hq
      generalize (if (w.top.ord == 0) = true then 1 else w.top.ord + 1) = o at hj
      by_cases hb : o.testBit j = true
      · simp only [hb, ↓reduceIte] at hj
        cases ht' : w.top.skips.lookup j with
        | some t =>
          simp only [ht', Option.some.injEq] at hj; subst hj
          exact hw.skips _ (bk_mem_of_lookup _ _ _ ht')
        | none =>
          simp only [ht', Option.some.injEq] at hj; subst hj
          exact hid
      · simp only [hb] at hj; cases hj
    · intro h; cases h
    · intro _; rfl
    · intro q hq
      exact ptrsId.mono (hw.madeFor q hq) (fun m hm => List.mem_append_left _ hm)

macro "ptNeutral" : tactic => `(tactic| (
  intro c w hv hw
  simp only [writerWP_bind, writerWP_get, writerWP_pure, writerWP_modify, writerWP_set,
    writerWP_read]
  repeat' first
    | split
    | exact writerWP_throw _ _ _ _
    | exact ⟨hw, MadeKept.refl _⟩
    | exact ⟨PtrsOK.upd hw _ _ _ _ _ _ _ _ _, MadeKept.refl _⟩
    | simp only [writerWP_bind, writerWP_get, writerWP_pure]))

theorem ptrs_note (Old : NodeId → Prop) (s : String) : KeepsPtrs Old (note s) := by
  unfold note; ptNeutral
theorem ptrs_pathClear (Old : NodeId → Prop) : KeepsPtrs Old pathClear := by
  unfold pathClear; ptNeutral
theorem ptrs_pathAdd (Old : NodeId → Prop) (cv : Option Nat) (x : NodeId) :
    KeepsPtrs Old (pathAdd cv x) := by
  unfold pathAdd; ptNeutral
theorem ptrs_takenBack (Old : NodeId → Prop) (x : NodeId) : KeepsPtrs Old (takenBack x) := by
  unfold takenBack; ptNeutral
theorem ptrs_fresh (Old : NodeId → Prop) : KeepsPtrs Old fresh := by
  unfold fresh; ptNeutral
theorem ptrs_pathSize (Old : NodeId → Prop) : KeepsPtrs Old pathSize := by
  unfold pathSize; ptNeutral
theorem ptrs_pathNode (Old : NodeId → Prop) (d : Nat) : KeepsPtrs Old (pathNode d) := by
  unfold pathNode; ptNeutral
theorem ptrs_klongAt (Old : NodeId → Prop) (d : Nat) : KeepsPtrs Old (klongAt d) := by
  unfold klongAt; ptNeutral

theorem ptrs_parentAt (Old : NodeId → Prop) (d : Nat) : KeepsPtrs Old (parentAt d) := by
  cases d with
  | zero => intro c w _ hw; simpa only [parentAt, writerWP_pure] using ⟨hw, MadeKept.refl w⟩
  | succ d =>
    intro c w hv hw
    unfold parentAt
    simp only [writerWP_bind]
    refine writerWP_mono (ptrs_pathNode Old d c w hv hw) ?_
    intro _ _ h
    simpa only [writerWP_pure] using h

theorem ptrs_findRoot (Old : NodeId → Prop) : KeepsPtrs Old findRoot := by
  intro c w hv hw
  unfold findRoot
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  exact ptrs_pathAdd Old none _ c w hv hw

theorem ptrs_ghOf (Old : NodeId → Prop) (x : NodeId) : KeepsPtrs Old (ghOf x) := by
  intro c w hv hw
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (ptrs_getNode Old x c w hv hw) ?_
  rintro _ v ⟨hwv, hk, _⟩
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact ⟨hwv, hk⟩
  · exact writerWP_throw _ _ _ _

/-! ## The tactics of the walk -/

theorem ptrsKs_halves_eq1 {P : NodeId → Prop} {leaf : Bool} {t : Time} {last : KNode}
    {ins : List (Nat × NodeId)} {f s : KNode} {sc : Nat} (he : halves leaf t last ins = (f, s, sc))
    (hl : ptrsKs P last.ks) (hi : ptrsPairs P ins) : ptrsKs P f.ks := by
  have h := (ptrsKs_halves leaf t hl hi).1
  rw [he] at h; exact h

theorem ptrsKs_halves_eq2 {P : NodeId → Prop} {leaf : Bool} {t : Time} {last : KNode}
    {ins : List (Nat × NodeId)} {f s : KNode} {sc : Nat} (he : halves leaf t last ins = (f, s, sc))
    (hl : ptrsKs P last.ks) (hi : ptrsPairs P ins) : ptrsKs P s.ks := by
  have h := (ptrsKs_halves leaf t hl hi).2
  rw [he] at h; exact h

/-- The klongs of `addKeys`. -/
theorem ptrsKs_addFold {P : NodeId → Prop} (t : Time) {n : KNode} {ins : List (Nat × NodeId)}
    (hn : ptrsKs P n.ks) (hi : ptrsPairs P ins) :
    ptrsKs P (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n).ks :=
  ptrsKs_foldl _ (fun _ q hn hq => ptrsKs_add_key t q.1 hn hq) hn hi

theorem ptrs_replaceOrAdd (Old : NodeId → Prop) (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hl : ptrsKs (ptrsId Old w) last.ks) (hi : ptrsPairs (ptrsId Old w) ins) :
    WriterWP (replaceOrAdd last ins) c w (fun l v => v = w ∧ ptrsKs (ptrsId Old w) l.ks) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨by trivial, hl⟩
  | cons q ins ih =>
    have hq := hi q List.mem_cons_self
    have hr : ptrsPairs (ptrsId Old w) ins := fun e he => hi e (List.mem_cons_of_mem _ he)
    rw [List.foldlM_cons, writerWP_bind]
    cases hrk : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        exact ih _ (ptrsKs_add_key _ _ hl hq) hr
      | some ks =>
        simp only [writerWP_pure]
        exact ih { last with ks := ks } (ptrsKs_replaceKlong hrk hl hq) hr

macro "ptState" : tactic => `(tactic| first
  | assumption
  | exact PtrsOK.upd (by assumption) _ _ _ _ _ _ _ _ _)

/-- `MadeKept a b` along the chain of the steps' hypotheses. -/
syntax "ptChain" : tactic
macro_rules
  | `(tactic| ptChain) => `(tactic| first
    | exact MadeKept.refl _
    | assumption
    | exact fun _ h => h
    | (refine MadeKept.trans ?ptL (by assumption); ptChain))

/-- A premise of a step: a pointer, the klongs of a node, pairs, an optional id. -/
syntax "ptPre" : tactic
macro_rules
  | `(tactic| ptPre) => `(tactic| first
    | assumption
    | exact ptrsId.mono (by assumption) (by ptChain)
    | exact ptrsKs.mono (by assumption) (by ptChain)
    | exact ptrsPairs.mono (by assumption) (by ptChain)
    | exact ptrsOpt.mono (by assumption) (by ptChain)
    | exact ptrsKs_nil _
    | exact ptrsPairs_nil _
    | exact ptrsOpt_none _ _
    | (refine ptrsOpt_some ?_; ptPre)
    | (refine ptrsOpt_get (by assumption) ?_; ptPre)
    | exact ptrsId.mono (ptrsOpt_get rfl (by assumption)) (by ptChain)
    | (refine ptrsId_of_ptr (by assumption) ?_; ptPre)
    | (refine ptrsPairs_cons _ ?_ ?_ <;> ptPre)
    | (refine ptrsKs_cons_time _ ?_; ptPre)
    | (refine ptrsKs_cons_key _ ?_ ?_ <;> ptPre)
    | (refine ptrsKs_cons_del _ ?_; ptPre)
    | (refine ptrsKs_add_key _ _ ?_ ?_ <;> ptPre)
    | (refine ptrsKs_add_del _ _ ?_; ptPre)
    | (refine ptrsKs_setAt_del _ _ ?_; ptPre)
    | (refine ptrsKs_toPrev _ ?_; ptPre)
    | (refine ptrsKs_repoint _ ?_ ?_ <;> ptPre)
    | (refine ptrsKs_lastVersionGivenDel _ _ ?_; ptPre)
    | (refine ptrsKs_lastVersion _ ?_; ptPre)
    | (refine (ptrsKs_halves _ _ ?_ ?_).1 <;> ptPre)
    | (refine (ptrsKs_halves _ _ ?_ ?_).2 <;> ptPre)
    | (refine ptrsKs_halves_eq1 (by assumption) ?_ ?_ <;> ptPre)
    | (refine ptrsKs_halves_eq2 (by assumption) ?_ ?_ <;> ptPre)
    | (refine ptrsKs_replaceKlong (by assumption) ?_ ?_ <;> ptPre)
    | (refine ptrsKs_insertSorted _ ?_ ?_ <;> ptPre)
    | (refine ptrsKs_newKlongs _ ?_; ptPre)
    | (refine ptrsPairs_live ?_; ptPre)
    | (refine ptrsKs_addFold _ ?_ ?_ <;> ptPre)
    | (refine ptrsKs_renameKey _ (by assumption) ?_; ptPre)
    | (refine (ptrsPairs_mergeKlongs _ _ _ ?_ ?_).1 <;> ptPre)
    | (refine ptrsPairs_mergeKlongs_eq1 (by assumption) ?_ ?_ <;> ptPre)
    | (refine ptrsPairs_mergeKlongs_eq2 (by assumption) (by assumption) ?_ ?_ <;> ptPre)
    | (refine ptrsPairs_mergeKlongs_eq2 (by assumption) rfl ?_ ?_ <;> ptPre)
    | (refine ptrsPairs_mergeKlongs_snd (by assumption) ?_ ?_ <;> ptPre)
    | (refine ptrsKs_retargetMap _ _ _ ?_ ?_ <;> ptPre)
    | (refine ptrsOpt_pair_get (by assumption) ?_; ptPre)
    | (refine ptrs_emptyKeyFold _ (by assumption) ?_; ptPre))

macro "ptDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = PtrsOK _ _ _ ∧ MadeKept _ _)
  refine ⟨?ptS, ?ptK⟩
  case ptS => ptState
  case ptK => ptChain))

macro "ptUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' ptrs_writerWP $h _ _ _ ?ptView ?ptState ?ptPost)
  case ptView => assumption
  case ptState => ptState
  intro _ _ _ _))

macro "ptNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (ptrs_getNode ?ptOld _ _ _ ?ptView ?ptState) ?ptPost)
  case ptView => assumption
  case ptState => ptState
  rintro _ _ ⟨_, _, _, _⟩))

macro "ptStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (ptrs_putNode ?ptOld _ _ _ _ ?ptState ?ptKs ?ptId) ?ptPost)
  case ptState => ptState
  case ptKs => ptPre
  case ptId => ptPre
  rintro _ _ ⟨_, _⟩))

macro "ptCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (refine writerWP_mono (ptrs_newKey ?ptOld _ _ _ _ _ _ ?ptState ?ptKs) ?ptPost)
  case ptState => ptState
  case ptKs => ptPre
  rintro _ _ ⟨_, _, _⟩))

macro "ptValue" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newValue _) _ _ _)
  (refine writerWP_mono (ptrs_newValue ?ptOld _ _ _ ?ptView ?ptState) ?ptPost)
  case ptView => assumption
  case ptState => ptState
  rintro _ _ ⟨_, _, _⟩))

macro "ptMadeFor" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (setMadeFor _ _) _ _ _)
  (refine writerWP_mono (ptrs_setMadeFor ?ptOld _ _ _ _ ?ptState ?ptO) ?ptPost)
  case ptState => ptState
  case ptO => ptPre
  rintro _ _ ⟨_, _⟩))

macro "ptReplaced" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
  (refine writerWP_mono (ptrs_replacedBy ?ptOld _ _ _ ?ptView ?ptState) ?ptPost)
  case ptView => assumption
  case ptState => ptState
  rintro _ _ ⟨_, _, _⟩))

macro "ptSuper" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newSuperRoot _) _ _ _)
  (refine writerWP_mono (ptrs_newSuperRoot ?ptOld _ _ _ ?ptState ?ptY) ?ptPost)
  case ptState => ptState
  case ptY => ptPre
  rintro _ _ ⟨_, _⟩))

macro "ptReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  (refine writerWP_mono (ptrs_replaceOrAdd ?ptOld _ _ _ _ ?ptL ?ptI) ?ptPost)
  case ptL => ptPre
  case ptI => ptPre
  rintro _ _ ⟨hptEq, _⟩
  subst hptEq))

macro "ptCore" : tactic => `(tactic| first
  | ptDone
  | ptNode
  | ptStore
  | ptCreate
  | ptValue
  | ptMadeFor
  | ptReplaced
  | ptSuper
  | ptUse (ptrs_ghOf _ _)
  | ptUse (ptrs_pathAdd _ _ _)
  | ptUse (ptrs_pathSize _)
  | ptUse (ptrs_pathNode _ _)
  | ptUse (ptrs_klongAt _ _)
  | ptUse (ptrs_parentAt _ _)
  | ptUse (ptrs_findRoot _)
  | ptUse (ptrs_note _ _)
  | ptUse (ptrs_fresh _)
  | ptUse (ptrs_takenBack _ _)
  | ptUse (ptrs_pathClear _)
  | exact writerWP_throw _ _ _ _)

/-! ## The splits -/

theorem ptrs_addKeys (Old : NodeId → Prop) (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx)
    (w : W) (hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w)
    (hi : ptrsPairs (ptrsId Old w) ins) :
    WriterWP (addKeys x ins) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  unfold addKeys
  repeat' first | wpSimplify | ptCore

/-- What a callback `up` of a split must do: keep `PtrsOK` for klongs that
meet `ptrsId`. -/
def ptrsUp (Old : NodeId → Prop) (up : NodeId → List (Nat × NodeId) → M Unit) : Prop :=
  ∀ q more c w, ViewPtrsOld Old c.view → PtrsOK Old c w → ptrsPairs (ptrsId Old w) more →
    WriterWP (up q more) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v)

macro "ptUp " h:term : tactic => `(tactic| (
  (refine' writerWP_mono ($h _ _ _ _ ?ptView ?ptState ?ptPre) ?ptPost)
  case ptView => assumption
  case ptState => ptState
  case ptPre => ptPre
  rintro _ _ ⟨_, _⟩))

set_option maxHeartbeats 1600000 in
/-- Every route of a full node's replacement keeps `PtrsOK`. -/
theorem ptrs_handleFullWith (Old : NodeId → Prop) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ptrsUp Old up) (c : Ctx) (w : W) (hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w)
    (hl : ptrsKs (ptrsId Old w) last.ks) (hi : ptrsPairs (ptrsId Old w) ins) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | ptCore
    | ptReplace
    | ptUp hup
    | wpSplit
    | split
    | contradiction

end SIS.Tree
