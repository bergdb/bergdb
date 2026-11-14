/-
The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name (`KindCache`, SIS/Tree/OverlayKinds.lean),
walked together with the books (`Book`). This file: the key klongs of the
node functions, as a statement about a compare value and a pointer (a leaf's
klongs keep their compare values; an inner node's may get the empty key,
which does not matter for its kind), the state of the walk, and the writer's
primitive steps.
-/
import SIS.Tree.OverlayKinds
import SIS.Tree.WriterBookMerge
import SIS.Tree.MergeFrameDead
import SIS.Tree.WriterSteps
import SIS.Tree.GetSplit
import SIS.Tree.WalkComplete
import SIS.Tree.CacheGood
import SIS.Tree.WriterNonemptyRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Key klongs with compare values -/

/-- Every key klong (c, y) of ks meets P c y. -/
def kdKs (P : Nat → NodeId → Prop) (ks : List Klong) : Prop :=
  ∀ c y, Klong.key c y ∈ ks → P c y

/-- Every pair (c, y) of l meets P c y. -/
def kdPairs (P : Nat → NodeId → Prop) (l : List (Nat × NodeId)) : Prop := ∀ q ∈ l, P q.1 q.2

/-- P does not look at the compare value. -/
def kdFree (P : Nat → NodeId → Prop) : Prop := ∀ c c' y, P c y → P c' y

theorem kdKs_nil (P : Nat → NodeId → Prop) : kdKs P [] := by
  intro c y h; cases h

theorem kdKs_of_sub {P : Nat → NodeId → Prop} {a b : List Klong} (hs : ∀ k ∈ a, k ∈ b)
    (h : kdKs P b) : kdKs P a := fun c y hm => h c y (hs _ hm)

theorem kdKs_append {P : Nat → NodeId → Prop} {a b : List Klong} (ha : kdKs P a)
    (hb : kdKs P b) : kdKs P (a ++ b) := by
  intro c y hm
  rcases List.mem_append.mp hm with hm | hm
  · exact ha c y hm
  · exact hb c y hm

theorem kdKs_cons_time {P : Nat → NodeId → Prop} (t : Time) {r : List Klong} (h : kdKs P r) :
    kdKs P (.time t :: r) := by
  intro c y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · exact h c y hm

theorem kdKs_cons_del {P : Nat → NodeId → Prop} (b : List Nat) {r : List Klong} (h : kdKs P r) :
    kdKs P (.del b :: r) := by
  intro c y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · exact h c y hm

theorem kdKs_cons_key {P : Nat → NodeId → Prop} {c : Nat} {y : NodeId} {r : List Klong}
    (hy : P c y) (h : kdKs P r) : kdKs P (.key c y :: r) := by
  intro c' z hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm; exact hy
  · exact h c' z hm

theorem kdKs_add_key {P : Nat → NodeId → Prop} {n : KNode} (t : Time) {c : Nat} {y : NodeId}
    (hn : kdKs P n.ks) (hy : P c y) : kdKs P (n.add t (.key c y)).ks := by
  have hk : kdKs P [.time t, .key c y] :=
    kdKs_cons_time t (kdKs_cons_key hy (kdKs_nil P))
  have hk1 : kdKs P [.key c y] := kdKs_cons_key hy (kdKs_nil P)
  unfold KNode.add
  split
  · split
    · exact kdKs_append hn hk
    · exact kdKs_append hn hk1
  · exact kdKs_append hn hk

theorem kdKs_add_del {P : Nat → NodeId → Prop} {n : KNode} (t : Time) (b : List Nat)
    (hn : kdKs P n.ks) : kdKs P (n.add t (.del b)).ks := by
  have hk : kdKs P [.time t, .del b] :=
    kdKs_cons_time t (kdKs_cons_del b (kdKs_nil P))
  have hk1 : kdKs P [.del b] := kdKs_cons_del b (kdKs_nil P)
  unfold KNode.add
  split
  · split
    · exact kdKs_append hn hk
    · exact kdKs_append hn hk1
  · exact kdKs_append hn hk

theorem kdKs_addFold {P : Nat → NodeId → Prop} (t : Time) {n : KNode}
    {ins : List (Nat × NodeId)} (hn : kdKs P n.ks) (hi : kdPairs P ins) :
    kdKs P (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n).ks := by
  induction ins generalizing n with
  | nil => exact hn
  | cons q ins ih =>
    rw [List.foldl_cons]
    exact ih (kdKs_add_key t hn (hi q List.mem_cons_self))
      (fun e he => hi e (List.mem_cons_of_mem _ he))

theorem kdKs_setAt_del {P : Nat → NodeId → Prop} {n : KNode} (i : Nat) (b : List Nat)
    (hn : kdKs P n.ks) : kdKs P (n.setAt i (.del b)).ks := by
  intro c y hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact hn c y hm
  · cases hm

theorem kdKs_toPrev {P : Nat → NodeId → Prop} {n : KNode} (t : Time) (hn : kdKs P n.ks) :
    kdKs P (n.toPrev t).ks :=
  kdKs_of_sub (fun _ hk => (List.takeWhile_sublist _).subset hk) hn

/-- Klong i pointed to y keeps its compare value. -/
theorem kdKs_repoint {P : Nat → NodeId → Prop} {n : KNode} (i : Nat) {y : NodeId}
    (hn : kdKs P n.ks) (hy : ∀ c z, n.ks[i]? = some (.key c z) → P c y) :
    kdKs P (n.repoint i y).ks := by
  unfold KNode.repoint
  split
  · rename_i c z hz
    intro c' y' hm
    rcases List.mem_or_eq_of_mem_set hm with hm | hm
    · exact hn c' y' hm
    · cases hm; exact hy c z hz
  · exact hn

theorem kd_ptr_mem {n : KNode} {i : Nat} {y : NodeId} (h : n.ptr? i = some y) :
    ∃ c, n.ks[i]? = some (.key c y) := by
  unfold KNode.ptr? at h
  split at h
  · rename_i c z hz
    cases h
    exact ⟨c, hz⟩
  · cases h

theorem kd_mem_of_get {ks : List Klong} {i : Nat} {k : Klong} (h : ks[i]? = some k) : k ∈ ks :=
  List.mem_of_getElem? h

theorem kd_setCv {P : Nat → NodeId → Prop} (m : List (Nat × NodeId)) (c : Nat) (y : NodeId)
    (hm : kdPairs P m) (hy : P c y) : kdPairs P (setCv m c y) := by
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

theorem kd_lastVersionFold {P : Nat → NodeId → Prop} (del : List Nat) (xs : List (Klong × Nat))
    (hx : ∀ q ∈ xs, ∀ cv y, q.1 = .key cv y → P cv y) (m : List (Nat × NodeId))
    (hm : kdPairs P m) :
    kdPairs P (xs.foldl (fun m (q : Klong × Nat) => match q.1 with
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
      · exact kd_setCv m c y hm (hx _ List.mem_cons_self c y rfl)
    | time t => exact hm
    | del b => exact hm

theorem kdKs_lastVersionGivenDel {P : Nat → NodeId → Prop} {n : KNode} (t : Time)
    (del : List Nat) (hn : kdKs P n.ks) : kdKs P (n.lastVersionGivenDel t del).ks := by
  unfold KNode.lastVersionGivenDel
  dsimp only
  apply kdKs_cons_time
  intro cv y hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  cases he
  have hq' := (List.mem_mergeSort).mp hq
  have hf := kd_lastVersionFold (P := P) del n.ks.zipIdx ?_ [] (fun q h => by cases h)
  · exact hf _ hq'
  · intro e he cv' y' hk
    have hm' : e.1 ∈ n.ks := List.fst_mem_of_mem_zipIdx (by obtain ⟨a, b⟩ := e; exact he)
    rw [hk] at hm'
    exact hn cv' y' hm'

theorem kdKs_lastVersion {P : Nat → NodeId → Prop} {n : KNode} (t : Time)
    (hn : kdKs P n.ks) : kdKs P (n.lastVersion t).ks :=
  kdKs_lastVersionGivenDel t _ hn

theorem kdPairs_live {P : Nat → NodeId → Prop} {n : KNode} (hn : kdKs P n.ks) :
    kdPairs P n.live := by
  intro q hq
  unfold KNode.live at hq
  obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp hq
  cases k with
  | key c y =>
    cases he
    exact kdKs_lastVersion 0 hn c y hk
  | time t => cases he
  | del b => cases he

theorem kdKs_of_pairs_map {P : Nat → NodeId → Prop} {l : List (Nat × NodeId)}
    (f : Nat × NodeId → Klong) (hf : ∀ q, f q = .key q.1 q.2 ∨ (kdFree P ∧ ∃ c, f q = .key c q.2))
    (h : kdPairs P l) : kdKs P (l.map f) := by
  intro cv y hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  rcases hf q with hc | ⟨hP, c, hc⟩
  · rw [hc] at he; cases he; exact h q hq
  · rw [hc] at he; cases he; exact hP _ _ _ (h q hq)

theorem kd_ite_key (b : Prop) [Decidable b] (a c : Nat) (y : NodeId) :
    ∃ c', (if b then Klong.key a y else Klong.key c y) = Klong.key c' y := by
  by_cases h : b
  · exact ⟨a, by simp [h]⟩
  · exact ⟨c, by simp [h]⟩

theorem kd_halves_shape {P : Nat → NodeId → Prop} (b leaf : Bool) (t : Time)
    (f s insK : List Klong) (sc : Nat) (hf : kdKs P f) (hs : kdKs P s) (hi : kdKs P insK) :
    kdKs P (if b = true then ((⟨leaf, .time t :: f⟩ : KNode), (⟨leaf, .time t :: s ++ insK⟩ : KNode), sc)
      else (⟨leaf, .time t :: f ++ insK⟩, ⟨leaf, .time t :: s⟩, sc)).1.ks ∧
    kdKs P (if b = true then ((⟨leaf, .time t :: f⟩ : KNode), (⟨leaf, .time t :: s ++ insK⟩ : KNode), sc)
      else (⟨leaf, .time t :: f ++ insK⟩, ⟨leaf, .time t :: s⟩, sc)).2.1.ks := by
  cases b
  · exact ⟨kdKs_cons_time t (kdKs_append hf hi), kdKs_cons_time t hs⟩
  · exact ⟨kdKs_cons_time t hf, kdKs_cons_time t (kdKs_append hs hi)⟩

theorem kdKs_halves {P : Nat → NodeId → Prop} (leaf : Bool) (t : Time) {last : KNode}
    {ins : List (Nat × NodeId)} (hP : leaf = false → kdFree P) (hl : kdKs P last.ks)
    (hi : kdPairs P ins) :
    kdKs P (halves leaf t last ins).1.ks ∧ kdKs P (halves leaf t last ins).2.1.ks := by
  have hbody : kdKs P (last.ks.drop 1) :=
    kdKs_of_sub (fun _ hk => List.mem_of_mem_drop hk) hl
  have hf : ∀ j, kdKs P ((last.ks.drop 1).take j) :=
    fun j => kdKs_of_sub (fun _ hk => List.mem_of_mem_take hk) hbody
  have hs : ∀ j, kdKs P ((last.ks.drop 1).drop j) :=
    fun j => kdKs_of_sub (fun _ hk => List.mem_of_mem_drop hk) hbody
  have hs' : ∀ (s : List Klong), kdKs P s → kdFree P → kdKs P (match s with
      | .key _ y :: r => .key 0 y :: r
      | s => s) := by
    intro s h hF
    split
    · rename_i c y r
      exact kdKs_cons_key (hF _ _ _ (h c y List.mem_cons_self))
        (kdKs_of_sub (fun _ hk => List.mem_cons_of_mem _ hk) h)
    · exact h
  unfold halves
  dsimp only
  apply kd_halves_shape
  · exact hf _
  · cases leaf with
    | true => exact hs _
    | false => exact hs' _ (hs _) (hP rfl)
  · apply kdKs_of_pairs_map _ _ hi
    intro q
    cases leaf with
    | true => left; simp
    | false =>
      right
      exact ⟨hP rfl, kd_ite_key _ _ _ _⟩

theorem kd_replaceKlong_go {P : Nat → NodeId → Prop} (t : Time) (c : Nat) {y : NodeId}
    (hy : P c y) (rest pre : List Klong) (cur : Option Time) (ks' : List Klong)
    (hp : kdKs P pre) (hr : kdKs P rest)
    (h : replaceKlong.go t c y pre rest cur = .ok (some ks')) : kdKs P ks' := by
  induction rest generalizing pre cur with
  | nil => simp [replaceKlong.go] at h
  | cons k r ih =>
    have hr' : kdKs P r := kdKs_of_sub (fun _ hk => List.mem_cons_of_mem _ hk) hr
    cases k with
    | time x =>
      simp only [replaceKlong.go] at h
      exact ih _ _ (kdKs_append hp (kdKs_cons_time x (kdKs_nil P))) hr' h
    | key c' y' =>
      simp only [replaceKlong.go] at h
      split at h
      · cases h
        exact kdKs_append hp (kdKs_cons_key hy hr')
      · exact ih _ _ (kdKs_append hp (kdKs_cons_key (hr c' y' List.mem_cons_self)
          (kdKs_nil P))) hr' h
    | del b => simp [replaceKlong.go] at h

theorem kdKs_replaceKlong {P : Nat → NodeId → Prop} {ks : List Klong} {t : Time} {c : Nat}
    {y : NodeId} {ks' : List Klong} (h : replaceKlong ks t c y = .ok (some ks'))
    (hk : kdKs P ks) (hy : P c y) : kdKs P ks' :=
  kd_replaceKlong_go t c hy ks [] none ks' (kdKs_nil P) hk h

theorem kdKs_insertSorted {P : Nat → NodeId → Prop} {ks : List Klong} (cv : Nat) {y : NodeId}
    (hk : kdKs P ks) (hy : P cv y) : kdKs P (insertSorted ks cv y) := by
  induction ks with
  | nil => exact kdKs_cons_key hy (kdKs_nil P)
  | cons k r ih =>
    have hr : kdKs P r := kdKs_of_sub (fun _ h => List.mem_cons_of_mem _ h) hk
    have hcons : ∀ s, kdKs P s → kdKs P (k :: s) := by
      intro s hs cv z hm
      rcases List.mem_cons.mp hm with hm | hm
      · rw [← hm] at hk; exact hk cv z List.mem_cons_self
      · exact hs cv z hm
    unfold insertSorted
    split
    · split
      · exact kdKs_cons_key hy hk
      · exact hcons _ (ih hr)
    · exact hcons _ (ih hr)

theorem kdKs_newKlongs {P : Nat → NodeId → Prop} (t : Time) {l : List (Nat × NodeId)}
    (h : kdPairs P l) : kdKs P (newKlongs t l) :=
  kdKs_cons_time t (kdKs_of_pairs_map _ (fun _ => Or.inl rfl) h)

theorem kdPairs_append {P : Nat → NodeId → Prop} {a b : List (Nat × NodeId)} (ha : kdPairs P a)
    (hb : kdPairs P b) : kdPairs P (a ++ b) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact ha q hq
  · exact hb q hq

theorem kdPairs_renameHead {P : Nat → NodeId → Prop} (c : Nat) {l : List (Nat × NodeId)}
    (hP : kdFree P) (h : kdPairs P l) : kdPairs P (renameHead c l) := by
  cases l with
  | nil => intro q hq; cases hq
  | cons a r =>
    obtain ⟨a1, y⟩ := a
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact hP _ _ _ (h (a1, y) List.mem_cons_self)
    · exact h q (List.mem_cons_of_mem _ hq)

theorem kdPairs_mergeKlongs {P : Nat → NodeId → Prop} (inner : Bool) (cap cR : Nat)
    {a b : List (Nat × NodeId)} (hP : inner = true → kdFree P) (ha : kdPairs P a)
    (hb : kdPairs P b) :
    kdPairs P (mergeKlongs inner cap cR a b).1 ∧
      ∀ s, (mergeKlongs inner cap cR a b).2 = some s → kdPairs P s.1 := by
  have he : kdPairs P (mergeList inner cR a b) := by
    unfold mergeList
    refine kdPairs_append ha ?_
    split
    · exact kdPairs_renameHead cR (hP (by assumption)) hb
    · exact hb
  unfold mergeKlongs splitMerged
  generalize mergeList inner cR a b = e at he
  split
  · exact ⟨he, fun s hs => by cases hs⟩
  · refine ⟨fun q hq => he q (List.mem_of_mem_take hq), ?_⟩
    intro s hs
    cases hs
    have hd : kdPairs P (e.drop ((e.length + 1) / 2)) :=
      fun q hq => he q (List.mem_of_mem_drop hq)
    dsimp only
    split
    · exact kdPairs_renameHead 0 (hP (by assumption)) hd
    · exact hd

theorem kdKs_renameKey {P : Nat → NodeId → Prop} {ks : List Klong} {t : Klong} {c1 : Nat}
    {y1 : NodeId} {r : List Klong} (c' : Nat) (hP : kdFree P) (he : ks = t :: .key c1 y1 :: r)
    (hk : kdKs P ks) : kdKs P (t :: .key c' y1 :: r) := by
  subst he
  intro cv y hm
  rcases List.mem_cons.mp hm with hm | hm
  · exact hk cv y (hm ▸ List.mem_cons_self)
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact hP _ _ _ (hk c1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact hk cv y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))

/-- LE-b's next live klong (`emptyKeyNext`) is a key klong of the node. -/
theorem kd_emptyKeyFold (del0 : List Nat) {ks : List Klong}
    {i cv : Nat} {y : NodeId}
    (h : ks.zipIdx.foldl (fun (best : Option (Nat × Nat × NodeId)) (k, i) =>
      match k with
      | .key cv y =>
        if del0.contains i then best else
          match best with
          | none => some (i, cv, y)
          | some (_, jcv, _) => if cv ≤ jcv then some (i, cv, y) else best
      | _ => best) none = some (i, cv, y)) : Klong.key cv y ∈ ks := by
  have hgen : ∀ (xs : List (Klong × Nat)) (b : Option (Nat × Nat × NodeId)),
      (∀ q ∈ xs, q.1 ∈ ks) →
      (∀ i cv y, b = some (i, cv, y) → Klong.key cv y ∈ ks) →
      ∀ i cv y, xs.foldl (fun (best : Option (Nat × Nat × NodeId)) (k, i) =>
        match k with
        | .key cv y =>
          if del0.contains i then best else
            match best with
            | none => some (i, cv, y)
            | some (_, jcv, _) => if cv ≤ jcv then some (i, cv, y) else best
        | _ => best) b = some (i, cv, y) → Klong.key cv y ∈ ks := by
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
          · cases hb'; exact hq
          · split at hb'
            · cases hb'; exact hq
            · exact hb _ _ _ hb'
      | time t => exact hb _ _ _ hb'
      | del b' => exact hb _ _ _ hb'
  refine hgen _ none ?_ (fun _ _ _ he => by cases he) i cv y h
  intro q hq
  exact List.fst_mem_of_mem_zipIdx (by obtain ⟨a, b⟩ := q; exact hq)

/-- The klongs of `retarget`: those of the node, some pointed to `dst` with
their compare values. -/
theorem kdKs_retargetMap {P : Nat → NodeId → Prop} (ti : Nat) (src dst : NodeId)
    {ks : List Klong} (hk : kdKs P ks) (hd : ∀ cv, Klong.key cv src ∈ ks → P cv dst) :
    kdKs P (ks.zipIdx.map (fun (k, i) => match k with
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
    · rename_i hc
      cases he
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rw [hc.2] at hkm
      exact hd _ hkm
    · cases he; exact hk _ _ hkm
  | time t => cases he
  | del b => cases he

/-- A search for compare value c finds a key klong of the node. -/
theorem kd_searchEq_mem (n : KNode) (t : Time) (c : Nat) (fd : Found)
    (h : n.searchEq t c = some fd) : Klong.key fd.c fd.y ∈ n.ks := by
  unfold KNode.searchEq at h
  have hsub : ∀ k ∈ prefixAt n.ks t, k ∈ n.ks :=
    fun _ hk => (List.takeWhile_sublist _).subset hk
  generalize prefixAt n.ks t = pre at h hsub
  suffices hs : ∀ (l : List (Klong × Nat)) (acc : Option Time × List Nat × Option Found),
      (∀ q ∈ l, q.1 ∈ pre) →
      (∀ f, acc.2.2 = some f → Klong.key f.c f.y ∈ pre) → ∀ f, (l.foldl
      (fun (acc : Option Time × List Nat × Option Found) (k, i) =>
      if acc.2.1.contains i then acc else
        match k with
        | .time x => (some x, acc.2.1, acc.2.2)
        | .key c' y => if c' == c then (acc.1, acc.2.1, some ⟨c, i, acc.1.getD 0, y⟩) else acc
        | .del b => (acc.1, b, match acc.2.2 with
          | some f => if b.contains f.idx then none else some f
          | none => none)) acc).2.2 = some f → Klong.key f.c f.y ∈ pre by
    exact hsub _ (hs pre.zipIdx _ (fun q hq => List.fst_mem_of_mem_zipIdx
      (by obtain ⟨a, b⟩ := q; exact hq)) (fun f hf => by simp at hf) fd h)
  intro l
  induction l with
  | nil => intro acc _ hacc f hf; exact hacc f hf
  | cons e rest ih =>
    intro acc hl hacc f hf
    rw [List.foldl_cons] at hf
    apply ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ f hf
    intro f' hf'
    rcases e with ⟨k, i⟩
    have hk := hl (k, i) List.mem_cons_self
    simp only at hf' hk
    split at hf'
    · exact hacc f' hf'
    · cases k with
      | time x => exact hacc f' hf'
      | key c' y =>
        simp only at hf'
        split at hf'
        · rename_i hcc
          simp only [beq_iff_eq] at hcc
          subst hcc
          simp only [Option.some.injEq] at hf'
          subst hf'
          exact hk
        · exact hacc f' hf'
      | del b =>
        simp only at hf'
        split at hf'
        · rename_i f0 hf0
          split at hf'
          · cases hf'
          · cases hf'; exact hacc _ hf0
        · cases hf'

/-- A search at or below a value finds a key klong of the node. -/
theorem kd_searchLte_mem (n : KNode) (t : Time) (c : Int) (fd : Found)
    (h : n.searchLte t c = some fd) : Klong.key fd.c fd.y ∈ n.ks :=
  KNode.liveAt_key_mem n t _ _ (KNode.searchLte_mem n t c fd h)

/-- The klong that `linkIndex` finds has the compare value asked for. -/
theorem kd_linkIndex_some (n : KNode) (y : NodeId) (cv j : Nat)
    (h : n.linkIndex y cv = some j) : n.ks[j]? = some (.key cv y) := by
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
      have hfind := List.find?_some hf
      simp only [beq_iff_eq] at hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      subst hfind
      rw [← hc.2]
      simpa using hget
    · cases h
  · cases h

/-! ## The state of the walk -/

/-- What the walk of the kinds keeps besides the books, with B the
transaction's first id: the kinds of the overlay's klongs, of the key access
path and of the made nodes' replaced nodes; a value made is no key node; a
node of the path that has a node after it, and a made node of `madeFor`, are
key nodes of the overlay. -/
structure KdInv (K : KindOracle) (B : NodeId) (w : W) : Prop where
  cache : KindCache K w
  path : PathKinds K w
  made : MadeForSeg K w
  vals : ∀ q ∈ w.vals, B ≤ q.1 ∧ q.1 < w.next ∧ q.1 ∉ w.gh.map (·.1)
  pathGh : ∀ d a q, w.path[d]? = some (a, q) → d + 1 < w.path.length → q ∈ w.gh.map (·.1)
  madeGh : ∀ q ∈ w.madeFor, q.1 ∈ w.gh.map (·.1)
  pathSome : ∀ d a q, w.path[d + 1]? = some (a, q) → a ≠ none

/-- A state and a later one: the books' relation, and every value stays. -/
def KdLe (w v : W) : Prop := Kept w v ∧ ∀ q ∈ w.vals, q ∈ v.vals

theorem KdLe.refl (w : W) : KdLe w w := ⟨Kept.refl w, fun _ h => h⟩

theorem KdLe.trans {a b d : W} (h1 : KdLe a b) (h2 : KdLe b d) : KdLe a d :=
  ⟨h1.1.trans h2.1, fun q hq => h2.2 q (h1.2 q hq)⟩

theorem KdLe.same {w v : W} (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hv : v.vals = w.vals) :
    KdLe w v := ⟨Kept.same hn hg, fun q hq => by rw [hv]; exact hq⟩

theorem IsKeySeg.kdMono {K : KindOracle} {w v : W} {y : NodeId} {g : Nat} (h : IsKeySeg K w y g)
    (hk : KdLe w v) : IsKeySeg K v y g := by
  rcases h with ⟨hh, hm⟩ | h
  · exact Or.inl ⟨hh, hk.1.2 _ hm⟩
  · exact Or.inr h

theorem IsValId.kdMono {K : KindOracle} {w v : W} {y : NodeId} (h : IsValId K w y)
    (hk : KdLe w v) : IsValId K v y := by
  rcases h with ⟨hh, hm⟩ | h
  · exact Or.inl ⟨hh, hk.2 _ hm⟩
  · exact Or.inr h

theorem KindKlong.kdMono {K : KindOracle} {w v : W} {g h c : Nat} {y : NodeId}
    (hy : KindKlong K w g h c y) (hk : KdLe w v) : KindKlong K v g h c y :=
  ⟨fun h0 => (hy.1 h0).kdMono hk,
   fun h0 => ⟨fun h7 => ((hy.2 h0).1 h7).kdMono hk, fun h7 => ((hy.2 h0).2 h7).kdMono hk⟩⟩

theorem kdKs_mono {K : KindOracle} {w v : W} {g h : Nat} {ks : List Klong}
    (hks : kdKs (KindKlong K w g h) ks) (hk : KdLe w v) : kdKs (KindKlong K v g h) ks :=
  fun c y hm => (hks c y hm).kdMono hk

theorem kdPairs_mono {K : KindOracle} {w v : W} {g h : Nat} {l : List (Nat × NodeId)}
    (hl : kdPairs (KindKlong K w g h) l) (hk : KdLe w v) : kdPairs (KindKlong K v g h) l :=
  fun q hq => (hl q hq).kdMono hk

/-- An inner node's klong: its compare value does not matter. -/
theorem kd_free {K : KindOracle} {w : W} {g h : Nat} (hh : h ≠ 0) : kdFree (KindKlong K w g h) :=
  fun _ _ _ hy => ⟨hy.1, fun h0 => absurd h0 hh⟩

theorem kd_free_of_leaf {K : KindOracle} {w : W} {g h : Nat} {leaf : Bool} (hl : leaf = (h == 0)) :
    leaf = false → kdFree (KindKlong K w g h) := by
  intro hf
  apply kd_free
  intro h0
  subst h0
  simp at hl
  rw [hl] at hf
  cases hf

/-! ## Facts of the state -/

section Facts

variable {K : KindOracle} {B : NodeId} {c : Ctx} {w : W}

theorem kd_mem_ids {x : NodeId} {g h : Nat} (hm : (x, g, h) ∈ w.gh) : x ∈ w.gh.map (·.1) :=
  List.mem_map.mpr ⟨_, hm, rfl⟩

/-- A node has one entry in `gh`. -/
theorem kd_tag_eq (hb : Book B c w) {x : NodeId} {g h g' h' : Nat} (h1 : (x, g, h) ∈ w.gh)
    (h2 : (x, g', h') ∈ w.gh) : g = g' ∧ h = h' := by
  have hn := hb.nodup
  generalize w.gh = l at h1 h2 hn
  induction l with
  | nil => cases h1
  | cons e l ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h1 with e1 | e1 <;> rcases List.mem_cons.mp h2 with e2 | e2
    · rw [← e1] at e2; cases e2; exact ⟨rfl, rfl⟩
    · subst e1; exact (hn.1 (List.mem_map.mpr ⟨_, e2, rfl⟩)).elim
    · subst e2; exact (hn.1 (List.mem_map.mpr ⟨_, e1, rfl⟩)).elim
    · exact ih e1 e2 hn.2

/-- One segment a node. -/
theorem kd_seg_unique (hb : Book B c w) (hk : ViewKinds K B c) {y : NodeId} {g h g' : Nat}
    (hm : (y, g, h) ∈ w.gh) (hs : IsKeySeg K w y g') : g = g' := by
  rcases hs with ⟨h', hm'⟩ | hs
  · exact (kd_tag_eq hb hm hm').1
  · rcases hb.tag y g h hm with ⟨nd, hnd, hd, hl, hg, _⟩ | ⟨hB, _, _⟩
    · have := hk.node y nd hnd hd hl
      subst hg
      exact hk.seg y _ _ this hs
    · have := hk.old y g' hs
      omega

/-- A key node is no value. -/
theorem kd_not_val (hb : Book B c w) (hk : ViewKinds K B c) (hi : KdInv K B w) {y : NodeId}
    {g h : Nat} (hm : (y, g, h) ∈ w.gh) : ¬ IsValId K w y := by
  rintro (⟨hh, hv⟩ | hv)
  · exact (hi.vals _ hv).2.2 (kd_mem_ids hm)
  · rcases hb.tag y g h hm with ⟨nd, hnd, hd, hl, _, _⟩ | ⟨hB, _, _⟩
    · exact hk.notBoth y _ (hk.node y nd hnd hd hl) hv
    · have := hk.oldVal y hv
      omega

/-- A klong that names key node x of segment g names a node of the right kind if
it names another key node of segment g instead. -/
theorem kd_swap (hb : Book B c w) (hk : ViewKinds K B c) (hi : KdInv K B w) {x y : NodeId}
    {g hx g' h' cv : Nat} (hm : (x, g, hx) ∈ w.gh) (hxk : KindKlong K w g' h' cv x)
    (hy : IsKeySeg K w y g) : KindKlong K w g' h' cv y := by
  refine ⟨fun h0 => ?_, fun h0 => ⟨fun h7 => ?_, fun h7 => ?_⟩⟩
  · have := kd_seg_unique hb hk hm (hxk.1 h0)
    subst this; exact hy
  · have := kd_seg_unique hb hk hm ((hxk.2 h0).1 h7)
    subst this; exact hy
  · exact absurd ((hxk.2 h0).2 h7) (kd_not_val hb hk hi hm)

/-- The same with another compare value, in an inner node. -/
theorem kd_swap_inner (hb : Book B c w) (hk : ViewKinds K B c) (hi : KdInv K B w) {x y : NodeId}
    {g hx g' h' cv cv' : Nat} (hh : h' ≠ 0) (hm : (x, g, hx) ∈ w.gh)
    (hxk : KindKlong K w g' h' cv x) (hy : IsKeySeg K w y g) : KindKlong K w g' h' cv' y :=
  kd_free hh _ _ _ (kd_swap hb hk hi hm hxk hy)

theorem kd_isKey {x : NodeId} {g h : Nat} (hm : (x, g, h) ∈ w.gh) : IsKeySeg K w x g :=
  Or.inl ⟨h, hm⟩

/-- The klongs of an overlay node, by its entry in `gh`. -/
theorem kd_cache_node (hi : KdInv K B w) {x : NodeId} {n : KNode} {g h : Nat}
    (hl : w.nodes.lookup x = some n) (hm : (x, g, h) ∈ w.gh) : kdKs (KindKlong K w g h) n.ks :=
  fun cv y hy => hi.cache x n g h (bk_mem_of_lookup _ _ _ hl) hm cv y hy

/-- The leaf flag of an overlay node, by its entry in `gh`. -/
theorem kd_leaf (hb : Book B c w) {x : NodeId} {n : KNode} {g h : Nat}
    (hl : w.nodes.lookup x = some n) (hm : (x, g, h) ∈ w.gh) : n.leaf = (h == 0) :=
  hb.leaf x n g h (bk_mem_of_lookup _ _ _ hl) hm

/-- A node of the overlay has an entry in `gh`. -/
theorem kd_tag_of_lookup (hb : Book B c w) {x : NodeId} {n : KNode}
    (hl : w.nodes.lookup x = some n) : ∃ g h, (x, g, h) ∈ w.gh := by
  have := bk_mem_ids_of_lookup _ _ _ hl
  rw [hb.ids] at this
  obtain ⟨⟨x', g, h⟩, hq, he⟩ := List.mem_map.mp (List.mem_reverse.mp this)
  simp only at he
  subst he
  exact ⟨g, h, hq⟩

theorem kd_lookup_of_tag (hb : Book B c w) {x : NodeId} {g h : Nat} (hm : (x, g, h) ∈ w.gh) :
    ∃ n, w.nodes.lookup x = some n := by
  apply bk_lookup_of_mem_ids
  rw [hb.ids]
  exact List.mem_reverse.mpr (kd_mem_ids hm)

/-- A new id is no id of `gh`. -/
theorem kd_next_not (hb : Book B c w) : w.next ∉ w.gh.map (·.1) := by
  intro hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have := hb.bound q hq
  rw [he] at this
  exact Nat.lt_irrefl _ this

end Facts

/-- Every field that the walk reads is kept, and the next id does not go down. -/
theorem KdInv.frame {K : KindOracle} {B : NodeId} {w : W} (hi : KdInv K B w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hv : v.vals = w.vals)
    (hm : v.madeFor = w.madeFor) (hp : v.path = w.path) (hx : w.next ≤ v.next) :
    KdInv K B v := by
  have hle : KdLe w v := KdLe.same hn hg hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n g h hn' hg' cv y hy
    rw [hn] at hn'; rw [hg] at hg'
    exact (hi.cache x n g h hn' hg' cv y hy).kdMono hle
  · intro d a q cv y h1 h2 g h hg'
    rw [hp] at h1 h2; rw [hg] at hg'
    exact (hi.path d a q cv y h1 h2 g h hg').kdMono hle
  · intro q hq g h hg'
    rw [hm] at hq; rw [hg] at hg'
    exact (hi.made q hq g h hg').kdMono hle
  · intro q hq
    rw [hv] at hq
    obtain ⟨h1, h2, h3⟩ := hi.vals q hq
    exact ⟨h1, by omega, by rw [hg]; exact h3⟩
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact hi.pathGh d a q h1 h2
  · intro q hq
    rw [hm] at hq; rw [hg]
    exact hi.madeGh q hq
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- The same with the path emptied. -/
theorem KdInv.clear {K : KindOracle} {B : NodeId} {w : W} (hi : KdInv K B w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hv : v.vals = w.vals)
    (hm : v.madeFor = w.madeFor) (hp : v.path = []) (hx : w.next ≤ v.next) :
    KdInv K B v := by
  have h0 : KdInv K B { w with path := [] } :=
    ⟨hi.cache, by intro d a q cv y h1; simp at h1, hi.made, hi.vals,
      by intro d a q h1; simp at h1, hi.madeGh, by intro d a q h1; simp at h1⟩
  exact h0.frame v hn hg hv hm hp hx

/-! ## The states the primitive steps make -/

/-- A node of the view loaded into the overlay. -/
theorem KdInv.load {K : KindOracle} {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hi : KdInv K B w) (x : NodeId)
    (nd : Node BVal) (hnd : c.view x = some nd) (hd : nd.isData = false)
    (hlv : nd.level ≤ c.p.keyMax) (hn0 : w.nodes.lookup x = none) (v : W)
    (hn : v.nodes = w.nodes ++ [(x, ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩)])
    (hg : v.gh = (x, c.p.segOf nd.level, c.p.heightOf nd.level) :: w.gh)
    (hvl : v.vals = w.vals) (hm : v.madeFor = w.madeFor) (hp : v.path = w.path)
    (hx : v.next = w.next) : KdInv K B v := by
  have hxn : x ∉ w.nodes.map (·.1) := bk_not_mem_ids_of_lookup _ x hn0
  have hxg : x ∉ w.gh.map (·.1) := by
    intro h; apply hxn; rw [hb.ids]; exact List.mem_reverse.mpr h
  have hle : KdLe w v :=
    ⟨Kept.grow _ [(x, c.p.segOf nd.level, c.p.heightOf nd.level)] hn hg,
      fun q hq => by rw [hvl]; exact hq⟩
  have hxB : x < B := hv x nd hnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y m g h hm' hg' cv z hz
    rw [hn] at hm'; rw [hg] at hg'
    simp only [List.mem_append, List.mem_singleton] at hm'
    simp only [List.mem_cons] at hg'
    rcases hm' with hm' | hm'
    · rcases hg' with hg' | hg'
      · cases hg'
        exact absurd (bk_mem_ids_of_mem _ _ _ hm') hxn
      · exact (hi.cache y m g h hm' hg' cv z hz).kdMono hle
    · cases hm'
      rcases hg' with hg' | hg'
      · cases hg'
        have hkl := hk.klongs x nd hnd hd hlv cv z hz
        exact ⟨fun h0 => Or.inr (hkl.1 h0),
          fun h0 => ⟨fun h7 => Or.inr ((hkl.2 h0).1 h7), fun h7 => Or.inr ((hkl.2 h0).2 h7)⟩⟩
      · exact absurd (kd_mem_ids hg') hxg
  · intro d a q cv y h1 h2 g h hg'
    rw [hp] at h1 h2; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    have hqg := hi.pathGh d a q h1 (List.getElem?_eq_some_iff.mp h2).1
    rcases hg' with hg' | hg'
    · cases hg'; exact absurd hqg hxg
    · exact (hi.path d a q cv y h1 h2 g h hg').kdMono hle
  · intro q hq g h hg'
    rw [hm] at hq; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    rcases hg' with hg' | hg'
    · have := hi.madeGh q hq
      rw [congrArg Prod.fst hg'] at this
      exact absurd this hxg
    · exact (hi.made q hq g h hg').kdMono hle
  · intro q hq
    rw [hvl] at hq
    obtain ⟨h1, h2, h3⟩ := hi.vals q hq
    refine ⟨h1, by omega, ?_⟩
    rw [hg]
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨by omega, h3⟩
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact List.mem_cons_of_mem _ (hi.pathGh d a q h1 h2)
  · intro q hq
    rw [hm] at hq; rw [hg]
    exact List.mem_cons_of_mem _ (hi.madeGh q hq)
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- A new key node with klongs of the right kind. -/
theorem KdInv.create {K : KindOracle} {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w)
    (hi : KdInv K B w) (g h : Nat) (N : KNode) (hks : kdKs (KindKlong K w g h) N.ks) (v : W)
    (hn : v.nodes = w.nodes ++ [(w.next, N)]) (hg : v.gh = (w.next, g, h) :: w.gh)
    (hv : v.vals = w.vals) (hm : v.madeFor = w.madeFor) (hp : v.path = w.path)
    (hx : v.next = w.next + 2) : KdInv K B v ∧ KdLe w v := by
  have hxg := kd_next_not hb
  have hxn : w.next ∉ w.nodes.map (·.1) := by
    rw [hb.ids]; intro h; exact hxg (List.mem_reverse.mp h)
  have hle : KdLe w v := ⟨Kept.grow _ [(w.next, g, h)] hn hg, fun q hq => by rw [hv]; exact hq⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hle⟩
  · intro y m g' h' hm' hg' cv z hz
    rw [hn] at hm'; rw [hg] at hg'
    simp only [List.mem_append, List.mem_singleton] at hm'
    simp only [List.mem_cons] at hg'
    rcases hm' with hm' | hm'
    · rcases hg' with hg' | hg'
      · cases hg'
        exact absurd (bk_mem_ids_of_mem _ _ _ hm') hxn
      · exact (hi.cache y m g' h' hm' hg' cv z hz).kdMono hle
    · cases hm'
      rcases hg' with hg' | hg'
      · cases hg'
        exact (hks cv z hz).kdMono hle
      · exact absurd (kd_mem_ids hg') hxg
  · intro d a q cv y h1 h2 g' h' hg'
    rw [hp] at h1 h2; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    have hqg := hi.pathGh d a q h1 (List.getElem?_eq_some_iff.mp h2).1
    rcases hg' with hg' | hg'
    · cases hg'; exact absurd hqg hxg
    · exact (hi.path d a q cv y h1 h2 g' h' hg').kdMono hle
  · intro q hq g' h' hg'
    rw [hm] at hq; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    rcases hg' with hg' | hg'
    · have := hi.madeGh q hq
      rw [congrArg Prod.fst hg'] at this
      exact absurd this hxg
    · exact (hi.made q hq g' h' hg').kdMono hle
  · intro q hq
    rw [hv] at hq
    obtain ⟨h1, h2, h3⟩ := hi.vals q hq
    refine ⟨h1, by omega, ?_⟩
    rw [hg]
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨by omega, h3⟩
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact List.mem_cons_of_mem _ (hi.pathGh d a q h1 h2)
  · intro q hq
    rw [hm] at hq; rw [hg]
    exact List.mem_cons_of_mem _ (hi.madeGh q hq)
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-! ## The primitive steps -/

section Steps

variable (K : KindOracle) (B : NodeId)

/-- Every field that the walk reads is kept, and the next id does not go down. -/
def KdFrame {α : Type} (f : M α) : Prop :=
  ∀ c w, WriterWP f c w (fun _ v => v.nodes = w.nodes ∧ v.gh = w.gh ∧ v.vals = w.vals ∧
    v.madeFor = w.madeFor ∧ v.path = w.path ∧ w.next ≤ v.next)

/-- A step that keeps the books, the walk's state and the path. -/
def KdKeeps {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KdInv K B w →
    WriterWP f c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path ∧
      v.madeFor = w.madeFor)

theorem kd_keeps_of_frame {α : Type} {f : M α} (hbk : KeepsBook B f) (hf : KdFrame f) :
    KdKeeps K B f := by
  intro c w hv _ hb hi
  refine writerWP_mono (writerWP_and (hbk c w hv hb) (hf c w)) ?_
  rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hvl, hm, hp, hx⟩
  exact ⟨hb', hi.frame v hn hg hvl hm hp hx, ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp, hm⟩

theorem kd_writerWP {α : Type} {f : M α} (hf : KdKeeps K B f) (c : Ctx) (w : W)
    (post : α → W → Prop) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c)
    (hb : Book B c w) (hi : KdInv K B w)
    (hp : ∀ r v, Book B c v → KdInv K B v → KdLe w v → v.path = w.path →
      v.madeFor = w.madeFor → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hv hk hb hi) (fun r v h => hp r v h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

macro "kdFrameTac" : tactic => `(tactic| (
  intro c w
  repeat' first
    | (simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure, writerWP_modify,
        writerWP_read])
    | split
    | exact writerWP_throw _ _ _ _
    | trivial
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega | (dsimp only; omega))
    | (simp only [true_and, Nat.le_refl]; done)
    | (simp only [true_and]; omega)))

theorem kdFrame_note (s : String) : KdFrame (note s) := by unfold note; kdFrameTac
theorem kdFrame_fresh : KdFrame fresh := by unfold fresh; kdFrameTac
theorem kdFrame_newSuperRoot (y : NodeId) : KdFrame (newSuperRoot y) := by
  unfold newSuperRoot note fresh; kdFrameTac
theorem kdFrame_takenBack (x : NodeId) : KdFrame (takenBack x) := by
  unfold takenBack; kdFrameTac

theorem kd_note (s : String) : KdKeeps K B (note s) :=
  kd_keeps_of_frame K B (book_note B s) (kdFrame_note s)
theorem kd_fresh : KdKeeps K B fresh := kd_keeps_of_frame K B (book_fresh B) kdFrame_fresh
theorem kd_newSuperRoot (y : NodeId) : KdKeeps K B (newSuperRoot y) :=
  kd_keeps_of_frame K B (book_newSuperRoot B y) (kdFrame_newSuperRoot y)

/-- The counters of merges and space splits. -/
theorem kd_counter (c : Ctx) (w : W) (f : W → W) (post : Unit → W → Prop)
    (hn : (f w).nodes = w.nodes) (hg : (f w).gh = w.gh) (hvl : (f w).vals = w.vals)
    (hm : (f w).madeFor = w.madeFor) (hp : (f w).path = w.path) (hx : (f w).next = w.next)
    (hbk : ∀ {c : Ctx} {w : W}, Book B c w → Book B c (f w)) (hb : Book B c w)
    (hi : KdInv K B w)
    (hq : ∀ v, Book B c v → KdInv K B v → KdLe w v → v.path = w.path →
      v.madeFor = w.madeFor → post () v) :
    WriterWP (modify f) c w post := by
  rw [writerWP_modify]
  exact hq _ (hbk hb) (hi.frame _ hn hg hvl hm hp (Nat.le_of_eq hx.symm)) (KdLe.same hn hg hvl) hp hm

/-- Reads that change nothing. -/
theorem kd_pathSize (c : Ctx) (w : W) : WriterWP pathSize c w (fun r v => v = w ∧ r = w.path.length) := by
  unfold pathSize
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  exact ⟨by trivial, by trivial⟩

theorem kd_pathNode (d : Nat) (c : Ctx) (w : W) :
    WriterWP (pathNode d) c w (fun r v => v = w ∧ ∃ a, w.path[d]? = some (a, r)) := by
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    exact ⟨by trivial, e.1, by rw [he]⟩
  · exact writerWP_throw _ _ _ _

theorem kd_klongAt (d : Nat) (c : Ctx) (w : W) :
    WriterWP (klongAt d) c w (fun r v => v = w ∧ ∃ y, w.path[d]? = some (some r, y)) := by
  unfold klongAt
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i cv y he
    simp only [writerWP_pure]
    exact ⟨by trivial, y, he⟩
  · exact writerWP_throw _ _ _ _

theorem kd_parentAt (d : Nat) (c : Ctx) (w : W) :
    WriterWP (parentAt d) c w (fun r v => v = w ∧ (d = 0 → r = none) ∧
      ∀ e, d = e + 1 → ∃ a q, r = some q ∧ w.path[e]? = some (a, q)) := by
  unfold parentAt
  split
  · simp only [writerWP_pure]
    exact ⟨by trivial, fun _ => by trivial, fun e he => by cases he⟩
  · rename_i e
    simp only [writerWP_bind]
    refine writerWP_mono (kd_pathNode e c w) ?_
    rintro q v ⟨rfl, a, ha⟩
    rw [writerWP_pure]
    refine ⟨rfl, fun h => absurd h (Nat.succ_ne_zero _), fun e' he' => ?_⟩
    cases he'
    exact ⟨a, q, rfl, ha⟩

theorem kd_replacedBy (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (replacedBy x) c w (fun r v => v = w ∧ ∀ o, r = some o → (x, o) ∈ w.madeFor) := by
  unfold replacedBy
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  exact ⟨by trivial, fun o ho => bk_mem_of_lookup _ _ _ ho⟩

/-- A read of key node x. -/
theorem kd_getNode (x : NodeId) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds K B c) (hb : Book B c w) (hi : KdInv K B w) :
    WriterWP (getNode x) c w (fun n v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.nodes.lookup x = some n ∧ v.path = w.path ∧ v.madeFor = w.madeFor) := by
  refine writerWP_mono (writerWP_and (book_getNode B x c w hv hb)
    (?_ : WriterWP (getNode x) c w (fun _ v => KdInv K B v ∧ (∀ q ∈ w.vals, q ∈ v.vals) ∧
      v.path = w.path ∧ v.madeFor = w.madeFor))) ?_
  · unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simp only [writerWP_pure]
      exact ⟨hi, fun _ h => h, by trivial, by trivial⟩
    · rename_i hn
      simp only [writerWP_bind, writerWP_read]
      split
      · rename_i nd hnd
        split
        · exact writerWP_throw _ _ _ _
        · rename_i hkind
          have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
          have hlv : nd.level ≤ c.p.keyMax := by
            have hh : ¬ c.p.keyMax < nd.level := by
              intro h; simp [h] at hkind
            omega
          simp only [writerWP_bind, writerWP_set, writerWP_pure]
          exact ⟨KdInv.load hb hv hk hi x nd hnd hd hlv hn _ rfl rfl rfl rfl rfl rfl,
            fun _ h => h, by trivial, by trivial⟩
      · exact writerWP_throw _ _ _ _
  · rintro n v ⟨⟨hb', hk', hl⟩, hi', hvl, hp, hm⟩
    exact ⟨hb', hi', ⟨hk', hvl⟩, hl, hp, hm⟩

/-- The segment and the height of key node x. -/
theorem kd_ghOf (x : NodeId) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds K B c) (hb : Book B c w) (hi : KdInv K B w) :
    WriterWP (ghOf x) c w (fun r v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ (x, r.1, r.2) ∈ v.gh ∧
      ∃ n, v.nodes.lookup x = some n ∧ n.leaf = (r.2 == 0)) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
  rintro n v ⟨hb', hi', hle, hl, hp, hm⟩
  simp only [writerWP_get]
  split
  · rename_i r hr
    simp only [writerWP_pure]
    have hmem := bk_mem_of_lookup _ _ _ hr
    exact ⟨hb', hi', hle, hp, hm, hmem, n, hl, kd_leaf hb' hl hmem⟩
  · exact writerWP_throw _ _ _ _

/-- A store of key node x of the overlay, with klongs of the right kind for its
entry in `gh`. -/
theorem kd_putNode (x : NodeId) (n' : KNode) (c : Ctx) (w : W) (hb : Book B c w)
    (hi : KdInv K B w) (n0 : KNode) (hl : w.nodes.lookup x = some n0)
    (hleaf : n'.leaf = n0.leaf) (g h : Nat) (hm : (x, g, h) ∈ w.gh)
    (hks : kdKs (KindKlong K w g h) n'.ks) :
    WriterWP (putNode x n') c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ v.nodes.lookup x = some n') := by
  refine writerWP_mono (writerWP_and (book_putNode B x n' c w hb ⟨n0, hl, hleaf⟩)
    (?_ : WriterWP (putNode x n') c w (fun _ v => KdInv K B v ∧ v.vals = w.vals ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ v.nodes.lookup x = some n'))) ?_
  · simp only [putNode, writerWP_modify]
    refine ⟨⟨?_, hi.path, hi.made, hi.vals, hi.pathGh, hi.madeGh, hi.pathSome⟩, by trivial, by trivial, by trivial, ?_⟩
    · intro y m g' h' hm' hg' cv z hz
      rcases bk_mem_upsert w.nodes x n' n0 hl y m hm' with ⟨rfl, rfl⟩ | hm'
      · obtain ⟨rfl, rfl⟩ := kd_tag_eq hb hm hg'
        exact hks cv z hz
      · exact hi.cache y m g' h' hm' hg' cv z hz
    · show (upsert w.nodes x n').lookup x = some n'
      rw [bk_lookup_upsert _ x x n' n0 hl]
      simp
  · rintro _ v ⟨⟨hb', hk'⟩, hi', hvl, hp, hm', hlk⟩
    exact ⟨hb', hi', ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp, hm', hlk⟩

/-- A new key node with klongs of the right kind for its segment and height. -/
theorem kd_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hb : Book B c w) (hi : KdInv K B w) (hleaf : leaf = (h == 0))
    (hks : kdKs (KindKlong K w g h) ks) :
    WriterWP (newKey g h leaf ks) c w (fun x v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ v.nodes.lookup x = some ⟨leaf, ks⟩ ∧
      (x, g, h) ∈ v.gh ∧ x = w.next) := by
  refine writerWP_mono (writerWP_and (book_newKey B g h leaf ks c w hb hleaf)
    (?_ : WriterWP (newKey g h leaf ks) c w (fun x v => KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ (x, g, h) ∈ v.gh ∧ x = w.next))) ?_
  · unfold newKey fresh
    simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
    split
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨(KdInv.create hb hi g h ⟨leaf, ks⟩ hks _ ?_ ?_ ?_ ?_ ?_ ?_).1,
        (KdInv.create hb hi g h ⟨leaf, ks⟩ hks _ ?_ ?_ ?_ ?_ ?_ ?_).2, ?_⟩
      all_goals first | rfl | simp
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨(KdInv.create hb hi g h ⟨leaf, ks⟩ hks _ ?_ ?_ ?_ ?_ ?_ ?_).1,
        (KdInv.create hb hi g h ⟨leaf, ks⟩ hks _ ?_ ?_ ?_ ?_ ?_ ?_).2, ?_⟩
      all_goals first | rfl | simp
  · rintro x v ⟨⟨hb', _, hlk⟩, hi', hle, hp, hm, hg, hx⟩
    exact ⟨hb', hi', hle, hp, hm, hlk, hg, hx⟩

/-- A new value. -/
theorem kd_newValue (h : Nat) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hb : Book B c w)
    (hi : KdInv K B w) :
    WriterWP (newValue h) c w (fun x v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ IsValId K v x) := by
  have hxg := kd_next_not hb
  refine writerWP_mono (writerWP_and (book_newValue B h c w hv hb)
    (?_ : WriterWP (newValue h) c w (fun x v => KdInv K B v ∧ (∀ q ∈ w.vals, q ∈ v.vals) ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ IsValId K v x))) ?_
  · unfold newValue fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure, writerWP_modify]
    have hle : KdLe w { w with next := w.next + 2, vals := w.vals ++ [(w.next, h)], made := w.made ++ [⟨w.next, 0, true⟩] } :=
      ⟨Kept.same rfl rfl, fun q hq => List.mem_append_left _ hq⟩
    refine ⟨⟨?_, ?_, ?_, ?_, hi.pathGh, hi.madeGh, hi.pathSome⟩, hle.2, by trivial, by trivial,
      Or.inl ⟨h, List.mem_append_right _ List.mem_cons_self⟩⟩
    · intro y m g' h' hm' hg' cv z hz
      exact (hi.cache y m g' h' hm' hg' cv z hz).kdMono hle
    · intro d a q cv y h1 h2 g' h' hg'
      exact (hi.path d a q cv y h1 h2 g' h' hg').kdMono hle
    · intro q hq g' h' hg'
      exact (hi.made q hq g' h' hg').kdMono hle
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨h1, h2, h3⟩ := hi.vals q hq
        exact ⟨h1, by show q.1 < w.next + 2; omega, h3⟩
      · rw [List.mem_singleton.mp hq]
        exact ⟨hb.next, by show w.next < w.next + 2; omega, hxg⟩
  · rintro x v ⟨⟨hb', hk'⟩, hi', hvl, hp, hm, hval⟩
    exact ⟨hb', hi', ⟨hk', hvl⟩, hp, hm, hval⟩

/-- `madeFor`: a made node of the overlay and a node of its segment. -/
theorem kd_setMadeFor (m : NodeId) (o : Option NodeId) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view)
    (hb : Book B c w) (hi : KdInv K B w)
    (hm : ∀ o', o = some o' → ∃ g h, (m, g, h) ∈ w.gh ∧ IsKeySeg K w o' g) :
    WriterWP (setMadeFor m o) c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path) := by
  refine writerWP_mono (writerWP_and (book_setMadeFor B m o c w hv hb)
    (?_ : WriterWP (setMadeFor m o) c w (fun _ v => KdInv K B v ∧ v.vals = w.vals ∧
      v.path = w.path))) ?_
  · unfold setMadeFor
    split
    · rename_i o'
      simp only [writerWP_modify]
      obtain ⟨g, h, hg, hs⟩ := hm o' rfl
      refine ⟨⟨hi.cache, hi.path, ?_, hi.vals, hi.pathGh, ?_, hi.pathSome⟩, by trivial, by trivial⟩
      · intro q hq g' h' hg'
        rcases List.mem_cons.mp hq with hq | hq
        · subst hq
          obtain ⟨rfl, rfl⟩ := kd_tag_eq hb hg hg'
          exact hs
        · exact hi.made q hq g' h' hg'
      · intro q hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst hq; exact kd_mem_ids hg
        · exact hi.madeGh q hq
    · simp only [writerWP_pure]
      exact ⟨hi, by trivial, by trivial⟩
  · rintro _ v ⟨⟨hb', hk'⟩, hi', hvl, hp⟩
    exact ⟨hb', hi', ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp⟩

/-- A node added to the key access path after its last node q, by a klong of
the right kind in q. -/
theorem kd_pathAdd (cv : Nat) (y : NodeId) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view)
    (hb : Book B c w) (hi : KdInv K B w) (a : Option Nat) (q : NodeId) (g h : Nat)
    (hlast : w.path[w.path.length - 1]? = some (a, q)) (hq : (q, g, h) ∈ w.gh)
    (hkl : KindKlong K w g h cv y) :
    WriterWP (pathAdd (some cv) y) c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ++ [(some cv, y)] ∧ v.madeFor = w.madeFor) := by
  have hL : 0 < w.path.length := by
    have := (List.getElem?_eq_some_iff.mp hlast).1
    omega
  refine writerWP_mono (writerWP_and (book_pathAdd B (some cv) y c w hv hb)
    (?_ : WriterWP (pathAdd (some cv) y) c w (fun _ v => KdInv K B v ∧ v.vals = w.vals ∧
      v.path = w.path ++ [(some cv, y)] ∧ v.madeFor = w.madeFor))) ?_
  · simp only [pathAdd, writerWP_modify]
    refine ⟨⟨hi.cache, ?_, hi.made, hi.vals, ?_, hi.madeGh, ?_⟩, by trivial, by trivial, by trivial⟩
    · intro d a' q' cv' y' h1 h2 g' h' hg'
      simp only at h1 h2
      by_cases hd : d + 1 < w.path.length
      · rw [List.getElem?_append_left (by omega)] at h1
        rw [List.getElem?_append_left hd] at h2
        exact hi.path d a' q' cv' y' h1 h2 g' h' hg'
      · have hd2 : d + 1 = w.path.length := by
          have := (List.getElem?_eq_some_iff.mp h2).1
          simp only [List.length_append, List.length_singleton] at this
          omega
        rw [List.getElem?_append_left (by omega)] at h1
        rw [List.getElem?_append_right (by omega), hd2, Nat.sub_self] at h2
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨⟨rfl⟩, rfl⟩ := h2
        have : d = w.path.length - 1 := by omega
        subst this
        rw [hlast] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl⟩ := kd_tag_eq hb hq hg'
        exact hkl
    · intro d a' q' h1 h2
      simp only [List.length_append, List.length_singleton] at h2 h1
      rw [List.getElem?_append_left (by omega)] at h1
      by_cases hd : d + 1 < w.path.length
      · exact hi.pathGh d a' q' h1 hd
      · have : d = w.path.length - 1 := by omega
        subst this
        rw [hlast] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact kd_mem_ids hq
    · intro d a' q' h1
      simp only at h1
      by_cases hd : d + 1 < w.path.length
      · rw [List.getElem?_append_left hd] at h1
        exact hi.pathSome d a' q' h1
      · have hd2 : d + 1 = w.path.length := by
          have := (List.getElem?_eq_some_iff.mp h1).1
          simp only [List.length_append, List.length_singleton] at this
          omega
        rw [List.getElem?_append_right (by omega), hd2, Nat.sub_self] at h1
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp
  · rintro _ v ⟨⟨hb', hk'⟩, hi', hvl, hp, hm⟩
    exact ⟨hb', hi', ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp, hm⟩

theorem kd_pathClear (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hb : Book B c w)
    (hi : KdInv K B w) :
    WriterWP pathClear c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = [] ∧ v.madeFor = w.madeFor) := by
  refine writerWP_mono (writerWP_and (book_pathClear B c w hv hb)
    (?_ : WriterWP pathClear c w (fun _ v => v.nodes = w.nodes ∧ v.gh = w.gh ∧ v.vals = w.vals ∧
      v.madeFor = w.madeFor ∧ v.path = [] ∧ w.next ≤ v.next))) ?_
  · simp only [pathClear, writerWP_modify]
    simp
  · rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hvl, hm, hp, hx⟩
    exact ⟨hb', hi.clear v hn hg hvl hm hp hx, ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp, hm⟩

/-- The space root starts an empty key access path. -/
theorem kd_findRoot (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hb : Book B c w)
    (hi : KdInv K B w) (hp0 : w.path = []) :
    WriterWP findRoot c w (fun r v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = [(none, r)] ∧ v.madeFor = w.madeFor) := by
  refine writerWP_mono (writerWP_and (book_findRoot B c w hv hb)
    (?_ : WriterWP findRoot c w (fun r v => v.nodes = w.nodes ∧ v.gh = w.gh ∧ v.vals = w.vals ∧
      v.madeFor = w.madeFor ∧ v.path = [(none, r)] ∧ w.next ≤ v.next))) ?_
  · simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure]
    simp [hp0]
  · rintro r v ⟨⟨hb', hk'⟩, hn, hg, hvl, hm, hp, hx⟩
    have h0 : KdInv K B { w with path := [(none, r)] } := by
      refine ⟨hi.cache, ?_, hi.made, hi.vals, ?_, hi.madeGh, ?_⟩
      · intro d a q cv y h1 h2
        have := (List.getElem?_eq_some_iff.mp h2).1
        simp at this
      · intro d a q h1 h2
        simp at h2
      · intro d a q h1
        have := (List.getElem?_eq_some_iff.mp h1).1
        simp at this
    exact ⟨hb', h0.frame v hn hg hvl hm hp hx, ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp, hm⟩

end Steps

end SIS.Tree
