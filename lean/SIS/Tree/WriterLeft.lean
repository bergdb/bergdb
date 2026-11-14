/-
The tree model (bergdb 024-12, TP7): the empty key in every inner node of the
writer's overlay (`LeftCache`, SIS/Tree/OverlayLeft.lean). This file: the rules
on nodes. An inner node keeps a live klong of the empty key (`Live0`) when a
key klong is added, when a bitmap is added that does not delete that klong,
and when a pointer changes in place; a last version starts with the empty key
(`Head0`) when the node has it live, and so do the lists that the splits and
the merges make of such a last version.
-/
import SIS.Tree.OverlayLeft
import SIS.Tree.WriterNonemptyRun
import SIS.Tree.NodeMap
import SIS.Tree.PhysicalSelection

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A last version that starts with the empty key: a time klong, then a klong
of compare value 0. -/
def Head0 (ks : List Klong) : Prop := ∃ t y r, ks = Klong.time t :: Klong.key 0 y :: r

/-- A klong of the empty key that bitmap `del` does not delete. -/
def Live0Given (ks : List Klong) (del : List Nat) : Prop :=
  ∃ i y, ks[i]? = some (Klong.key 0 y) ∧ del.contains i = false

/-! ## Lists without bitmaps -/

theorem left_getElem?_append {α : Type} (l l' : List α) (i : Nat) (a : α) (h : l[i]? = some a) :
    (l ++ l')[i]? = some a := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hi]
  exact h

theorem lastBitmapOf_append_nodel (a b : List Klong) (hd : ∀ bits, Klong.del bits ∉ b) :
    lastBitmapOf (a ++ b) = lastBitmapOf a := by
  unfold lastBitmapOf
  rw [List.foldl_append]
  generalize a.foldl _ [] = d
  induction b generalizing d with
  | nil => rfl
  | cons k b ih =>
    have ht : ∀ bits, Klong.del bits ∉ b := fun bits hb => hd bits (List.mem_cons_of_mem _ hb)
    cases k with
    | time t => exact ih ht d
    | key c y => exact ih ht d
    | del bits => exact absurd List.mem_cons_self (hd bits)

theorem left_flat_nodel (i : Time) (ks : List Klong) (hf : FlatAt i ks) :
    ∀ bits, Klong.del bits ∉ ks := by
  obtain ⟨r, rfl, hr⟩ := hf
  intro bits hm
  rcases List.mem_cons.mp hm with h | h
  · cases h
  · obtain ⟨cv, y, h'⟩ := hr _ h
    cases h'

/-- A list that starts with the empty key and holds no bitmap: an inner node of
it has the empty key live. -/
theorem left_of_head0_nodel (leaf : Bool) (ks : List Klong) (hh : Head0 ks)
    (hd : ∀ bits, Klong.del bits ∉ ks) : LeftNode ⟨leaf, ks⟩ := by
  intro _
  obtain ⟨t, y, r, rfl⟩ := hh
  refine ⟨List.cons_ne_nil _ _, 1, y, rfl, ?_⟩
  show (lastBitmapOf _).contains 1 = false
  rw [lastBitmapOf_no_delete _ hd]
  rfl

theorem left_of_head0_flat (leaf : Bool) (i : Time) (ks : List Klong) (hf : FlatAt i ks)
    (hh : Head0 ks) : LeftNode ⟨leaf, ks⟩ :=
  left_of_head0_nodel leaf ks hh (left_flat_nodel i ks hf)

theorem left_leaf (n : KNode) (h : n.leaf = true) : LeftNode n := by
  intro hl; rw [h] at hl; cases hl

/-! ## `Live0` kept -/

theorem Live0.append_nodel {n : KNode} (h : Live0 n) (leaf : Bool) (b : List Klong)
    (hd : ∀ bits, Klong.del bits ∉ b) : Live0 ⟨leaf, n.ks ++ b⟩ := by
  obtain ⟨i, y, hi, hc⟩ := h
  refine ⟨i, y, left_getElem?_append _ _ _ _ hi, ?_⟩
  show (lastBitmapOf (n.ks ++ b)).contains i = false
  rw [lastBitmapOf_append_nodel _ _ hd]
  exact hc

theorem Live0.add_key {n : KNode} (h : Live0 n) (t : Time) (c : Nat) (y : NodeId) :
    Live0 (n.add t (.key c y)) := by
  have hl : (n.add t (.key c y)).leaf = n.leaf := KNode.add_leaf _ _ _
  rcases n.add_ks t (.key c y) with he | he
  · have := h.append_nodel n.leaf [.time t, .key c y] (by simp)
    obtain ⟨i, z, hi, hc⟩ := this
    exact ⟨i, z, by rw [he]; exact hi, by
      show (lastBitmapOf (n.add t (.key c y)).ks).contains i = false
      rw [he]; exact hc⟩
  · have := h.append_nodel n.leaf [.key c y] (by simp)
    obtain ⟨i, z, hi, hc⟩ := this
    exact ⟨i, z, by rw [he]; exact hi, by
      show (lastBitmapOf (n.add t (.key c y)).ks).contains i = false
      rw [he]; exact hc⟩

theorem Live0.fold_add {n : KNode} (h : Live0 n) (i : Time) (ins : List (Nat × NodeId)) :
    Live0 (ins.foldl (fun n (q : Nat × NodeId) => n.add i (.key q.1 q.2)) n) := by
  induction ins generalizing n with
  | nil => exact h
  | cons q ins ih => exact ih (h.add_key i q.1 q.2)

theorem LeftNode.add_key {n : KNode} (h : LeftNode n) (t : Time) (c : Nat) (y : NodeId) :
    LeftNode (n.add t (.key c y)) := by
  intro hl
  rw [KNode.add_leaf] at hl
  exact ⟨nex_add_ne _ _ _, (h hl).2.add_key t c y⟩

theorem LeftNode.fold_add {n : KNode} (h : LeftNode n) (i : Time) (ins : List (Nat × NodeId)) :
    LeftNode (ins.foldl (fun n (q : Nat × NodeId) => n.add i (.key q.1 q.2)) n) := by
  intro hl
  rw [bk_foldl_add_leaf] at hl
  refine ⟨?_, (h hl).2.fold_add i ins⟩
  intro he
  exact (h hl).1 (nex_fold_nil n i ins he)

/-- A new bitmap that does not delete the empty key's klong. -/
theorem left_add_del (n : KNode) (t : Time) (bits : List Nat) (h : Live0Given n.ks bits) :
    LeftNode (n.add t (.del bits)) := by
  intro _
  refine ⟨nex_add_ne _ _ _, ?_⟩
  obtain ⟨i, y, hi, hc⟩ := h
  refine ⟨i, y, ?_, by rw [KNode.add_delete_lastBitmap]; exact hc⟩
  rcases n.add_ks t (.del bits) with he | he <;> rw [he] <;> exact left_getElem?_append _ _ _ _ hi

theorem left_set_last_del (ks : List Klong) (b : List Nat) (hne : ks ≠ []) :
    lastBitmapOf (ks.set (ks.length - 1) (.del b)) = b := by
  obtain ⟨init, last, rfl⟩ := List.eq_nil_or_concat ks |>.resolve_left hne
  rw [List.concat_eq_append, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.set_append_right _ _ (Nat.le_refl _)]
  simp only [Nat.sub_self, List.set_cons_zero]
  exact lastBitmapOf_append_delete _ _

/-- The transaction's own bitmap, the node's last klong, set to bits that do not
delete the empty key's klong. -/
theorem left_setAt_del (n : KNode) (bits : List Nat) (b0 : List Nat)
    (hlast : n.ks.getLast? = some (.del b0)) (h : Live0Given n.ks bits) :
    LeftNode (n.setAt (n.size - 1) (.del bits)) := by
  intro _
  obtain ⟨i, y, hi, hc⟩ := h
  have hne : n.ks ≠ [] := by intro he; rw [he] at hlast; cases hlast
  have hil : i ≠ n.ks.length - 1 := by
    intro he
    rw [List.getLast?_eq_getElem?, ← he, hi] at hlast
    cases hlast
  refine ⟨by simp [KNode.setAt, hne], i, y, ?_, ?_⟩
  · show (n.ks.set (n.ks.length - 1) _)[i]? = _
    rw [List.getElem?_set_ne (Ne.symm hil)]
    exact hi
  · show (lastBitmapOf (n.ks.set (n.ks.length - 1) _)).contains i = false
    rw [left_set_last_del _ _ hne]
    exact hc

/-! ## Shapes: pointers changed in place -/

theorem left_shape_getElem? (a b : List Klong) (h : a.map klongShape = b.map klongShape)
    (i : Nat) (y : NodeId) (c : Nat) (hi : a[i]? = some (.key c y)) :
    ∃ y', b[i]? = some (.key c y') := by
  have h1 : (a.map klongShape)[i]? = some (.key c 0) := by simp [hi, klongShape]
  rw [h] at h1
  simp only [List.getElem?_map] at h1
  cases hb : b[i]? with
  | none => rw [hb] at h1; cases h1
  | some k =>
    rw [hb] at h1
    cases k with
    | key c' y' =>
      simp [klongShape] at h1
      exact ⟨y', by rw [h1]⟩
    | time t => simp [klongShape] at h1
    | del bs => simp [klongShape] at h1

theorem Live0.of_shape {n : KNode} (h : Live0 n) (n' : KNode)
    (hs : n.ks.map klongShape = n'.ks.map klongShape) : Live0 n' := by
  obtain ⟨i, y, hi, hc⟩ := h
  obtain ⟨y', hy'⟩ := left_shape_getElem? _ _ hs i y 0 hi
  refine ⟨i, y', hy', ?_⟩
  show (lastBitmapOf n'.ks).contains i = false
  rw [← lastBitmapOf_map_shape n'.ks, ← hs, lastBitmapOf_map_shape]
  exact hc

theorem LeftNode.of_shape {n : KNode} (h : LeftNode n) (n' : KNode) (hl : n'.leaf = n.leaf)
    (hs : n.ks.map klongShape = n'.ks.map klongShape) : LeftNode n' := by
  intro hl'
  rw [hl] at hl'
  obtain ⟨hne, h0⟩ := h hl'
  refine ⟨?_, h0.of_shape n' hs⟩
  intro he
  rw [he] at hs
  exact hne (List.map_eq_nil_iff.mp hs)

theorem Head0.of_shape {ks : List Klong} (h : Head0 ks) (ks' : List Klong)
    (hs : ks.map klongShape = ks'.map klongShape) : Head0 ks' := by
  obtain ⟨t, y, r, rfl⟩ := h
  match ks', hs with
  | a :: b :: r', hs =>
    simp only [List.map_cons, List.cons.injEq] at hs
    obtain ⟨ha, hb, _⟩ := hs
    cases a <;> simp [klongShape] at ha
    cases b <;> simp [klongShape] at hb
    subst ha; subst hb
    exact ⟨_, _, _, rfl⟩
  | [], hs => simp at hs
  | [_], hs => simp at hs

theorem left_repoint_shape (n : KNode) (e : Nat) (y : NodeId) :
    n.ks.map klongShape = (n.repoint e y).ks.map klongShape := by
  unfold KNode.repoint
  split
  · rename_i c y0 he
    show _ = (n.ks.set e (.key c y)).map klongShape
    rw [List.map_set]
    have : klongShape (.key c y) = (n.ks.map klongShape)[e]?.getD (.key c 0) := by
      simp [he, klongShape]
    apply List.ext_getElem?
    intro j
    by_cases hj : j = e
    · subst hj
      have hlt : j < n.ks.length := (List.getElem?_eq_some_iff.mp he).1
      rw [List.getElem?_set_self (by simpa using hlt), List.getElem?_map, he]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm hj)]
  · rfl

theorem left_zipIdx_shape (ks : List Klong) (F : Klong × Nat → Klong)
    (hF : ∀ q, klongShape (F q) = klongShape q.1) :
    ks.map klongShape = (ks.zipIdx.map F).map klongShape := by
  rw [List.map_map]
  have : (klongShape ∘ F) = (klongShape ∘ Prod.fst) := by funext q; exact hF q
  rw [this, ← List.map_map, List.zipIdx_map_fst]

theorem LeftNode.repoint {n : KNode} (h : LeftNode n) (e : Nat) (y : NodeId) :
    LeftNode (n.repoint e y) :=
  h.of_shape _ (bk_repoint_leaf n e y) (left_repoint_shape n e y)

/-! ## Last versions -/

/-- The last version given a bitmap that does not delete a klong of the empty
key starts with the empty key. -/
theorem left_head0_lastVersionGivenDel (n : KNode) (t : Time) (del : List Nat)
    (h : Live0Given n.ks del) : Head0 (n.lastVersionGivenDel t del).ks := by
  obtain ⟨i, y, hi, hc⟩ := h
  obtain ⟨pairs, he, hord⟩ := n.lastVersionGivenDel_order t del
  have hk := (n.lastVersionGivenDel_has_key t del 0).mpr
    ⟨y, i, List.mem_zipIdx_iff_getElem?.mpr hi, by simpa using hc⟩
  rw [he] at hk
  have hk' : 0 ∈ pairs.map Prod.fst := by
    simp only [List.mem_filterMap, List.mem_cons, List.mem_map] at hk
    obtain ⟨k, hk1, hk2⟩ := hk
    rcases hk1 with rfl | ⟨q, hq, rfl⟩
    · simp at hk2
    · simp at hk2
      exact List.mem_map.mpr ⟨q, hq, hk2⟩
  clear hk
  rw [he]
  match pairs, hord, hk' with
  | p :: rest, hord, hk =>
    have hp : p.1 = 0 := by
      rcases List.mem_cons.mp hk with h0 | h0
      · exact h0.symm
      · obtain ⟨q, hq, hq0⟩ := List.mem_map.mp h0
        have := (List.pairwise_cons.mp hord).1 q hq
        omega
    obtain ⟨a, b⟩ := p
    simp only at hp
    subst hp
    exact ⟨t, b, _, rfl⟩

theorem left_head0_lastVersion (n : KNode) (t : Time) (h : Live0 n) :
    Head0 (n.lastVersion t).ks := left_head0_lastVersionGivenDel n t n.lastBitmap h

/-- The bitmap of a delete of a compare value other than the empty key's keeps
the empty key's klong live. -/
theorem left_given_union (n : KNode) (cv : Nat) (hcv : cv ≠ 0) (h : Live0 n) :
    Live0Given n.ks (bitsUnion n.lastBitmap (n.bitsOf cv)) := by
  obtain ⟨i, y, hi, hc⟩ := h
  refine ⟨i, y, hi, ?_⟩
  have hn : i ∉ bitsUnion n.lastBitmap (n.bitsOf cv) := by
    rw [mem_bitsUnion_iff]
    rintro (h1 | h1)
    · simp [h1] at hc
    · exact n.not_mem_bitsOf_of_key_ne 0 cv y i (List.mem_zipIdx_iff_getElem?.mpr hi)
        (Ne.symm hcv) h1
  simpa using hn

/-! ## Lists that keep the head -/

theorem Head0.append {ks : List Klong} (h : Head0 ks) (l : List Klong) : Head0 (ks ++ l) := by
  obtain ⟨t, y, r, rfl⟩ := h
  exact ⟨t, y, r ++ l, rfl⟩

theorem Head0.add {n : KNode} (h : Head0 n.ks) (t : Time) (k : Klong) : Head0 (n.add t k).ks := by
  rcases n.add_ks t k with he | he <;> rw [he] <;> exact h.append _

theorem Head0.insertKey {ks : List Klong} (h : Head0 ks) (g : Nat) (y : NodeId) :
    Head0 (insertSorted ks g y) := by
  obtain ⟨t, z, r, rfl⟩ := h
  refine ⟨t, z, insertSorted r g y, ?_⟩
  simp [insertSorted]

theorem Head0.replaceK {ks : List Klong} (h : Head0 ks) (t : Time) (c : Nat) (y : NodeId)
    (out : List Klong) (he : replaceKlong ks t c y = .ok (some out)) : Head0 out :=
  h.of_shape out (replaceKlong_shape ks t c y out he).symm

/-- The loop of a time split changes no state and keeps the head. -/
theorem left_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun l v => v = w ∧ (Head0 last.ks → Head0 l.ks)) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  suffices hs : ∀ (P : List Klong → Prop), (∀ ks t c y out, P ks →
      replaceKlong ks t c y = .ok (some out) → P out) → (∀ n t k, P n.ks → P (KNode.add n t k).ks) →
      ∀ last : KNode, WriterWP (ins.foldlM (fun last (cv, y) =>
        match replaceKlong last.ks c.i cv y with
        | .error e => throw e
        | .ok (some ks) => pure { last with ks := ks }
        | .ok none => pure (last.add c.i (.key cv y))) last) c w
          (fun l v => v = w ∧ (P last.ks → P l.ks)) by
    exact hs Head0 (fun ks t c y out h he => h.replaceK t c y out he)
      (fun n t k h => h.add t k) last
  intro P hr ha
  induction ins with
  | nil => intro last; simp only [List.foldlM_nil, writerWP_pure]; simp
  | cons q ins ih =>
    intro last
    rcases q with ⟨cv, y⟩
    rw [List.foldlM_cons, writerWP_bind]
    dsimp only
    split
    · exact writerWP_throw _ _ _ _
    · rename_i ks hks
      simp only [writerWP_pure]
      refine writerWP_mono (ih _) ?_
      rintro l v ⟨rfl, hl⟩
      exact ⟨rfl, fun h => hl (hr _ _ _ _ _ h hks)⟩
    · simp only [writerWP_pure]
      refine writerWP_mono (ih _) ?_
      rintro l v ⟨rfl, hl⟩
      exact ⟨rfl, fun h => hl (ha _ _ _ h)⟩

/-! ## A space split's halves -/

theorem left_halves (t : Time) (last : KNode) (ins : List (Nat × NodeId)) (h : Head0 last.ks)
    (hs : 3 ≤ last.size) (hk : ∀ k ∈ last.ks.drop 1, ∃ cv y, k = Klong.key cv y) :
    Head0 (halves false t last ins).1.ks ∧ Head0 (halves false t last ins).2.1.ks := by
  obtain ⟨t0, y, r, hl⟩ := h
  have hlen : last.size = r.length + 2 := by simp [KNode.size, hl]
  have hr : 1 ≤ r.length := by omega
  have hb : last.ks.drop 1 = Klong.key 0 y :: r := by rw [hl]; rfl
  rw [hb] at hk
  have hm : (last.size - 1) / 2 + 1 - 1 = ((r.length + 1) / 2 - 1) + 1 := by omega
  have hlt : (r.length + 1) / 2 - 1 < r.length := by omega
  obtain ⟨c1, y1, hc1⟩ := hk r[(r.length + 1) / 2 - 1] (List.mem_cons_of_mem _ (List.getElem_mem _))
  have hdrop : (Klong.key 0 y :: r).drop (((r.length + 1) / 2 - 1) + 1) =
      Klong.key c1 y1 :: r.drop ((r.length + 1) / 2) := by
    rw [List.drop_succ_cons, List.drop_eq_getElem_cons hlt, hc1]
    congr 2
    omega
  unfold halves
  simp only [hb, hm, hdrop, List.take_succ_cons, List.head?_cons, Bool.false_eq_true,
    ↓reduceIte, List.cons_append]
  repeat' split
  all_goals exact ⟨⟨t, y, _, rfl⟩, ⟨t, y1, _, rfl⟩⟩

/-! ## The merges -/

theorem left_newKlongs (leaf : Bool) (t : Time) (l : List (Nat × NodeId))
    (h : l.head?.map (·.1) = some 0) : LeftNode ⟨leaf, newKlongs t l⟩ := by
  match l, h with
  | (a, y) :: r, h =>
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h
    subst h
    exact left_of_head0_nodel leaf _ ⟨t, y, _, rfl⟩ (by
      intro bits hm
      simp only [newKlongs, List.map_cons, List.mem_cons, List.mem_map] at hm
      rcases hm with h1 | h1 | ⟨q, _, h1⟩ <;> cases h1)

theorem left_mergeKlongs (cap cR : Nat) (lvL lvR : List (Nat × NodeId)) (hcap : 1 ≤ cap)
    (hL : lvL.head?.map (·.1) = some 0) :
    (mergeKlongs true cap cR lvL lvR).1.head?.map (·.1) = some 0 ∧
    ∀ ks2 g2, (mergeKlongs true cap cR lvL lvR).2 = some (ks2, g2) →
      ks2.head?.map (·.1) = some 0 := by
  match lvL, hL with
  | (a, y) :: r, hL =>
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hL
    subst hL
    unfold mergeKlongs splitMerged
    generalize he : mergeList true cR ((0, y) :: r) lvR = e
    have he0 : e.head? = some (0, y) := by rw [← he]; simp [mergeList]
    have hpos : 1 ≤ e.length := by
      cases e with
      | nil => cases he0
      | cons _ _ => simp
    split
    · refine ⟨by rw [he0]; rfl, ?_⟩
      intro _ _ h; cases h
    · rename_i hgt
      refine ⟨?_, ?_⟩
      · rw [List.head?_take]
        have : (e.length + 1) / 2 ≠ 0 := by omega
        simp [this, he0]
      · intro ks2 g2 h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        have hlt : (e.length + 1) / 2 < e.length := by omega
        rw [List.drop_eq_getElem_cons hlt]
        rfl

/-! ## The merge's compare values -/

/-- What the merge's selector keeps: the index of cx, the next compare value
above it, the next below it. -/
def LeftMergeOrd (ks : List Klong) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) : Prop :=
  (∀ i, acc.1 = some i → ∃ y, ks[i]? = some (.key cx y)) ∧
  (∀ i a, acc.2.1 = some (i, a) → cx < a ∧ ∃ y, ks[i]? = some (.key a y)) ∧
  (∀ i b, acc.2.2 = some (i, b) → b < cx ∧ ∃ y, ks[i]? = some (.key b y))

theorem left_mergeStep_ord (ks : List Klong) (del : List Nat) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) (q : Klong × Nat)
    (ha : LeftMergeOrd ks cx acc) (hq : q ∈ ks.zipIdx) :
    LeftMergeOrd ks cx (mergePhysicalStep del cx acc q) := by
  rcases q with ⟨k, i⟩
  have hi := List.mem_zipIdx_iff_getElem?.mp hq
  cases k with
  | time t => exact ha
  | del bits => exact ha
  | key cv y =>
    unfold mergePhysicalStep
    dsimp only
    split
    · exact ha
    · split
      · rename_i _ hcv
        have hcv' : cv = cx := by simpa using hcv
        subst hcv'
        refine ⟨?_, ha.2.1, ha.2.2⟩
        intro j hj; cases hj; exact ⟨y, hi⟩
      · split
        · rename_i _ _ hlt
          refine ⟨ha.1, ?_, ha.2.2⟩
          cases hp : acc.2.1 with
          | none => intro j a he; cases he; exact ⟨hlt, y, hi⟩
          | some p =>
            rcases p with ⟨j0, a0⟩
            dsimp only
            split
            · intro j a he; cases he; exact ⟨hlt, y, hi⟩
            · intro j a he; exact ha.2.1 j a (by rw [hp]; exact he)
        · rename_i hne hnlt
          have hlt : cv < cx := by
            have : cv ≠ cx := by simpa using hne
            omega
          refine ⟨ha.1, ha.2.1, ?_⟩
          cases hp : acc.2.2 with
          | none => intro j b he; cases he; exact ⟨hlt, y, hi⟩
          | some p =>
            rcases p with ⟨j0, b0⟩
            dsimp only
            split
            · intro j b he; cases he; exact ⟨hlt, y, hi⟩
            · intro j b he; exact ha.2.2 j b (by rw [hp]; exact he)

theorem left_mergeIdx_ord (n : KNode) (cx : Nat) : LeftMergeOrd n.ks cx (mergeIdx n cx) := by
  have hg : ∀ (xs : List (Klong × Nat)), (∀ q ∈ xs, q ∈ n.ks.zipIdx) →
      ∀ acc, LeftMergeOrd n.ks cx acc →
        LeftMergeOrd n.ks cx (xs.foldl (mergePhysicalStep n.lastBitmap cx) acc) := by
    intro xs
    induction xs with
    | nil => intro _ acc ha; exact ha
    | cons q xs ih =>
      intro hx acc ha
      exact ih (fun a ha => hx a (List.mem_cons_of_mem q ha)) _
        (left_mergeStep_ord n.ks n.lastBitmap cx acc q ha (hx q List.mem_cons_self))
  exact hg n.ks.zipIdx (fun q hq => hq) _ ⟨(fun i h => by cases h), (fun i a h => by cases h),
    (fun i b h => by cases h)⟩

end SIS.Tree
