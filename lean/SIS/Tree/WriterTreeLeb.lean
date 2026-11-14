/-
LE-b at the writer (bergdb 024-22, `OpTreeOK`; `emptyKeyNext`): the empty key
of an inner node takes the pointer of the next live klong, whose compare value
is deleted. With room and no compaction it keeps the writer's tree
(`writerWP_emptyKeyNext_tree`): the next child is still named once, the empty
key's old child is left behind.
-/
import SIS.Tree.WriterTreeCollapse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- LE-b's choice of the next klong, one klong at a time. -/
def lebStep (del0 : List Nat) (best : Option (Nat × Nat × NodeId)) (q : Klong × Nat) :
    Option (Nat × Nat × NodeId) :=
  match q.1 with
  | .key cv y =>
    if del0.contains q.2 then best else
      match best with
      | none => some (q.2, cv, y)
      | some (_, jcv, _) => if cv ≤ jcv then some (q.2, cv, y) else best
  | _ => best

def LebOK (ks : List Klong) (del0 : List Nat) (best : Option (Nat × Nat × NodeId)) : Prop :=
  ∀ i cv y, best = some (i, cv, y) → ks[i]? = some (.key cv y) ∧ i ∉ del0 ∧
    ∀ j y', i < j → ks[j]? = some (.key cv y') → j ∈ del0

theorem lebOK_step (ks : List Klong) (del0 : List Nat) (best : Option (Nat × Nat × NodeId))
    (k : Klong) (hb : LebOK ks del0 best) : LebOK (ks ++ [k]) del0 (lebStep del0 best (k, ks.length)) := by
  have keep : ∀ i cv y, best = some (i, cv, y) → (∀ y', k = .key cv y' → ks.length ∈ del0) →
      (ks ++ [k])[i]? = some (.key cv y) ∧ i ∉ del0 ∧
        ∀ j y', i < j → (ks ++ [k])[j]? = some (.key cv y') → j ∈ del0 := by
    intro i cv y hbest hk
    obtain ⟨hy, hd, hl⟩ := hb i cv y hbest
    have hi : i < ks.length := by rw [List.getElem?_eq_some_iff] at hy; exact hy.1
    refine ⟨by rw [getElem?_append_single_lt _ _ _ hi]; exact hy, hd, ?_⟩
    intro j y' hij hj
    rcases Nat.lt_trichotomy j ks.length with h1 | h1 | h1
    · rw [getElem?_append_single_lt _ _ _ h1] at hj; exact hl j y' hij hj
    · subst h1; rw [getElem?_append_single_eq] at hj
      simp only [Option.some.injEq] at hj
      exact hk y' hj
    · rw [getElem?_append_single_gt _ _ _ h1] at hj; cases hj
  have fresh : ∀ cv y, k = .key cv y → ks.length ∉ del0 →
      (ks ++ [k])[ks.length]? = some (.key cv y) ∧ ks.length ∉ del0 ∧
        ∀ j y', ks.length < j → (ks ++ [k])[j]? = some (.key cv y') → j ∈ del0 := by
    intro cv y hk hd
    refine ⟨by rw [getElem?_append_single_eq, hk], hd, ?_⟩
    intro j y' hij hj
    rw [getElem?_append_single_gt _ _ _ hij] at hj; cases hj
  intro i cv y h
  unfold lebStep at h
  cases k with
  | time t => exact keep i cv y h (fun _ he => by cases he)
  | del b => exact keep i cv y h (fun _ he => by cases he)
  | key c0 y0 =>
    simp only at h
    by_cases hd : del0.contains ks.length = true
    · simp only [hd, ↓reduceIte] at h
      exact keep i cv y h (fun _ _ => by simpa using hd)
    · have hd' : ks.length ∉ del0 := by simpa using hd
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      cases best with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact fresh _ _ rfl hd'
      | some b =>
        rcases b with ⟨i0, jcv, jy⟩
        simp only at h
        by_cases hle : c0 ≤ jcv
        · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact fresh _ _ rfl hd'
        · simp only [hle, ↓reduceIte] at h
          refine keep i cv y h (fun y' he => ?_)
          exfalso
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          simp only [Klong.key.injEq] at he
          omega

theorem lebOK_fold (del0 : List Nat) (ks : List Klong) :
    LebOK ks del0 (ks.zipIdx.foldl (lebStep del0) none) := by
  have key : ∀ rs : List Klong, LebOK rs.reverse del0 (rs.reverse.zipIdx.foldl (lebStep del0) none) := by
    intro rs
    induction rs with
    | nil => intro i cv y h; cases h
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact lebOK_step rs.reverse del0 _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- LE-b's node with room, its choices free: the transaction's own bitmap set
in place or added, the empty key's klong pointed in place or added. -/
def lebNode (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId) : KNode :=
  let union := bitsUnion n.lastBitmap (n.bitsOf jcv)
  let n1 := if htd then n.setAt (n.size - 1) (.del union) else n.add tt (.del union)
  if lip then n1.repoint e jy else n1.add tt (.key 0 jy)

theorem need_le_three (b1 b2 b3 : Bool) :
    ((if b1 = true then 0 else 1) + (if b2 = true then 0 else 1)) + (if b3 = true then 0 else 1) ≤ 3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> simp

end SIS.Tree
