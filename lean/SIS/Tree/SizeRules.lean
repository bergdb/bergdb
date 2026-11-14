/-
The tree model (bergdb 024-12, TP5's writer part): a key node holds at most M
klongs. A node of the writer's overlay is `SizedNode` when it has at most M
klongs and starts with a time klong (or has none); with a time klong first, the
last version of a node is no larger than the node.

This file has the rules on single nodes: what each change the writer makes to
a node does to its size. SIS/Tree/WriterSize*.lean take them through the
writer.
-/
import SIS.Tree.CacheGood
import SIS.Tree.MergeLiveOrder

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The invariant -/

/-- No klong, or a time klong first. -/
def TimeFirst (ks : List Klong) : Prop := ks = [] ∨ ∃ t r, ks = Klong.time t :: r

/-- At most M klongs, and a time klong first (or no klong). -/
def SizedNode (p : Params) (n : KNode) : Prop :=
  n.size ≤ p.M ∧ (n.ks = [] ∨ ∃ t r, n.ks = Klong.time t :: r)

/-- The key nodes that the writer can read have at most M klongs. -/
def ViewSizeOK (p : Params) (v : View BVal) : Prop :=
  ∀ x nd, v x = some nd → nd.isData = false → nd.level ≤ p.keyMax → (klongsOf nd.hist).length ≤ p.M

/-- Every node of the writer's overlay has at most M klongs. -/
def WriterSizeOK (p : Params) (w : W) : Prop := ∀ q ∈ w.nodes, SizedNode p q.2

theorem viewSizeOK_rootless (p : Params) (v : View BVal) (hv : ViewSizeOK p v) :
    ViewSizeOK p (rootless v) := by
  intro x n hn hd hl
  unfold rootless at hn
  split at hn
  · cases hn
  · exact hv x n hn hd hl

theorem sized_load (p : Params) (v : View BVal) (hv : ViewSizeOK p v) (x : NodeId)
    (nd : Node BVal) (leaf : Bool) (hx : v x = some nd) (hd : nd.isData = false)
    (hl : nd.level ≤ p.keyMax) : SizedNode p ⟨leaf, klongsOf nd.hist⟩ :=
  ⟨hv x nd hx hd hl, klongsOf_head nd.hist⟩

/-! ## Last versions -/

theorem setCv_length (m : List (Nat × NodeId)) (c : Nat) (y : NodeId) :
    (setCv m c y).length ≤ m.length + 1 := by
  unfold setCv
  split <;> simp

theorem liveFold_length (l : List (Klong × Nat)) (del : List Nat) (m : List (Nat × NodeId)) :
    (l.foldl (fun m (q : Klong × Nat) => match q.1 with
      | .key c y => if del.contains q.2 then m else setCv m c y
      | _ => m) m).length ≤ m.length + l.length := by
  induction l generalizing m with
  | nil => simp
  | cons q l ih =>
    rcases q with ⟨k, i⟩
    simp only [List.foldl_cons, List.length_cons]
    cases k with
    | time t => exact Nat.le_trans (ih m) (by omega)
    | del b => exact Nat.le_trans (ih m) (by omega)
    | key c y =>
      dsimp only
      split
      · have := ih m; omega
      · have := ih (setCv m c y); have := setCv_length m c y; omega

/-- With a time klong first, the last version has at most as many klongs as the
node; of a node without klongs, it has one. -/
theorem KNode.lastVersionGivenDel_size (n : KNode) (t : Time) (del : List Nat)
    (hf : TimeFirst n.ks) :
    1 ≤ (n.lastVersionGivenDel t del).size ∧
      (n.lastVersionGivenDel t del).size - 1 ≤ n.size - 1 := by
  unfold KNode.lastVersionGivenDel KNode.size
  simp only [List.length_cons, List.length_map, List.length_mergeSort]
  refine ⟨by omega, ?_⟩
  rcases hf with he | ⟨u, r, he⟩
  · rw [he]; simp
  · rw [he]
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons]
    refine Nat.le_trans (liveFold_length (r.zipIdx 1) del []) ?_
    simp

theorem KNode.lastVersionGivenDel_le (n : KNode) (t : Time) (del : List Nat) (m : Nat)
    (hf : TimeFirst n.ks) (hs : n.size ≤ m) (h1 : 1 ≤ m) :
    (n.lastVersionGivenDel t del).size ≤ m := by
  have := n.lastVersionGivenDel_size t del hf
  omega

theorem KNode.lastVersionGivenDel_add_le (n : KNode) (t : Time) (del : List Nat) (k m : Nat)
    (hf : TimeFirst n.ks) (hs : n.size + k ≤ m) (h1 : 1 + k ≤ m) :
    (n.lastVersionGivenDel t del).size + k ≤ m := by
  have := n.lastVersionGivenDel_size t del hf
  omega

/-- The live klongs of a node with a time klong first: fewer than its klongs. -/
theorem KNode.live_length_le (n : KNode) (m : Nat) (hf : TimeFirst n.ks) (hs : n.size ≤ m)
    (h1 : 1 ≤ m) : n.live.length + 1 ≤ m := by
  have h := n.lastVersion_size 0
  have h2 := n.lastVersionGivenDel_le 0 n.lastBitmap m hf hs h1
  unfold KNode.cnt at h
  unfold KNode.lastVersion at h
  omega

theorem SizedNode.live (p : Params) (n : KNode) (h : SizedNode p n) (h1 : 1 ≤ p.M) :
    n.live.length + 1 ≤ p.M :=
  n.live_length_le p.M h.2 h.1 h1

/-! ## The last time, and adds -/

/-- The slack of a node at time t: 1 if an add at t puts a time klong first,
else 0. -/
def KNode.slack (n : KNode) (t : Time) : Nat :=
  match n.lastTime with
  | some lt => if lt < t then 1 else 0
  | none => 1

/-- A node's size and its slack: what bounds a run of adds at one time. -/
def KNode.room (n : KNode) (t : Time) : Nat := n.size + n.slack t

theorem KNode.slack_le (n : KNode) (t : Time) : n.slack t ≤ 1 := by
  unfold KNode.slack
  split
  · split <;> omega
  · omega

theorem KNode.size_le_room (n : KNode) (t : Time) : n.size ≤ n.room t := by
  unfold KNode.room; omega

theorem KNode.room_le (n : KNode) (t : Time) :
    n.room t ≤ n.size + (if (n.lastTime == some t) = true then 0 else 1) := by
  unfold KNode.room KNode.slack
  split
  · rename_i lt hl
    rw [hl]
    by_cases ht : lt = t
    · subst ht; simp
    · split <;> simp [ht]
  · rename_i hl
    rw [hl]
    simp

def timeStep (t : Option Time) (k : Klong) : Option Time :=
  match k with
  | .time x => some x
  | _ => t

theorem KNode.lastTime_eq (n : KNode) : n.lastTime = n.ks.foldl timeStep none := rfl

theorem foldl_timeStep_nonTime (ks : List Klong) (k : Klong) (o : Option Time)
    (hk : ∀ u, k ≠ .time u) : (ks ++ [k]).foldl timeStep o = ks.foldl timeStep o := by
  rw [List.foldl_append]
  cases k with
  | time u => exact (hk u rfl).elim
  | key c y => rfl
  | del b => rfl

theorem KNode.add_slack (n : KNode) (t : Time) (k : Klong) (hk : ∀ u, k ≠ .time u) :
    (n.add t k).slack t = 0 := by
  unfold KNode.add
  cases hl : n.lastTime with
  | none =>
    simp only
    unfold KNode.slack
    rw [KNode.lastTime_eq]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    cases k with
    | time u => exact (hk u rfl).elim
    | key c y => simp [timeStep]
    | del b => simp [timeStep]
  | some lt =>
    simp only
    split
    · unfold KNode.slack
      rw [KNode.lastTime_eq]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases k with
      | time u => exact (hk u rfl).elim
      | key c y => simp [timeStep]
      | del b => simp [timeStep]
    · rename_i hlt
      unfold KNode.slack
      rw [KNode.lastTime_eq]
      show (match (n.ks ++ [k]).foldl timeStep none with
        | some lt => if lt < t then 1 else 0
        | none => 1) = 0
      rw [foldl_timeStep_nonTime _ _ _ hk, ← KNode.lastTime_eq, hl]
      simp [hlt]

theorem KNode.add_size (n : KNode) (t : Time) (k : Klong) :
    (n.add t k).size = n.size + n.slack t + 1 := by
  unfold KNode.add KNode.slack KNode.size
  cases n.lastTime with
  | none => simp
  | some lt =>
    simp only
    split <;> simp

theorem KNode.add_room (n : KNode) (t : Time) (k : Klong) (hk : ∀ u, k ≠ .time u) :
    (n.add t k).room t ≤ n.room t + 1 := by
  unfold KNode.room
  rw [n.add_slack t k hk, n.add_size t k]
  omega

theorem KNode.add_size_le (n : KNode) (t : Time) (k : Klong) : (n.add t k).size ≤ n.size + 2 := by
  rw [n.add_size t k]
  unfold KNode.slack
  split
  · split <;> omega
  · omega

theorem timeFirst_add (n : KNode) (t : Time) (k : Klong) (h : TimeFirst n.ks) :
    TimeFirst (n.add t k).ks := by
  rcases h with he | ⟨u, r, he⟩
  · have hl : n.lastTime = none := by rw [KNode.lastTime_eq, he]; rfl
    unfold KNode.add
    rw [hl]
    simp only
    rw [he]
    exact Or.inr ⟨t, [k], rfl⟩
  · rcases n.add_ks t k with h2 | h2 <;> rw [h2, he] <;> exact Or.inr ⟨u, _, rfl⟩

theorem timeFirst_fold_add (ins : List (Nat × NodeId)) (t : Time) (n : KNode)
    (h : TimeFirst n.ks) :
    TimeFirst (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n).ks := by
  induction ins generalizing n with
  | nil => exact h
  | cons q ins ih => exact ih _ (timeFirst_add n t _ h)

theorem fold_add_room (ins : List (Nat × NodeId)) (t : Time) (n : KNode) :
    (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n).room t ≤
      n.room t + ins.length := by
  induction ins generalizing n with
  | nil => simp
  | cons q ins ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (n.add t (.key q.1 q.2))
    have h2 := n.add_room t (.key q.1 q.2) (by intro u hu; cases hu)
    omega

/-- Keys added at one time: at most one time klong more. -/
theorem fold_add_size (ins : List (Nat × NodeId)) (t : Time) (n : KNode) :
    (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n).size ≤
      n.size + ins.length + 1 := by
  have h1 := fold_add_room ins t n
  have h2 := KNode.size_le_room (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n) t
  have h3 := n.slack_le t
  unfold KNode.room at *
  omega

/-! ## Klongs set in place -/

theorem foldl_set_id {α β : Type} (f : β → α → β) (l : List α) (j : Nat) (k : α)
    (hk : ∀ b, f b k = b) (hj : ∀ b x, l[j]? = some x → f b x = b) (b : β) :
    (l.set j k).foldl f b = l.foldl f b := by
  induction l generalizing j b with
  | nil => simp
  | cons a l ih =>
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      rw [hk b, hj b a (by simp)]
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih j (fun b x hx => hj b x (by simpa using hx)) _

def NotTime (k : Klong) : Prop := ∀ u, k ≠ .time u

theorem timeStep_notTime (k : Klong) (hk : NotTime k) (o : Option Time) : timeStep o k = o := by
  cases k with
  | time u => exact (hk u rfl).elim
  | key c y => rfl
  | del b => rfl

theorem KNode.setAt_lastTime (n : KNode) (j : Nat) (k : Klong) (hk : NotTime k)
    (hj : ∀ x, n.ks[j]? = some x → NotTime x) : (n.setAt j k).lastTime = n.lastTime := by
  rw [KNode.lastTime_eq, KNode.lastTime_eq]
  exact foldl_set_id timeStep n.ks j k (fun b => timeStep_notTime k hk b)
    (fun b x hx => timeStep_notTime x (hj x hx) b) none

theorem KNode.setAt_size (n : KNode) (j : Nat) (k : Klong) : (n.setAt j k).size = n.size := by
  simp [KNode.setAt, KNode.size]

theorem KNode.setAt_room (n : KNode) (t : Time) (j : Nat) (k : Klong) (hk : NotTime k)
    (hj : ∀ x, n.ks[j]? = some x → NotTime x) : (n.setAt j k).room t = n.room t := by
  unfold KNode.room KNode.slack
  rw [n.setAt_lastTime j k hk hj, n.setAt_size j k]

theorem timeFirst_setAt (n : KNode) (j : Nat) (k : Klong) (_hk : NotTime k)
    (hj : ∀ x, n.ks[j]? = some x → NotTime x) (h : TimeFirst n.ks) :
    TimeFirst (n.setAt j k).ks := by
  rcases h with he | ⟨u, r, he⟩
  · left; show n.ks.set j k = []; rw [he]; rfl
  · cases j with
    | zero =>
      exfalso
      have := hj (.time u) (by rw [he]; rfl)
      exact this u rfl
    | succ j =>
      right
      refine ⟨u, r.set j k, ?_⟩
      show n.ks.set (j + 1) k = _
      rw [he]; rfl

theorem KNode.repoint_room (n : KNode) (t : Time) (j : Nat) (y : NodeId) :
    (n.repoint j y).room t = n.room t := by
  unfold KNode.repoint
  split
  · rename_i c y' he
    exact n.setAt_room t j _ (by intro u hu; cases hu)
      (by intro x hx; rw [he] at hx; cases hx; intro u hu; cases hu)
  · rfl

theorem KNode.repoint_size (n : KNode) (j : Nat) (y : NodeId) :
    (n.repoint j y).size = n.size := by
  unfold KNode.repoint
  split
  · exact n.setAt_size _ _
  · rfl

theorem timeFirst_repoint (n : KNode) (j : Nat) (y : NodeId) (h : TimeFirst n.ks) :
    TimeFirst (n.repoint j y).ks := by
  unfold KNode.repoint
  split
  · rename_i c y' he
    exact timeFirst_setAt n j _ (by intro u hu; cases hu)
      (by intro x hx; rw [he] at hx; cases hx; intro u hu; cases hu) h
  · exact h

theorem SizedNode.repoint (p : Params) (n : KNode) (j : Nat) (y : NodeId) (h : SizedNode p n) :
    SizedNode p (n.repoint j y) :=
  ⟨by rw [n.repoint_size]; exact h.1, timeFirst_repoint n j y h.2⟩

/-- The test of the writer for "the node's last klong is the transaction's
own bitmap", as in WriterGoodOps.lean's `lastDelFlag`. -/
abbrev lastDelTest (n : KNode) (i : Time) : Bool :=
  (match n.ks.getLast? with
    | some (.del _) => true
    | _ => false) && n.lastTime == some i

theorem lastDelTest_last (n : KNode) (i : Time) (h : lastDelTest n i = true) :
    ∀ x, n.ks[n.size - 1]? = some x → NotTime x := by
  intro x hx
  simp only [lastDelTest, Bool.and_eq_true] at h
  have hl := h.1
  rw [List.getLast?_eq_getElem?] at hl
  unfold KNode.size at hx
  rw [hx] at hl
  intro u hu
  subst hu
  simp at hl

theorem KNode.setLastDel_room (n : KNode) (t i : Time) (bits : List Nat)
    (h : lastDelTest n i = true) : (n.setAt (n.size - 1) (.del bits)).room t = n.room t :=
  n.setAt_room t _ _ (by intro u hu; cases hu) (lastDelTest_last n i h)

theorem timeFirst_setLastDel (n : KNode) (i : Time) (bits : List Nat)
    (h : lastDelTest n i = true) (hf : TimeFirst n.ks) :
    TimeFirst (n.setAt (n.size - 1) (.del bits)).ks :=
  timeFirst_setAt n _ _ (by intro u hu; cases hu) (lastDelTest_last n i h) hf

theorem SizedNode.setLastDel (p : Params) (n : KNode) (i : Time) (bits : List Nat)
    (h : SizedNode p n) (hd : lastDelTest n i = true) :
    SizedNode p (n.setAt (n.size - 1) (.del bits)) :=
  ⟨by rw [n.setAt_size]; exact h.1, timeFirst_setLastDel n i bits hd h.2⟩

theorem SizedNode.add (p : Params) (n : KNode) (t : Time) (k : Klong) (h : TimeFirst n.ks)
    (hs : n.size + 2 ≤ p.M) : SizedNode p (n.add t k) :=
  ⟨by have := n.add_size_le t k; omega, timeFirst_add n t k h⟩

/-- A put's klong in a segment leaf with room, as `setValue` tests it. -/
theorem SizedNode.add_and (p : Params) (n : KNode) (t : Time) (k : Klong) (b : Bool)
    (h : TimeFirst n.ks) (hs : (decide (n.size + 1 < p.M) && b) = true) :
    SizedNode p (n.add t k) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  exact SizedNode.add p n t k h (by omega)

/-- The bitmap of a delete, in place or new: one klong more at most, after
the time klong. -/
theorem KNode.delWrite_room (n : KNode) (t : Time) (bits : List Nat) (hasTransDel : Bool)
    (hT : hasTransDel = lastDelTest n t) :
    (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add t (.del bits)).room t ≤
      n.room t + (if hasTransDel then 0 else 1) := by
  cases hd : hasTransDel with
  | true =>
    simp only [↓reduceIte]
    rw [hd] at hT
    rw [n.setLastDel_room t t bits hT.symm]
    omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact n.add_room t _ (by intro u hu; cases hu)

theorem timeFirst_delWrite (n : KNode) (t : Time) (bits : List Nat) (hasTransDel : Bool)
    (hT : hasTransDel = lastDelTest n t) (hf : TimeFirst n.ks) :
    TimeFirst (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add t (.del bits)).ks := by
  cases hd : hasTransDel with
  | true =>
    simp only [↓reduceIte]
    rw [hd] at hT
    exact timeFirst_setLastDel n t bits hT.symm hf
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact timeFirst_add n t _ hf

/-- A pointer set in place or by a new klong. -/
theorem KNode.ptrWrite_room (n : KNode) (t : Time) (inPlace : Bool) (e cv : Nat) (y : NodeId) :
    (if inPlace then n.repoint e y else n.add t (.key cv y)).room t ≤
      n.room t + (if inPlace then 0 else 1) := by
  cases inPlace with
  | true => simp only [↓reduceIte]; rw [n.repoint_room]; omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact n.add_room t _ (by intro u hu; cases hu)

theorem timeFirst_ptrWrite (n : KNode) (t : Time) (inPlace : Bool) (e cv : Nat) (y : NodeId)
    (hf : TimeFirst n.ks) :
    TimeFirst (if inPlace then n.repoint e y else n.add t (.key cv y)).ks := by
  cases inPlace with
  | true => exact timeFirst_repoint n e y hf
  | false => exact timeFirst_add n t _ hf

/-- LE-b's write with room (`emptyKeyNext`): the klongs it needs fit. -/
theorem SizedNode.lebWrite (p : Params) (n : KNode) (t : Time) (bits : List Nat)
    (hasTransDel inPlace ofTt : Bool) (e : Nat) (y : NodeId) (h : SizedNode p n)
    (hT : hasTransDel = lastDelTest n t) (hO : ofTt = (n.lastTime == some t))
    (hroom : n.size + ((if hasTransDel then 0 else 1) + (if inPlace then 0 else 1) +
      (if ofTt then 0 else 1)) ≤ p.M) :
    SizedNode p (if inPlace then
        (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add t (.del bits)).repoint e y
      else (if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)).add t (.key 0 y)) := by
  have h1 := n.delWrite_room t bits hasTransDel hT
  have h2 := KNode.ptrWrite_room
    (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add t (.del bits)) t inPlace e 0 y
  have h3 := KNode.size_le_room (if inPlace then
        (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add t (.del bits)).repoint e y
      else (if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)).add t (.key 0 y)) t
  have h4 := n.room_le t
  rw [← hO] at h4
  refine ⟨by omega, ?_⟩
  exact timeFirst_ptrWrite _ t inPlace e 0 y (timeFirst_delWrite n t bits hasTransDel hT h.2)

/-- The merge parent's write with room (`mergeParent`): the klongs it needs
fit. -/
theorem SizedNode.mergeWrite (p : Params) (n : KNode) (t : Time) (bits : List Nat)
    (deleteR hasTransDel lInPlace rInPlace ofTt : Bool) (il ir cL : Nat) (m1 : NodeId)
    (m2 : Option (NodeId × Nat)) (kcv : Nat → Nat) (h : SizedNode p n)
    (hT : hasTransDel = lastDelTest n t) (hO : ofTt = (n.lastTime == some t))
    (hroom : n.size + ((if (deleteR && !hasTransDel) then 1 else 0) + (if lInPlace then 0 else 1) +
      (if (m2.isNone || rInPlace) then 0 else 1) + (if ofTt then 0 else 1)) ≤ p.M) :
    SizedNode p (match (generalizing := false) m2 with
      | some (y, g) =>
        if rInPlace then
          (if lInPlace then
            (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).repoint il m1
          else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).add t (.key cL m1)).repoint ir y
        else (if lInPlace then
            (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).repoint il m1
          else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).add t (.key cL m1)).add t (.key (kcv g) y)
      | none =>
        if lInPlace then
          (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
            else n.add t (.del bits)).repoint il m1
        else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
            else n.add t (.del bits)).add t (.key cL m1)) := by
  have h4 := n.room_le t
  rw [← hO] at h4
  have h1 : (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)).room t ≤ n.room t + (if (deleteR && !hasTransDel) then 1 else 0) ∧
      TimeFirst (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)).ks := by
    cases deleteR with
    | false => simp only [Bool.not_false, ↓reduceIte, Bool.false_and]; exact ⟨by omega, h.2⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
      have := n.delWrite_room t bits hasTransDel hT
      refine ⟨?_, timeFirst_delWrite n t bits hasTransDel hT h.2⟩
      cases hasTransDel <;> simp only [Bool.not_true, Bool.not_false, ↓reduceIte,
        Bool.false_eq_true] at this ⊢ <;> omega
  generalize (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)) = n1 at h1 ⊢
  have h2 := KNode.ptrWrite_room n1 t lInPlace il cL m1
  have f2 := timeFirst_ptrWrite n1 t lInPlace il cL m1 h1.2
  generalize (if lInPlace then n1.repoint il m1 else n1.add t (.key cL m1)) = n2 at h2 f2 ⊢
  cases m2 with
  | none =>
    simp only [Option.isNone_none, Bool.true_or, ↓reduceIte] at hroom ⊢
    have := n2.size_le_room t
    exact ⟨by omega, f2⟩
  | some pair =>
    obtain ⟨y, g⟩ := pair
    simp only [Option.isNone_some, Bool.false_or] at hroom ⊢
    have h3 := KNode.ptrWrite_room n2 t rInPlace ir (kcv g) y
    have := KNode.size_le_room (if rInPlace then n2.repoint ir y else n2.add t (.key (kcv g) y)) t
    exact ⟨by omega, timeFirst_ptrWrite n2 t rInPlace ir (kcv g) y f2⟩

/-! ## Prefixes, retargets -/

theorem prefixAt_length (ks : List Klong) (t : Time) : (prefixAt ks t).length ≤ ks.length :=
  (prefixAt_prefix ks t).length_le

theorem timeFirst_prefixAt (ks : List Klong) (t : Time) (h : TimeFirst ks) :
    TimeFirst (prefixAt ks t) := by
  rcases h with he | ⟨u, r, he⟩
  · left; rw [he]; rfl
  · rw [he]
    by_cases hu : u ≤ t
    · right; refine ⟨u, prefixAt r t, ?_⟩
      simp [prefixAt, hu]
    · left; simp [prefixAt, hu]

theorem SizedNode.toPrev (p : Params) (n : KNode) (t : Time) (h : SizedNode p n) :
    SizedNode p (n.toPrev t) :=
  ⟨Nat.le_trans (prefixAt_length n.ks t) h.1, timeFirst_prefixAt n.ks t h.2⟩

theorem SizedNode.mapIdx (p : Params) (n : KNode) (F : Klong × Nat → Klong)
    (hF : ∀ u i, F (.time u, i) = .time u) (h : SizedNode p n) :
    SizedNode p { n with ks := n.ks.zipIdx.map F } := by
  refine ⟨?_, ?_⟩
  · show (n.ks.zipIdx.map F).length ≤ p.M
    simp only [List.length_map, List.length_zipIdx]
    exact h.1
  · rcases h.2 with he | ⟨u, r, he⟩
    · left; show n.ks.zipIdx.map F = []; rw [he]; rfl
    · right
      refine ⟨u, (r.zipIdx 1).map F, ?_⟩
      show n.ks.zipIdx.map F = _
      rw [he, List.zipIdx_cons, List.map_cons, hF]

/-! ## Splits and merges -/

theorem halves_size (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (halves leaf t last ins).1.size ≤ 1 + last.size / 2 + ins.length ∧
      (halves leaf t last ins).2.1.size ≤ 1 + last.size / 2 + ins.length := by
  have hs : ∀ s : List Klong, (if leaf = true then s else
      match s with
      | .key _ y :: r' => .key 0 y :: r'
      | s => s).length = s.length := by
    intro s
    split
    · rfl
    · split <;> simp
  have hd : (last.ks.drop 1).length = last.size - 1 := by simp [KNode.size]
  unfold halves
  dsimp only
  refine ite_both (fun z : KNode × KNode × Nat =>
    z.1.size ≤ 1 + last.size / 2 + ins.length ∧ z.2.1.size ≤ 1 + last.size / 2 + ins.length)
    _ _ _ ?_ ?_
  all_goals
    simp only [KNode.size, List.length_cons, List.length_append, List.length_map,
      List.length_take, List.length_drop] at hd ⊢
    constructor <;> (repeat' split) <;>
      (try (rename_i heq; have := congrArg List.length heq)) <;>
      (try simp only [List.length_cons, List.length_drop] at *) <;> omega

theorem halves_timeFirst (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    TimeFirst (halves leaf t last ins).1.ks ∧ TimeFirst (halves leaf t last ins).2.1.ks := by
  unfold halves
  dsimp only
  exact ite_both (fun z : KNode × KNode × Nat => TimeFirst z.1.ks ∧ TimeFirst z.2.1.ks) _ _ _
    ⟨Or.inr ⟨t, _, rfl⟩, Or.inr ⟨t, _, rfl⟩⟩ ⟨Or.inr ⟨t, _, rfl⟩, Or.inr ⟨t, _, rfl⟩⟩

theorem replaceKlong_length (ks : List Klong) (t c : Nat) (y : NodeId) (out : List Klong)
    (h : replaceKlong ks t c y = .ok (some out)) : out.length = ks.length := by
  have := congrArg List.length (replaceKlong_shape ks t c y out h)
  simpa using this

theorem insertSorted_length (ks : List Klong) (cv : Nat) (y : NodeId) :
    (insertSorted ks cv y).length = ks.length + 1 := by
  induction ks with
  | nil => rfl
  | cons k r ih =>
    unfold insertSorted
    split
    · split <;> simp [ih]
    · simp [ih]

theorem newKlongs_size (t : Time) (l : List (Nat × NodeId)) : (newKlongs t l).length = l.length + 1 := by
  simp [newKlongs]

theorem splitMerged_first (M cap : Nat) (inr : Bool) (e : List (Nat × NodeId))
    (hcap : cap + 1 ≤ M) (he : e.length + 2 ≤ 2 * M) :
    (splitMerged inr cap e).1.length + 1 ≤ M := by
  unfold splitMerged
  by_cases hle : e.length ≤ cap
  · simp only [hle, ↓reduceIte]; omega
  · simp only [hle, ↓reduceIte, List.length_take]; omega

theorem splitMerged_second (M cap : Nat) (inr : Bool) (e : List (Nat × NodeId))
    (he : e.length + 2 ≤ 2 * M) (ks2 : List (Nat × NodeId)) (g : Nat)
    (h : (splitMerged inr cap e).2 = some (ks2, g)) : ks2.length + 1 ≤ M := by
  unfold splitMerged at h
  by_cases hle : e.length ≤ cap
  · simp only [hle, ↓reduceIte] at h; cases h
  · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    cases inr <;> simp only [Bool.false_eq_true, ↓reduceIte, renameHead_length, List.length_drop] <;> omega

/-- The first node of a merge: at most c klongs, or half of at most 2 (M - 1). -/
theorem mergeKlongs_first (M cap cR : Nat) (inr : Bool) (lvL lvR : List (Nat × NodeId))
    (hcap : cap + 1 ≤ M) (hL : lvL.length + 1 ≤ M) (hR : lvR.length + 1 ≤ M) (t : Time) :
    (newKlongs t (mergeKlongs inr cap cR lvL lvR).1).length ≤ M := by
  rw [newKlongs_size]
  have := splitMerged_first M cap inr (mergeList inr cR lvL lvR) hcap
    (by rw [mergeList_length]; omega)
  unfold mergeKlongs
  omega

/-- The second node of a merge into two: at most half of 2 (M - 1) klongs. -/
theorem mergeKlongs_second (M cap cR : Nat) (inr : Bool) (lvL lvR : List (Nat × NodeId))
    (hL : lvL.length + 1 ≤ M) (hR : lvR.length + 1 ≤ M) (ks2 : List (Nat × NodeId)) (g : Nat)
    (h : (mergeKlongs inr cap cR lvL lvR).2 = some (ks2, g)) (t : Time) :
    (newKlongs t ks2).length ≤ M := by
  rw [newKlongs_size]
  have := splitMerged_second M cap inr (mergeList inr cR lvL lvR)
    (by rw [mergeList_length]; omega) ks2 g h
  omega

end SIS.Tree
