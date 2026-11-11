/-
The trace checker's instance meets what the model assumes of the function
`live` (bergdb 024-09, step A2).

Two of the model's assumptions are about the function `Spec.live` alone, for
every history, so no check of a trace can establish them: `SpecOK.liveSub` (a
live child is a pointee of an entry) and `LiveAppend`
(SIS/Phys.lean: entries added at the end of a history give no
live child but their own pointees), which gives `PhysStep.liveNew`. This file
proves both for `blive`, the live children of the BergDB instance
(Check/Trace.lean): a key entry sets its compare value's child to its own
pointee, a delete entry only clears compare values, and a root pointer or a top
entry replaces the one before it by its own pointee.

With that, `PhysRunOK` holds for the instance of every trace (`bspec`) in a run
that meets `RunOK` and has TREE after every transaction (`bspec_physRunOK`,
`bspec_physRunOK_evict`): the assumption of the theorems of lazy reading and of
the theorems with handles that the checker did not check is a consequence of
those that C-A checks. Since 024-09's follow-up those theorems assume
`LiveAppend` and TREE in its place; for a trace's instance `LiveAppend` is
`bspec_liveAppend`.

Not part of the trusted part, and not part of the checker's program.
-/
import Check.Trace
import SIS.Proof.PhysAssumptions
import SIS.Proof.HandleReadT

namespace SIS.Check

open SIS

/-- The state of `blive`'s fold: the child of each compare value (none when
deleted), the last root pointer, the last top entry. -/
abbrev LState := List (Nat × Option Nat) × Option Nat × Option Nat

/-- One entry of `blive`'s fold. -/
def bstep (acc : LState) (e : Entry BVal) : LState :=
  match e.val with
  | .key c y => (setAssoc acc.1 c (some y), acc.2.1, acc.2.2)
  | .del cs =>
    (cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) acc.1,
      acc.2.1, acc.2.2)
  | .rootKey y => (acc.1, some y, acc.2.2)
  | .top z => (acc.1, acc.2.1, some z)
  | _ => acc

/-- The live children that a state of `blive`'s fold gives. -/
def bout (st : LState) : List NodeId :=
  ((st.1.filterMap (·.2)) ++ st.2.1.toList ++ st.2.2.toList).eraseDups

/-- `blive` is its fold, then `bout`. -/
theorem blive_eq (h : History BVal) : blive h = bout (h.foldl bstep ([], none, none)) := rfl

/-- State st gives y as a live child. -/
def Has (st : LState) (y : NodeId) : Prop :=
  (∃ p ∈ st.1, p.2 = some y) ∨ st.2.1 = some y ∨ st.2.2 = some y

theorem mem_bout (st : LState) (y : NodeId) : y ∈ bout st ↔ Has st y := by
  simp only [bout, Has, List.mem_eraseDups, List.mem_append, List.mem_filterMap, Option.mem_toList,
    or_assoc]

/-- `setAssoc` keeps the pairs it has, or sets the new one. -/
theorem mem_setAssoc {m : List (Nat × Option Nat)} {c : Nat} {v : Option Nat} {p : Nat × Option Nat}
    (hp : p ∈ setAssoc m c v) : p ∈ m ∨ p = (c, v) := by
  unfold setAssoc at hp
  split at hp
  · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hp
    by_cases hc : (q.1 == c) = true
    · simp only [hc, ↓reduceIte] at hqp
      exact Or.inr hqp.symm
    · simp only [hc] at hqp
      exact Or.inl (hqp ▸ hq)
  · rcases List.mem_append.mp hp with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)

/-- A delete entry gives no compare value a child. -/
theorem mem_delFold (y : Nat) : ∀ (cs : List Nat) (m : List (Nat × Option Nat)) (p : Nat × Option Nat),
    p ∈ cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) m →
    p.2 = some y → ∃ q ∈ m, q.2 = some y := by
  intro cs
  induction cs with
  | nil => intro m p hp hy; exact ⟨p, hp, hy⟩
  | cons c cs ih =>
    intro m p hp hy
    simp only [List.foldl_cons] at hp
    obtain ⟨q, hq, hqy⟩ := ih _ p hp hy
    split at hq
    · rcases mem_setAssoc hq with h | h
      · exact ⟨q, h, hqy⟩
      · rw [h] at hqy
        cases hqy
    · exact ⟨q, hq, hqy⟩

/-- After one entry, a live child was one before, or is the entry's pointee. -/
theorem has_bstep {st : LState} {e : Entry BVal} {y : NodeId} (h : Has (bstep st e) y) :
    Has st y ∨ y ∈ bptrs e.val := by
  unfold bstep at h
  cases hv : e.val with
  | key c y' =>
    rw [hv] at h
    rcases h with ⟨p, hp, hpy⟩ | h | h
    · rcases mem_setAssoc hp with hp | hp
      · exact Or.inl (Or.inl ⟨p, hp, hpy⟩)
      · rw [hp] at hpy
        simp only [Option.some.injEq] at hpy
        right
        simp [bptrs, hpy]
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
  | del cs =>
    rw [hv] at h
    rcases h with ⟨p, hp, hpy⟩ | h | h
    · exact Or.inl (Or.inl (mem_delFold y cs st.1 p hp hpy))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
  | rootKey y' =>
    rw [hv] at h
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · simp only [Option.some.injEq] at h
      right
      simp [bptrs, h]
    · exact Or.inl (Or.inr (Or.inr h))
  | top z =>
    rw [hv] at h
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · simp only [Option.some.injEq] at h
      right
      simp [bptrs, h]
  | skip j z => rw [hv] at h; exact Or.inl h
  | data d => rw [hv] at h; exact Or.inl h

/-- After the entries h', a live child was one before, or is a pointee of one of them. -/
theorem has_foldl {y : NodeId} : ∀ (h' : History BVal) (st : LState), Has (h'.foldl bstep st) y →
    Has st y ∨ ∃ e ∈ h', y ∈ bptrs e.val := by
  intro h'
  induction h' with
  | nil => intro st h; exact Or.inl h
  | cons e h' ih =>
    intro st h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨e', he', hy⟩
    · rcases has_bstep h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨e, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hy⟩

/-- `LiveAppend` for `blive`: a live child of a history h followed by the
entries h' is a live child of h, or a pointee of an entry of h'. -/
theorem blive_append (h h' : History BVal) (y : NodeId) (hy : y ∈ blive (h ++ h')) :
    y ∈ blive h ∨ ∃ e ∈ h', y ∈ bptrs e.val := by
  rw [blive_eq, List.foldl_append, mem_bout] at hy
  rw [blive_eq, mem_bout]
  exact has_foldl h' _ hy

/-- `SpecOK.liveSub` for `blive`: a live child is a pointee of an entry. -/
theorem blive_sub (h : History BVal) (y : NodeId) (hy : y ∈ blive h) :
    ∃ e ∈ h, y ∈ bptrs e.val := by
  rw [blive_eq, mem_bout] at hy
  rcases has_foldl h _ hy with h0 | h0
  · exfalso
    simp [Has] at h0
  · exact h0

/-- The instance of every trace has `LiveAppend`. -/
theorem bspec_liveAppend (chs : Array (Changes BVal)) (p0 : Struct BVal) (virt : Bool) :
    LiveAppend (bspec chs p0 virt) :=
  blive_append

/-- The instance of every trace has `SpecOK.liveSub`. -/
theorem bspec_liveSub (chs : Array (Changes BVal)) (p0 : Struct BVal) (virt : Bool) :
    LiveSub (bspec chs p0 virt) :=
  blive_sub

/-- `PhysRunOK` for the instance of a trace: it holds in every run that meets
`RunOK` and has TREE after every transaction. C-A checks `RunOK`'s parts
(`liveSub` aside, which is `bspec_liveSub`) and TREE for every transaction of a
trace. -/
theorem bspec_physRunOK {chs : Array (Changes BVal)} {p0 : Struct BVal} {virt : Bool}
    {al : Algo BVal Nat} {ts : List Nat} (hok : RunOK (bspec chs p0 virt) al ts)
    (htree : ∀ j < ts.length,
      treeAt (bspec chs p0 virt) (run (bspec chs p0 virt) al (ts.take (j + 1))).P (j + 1)) :
    PhysRunOK (bspec chs p0 virt) al ts :=
  physRunOK_of_tree hok (bspec_liveAppend chs p0 virt) htree

/-- `PhysRunOK` for the instance of a trace, from the two other assumptions of
the theorems with handles. -/
theorem bspec_physRunOK_evict {chs : Array (Changes BVal)} {p0 : Struct BVal} {virt : Bool}
    {al : Algo BVal Nat} {ts : List Nat} (hok : RunOK (bspec chs p0 virt) al ts)
    (hev : EvictRunOK (bspec chs p0 virt) al ts) : PhysRunOK (bspec chs p0 virt) al ts :=
  physRunOK_of_evict hok (bspec_liveAppend chs p0 virt) hev

/-- An example of the use: T-READ with handles (`TR_handles`,
SIS/HandleTheorems.lean) for the instance of a trace, with no assumption of the
physical layer. In a run with BergDB's still-dirty test and marking that meets
`RunOK` and `EvictRunOK`, with any reads and evictions and no restart, a read
through the handles at any time up to the last record gives P at that time. The
other theorems with handles lose `LiveAppend` the same way
(`bspec_liveAppend`). -/
theorem bspec_tr_handles {chs : Array (Changes BVal)} {p0 : Struct BVal} {virt : Bool}
    {al : Algo BVal Nat} :
    ∀ ts : List (Nat × Bool × List HCacheOp),
      RunOK (bspec chs p0 virt) al (ts.map (·.1)) →
      EvictRunOK (bspec chs p0 virt) al (ts.map (·.1)) →
      al.stillDirty = javaTest (bspec chs p0 virt) → al.mark = true →
      (∀ p ∈ ts, p.2.1 = false) →
      ∀ j ≤ ts.length, ∀ t ≤ j,
        let db := run (bspec chs p0 virt) al ((ts.take j).map (·.1))
        let m := (runHandles (bspec chs p0 virt) al (ts.take j)).2.1
        (m.read (bspec chs p0 virt) (init (bspec chs p0 virt)).S db.S t).2.map (·.1) =
            reachList (bspec chs p0 virt) db.P t ∧
          ∀ p ∈ (m.read (bspec chs p0 virt) (init (bspec chs p0 virt)).S db.S t).2,
            view (bspec chs p0 virt) db.P t p.1 = some p.2 :=
  fun ts hok hev => tr_handles (bspec chs p0 virt) al ts hok (bspec_liveAppend chs p0 virt) hev

end SIS.Check
