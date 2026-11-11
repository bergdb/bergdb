/-
The tree model (bergdb 024-12, section 6): the two properties about the root
that are proved, TP17 and TP18.

TP18, `VirtLiveOKTree`: the root's live children are those of its last entry
(`blive` on a history of entries for top nodes). TP17, `ExecRootOKTree`: the
tree's `exec` sees the root only through its live child: the writer gets the
top node of the root's last entry (`lastTop`) and a view without the root
(`rootless`), and both are the same for two views that agree off the root and
on the root's live children. Proofs; not needed for reading the statements.
-/
import SIS.Tree.Props

namespace SIS.Tree

open SIS SIS.Check

/-- The top node that the last entry of a history of top entries names; r for
an empty history. -/
def lastTopOf (r : Option Nat) : History BVal → Option Nat
  | [] => r
  | e :: t => lastTopOf (match e.val with
    | .top z => some z
    | _ => r) t

theorem fold_tops (h : History BVal) (hh : ∀ e ∈ h, ∃ z, e.val = BVal.top z) (r : Option Nat) :
    h.foldl (fun (acc : List (Nat × Option Nat) × Option Nat × Option Nat) e =>
      match e.val with
      | .key c y => (setAssoc acc.1 c (some y), acc.2.1, acc.2.2)
      | .del cs =>
        (cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) acc.1,
          acc.2.1, acc.2.2)
      | .rootKey y => (acc.1, some y, acc.2.2)
      | .top z => (acc.1, acc.2.1, some z)
      | _ => acc) ([], none, r) = ([], none, lastTopOf r h) := by
  induction h generalizing r with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨z, hz⟩ := hh e (List.mem_cons_self ..)
    have ht : ∀ e' ∈ t, ∃ z, e'.val = BVal.top z := fun e' he' => hh e' (List.mem_cons_of_mem _ he')
    rw [List.foldl_cons]
    simp only [hz, lastTopOf]
    exact ih ht (some z)

theorem lastTopOf_toList (h : History BVal) (hh : ∀ e ∈ h, ∃ z, e.val = BVal.top z)
    (r : Option Nat) :
    (lastTopOf r h).toList = (h.getLast?.map (fun e => bptrs e.val)).getD r.toList := by
  induction h generalizing r with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨z, hz⟩ := hh e (List.mem_cons_self ..)
    have ht : ∀ e' ∈ t, ∃ z, e'.val = BVal.top z := fun e' he' => hh e' (List.mem_cons_of_mem _ he')
    simp only [lastTopOf, hz]
    rw [ih ht (some z)]
    cases t with
    | nil => simp [hz, bptrs]
    | cons e2 t2 =>
      rw [List.getLast?_cons_cons]
      cases hl : (e2 :: t2).getLast? with
      | none => simp at hl
      | some x => rfl

/-- The live children of a history of entries for top nodes: the top node of its
last entry. -/
theorem blive_eq_lastTopOf (h : History BVal) (hh : ∀ e ∈ h, ∃ z, e.val = BVal.top z) :
    blive h = (lastTopOf none h).toList := by
  have h1 := fold_tops h hh none
  have h2 : blive h = ((([] : List (Nat × Option Nat)).filterMap (·.2)) ++
      (none : Option Nat).toList ++ (lastTopOf none h).toList).eraseDups := by
    unfold blive
    exact congrArg (fun (st : List (Nat × Option Nat) × Option Nat × Option Nat) =>
      ((st.1.filterMap (·.2)) ++ st.2.1.toList ++ st.2.2.toList).eraseDups) h1
  rw [h2]
  cases lastTopOf none h <;> rfl

/-- The live children of a history of entries for top nodes are the pointers of
its last entry. -/
theorem blive_tops (h : History BVal) (hh : ∀ e ∈ h, ∃ z, e.val = BVal.top z) :
    blive h = (h.getLast?.map (fun e => bptrs e.val)).getD [] := by
  rw [blive_eq_lastTopOf h hh, lastTopOf_toList h hh none]
  rfl

/-- TP18, proved: with a virtual root, the root's live children are those of its
last entry. -/
theorem virtLiveOKTree (p : Params) : VirtLiveOKTree p := by
  intro _ h hh
  exact blive_tops h hh

/-- The top node that an entry names, if it is an entry for a top node. -/
def topOfLast : Option (Entry BVal) → Option Nat
  | some ⟨_, .top z⟩ => some z
  | _ => none

theorem lastTopOf_eq (h : History BVal) (hh : ∀ e ∈ h, ∃ z, e.val = BVal.top z) (r : Option Nat) :
    lastTopOf r h = match h.getLast? with
      | none => r
      | some e => topOfLast (some e) := by
  induction h generalizing r with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨z, hz⟩ := hh e (List.mem_cons_self ..)
    have ht : ∀ e' ∈ t, ∃ z, e'.val = BVal.top z := fun e' he' => hh e' (List.mem_cons_of_mem _ he')
    simp only [lastTopOf, hz]
    rw [ih ht (some z)]
    cases t with
    | nil =>
      obtain ⟨tm, val⟩ := e
      simp at hz
      subst hz
      rfl
    | cons e2 t2 =>
      rw [List.getLast?_cons_cons]
      cases hx : (e2 :: t2).getLast? with
      | none => simp at hx
      | some x => rfl

/-- The writer's super root, for a root whose entries are for top nodes. -/
theorem lastTop_eq_lastTopOf (v : View BVal) (n : Node BVal) (h : v root = some n)
    (hh : ∀ e ∈ n.hist, ∃ z, e.val = BVal.top z) : lastTop v = lastTopOf none n.hist := by
  have h1 : lastTop v = topOfLast n.hist.getLast? := by
    unfold lastTop
    rw [h]
    rfl
  rw [h1, lastTopOf_eq n.hist hh none]
  cases n.hist.getLast? <;> rfl

/-- Two views whose roots hold entries for top nodes only, with the same live
children, have the same last top node. -/
theorem lastTop_of_live (v v' : View BVal)
    (hv : ∀ n, v root = some n → ∀ e ∈ n.hist, ∃ z, e.val = BVal.top z)
    (hv' : ∀ n, v' root = some n → ∀ e ∈ n.hist, ∃ z, e.val = BVal.top z)
    (hl : (v root).map (fun n => blive n.hist) = (v' root).map (fun n => blive n.hist)) :
    lastTop v = lastTop v' := by
  cases h : v root with
  | none =>
    cases h' : v' root with
    | none => unfold lastTop; rw [h, h']
    | some n' => rw [h, h'] at hl; simp at hl
  | some n =>
    cases h' : v' root with
    | none => rw [h, h'] at hl; simp at hl
    | some n' =>
      rw [h, h'] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      rw [blive_eq_lastTopOf n.hist (hv n h), blive_eq_lastTopOf n'.hist (hv' n' h')] at hl
      rw [lastTop_eq_lastTopOf v n h (hv n h), lastTop_eq_lastTopOf v' n' h' (hv' n' h')]
      cases ha : lastTopOf none n.hist <;> cases hb : lastTopOf none n'.hist <;>
        rw [ha, hb] at hl <;> simp at hl <;> simp [hl]

/-- Views that agree off the root are the same view without the root. -/
theorem rootless_eq (v v' : View BVal) (h : ∀ x, x ≠ root → v x = v' x) :
    rootless v = rootless v' := by
  funext x
  unfold rootless
  by_cases hx : x = root
  · simp [hx]
  · have hb : (x == root) = false := by simp [hx]
    simp [hb, h x hx]

/-- TP17, proved: the tree's `exec` sees the root only through its live child. -/
theorem execRootOKTree (p : Params) : ExecRootOKTree p := by
  intro _ tr i v v' hv hv' hne hl
  have h1 := lastTop_of_live v v' hv hv' hl
  have h2 := rootless_eq v v' hne
  show exec p tr i v = exec p tr i v'
  unfold exec exec? runOps touchOf
  rw [h1, h2]

end SIS.Tree
