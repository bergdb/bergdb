import SIS.Tree.InvInit
import SIS.Proof.Basic

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem treeRun_snoc (p : Params) (ts : List Tx) (tx : Tx) :
    treeRun p (ts ++ [tx]) = (treeRun p ts).apply (ts.length + 1)
      (exec p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length)) := by
  simp [treeRun, List.zipIdx_append, List.foldl_append]

theorem within_take (p : Params) (ts : List Tx) (hw : Within p ts) (k : Nat) :
    Within p (ts.take k) := by
  constructor
  · intro tx htx
    exact hw.1 tx (List.take_subset k ts htx)
  · intro j hj
    have hlen : (ts.take k).length = min k ts.length := List.length_take
    have hjts : j < ts.length := by omega
    have hjk : j ≤ k := by omega
    simpa only [List.take_take, Nat.min_eq_left hjk, List.getElem_take] using hw.2 j hjts

theorem refGet_take_eq (ts : List Tx) (k t : Nat) (ht : t ≤ k) (key : Key) :
    refGet (ts.take k) t key = refGet ts t key := by
  simp only [refGet, List.take_take, Nat.min_eq_left ht]

theorem refGet_snoc_past (ts : List Tx) (tx : Tx) (t : Nat) (ht : t ≤ ts.length) (key : Key) :
    refGet (ts ++ [tx]) t key = refGet ts t key := by
  simp only [refGet, List.take_append_of_le_length ht]

def StructTimesLE (P : Struct BVal) (t : Time) : Prop :=
  ∀ q ∈ P, ∀ e ∈ q.2.hist, e.time ≤ t

theorem structTimesLE_addEntry (P : Struct BVal) (t i : Time) (x : NodeId) (val : BVal)
    (hP : StructTimesLE P t) (hi : i ≤ t) : StructTimesLE (P.addEntry i x val) t := by
  intro q hq
  unfold Struct.addEntry at hq
  obtain ⟨old, hold, he⟩ := List.mem_map.mp hq
  split at he
  · cases he
    intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hP old hold e hm
    · have heq := List.mem_singleton.mp hm
      subst e; exact hi
  · cases he
    exact hP _ hold

theorem structTimesLE_apply (P : Struct BVal) (t i : Time) (c : Changes BVal)
    (hP : StructTimesLE P t) (hi : i ≤ t) : StructTimesLE (P.apply i c) t := by
  have hf : ∀ (qs : List (NodeId × BVal)) (Q : Struct BVal), StructTimesLE Q t →
      StructTimesLE (qs.foldl (fun Q q => Q.addEntry i q.1 q.2) Q) t := by
    intro qs
    induction qs with
    | nil => intro Q hQ; exact hQ
    | cons q qs ih => intro Q hQ; exact ih _ (structTimesLE_addEntry Q t i q.1 q.2 hQ hi)
  apply hf c.adds
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hP q hq
  · obtain ⟨node, _, he⟩ := List.mem_map.mp hq
    cases he
    intro e he
    cases he

theorem treeRun_timesLE (p : Params) (ts : List Tx) : StructTimesLE (treeRun p ts) ts.length := by
  have hf : ∀ (qs : List (Tx × Nat)) (P : Struct BVal),
      (∀ q ∈ qs, q.2 < ts.length) → StructTimesLE P ts.length →
        StructTimesLE (qs.foldl (fun P (q : Tx × Nat) =>
          P.apply (q.2 + 1) (exec p q.1 (q.2 + 1) (view (treeSpec p) P q.2))) P) ts.length := by
    intro qs
    induction qs with
    | nil => intro P _ hP; exact hP
    | cons q qs ih =>
      intro P hq hP
      exact ih _ (fun a ha => hq a (List.mem_cons_of_mem q ha))
        (structTimesLE_apply P ts.length (q.2 + 1) _ hP (hq q List.mem_cons_self))
  apply hf ts.zipIdx (initStruct p)
  · intro q hq
    exact (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)).1
  · intro q hq
    rcases mem_init p q hq with rfl | rfl | rfl <;> intro e he <;>
      (have heq := List.mem_singleton.mp he; subst e; exact Nat.zero_le _)

end SIS.Tree
