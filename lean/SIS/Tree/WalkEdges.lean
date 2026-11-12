import SIS.Tree.TreeGet
import SIS.Tree.DataEntries

namespace SIS.Tree

open SIS SIS.Check

/-- The invariant walk classifies every live edge: a short segment has a
data value; every other edge has a fault-free recursive walk. -/
theorem walk_edge_info (p : Params) (P : Struct BVal) (t f x lo : Nat)
    (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hdata : DataEntriesOK P) (hv : P.get? x = some nd) (hd : nd.isData = false)
    (hw : walk p (viewOf P) t (f+1) x lo hi isRoot space = [])
    (q : Nat × NodeId) (b : Option Nat)
    (hq : (q,b) ∈ childBounds
      ((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t) hi) :
    let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
    ((n.leaf && segLen q.1 != 7) = true → ∃ h, valueOf (viewOf P) q.2 = some h) ∧
    ((n.leaf && segLen q.1 != 7) = false →
      walk p (viewOf P) t f q.2
        (if n.leaf then 0 else if q.1 == 0 then lo else q.1)
        (if n.leaf then none else b) n.leaf (if n.leaf then false else space) = []) := by
  let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
  have hmem := childBounds_fst _ _ _ _ hq
  have hp := walk_current_pointer p (viewOf P) t f x lo hi isRoot space nd hv hd hw
    q.1 q.2 (n.liveAt_key_mem t q.1 q.2 hmem)
  have hchild := List.flatMap_eq_nil_iff.mp
    (walk_child_faults_nil p (viewOf P) t f x lo hi isRoot space nd hv hd hw) (q,b) hq
  change walkChildFaults p (viewOf P) t f x n (p.segOf nd.level)
    (p.heightOf nd.level) lo space (q,b) = [] at hchild
  change _ ∧ _
  cases hy : P.get? q.2 with
  | none => simp [viewOf,hy] at hp
  | some ny =>
    cases hleaf : n.leaf with
    | true =>
      by_cases hlen : segLen q.1 = 7
      · simp only [walkChildFaults,hleaf,hlen,beq_self_eq_true,↓reduceIte,viewOf,hy] at hchild
        change _ ∧ _
        simp only [hleaf,hlen,bne_self_eq_false,Bool.and_false,Bool.false_eq_true,
          false_implies,true_implies,true_and,↓reduceIte]
        split at hchild
        · cases hchild
        · split at hchild
          · cases hchild
          · exact hchild
      · simp only [walkChildFaults,hleaf,show (segLen q.1 == 7) = false by simp [hlen],
          Bool.false_eq_true,↓reduceIte,viewOf,hy] at hchild
        cases hny : ny.isData with
        | false => simp [hny] at hchild
        | true =>
          simp only [hleaf,show (segLen q.1 != 7) = true by simp [hlen],Bool.and_self,
            Bool.true_eq_false,false_implies,true_implies,and_true]
          exact valueOf_some_of_dataEntriesOK P q.2 ny hdata hy hny
    | false =>
      simp only [walkChildFaults,hleaf,Bool.false_eq_true,↓reduceIte,viewOf,hy] at hchild
      simp only [hleaf,Bool.false_and,Bool.false_eq_true,false_implies,true_implies,
        true_and,↓reduceIte]
      split at hchild
      · cases hchild
      · split at hchild
        · cases hchild
        · exact hchild

theorem walk_current_nonempty (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) (hnotspace : (space && isRoot) = false) :
    (⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t ≠ [] := by
  intro he
  have hm : s!"NonEmptyOK: key node {x} has no live klong at {t}" ∈
      walk p v t (f+1) x lo hi isRoot space := by
    rw [walk]
    simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
    simp [he,hnotspace,Bool.and_assoc]
  simp [hw] at hm

end SIS.Tree
