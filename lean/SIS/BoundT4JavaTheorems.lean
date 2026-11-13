/-
Self-indexed streams in Lean: bounds, part 2, T4's debt for BergDB's
still-dirty test (bergdb item 007; 007-01, section 6, second point).

Trusted part: the statements. The definitions they are about are in
SIS/BoundT4Java.lean (`PtrBelow`, `DebtByChains`, `ptrParents`, `geomSum`) and
SIS/BoundT4.lean, the proofs in SIS/Proof/BoundT4Java.lean; the proofs here only
connect them. SIS/BoundT4JavaExample.lean has a run, checked by running, in
which no bound in the changes of the last sections holds. Added 2026-11-13.
-/
import SIS.Proof.BoundT4Java

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T4, the debt of D, with BergDB's still-dirty test (`javaTest`, Rule A over
all pointers, live or dead; 007-01, section 6, second point): after a run that
meets the assumptions (`RunOK`), every node x of D reaches, through pointers
live or dead (x included), a node on the access path of the change of a
transaction of the last lev(x) + 1 startup sections (`DebtByChains`). With a
virtual root too (BergDB's). The proof: a node that step 7 puts back has a
pointee, on a lower level, in D (SIS/Proof/BoundT4Java.lean). -/
theorem T4_debt_java (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) : DebtByChains sp al ts :=
  debtByChains_java sp al ts hok hj

/-- T4's debt with BergDB's test, counted: with the assumptions of
`T4_debt_java`, if every node of D is on a level up to H, then D has at most as
many nodes as there are nodes on levels up to H that reach, through pointers
live or dead, a node on the access path of a transaction of the last H + 1
startup sections, a < τ ≤ k, a = spIter S (H + 1) k: for any N such that N τ
bounds those of T(τ), |D| ≤ N (a + 1) + ... + N k. -/
theorem T4_debt_java_count (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (H : Nat)
    (hH : ∀ e ∈ (run sp al ts).D, levelOf (run sp al ts).P e.1 ≤ H) (N : Nat → Nat)
    (hN : ∀ τ (L : List NodeId), L.Nodup →
      (∀ x ∈ L, (∃ z, PtrBelow sp (run sp al ts).P x z ∧ onAccessPath sp al ts τ z) ∧
        levelOf (run sp al ts).P x ≤ H) → L.length ≤ N τ) :
    let a := spIter (run sp al ts).S (H + 1) ts.length
    (run sp al ts).D.length ≤ ((List.range' (a + 1) (ts.length - a)).map N).sum :=
  debt_count_java sp al ts hok hj H hH N hN

/-- T4's debt with BergDB's test and TREE, counted (007-01, section 6: "A bound
needs an assumption on how many such nodes point to a node of D"): with the
assumptions of `T4_debt_java`, TREE after every transaction (`TreeRunOK`), H the
root's level after the run, and at most Q pointer parents for every node of P
after the run (`ptrParents`: the nodes with an entry that points to it, live or
dead), D has at most

  (1 + Q + ... + Q^H) ((H + 1) (new nodes + entries of T(τ)) + (touched nodes of T(τ)))

summed over the transactions T(τ) of the last H + 1 startup sections,
a < τ ≤ k, a = spIter S (H + 1) k: `T4_debt_tree`'s bound times
1 + Q + ... + Q^H (`geomSum`). With Q = 1, a tree without old parents, that is
H + 1 times it. -/
theorem T4_debt_java_tree (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (htree : TreeRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) (Q : Nat)
    (hQ : ∀ z, (ptrParents sp (run sp al ts).P z).length ≤ Q) :
    let a := spIter (run sp al ts).S (n0.level + 1) ts.length
    (run sp al ts).D.length ≤ geomSum Q n0.level *
      ((List.range' (a + 1) (ts.length - a)).map (fun τ =>
        (n0.level + 1) * ((changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length) +
          (changeAt sp al ts τ).touch.length)).sum :=
  debt_tree_java sp al ts hok hj htree n0 h0 Q hQ

/-- T4's debt with BergDB's test, with restarts (crashes and startups) after any
transactions (`runRestarts`): as `T4_debt_java`. -/
theorem T4_debt_java_restarts (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
    (hok : RunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp) :
    let db := runRestarts sp al ts
    ∀ e ∈ db.D, ∃ τ z, spIter db.S (levelOf db.P e.1 + 1) ts.length < τ ∧ τ ≤ ts.length ∧
      PtrBelow sp db.P e.1 z ∧ onAccessPath sp al (ts.map (·.1)) τ z :=
  debtByChains_restarts sp al ts hok hj

/-- T4's debt with BergDB's test, by height (in place of level, which in 024-12's
tree model is a code; `PtrHeightLe`): with the assumptions of `T4_debt_java`,
every node x of D whose height in the pointer graph is at most h reaches,
through pointers live or dead, a node on the access path of a change of the
last h + 1 startup sections (`DebtByChainsH`). With a virtual root too. -/
theorem T4_debt_java_height (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) : DebtByChainsH sp al ts :=
  debtByChainsH_java sp al ts hok hj

/-- T4's debt with BergDB's test, by height, counted: if every node of D has
height at most H in the pointer graph, D has at most N (a + 1) + ... + N k
nodes, a = spIter S (H + 1) k, for any N such that N τ bounds the nodes that
reach, through pointers, the access path of T(τ). -/
theorem T4_debt_java_height_count (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (H : Nat)
    (hH : ∀ e ∈ (run sp al ts).D, PtrHeightLe sp (run sp al ts).P H e.1) (N : Nat → Nat)
    (hN : ∀ τ (L : List NodeId), L.Nodup →
      (∀ x ∈ L, ∃ z, PtrBelow sp (run sp al ts).P x z ∧ onAccessPath sp al ts τ z) →
        L.length ≤ N τ) :
    let a := spIter (run sp al ts).S (H + 1) ts.length
    (run sp al ts).D.length ≤ ((List.range' (a + 1) (ts.length - a)).map N).sum :=
  debt_count_java_h sp al ts hok hj H hH N hN

end SIS
