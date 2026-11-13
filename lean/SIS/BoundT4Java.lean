/-
Self-indexed streams in Lean: bounds, part 2, T4's debt for BergDB's
still-dirty test (bergdb item 007; 007-01, section 6, second point).

Trusted part: the definitions that the theorems are about. The theorems are in
SIS/BoundT4JavaTheorems.lean, the proofs in SIS/Proof/BoundT4Java.lean, a run
that shows what does not hold in SIS/BoundT4JavaExample.lean. Added
2026-11-13.

The prose (007-01, section 6, second point): "With BergDB's test (Rule A over
all pointers), a written node stays dirty while any pointee is in D, so nodes
that are no longer current stay dirty too (sis-model.md, section 11). They are
20 to 46 percent of the index nodes written at 50 MB (levels.md, "Bounds,
measured"). A bound needs an assumption on how many such nodes point to a node
of D, to state, and to check on Java's runs as TREE and A6' are."

`DebtByChains` states what holds with BergDB's test: every node of D reaches,
through pointers live or dead, a node on the access path of a change of the
last lev + 1 sections. `ptrParents` is "how many such nodes point to a node":
the assumption that the count needs (SIS/BoundT4JavaTheorems.lean). Without
it no bound in the changes of the last sections holds
(SIS/BoundT4JavaExample.lean).
-/
import SIS.BoundT4

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- z is x, or below x through pointers of the histories in P, live or dead: x
has an entry with a pointer to some y (`pointees`), and z is y or below y. A
node that is no longer reachable keeps its entries, so its pointers too. By A4
each pointer goes to a node on a lower level. -/
inductive PtrBelow (sp : Spec V T) (P : Struct V) : NodeId → NodeId → Prop
  | refl (x : NodeId) : PtrBelow sp P x x
  | step {x y z : NodeId} (n : Node V) : P.get? x = some n → y ∈ pointees sp n.hist →
      PtrBelow sp P y z → PtrBelow sp P x z

/-- T4, the debt of D with BergDB's still-dirty test (`javaTest`, Rule A over
all pointers, live or dead; 007-01, section 6, second point): after the run ts,
of k = ts.length transactions, every node x of D reaches, through pointers live
or dead (`PtrBelow`, x itself included), a node z on the access path of the
change of a transaction T(τ) of the last lev(x) + 1 startup sections,
spIter S (lev(x) + 1) k < τ ≤ k (`onAccessPath`).

With the exact test (`DebtByChanges`) z is x itself. With BergDB's test x may
stay in D through a pointee that is in D, also one that x no longer points to
live, or when x itself is no longer reachable: a node that a split replaced
keeps its pointers to its old children. -/
def DebtByChains (sp : Spec V T) (al : Algo V T) (ts : List T) : Prop :=
  let db := run sp al ts
  ∀ e ∈ db.D, ∃ τ z, spIter db.S (levelOf db.P e.1 + 1) ts.length < τ ∧ τ ≤ ts.length ∧
    PtrBelow sp db.P e.1 z ∧ onAccessPath sp al ts τ z

/-- The pointer parents of z in P: the nodes of P with an entry that points to
z, live or dead (007-01, section 6: "how many such nodes point to a node of
D"). In BergDB, z's parent and the nodes that splits replaced while z was their
child. -/
def ptrParents (sp : Spec V T) (P : Struct V) (z : NodeId) : List NodeId :=
  (allIds P).filter (fun x => match P.get? x with
    | some n => (pointees sp n.hist).contains z
    | none => false)

/-- 1 + Q + Q^2 + ... + Q^h: the most nodes that reach a node through pointers
over h levels or fewer, with at most Q pointer parents per node. -/
def geomSum (Q : Nat) : Nat → Nat
  | 0 => 1
  | h + 1 => 1 + Q * geomSum Q h

end SIS
