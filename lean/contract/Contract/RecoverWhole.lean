/-
The contract package (bergdb 030-17): Java's tree holds the model's
structure whole. To read and to trust, with RecoverJava.lean.

030-14's premise of Java's reads, `HoldsView V leaf t s` (RecoverJava.lean),
is said of one time t: every node of the view at t is a node of Java's tree s
whose klongs, as a reader at t sees them (`prefixAt`), have the view's
entries. Java's startup builds one tree for every time, so the premise is
said here once, of whole nodes (030-14's State note, item 3):

* `HoldsP sp P leaf s`: every node of the structure P but the root and the
  top nodes (`SIS.isTop`: on the top nodes' levels) is a node of s with all
  its contents: a key node with P's level, the kind `leaf x`, and klongs that
  are well formed (W1 to W5) and whose entries are the node's whole history
  in P; a value with its value.
* `kindOfP kind P`: each node's kind from its level in P, as `kindOf` does
  for a view.

From it `HoldsView` follows at every time up to the structure's last
transaction (Proof/RecoverWhole.lean: the klongs cut at t are well formed and
have the entries up to t, Proof/Prefix.lean), so Java's reads are right at
every such time with one premise (RecoverWholeTheorems.lean).

Everything here runs; nothing needs Mathlib.
-/
import Contract.RecoverJava

namespace Contract

open SIS (Struct Node)
open SIS.Check (BVal)

/-- The kinds of the nodes of a structure, from their levels. -/
def kindOfP (kind : Nat → Bool) (P : Struct BVal) (x : NodeId) : Bool :=
  match P.get? x with
  | some n => kind n.level
  | none => false

/-- The tree s holds the structure P whole, with the kinds `leaf`: every node
of P but the root and the top nodes is a node of s with all its contents. -/
def HoldsP (sp : SIS.Spec BVal Nat) (P : Struct BVal) (leaf : NodeId → Bool) (s : Tree) : Prop :=
  ∀ x N, x ≠ SIS.root → SIS.isTop sp P x = false → P.get? x = some N →
    (N.isData = false → ∃ kn, s.obj x = some (.key kn) ∧ kn.level = N.level ∧
      kn.leaf = leaf x ∧ klongsWf kn.ks = true ∧ fullOk kn.ks = true ∧
      entriesOf kn.ks = N.hist) ∧
    (N.isData = true → ∃ v, dataOf N.hist = some v ∧ s.obj x = some (.val v))

end Contract
