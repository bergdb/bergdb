/-
bergdb 030-21, part 3: the statement of PE's acceptance, to read and to trust
with Contract/PeWriter.lean (the program) and Contract/PeStatement.lean
(`Inv`). The theorem is `pe_accepts` in Contract/Proof/PeAccept.lean: from a
state PE keeps, PE's transaction (`peTx`) gives a state for every
transaction but those the program refuses by design:

* a put of a key the tree cannot hold: not well formed, or of more than G + 1
  segments (`keyOk`); a delete of such a key is dropped as the noop it is;
* a tree that would grow past H (`Room`): a root cut into parts gets a new
  root above it, so a transaction can raise a segment's tree;
* more operations, or larger parameters, than the program's fuel allows
  (`FuelOk`, with `fuel` = 2^40).

The first is exact (`pe_refuses`: a put of such a key is refused); the
other two are bounds that suffice, not the program's exact limits.
-/
import Contract.PeStatement

namespace Contract.PE

/-- The program's fuel suffices: each recursion of `peTx` (plan, the
children planned, the groups of a segment leaf, a segment's tree, settle,
rebalance) uses at most M + p + 2 H + 6 of it a level, and a key goes down
at most (G + 1)(H + 1) levels, for a transaction of p operations. -/
def FuelOk (cf : Cfg) (p : Nat) : Prop :=
  (cf.G + 1) * (cf.H + 1) * (cf.M + p + 2 * cf.H + 6) ≤ fuel

/-- H leaves room for a transaction of p operations on the tree s, so that
no root grows past H. A root cut into k parts gets a new root above it of k
entries, cut again if k is more than h (a cut gives at most half as many
parts again when h and cap are at least 2); and a root that a transaction
plans holds at most the nodes of the tree plus the operations. So it is
enough that 2^(H - e) exceeds the tree's nodes (`reach s`, TREE's list) plus
p, for the height e of every node of the tree (`htIn`, 0 for a value). -/
structure Room (cf : Cfg) (s : Tree) (p : Nat) : Prop where
  h2 : 2 ≤ cf.h
  cap2 : 2 ≤ cf.cap
  room : ∀ y ∈ reach s, (reach s).length + p < 2 ^ (cf.H - htIn cf s y)

end Contract.PE
