/-
bergdb 030-29: the statement that Java's dirty-node bound bounds PE, to read
and to trust with Contract/DirtyBound.lean (`DNB.dirtyNodeBound`, Java's count,
and `DNB.keyWrites`, the key nodes a transaction of PE writes),
Contract/PeWriter.lean (PE), Contract/PeStatement.lean (`Inv`, a state PE
keeps) and Contract/Shape.lean (`shapeFaults`, the writer's fill rules as the
trace checker computes them). The theorems are in Contract/Proof/DnbMain.lean.

* `Cfg.java b G H`: PE's parameters as Java has them at node size b (Dag's
  thresholds h = c = 17 b / 30, m, theta, and the cut size b / 2), with the
  model's level bounds G and H, which Java does not have.
* `FillOk b H s`: the tree s meets the writer's fill rules (RootsOK: an inner
  root of a segment tree has at least two live klongs; FillOK: every other key
  node at least m; and LeftmostOK, DeadOK, BalancedOK): `shapeFaults` finds no
  fault. The tree checker checks it on Java's tree after every traced
  transaction (C-T6); that PE keeps it is not proved here.
-/
import Contract.DirtyBound
import Contract.PeStatement

namespace Contract.PE

/-- PE's parameters as Java has them at node size b (`Dag.splitAbove`,
`Dag.minFill`, `Dag.mergeCap`, `Dag.theta`, `Dag.cutSize`), with the level
bounds G and H. -/
def Cfg.java (b G H : Nat) : Cfg :=
  { M := b, G := G, H := H, m := DNB.minFill b, c := DNB.mergeCap b, h := DNB.splitAbove b,
    theta := DNB.theta b, cap := DNB.cutSize b }

/-- The writer's fill rules hold on the tree s at node size b with height bound
H: the trace checker's walk (`shapeFaults`) finds no fault. -/
def FillOk (b H : Nat) (s : Tree) : Prop :=
  shapeFaults ⟨H, DNB.minFill b, DNB.theta b⟩ s = []

end Contract.PE
