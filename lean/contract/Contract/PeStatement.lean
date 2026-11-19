/-
bergdb 030-21: the statements of PE's writer proof, to read and to trust with
Contract/PeWriter.lean (the program), Statement.lean and ShapeStatement.lean
(the contract), Top.lean (the top), Contract/Proof/PeDefs.lean (`Cfg.Ok`,
`Shaped`, `htIn`) and Contract/Proof/PeTop.lean (`TopInv`). The theorems
are in Contract/Proof/PeTx.lean:

* `pe_step`: from a state PE keeps (`Inv` at i - 1), a transaction PE
  accepts at time i (`peTx` gives `some o`) meets the writer's contract
  (`Contract`: clauses 1 to 3), the tree after meets TREE at i, the top after
  meets the top's clauses (`TopStep`) and names the tree's space roots, and
  the state after is one PE keeps (`Inv` at i).
* `pe_meetsTop`: every history PE writes (`PeHist`) from a state PE keeps at
  time 0 whose tree is a start tree of the contract (`Start`) with a start
  top meets `MeetsTop` (the contract, TREE and the top), and PE keeps its
  state; `pe_meets`: it meets `Meets`.
* `pe_meetsTop_start`: every history PE writes from the empty tree
  (`startTree`, `startTop`, `startNext`) meets `MeetsTop`.
-/
import Contract.ShapeStatement
import Contract.Proof.PeDefs
import Contract.Proof.PeTop

namespace Contract.PE

/-! ## The writer's state -/

/-- What PE keeps of its state after the transaction of time t: the tree s
meets the contract's invariants and TREE; its space root is shaped as PE's
trees; every key node meets the rules of one node, has a klong, and has no
klong of a time after t (so s is the tree at t); no node has an id from
`next` on; the top meets its own rules (`TopInv`) and its root
pointers are the tree's space roots. -/
structure Inv (cf : Cfg) (t : Time) (s : Tree) (tp : Top) (next : NodeId) : Prop where
  inv : invOk cf.params s = true
  tree : Contract.TreeOk s
  shaped : ∃ r, s.root = some r ∧ Shaped cf s 0 (htIn cf s r) r
  sok : ∀ x n, s.obj x = some (.key n) →
    nodeOk cf.params s n = true ∧ n.ks ≠ [] ∧ ∀ u, Klong.time u ∈ n.ks → u < t + 1
  fresh : ∀ x, next ≤ x → s.obj x = none
  top : TopInv tp next t
  roots : s.roots = rootsOf tp

/-! ## Histories -/

/-- The histories PE writes: from the state (s0, tp0, nx0) at time 0, the
transactions txs in order, the j-th at time j, each accepted by PE (`peTx`
gives a state), end in the state (s, tp, nx). -/
inductive PeHist (cf : Cfg) (s0 : Tree) (tp0 : Top) (nx0 : NodeId) :
    List (List Op) → Tree → Top → NodeId → Prop where
  | start : PeHist cf s0 tp0 nx0 [] s0 tp0 nx0
  | step {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId} {ops : List Op} {o : Out} :
      PeHist cf s0 tp0 nx0 txs s tp nx → peTx cf (txs.length + 1) s tp nx ops = some o →
      PeHist cf s0 tp0 nx0 (txs ++ [ops]) (o.tree s) o.top o.next

end Contract.PE
