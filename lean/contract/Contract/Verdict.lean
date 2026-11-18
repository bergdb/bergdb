/-
The contract package (bergdb 030-15): the contract checker's verdict on a
whole trace, as one function with a theorem.

Until 030-15 `contractcheck` (ContractCheck.lean) checked each transaction
in a loop and failed a trace when a count of failures was not zero; that its
exit status meant `historyTopOk` (HistoryTop.lean), and so `MeetsTop`, was
seen by reading the loop, not proved (an independent review, the night of
17 November, section 4). Now the checker computes `contractVerdict` on each
trace's lines and passes a trace only if it is true; `contractVerdict_sound`
proves that a trace with that verdict is whole (`completeFault`), readable
(`readTrace`) and gives a history that meets the contract with TREE and the
top (`MeetsTop`), its transactions those of the trace after `TX 0` in order:
the j-th at time j, with the operations of its OP lines, D the nodes of the
DIRTY line before it and its GD line, the heap and the top that its lines
give (`applyTx`, `applyTop`). The bridge checker's verdict is
`fullHistoryOk` (BridgeHeap.lean, `fullHistoryOk_meets`), in the same way.

The verdict also asks that Java's reads agree with the package's
(`readsOk`): each GET and SCAN line is the package's `get` and `scan` on the
tree after its transaction at the line's time, and the LIVE and SKIPT lines
are the package's searches and the top's cached times. They are tests of
the assumptions that reads rest on (030-04, section 3.5), not part of the
contract; the theorem speaks of the contract only. So the verdict is all
that the checker's loop counts: a trace passes if and only if no count is
other than zero, which the checker also checks. Since bergdb 030-19 a whole
trace (`completeFault`) has reads in every transaction after `TX 0`, so
`readsOk` is not true for want of reads, and no PROBE line that fails (an
independent review, Codex 3: the checkers passed a trace with neither).
Nothing here needs Mathlib.
-/
import Contract.Complete
import Contract.HistoryTop
import Contract.TraceTop

namespace Contract

/-- The traced steps after `TX 0`: for each transaction its operations, its
D (the DIRTY line of the transaction before it and its own GD line), and the
heap and the top after it, from the heap h and the top tp before it and the
DIRTY line `dirty` of the transaction before. -/
def traceSteps (h : Heap) (tp : Top) (dirty : List NodeId) :
    List TxLines → List (List Op × List NodeId × Heap × Top)
  | [] => []
  | tx :: rest =>
    let h' := applyTx h tx
    let tp' := applyTop tp tx
    (tx.ops, dirty ++ tx.gd, h', tp') :: traceSteps h' tp' tx.dirty rest

/-- The heap and the top that `TX 0`'s lines make. -/
def traceStart (tx0 : TxLines) : Heap × Top := (applyTx {} tx0, applyTop [] tx0)

/-- The verdict on the contract with TREE and the top for a trace read:
`TX 0` is the start (`startTopOk`) and the transactions after it, the j-th
at time j, each pass `checkTopTx` (`historyTopOk`). -/
def traceTopOk (tr : Trace) : Bool :=
  match tr.txs.toList with
  | [] => false
  | tx0 :: rest =>
    startTopOk { M := tr.M } (traceStart tx0).1 (traceStart tx0).2 &&
      historyTopOk { M := tr.M } 1 (traceStart tx0).1 (traceStart tx0).2
        (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty rest)

/-- Java's lines of a transaction agree with the package, on the heap h' and
the top tp' after it, `topRoot` the root pointers of the top nodes made up to
it: each GET and SCAN line is the package's `get` and `scan` at the line's
time (R1), each LIVE line Java's search and top search as the package's
(`liveOk`, L1), each SKIPT line the cached time of the top (`skiptFaults`,
C5), each LIVE 0 line the search through the skip pointers (`liveFaults`,
L2). -/
def txReadsOk (h' : Heap) (tp' : Top) (topRoot : List (NodeId × NodeId)) (tx : TxLines) : Bool :=
  tx.gets.all (fun g => get (h'.tree.at g.t) g.key == g.v) &&
    tx.scans.all (fun sc => scan (h'.tree.at sc.t) sc.req sc.limit == sc.res) &&
    tx.lives.all (fun (x, t, ys) => liveOk h' topRoot x t ys) &&
    (skiptFaults tp' tx).1.isEmpty && (liveFaults tp' tx).1.isEmpty

/-- Java's lines of every transaction agree with the package (`txReadsOk`). -/
def readsOk (tr : Trace) : Bool :=
  (tr.txs.toList.foldl (fun (acc : Bool × Heap × Top × List (NodeId × NodeId)) tx =>
    let h' := applyTx acc.2.1 tx
    let tp' := applyTop acc.2.2.1 tx
    let topRoot := acc.2.2.2 ++ tx.rootPtrs
    (acc.1 && txReadsOk h' tp' topRoot tx, h', tp', topRoot))
    (true, {}, [], [])).1

/-- The contract checker's verdict on a trace's lines: whole, readable, the
contract with TREE and the top on its history, and Java's reads the
package's. -/
def contractVerdict (lines : Array String) : Bool :=
  (completeFault lines).isNone &&
    match readTrace lines with
    | .ok tr => traceTopOk tr && readsOk tr
    | .error _ => false

theorem traceSteps_ops (h : Heap) (tp : Top) (dirty : List NodeId) :
    ∀ txs : List TxLines, (traceSteps h tp dirty txs).map (·.1) = txs.map (·.ops)
  | [] => rfl
  | tx :: rest => by
    simp only [traceSteps, List.map_cons]
    rw [traceSteps_ops _ _ _ rest]

/-- A trace that passes `traceTopOk` is a history that meets the contract
with TREE and the top: from the start that `TX 0` makes, the transactions
after it, with the operations of their OP lines, end in the tree and top
after the last of them. -/
theorem traceTopOk_meetsTop (tr : Trace) (hc : traceTopOk tr = true) :
    ∃ tx0 rest, tr.txs.toList = tx0 :: rest ∧
      MeetsTop { M := tr.M } (rest.map (·.ops))
        (lastTop (traceStart tx0) (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty
          rest)).1.tree
        (lastTop (traceStart tx0) (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty
          rest)).2 := by
  unfold traceTopOk at hc
  match hm : tr.txs.toList, hc with
  | [], hc => simp at hc
  | tx0 :: rest, hc =>
    simp only [Bool.and_eq_true] at hc
    refine ⟨tx0, rest, rfl, ?_⟩
    have := historyTopOk_meetsTop { M := tr.M } (traceStart tx0).1 (traceStart tx0).2
      (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty rest) hc.1 hc.2
    rw [traceSteps_ops] at this
    exact this

/-- The contract checker's verdict (`contractVerdict`, what `contractcheck`
passes a trace on) is sound: the trace is whole and readable, and its
history meets the contract with TREE and the top (`MeetsTop`), so that the
theorems of TheoremsTop.lean, Java's readers through the top among them,
hold for the traced tree at every time of the trace. -/
theorem contractVerdict_sound (lines : Array String) (hv : contractVerdict lines = true) :
    completeFault lines = none ∧ ∃ tr, readTrace lines = .ok tr ∧ readsOk tr = true ∧
      ∃ tx0 rest, tr.txs.toList = tx0 :: rest ∧
        MeetsTop { M := tr.M } (rest.map (·.ops))
          (lastTop (traceStart tx0) (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty
            rest)).1.tree
          (lastTop (traceStart tx0) (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty
            rest)).2 := by
  unfold contractVerdict at hv
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hv
  refine ⟨hv.1, ?_⟩
  match hr : readTrace lines, hv.2 with
  | .ok tr, h2 =>
    simp only [Bool.and_eq_true] at h2
    exact ⟨tr, rfl, h2.2, traceTopOk_meetsTop tr h2.1⟩
  | .error _, h2 => simp at h2

end Contract
