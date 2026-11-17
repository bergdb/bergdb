/-
The contract package (bergdb 030-08): a traced history with its top is a
history that meets the contract with TREE and the top (`MeetsTop`), as
History.lean (bergdb 030-09) proves it for `Meets`.

The checker checks each transaction alone with `checkTopTx` and the start
with `startTopOk`; `historyTopOk` is its verdict on a whole trace, the j-th
transaction at time j, and `historyTopOk_meetsTop` proves that it gives
`MeetsTop`: the theorems of TheoremsTop.lean, Java's readers through the top
among them, then hold for the traced tree at every time of the trace.
Nothing here needs Mathlib.
-/
import Contract.History
import Contract.CheckShape
import Contract.ShapeStatement

namespace Contract

/-- The start with its top, computed. -/
def startTopOk (p : Params) (h : Heap) (tp : Top) : Bool :=
  startOk p h && treeOkB (h.tree.at 0) && topStartB tp && h.roots == rootsOf tp

/-- A traced history with its top from heap h and top tp at time i: each
step its operations, its D, the heap and the top after it. -/
def historyTopOk (p : Params) :
    Time → Heap → Top → List (List Op × List NodeId × Heap × Top) → Bool
  | _, _, _, [] => true
  | i, h, tp, (ops, D, h', tp') :: rest =>
    checkTopTx p i h tp ops D h' tp' && historyTopOk p (i + 1) h' tp' rest

/-- The heap and the top after the last step. -/
def lastTop : Heap × Top → List (List Op × List NodeId × Heap × Top) → Heap × Top
  | ht, [] => ht
  | _, (_, _, h', tp') :: rest => lastTop (h', tp') rest

theorem historyTopOk_meetsTop' (p : Params) :
    ∀ (steps : List (List Op × List NodeId × Heap × Top)) (txs : List (List Op)) (h : Heap)
      (tp : Top),
      MeetsTop p txs h.tree tp → historyTopOk p (txs.length + 1) h tp steps = true →
      MeetsTop p (txs ++ steps.map (·.1)) (lastTop (h, tp) steps).1.tree
        (lastTop (h, tp) steps).2
  | [], txs, h, tp, hm, _ => by simpa [lastTop] using hm
  | (ops, D, h', tp') :: rest, txs, h, tp, hm, hc => by
    simp only [historyTopOk, Bool.and_eq_true] at hc
    obtain ⟨h1, h2, h3, h4⟩ := checkTopTx_sound p _ h tp ops D h' tp' hc.1
    have hm' : MeetsTop p (txs ++ [ops]) h'.tree tp' :=
      MeetsTop.step txs h.tree tp ops D h'.tree tp' hm h1 h2 h3 h4
    have := historyTopOk_meetsTop' p rest (txs ++ [ops]) h' tp' hm'
      (by simpa [Nat.add_assoc] using hc.2)
    simpa [lastTop, List.append_assoc] using this

/-- The start, computed, gives the start of `MeetsTop`. -/
theorem startTopOk_meetsTop (p : Params) (h : Heap) (tp : Top) (hs : startTopOk p h tp = true) :
    MeetsTop p [] h.tree tp := by
  simp only [startTopOk, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  exact MeetsTop.start h.tree tp (startOk_sound p h h1) (treeOkB_sound _ h2) (topStartB_sound tp h3) h4

/-- What the trace checker computes for a whole trace with its top gives a
history that meets the contract with TREE and the top. -/
theorem historyTopOk_meetsTop (p : Params) (h : Heap) (tp : Top)
    (steps : List (List Op × List NodeId × Heap × Top)) (hs : startTopOk p h tp = true)
    (hc : historyTopOk p 1 h tp steps = true) :
    MeetsTop p (steps.map (·.1)) (lastTop (h, tp) steps).1.tree (lastTop (h, tp) steps).2 := by
  simpa using historyTopOk_meetsTop' p steps [] h tp (startTopOk_meetsTop p h tp hs) (by simpa using hc)

end Contract
