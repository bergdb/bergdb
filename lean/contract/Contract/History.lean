/-
The contract package (bergdb 030-09): a traced history is a history that meets
the contract (030-06, finding 2).

The trace checker checks each transaction alone (`checkTx`). `Meets` asks for
more: a start tree, then the transactions in order, the j-th at time j. The
checker gives that when the trace's transactions are numbered 0, 1, 2, ...
with no gap, TX 0 being the start, and the trace is not cut (`DONE`): this is
what `completeFault` (Complete.lean) checks of the lines, and the checker
checks TX j at time j. `historyOk` is the checker's verdict on such a trace,
and `historyOk_meets` proves that it gives `Meets`: the theorems on reads
(Theorems.lean) then hold for the traced tree at every time of the trace.
Nothing here needs Mathlib.
-/
import Contract.Check

namespace Contract

/-- The start, computed: the tree at time 0 meets the invariants and is
empty (`Start`). -/
def startOk (p : Params) (h : Heap) : Bool :=
  invOk p (h.tree.at 0) && (contents (h.tree.at 0)).isEmpty

/-- A traced history from heap h at time i: each step its operations, its D
and the heap after it, the j-th (from 0) at time i + j, each meeting the
contract as the checker computes it. -/
def historyOk (p : Params) : Time → Heap → List (List Op × List NodeId × Heap) → Bool
  | _, _, [] => true
  | i, h, (ops, D, h') :: rest => checkTx p i h ops D h' && historyOk p (i + 1) h' rest

/-- The heap after the last step. -/
def lastHeap : Heap → List (List Op × List NodeId × Heap) → Heap
  | h, [] => h
  | _, (_, _, h') :: rest => lastHeap h' rest

theorem startOk_sound (p : Params) (h : Heap) (hs : startOk p h = true) : Start p h.tree := by
  simp only [startOk, Bool.and_eq_true, List.isEmpty_iff] at hs
  exact hs

theorem historyOk_meets' (p : Params) :
    ∀ (steps : List (List Op × List NodeId × Heap)) (txs : List (List Op)) (h : Heap),
      Meets p txs h.tree → historyOk p (txs.length + 1) h steps = true →
      Meets p (txs ++ steps.map (·.1)) (lastHeap h steps).tree
  | [], txs, h, hm, _ => by simpa [lastHeap] using hm
  | (ops, D, h') :: rest, txs, h, hm, hc => by
    simp only [historyOk, Bool.and_eq_true] at hc
    have h1 : Meets p (txs ++ [ops]) h'.tree :=
      Meets.step txs h.tree ops D h'.tree hm (checkTx_sound p _ h ops D h' hc.1)
    have h2 := historyOk_meets' p rest (txs ++ [ops]) h' h1
      (by simpa [Nat.add_assoc] using hc.2)
    simpa [lastHeap, List.append_assoc] using h2

/-- What the trace checker computes for a whole trace gives a history that
meets the contract: from a start heap that passes the start check, the
traced transactions at times 1, 2, ..., each passing `checkTx`, end in a tree
that `Meets` the contract with their operations. -/
theorem historyOk_meets (p : Params) (h : Heap) (steps : List (List Op × List NodeId × Heap))
    (hs : startOk p h = true) (hc : historyOk p 1 h steps = true) :
    Meets p (steps.map (·.1)) (lastHeap h steps).tree := by
  simpa using historyOk_meets' p steps [] h (Meets.start _ (startOk_sound p h hs)) (by simpa using hc)

end Contract
