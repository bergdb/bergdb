/-
The contract package (bergdb 030-07): the bridge's clauses on a heap that a
program can hold, for the trace checker (BridgeCheck.lean). The computed
clauses of Bridge.lean (`bridgeOk`) run on a heap as they stand
(`Heap.tree`). `Made` speaks of every node, so it is computed here over the
nodes of the heap (`madeCheck`), and `madeCheck_sound` proves that the
computation gives `Made`. The start is computed by `startCheck`.
`checkBridgeTx` is all of the bridge's clauses for one traced transaction,
with the ones in the model's words (BridgeModel.lean), and `checkEvictTx`
what eviction needs besides; Proof/BridgeModel.lean proves that they give
the clauses (`checkBridgeTx_sound`, `checkEvictTx_sound`).
-/
import Contract.BridgeModel
import Contract.Check

namespace Contract

open SIS (Struct Changes NewNode Spec)
open SIS.Check (BVal)

/-- `Made`, computed over the nodes of the heap after the transaction. -/
def madeCheck (h h' : Heap) (c : Changes BVal) : Bool :=
  h'.objs.toList.all (fun xo => h.objs.contains xo.1 || (c.new.map (·.id)).contains xo.1)

theorem madeCheck_sound (h h' : Heap) (c : Changes BVal) (hc : madeCheck h h' c = true) :
    Made h.tree h'.tree c := by
  intro x hx hs
  simp only [Heap.tree] at hx hs
  cases ho : h'.objs[x]? with
  | none => simp [ho] at hs
  | some o =>
    have hm : (x, o) ∈ h'.objs.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ho
    simp only [madeCheck, List.all_eq_true, Bool.or_eq_true] at hc
    rcases hc (x, o) hm with h4 | h4
    · have : x ∈ h.objs := Std.HashMap.contains_iff_mem.mp h4
      have h5 := Std.HashMap.mem_iff_isSome_getElem?.mp this
      simp [hx] at h5
    · simpa using h4

/-- The start, computed: the change of TX 0 and the heap after it. -/
def startCheck (c0 : Changes BVal) (h : Heap) : Bool :=
  match c0.new, c0.adds with
  | [⟨0, l0, false⟩, ⟨r, lr, false⟩, ⟨z, lz, false⟩], [(0, .top z'), (z'', .rootKey r')] =>
    z' == z && z'' == z && r' == r && r != 0 && z != 0 && z != r &&
    decide (0 < lr) && decide (lr < lz) && decide (lz < l0) && decide (lz ≤ 2 ^ 62) &&
    h.objs[r]? == some (.key { level := lr, leaf := true, ks := [.time 0] }) &&
    h.objs.toList.all (fun xo => xo.1 == r) && h.roots == [(0, r)]
  | _, _ => false

/-- The bridge's clauses for one traced transaction, computed: at time i, from
the heap h and the model's structure P, with the dirty nodes D, to the heap
h', with the change c. -/
def checkBridgeTx (sp : Spec BVal Nat) (P : Struct BVal) (i : Nat) (h : Heap) (D : List NodeId)
    (h' : Heap) (c : Changes BVal) : Bool :=
  bridgeOk sp.topLevel i h.tree h'.tree D c && madeCheck h h' c &&
  topOkB sp P (P.apply i c) i h.tree h'.tree c && touchB sp P i c

/-- What eviction needs besides, for one traced transaction, computed: TREE
and A6' after it, A-COPY for its change. -/
def checkEvictTx (sp : Spec BVal Nat) (P : Struct BVal) (i : Nat) (h' : Heap)
    (c : Changes BVal) : Bool :=
  treeOkB (h'.tree.at i) && adoptB sp (P.apply i c) i && copyB sp P (P.apply i c) i c

/-! ## A whole trace -/

/-- A traced transaction: its operations, the dirty nodes when it ends, the
heap after it, and its change. -/
structure TStep where
  ops : List Op
  D : List NodeId
  heap : Heap
  c : Changes BVal

/-- The history of a trace: the heap and the change of TX 0, and the traced
transactions. -/
def histOf (h0 : Heap) (c0 : Changes BVal) (steps : List TStep) : BHist :=
  { s0 := h0.tree, c0 := c0,
    txs := steps.map (fun st => { ops := st.ops, D := st.D, s := st.heap.tree, c := st.c }) }

/-- The checker's verdict on the transactions from time i on, the first from
the heap h and the model's structure P: each meets the writer's contract
(`checkTx`), the bridge's clauses (`checkBridgeTx`) and what eviction needs
(`checkEvictTx`). -/
def stepsOk (p : Params) (sp : Spec BVal Nat) : Nat → Heap → Struct BVal → List TStep → Bool
  | _, _, _, [] => true
  | i, h, P, st :: rest =>
    checkTx p i h st.ops st.D st.heap && checkBridgeTx sp P i h st.D st.heap st.c &&
    checkEvictTx sp P i st.heap st.c && stepsOk p sp (i + 1) st.heap (P.apply i st.c) rest

/-- The checker's verdict on a whole trace: the start, TREE and A6' at the
start, and every transaction, the j-th at time j, on the model's instance of
the trace's history. -/
def bridgeHistoryOk (p : Params) (h0 : Heap) (c0 : Changes BVal) (steps : List TStep) : Bool :=
  startCheck c0 h0 && treeOkB (h0.tree.at 0) &&
  adoptB (histOf h0 c0 steps).spec (histOf h0 c0 steps).p0 0 &&
  stepsOk p (histOf h0 c0 steps).spec 1 h0 (histOf h0 c0 steps).p0 steps

end Contract
