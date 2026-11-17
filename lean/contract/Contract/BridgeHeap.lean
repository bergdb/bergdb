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

end Contract
