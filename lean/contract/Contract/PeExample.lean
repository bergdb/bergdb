/-
bergdb 030-21: PE's theorems are not vacuous. With record format 7's
parameters at node size 8 (h = c = 4, m = 2, theta = 2; cap = h, as the
trial's mode pe), PE accepts transactions from the empty tree, so there are
histories it writes, and `pe_meetsTop_start` holds for them: a history of
three transactions (puts, a put of a key of two segments, a delete) meets
`MeetsTop`. The trace runs of 030-21 (21-pe-proof/runs) show PE accepting
all 221,142 transactions of 288 traces.
-/
import Contract.Proof.PeTx

namespace Contract.PE.Example

open Contract Contract.PE

/-- Record format 7's parameters at node size 8. -/
def cfE : Cfg := { M := 8, G := 3, H := 5, m := 2, c := 4, h := 4, theta := 2, cap := 4 }

theorem cfE_ok : cfE.Ok := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Three transactions: puts of keys of one segment; a put of a key of two
segments (its first segment long, 56) and of one more key; a delete. -/
def txs : List (List Op) :=
  [[.put [72] 5, .put [80] 6, .put [88] 7],
   [.put [56, 136] 8, .put [96] 9],
   [.del [80]]]

theorem acc1 : (peTx cfE 1 (startTree cfE) startTop startNext (txs[0]!)).isSome = true := by
  decide +kernel

def o1 : Out := (peTx cfE 1 (startTree cfE) startTop startNext (txs[0]!)).get acc1

theorem acc2 : (peTx cfE 2 (o1.tree (startTree cfE)) o1.top o1.next (txs[1]!)).isSome = true := by
  decide +kernel

def o2 : Out := (peTx cfE 2 (o1.tree (startTree cfE)) o1.top o1.next (txs[1]!)).get acc2

theorem acc3 : (peTx cfE 3 (o2.tree (o1.tree (startTree cfE))) o2.top o2.next (txs[2]!)).isSome = true := by
  decide +kernel

def o3 : Out := (peTx cfE 3 (o2.tree (o1.tree (startTree cfE))) o2.top o2.next (txs[2]!)).get acc3

/-- PE accepts the three transactions: a history PE writes. -/
theorem hist : PeHist cfE (startTree cfE) startTop startNext txs
    (o3.tree (o2.tree (o1.tree (startTree cfE)))) o3.top o3.next := by
  have h1 := PeHist.step (txs := []) (ops := txs[0]!) (o := o1) PeHist.start (Option.some_get acc1).symm
  have h2 := PeHist.step (ops := txs[1]!) (o := o2) h1 (Option.some_get acc2).symm
  have h3 := PeHist.step (ops := txs[2]!) (o := o3) h2 (Option.some_get acc3).symm
  exact h3

/-- The history meets the contract with TREE and the top. -/
theorem meetsTop : MeetsTop cfE.params txs (o3.tree (o2.tree (o1.tree (startTree cfE)))) o3.top :=
  pe_meetsTop_start cfE_ok hist

end Contract.PE.Example
