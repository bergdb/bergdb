/-
bergdb 030-21, part 2: PE's `MeetsFull` is not vacuous. PE's history from
the empty tree of three transactions (Contract/PeExample.lean: puts, a put
of a key of two segments, a delete), with its record in the model's words,
meets `MeetsFull` and K-LEVEL (its provenance computed by the kernel,
PeAdoptExample.lean), so the reads after a crash are right for it.
-/
import Contract.Proof.PeFull
import Contract.PeAdoptExample

namespace Contract.PE.FullExample

open Contract Contract.PE Contract.PE.Example Contract.PE.AdoptExample

theorem capE : cfE.topBase ≤ 2 ^ 62 := by decide

theorem lenE' : txs.length < 2 ^ 48 - 1 := by decide

/-- The example history meets `MeetsFull` and K-LEVEL. -/
theorem full : MeetsFull cfE.params hE topE ∧ KindsOK (peKind cfE) hE :=
  pe_full_of_prov cfE_ok capE lenE' keysE histE provE

end Contract.PE.FullExample
