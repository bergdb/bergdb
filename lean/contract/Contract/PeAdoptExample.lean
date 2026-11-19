/-
bergdb 030-21, part 2: `pe_adopt_hist` is not vacuous. PE's history from the
empty tree of three transactions (puts, a put of a key of two segments, a
delete; the history of Contract/PeExample.lean) has its provenance (`Prov`,
computed by the kernel with `provB`), so it meets A6' at every time and
A-COPY at every transaction.
-/
import Contract.Proof.PeAdopt
import Contract.PeExample

namespace Contract.PE.AdoptExample

open Contract Contract.PE Contract.PE.Example

theorem accH : (peHist cfE txs).isSome = true := by decide +kernel

/-- The history and its tops. -/
def hE : BHist := ((peHist cfE txs).get accH).1

def topE : Nat → Top := ((peHist cfE txs).get accH).2

theorem histE : peHist cfE txs = some (hE, topE) := by
  rw [← Option.some_get accH]
  rfl

theorem keysE : ∀ ops ∈ txs, (ops.map Op.key).Nodup := by decide

theorem lenE : hE.txs.length = 3 := by decide +kernel

/-- Every transaction's provenance, computed. -/
theorem provE_b : (List.range 3).all (fun j =>
    provB (hE.tree j) (hE.tree (j + 1)) ((hE.txs[j]?.map (·.D)).getD [])) = true := by
  decide +kernel

theorem provE : ∀ j (hj : j < hE.txs.length), Prov (hE.tree j) (hE.tree (j + 1)) hE.txs[j].D := by
  intro j hj
  have h1 := List.all_eq_true.mp provE_b j (List.mem_range.mpr (lenE ▸ hj))
  simp only [List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some] at h1
  exact provB_sound h1

/-- The history meets A6' at every time and A-COPY at every transaction. -/
theorem adoptCopy :
    (∀ j, j ≤ hE.txs.length → adoptOk ((hE.tree j).at j) = true) ∧
    (∀ j (hj : j < hE.txs.length),
      copyOk (j + 1) (hE.tree j) (hE.tree (j + 1)) (topE j) hE.txs[j].c = true) ∧
    ∀ j, j ≤ hE.txs.length → InvA cfE (hE.tree j) :=
  pe_adopt_hist cfE_ok keysE histE provE

end Contract.PE.AdoptExample
