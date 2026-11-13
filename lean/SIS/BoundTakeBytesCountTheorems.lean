/-
Self-indexed streams in Lean: bounds, part 1, BergDB's take with its byte limit,
counted in transactions (bergdb item 007; 007-09's second review). Trusted
part: the statement. The definitions it is about are in SIS/BoundTakeBytes.lean
(`takePolicyB`) and SIS/Bound.lean; the proof in SIS/Proof/BoundTakeBytes.lean.
Added 2026-11-13.

In plain words: the byte limit cannot stop the take's progress when each
transaction's own nodes fit in the limit (005-31): the section then holds
fewer than 2 M / m + 2 transactions, m the least cost of a record. What it can
break is `T3_take`'s bound on the span in cost: transactions that wait behind
the limit may be costly (SIS/BoundTakeBytesExample.lean, case 2).
-/
import SIS.Proof.BoundTakeBytes

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T3 for BergDB's take with its byte limit, in transactions: with settings at
most M in T(1), ..., T(k), every record costing at least m, and the got-dirty
nodes of each single transaction of D fitting in the limit (`nodeB` bytes a
node) before every transaction, the startup section after T(k) has at most one
transaction, or n of them with (n - 2) m < 2 M. -/
theorem T3_takeB_count (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (sd : Time → Nat)
    (pace : Pace V T) (nodeB maxB : Nat) (hp : al.policy = takePolicyB size sd pace nodeB maxB)
    (M m : Nat) (ts : List T) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R)
    (hfit : ∀ j < ts.length, ∀ τ,
      ((run sp al (ts.take j)).D.filter (fun e => e.2 == τ)).length * nodeB ≤ maxB) :
    let S := (run sp al ts).S
    ((sectionIdx S (lastSp S)).length - 2) * m < 2 * M ∨ (sectionIdx S (lastSp S)).length ≤ 1 :=
  takeB_count sp al size sd pace nodeB maxB hp M m ts hM hm hfit

end SIS
