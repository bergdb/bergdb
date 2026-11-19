/-
bergdb 030-21, part 3: the premises of PE's acceptance are not vacuous. With
Java's thresholds at node size 30 (`Params.withMerges`: h = c = 17, m = 8,
theta = 7; cap = h), keys of up to 4 segments and heights up to 15, the empty
tree leaves room (`Room`) and the fuel suffices (`FuelOk`) for every
transaction of at most 1,000 operations, so PE accepts every such transaction
whose puts' keys the tree can hold (`accepts`), by `pe_accepts`.
-/
import Contract.Proof.PeAccept

namespace Contract.PE.AcceptExample

open Contract Contract.PE

/-- Java's thresholds at node size 30, G = 3, H = 15. -/
def cf0 : Cfg := { M := 30, G := 3, H := 15, m := 8, c := 17, h := 17, theta := 7, cap := 17 }

theorem cf0_ok : cf0.Ok := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem room {p : Nat} (hp : p ≤ 1000) : Room cf0 (startTree cf0) p := by
  refine ⟨by decide, by decide, fun y hy => ?_⟩
  rw [start_reach] at hy ⊢
  simp only [List.mem_singleton] at hy
  subst hy
  have h0 : htIn cf0 (startTree cf0) 1 = 0 := by decide
  rw [h0]
  have : (2 : Nat) ^ (cf0.H - 0) = 32768 := by decide
  simp only [List.length_singleton, this]
  omega

theorem fuelOk {p : Nat} (hp : p ≤ 1000) : FuelOk cf0 p := by
  unfold FuelOk fuel
  simp only [cf0]
  omega

/-- **From the empty tree, PE accepts every transaction of at most 1,000
operations whose puts' keys the tree can hold.** -/
theorem accepts {ops : List Op} (hp : ops.length ≤ 1000)
    (hputs : ∀ k v, Op.put k v ∈ ops → keyOk cf0 k = true) :
    ∃ o, peTx cf0 1 (startTree cf0) startTop startNext ops = some o :=
  pe_accepts cf0_ok (start_inv cf0_ok).1 hputs (fuelOk hp) (room hp)

end Contract.PE.AcceptExample
