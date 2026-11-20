/-
bergdb 030-29: the dirty-node bound's premises are not vacuous. With Java's
parameters at node size 30 (h = c = 17, m = 8, theta = 7, cut size 15), keys
of up to 4 segments and heights up to 15, the empty tree is a state PE keeps
and meets the fill rules (`FillOk`), PE accepts a transaction of two puts
from it, and `pe_dirtyNodeBound_puts` applies: PE writes one key node, the
new space root (the empty leaf with two entries appended), and Java's count
is one, the space root walked.
-/
import Contract.Proof.DnbMain

namespace Contract.PE.DnbExample

open Contract Contract.PE

/-- Java's parameters at node size 30, G = 3, H = 15. -/
def cfJ : Cfg := Cfg.java 30 3 15

/-- Two puts of keys of one segment. -/
def ops : List Op := [.put [72] 5, .put [80] 6]

theorem fill0 : FillOk 30 15 (startTree cfJ) := by unfold FillOk; decide

theorem acc1 : (peTx cfJ 1 (startTree cfJ) startTop startNext ops).isSome = true := by
  decide +kernel

def o1 : Out := (peTx cfJ 1 (startTree cfJ) startTop startNext ops).get acc1

/-- The theorem applies to the empty tree and the two puts. -/
theorem bound : DNB.keyWrites o1.ws ≤ DNB.dirtyNodeBound 30 (startTree cfJ) 0 (DNB.opsKd ops) :=
  pe_dirtyNodeBound_puts (b := 30) (G := 3) (H := 15) (by decide)
    (start_inv (cf := cfJ) (cfgOk_java (b := 30) (G := 3) (H := 15) (by decide)).1).1 fill0 (fun op hop => by
      simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> exact ⟨_, _, rfl⟩) (Option.some_get acc1).symm

/-- PE writes one key node and Java counts one: the bound is met exactly. -/
theorem writes_one : DNB.keyWrites o1.ws = 1 := by decide +kernel

theorem count_one : DNB.dirtyNodeBound 30 (startTree cfJ) 0 (DNB.opsKd ops) = 1 := by
  decide +kernel

end Contract.PE.DnbExample
