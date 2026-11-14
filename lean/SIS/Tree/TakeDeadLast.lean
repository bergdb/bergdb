/-
A fact for the take-back's (B), (C) and node facts after a split of a full node
with a last version given by the caller and its cascade (bergdb 024-12, TP7): a
delete's full leaf (`lastVersionGivenDel`) or a merge's full parent
(`mergeFullLast`).
-/
import SIS.Tree.TakeDeadChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node left behind holds no klong of the transaction's time. -/
theorem time_not_mem_toPrev (n : KNode) (t : Time) (hpos : 0 < t) :
    Klong.time t ∉ (n.toPrev (t - 1)).ks := by
  intro h
  have := time_le_of_mem_prefixAt n.ks (t - 1) t h
  omega

end SIS.Tree
