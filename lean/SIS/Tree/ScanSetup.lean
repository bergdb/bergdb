import SIS.Tree.ScanStep

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The target compare value used at one level of setup. -/
def setupTarget (forward : Bool) (start : List Int) (index : Nat) : Int :=
  match start[index]? with
  | some s => s
  | none => if forward then cvHi else cvLo

/-- Setup's node search, separated out for its live-pointer specification. -/
def setupChoice (n : KNode) (t : Time) (forward hasDiff : Bool) (sks : Int) : Option Found :=
  if hasDiff then (if forward then n.searchLt t cvHi else n.searchGt t cvLo)
  else if forward then n.searchLte t sks
  else if n.leaf then n.searchGte t sks
  else n.searchLte t sks

theorem setupChoice_mem (n : KNode) (t : Time) (forward hasDiff : Bool) (sks : Int)
    (fd : Found) (hf : setupChoice n t forward hasDiff sks = some fd) :
    (fd.c, fd.y) ∈ n.liveAt t := by
  unfold setupChoice at hf
  split at hf
  · split at hf
    · exact ((n.searchLt_spec t cvHi).1 fd hf).1
    · exact ((n.searchGt_spec t cvLo).1 fd hf).1
  · split at hf
    · exact ((n.searchLte_spec t sks).1 fd hf).1
    · split at hf
      · exact ((n.searchGte_spec t sks).1 fd hf).1
      · exact ((n.searchLte_spec t sks).1 fd hf).1

/-- A setup call on a non-key node stops without changing the chain. -/
theorem setupGo_no_node (p : Params) (v : View BVal) (t : Time) (forward : Bool)
    (start : List Int) (fuel x index : Nat) (hasDiff : Bool) (ch : Chain)
    (hn : knodeOf p v x = none) :
    setupGo p v t forward start fuel x index hasDiff ch = ch := by
  cases fuel <;> simp [setupGo, hn]

theorem knodeOf_not_data (p : Params) (v : View BVal) (x : NodeId)
    (nd : Node BVal) (hv : v x = some nd) (hd : nd.isData = true) :
    knodeOf p v x = none := by simp [knodeOf, hv, hd]

end SIS.Tree
