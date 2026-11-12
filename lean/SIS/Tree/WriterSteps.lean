import SIS.Tree.MergeProps

namespace SIS.Tree

open SIS SIS.Check

/-- One append step, including compaction when the write exceeds theta. -/
theorem appendKlongs_step_dead (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    appendKlongs depth x ins = (do
      let c ← read
      let n ← getNode x
      let up : NodeId → List (Nat × NodeId) → M Unit := match depth with
        | 0 => fun _ _ => throw "corrupt: a split's parent above depth 0"
        | d + 1 => fun q more => appendKlongs d q more
      if n.size + ins.length + 1 > c.p.M then
        handleFullWith up depth x ins (n.lastVersion c.i)
      else if deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) then
        handleFullWith up depth x ins (n.lastVersion c.i) true
      else addKeys x ins) := by
  cases depth <;> rfl

end SIS.Tree
