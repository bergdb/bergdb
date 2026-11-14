/-
The writer's reading at a fuel f (bergdb 024-22, 024-12's (4), option (a)):
`wGet` at `p.fuel` is `wGetAt` at f := p.fuel. States inside an operation are
read at a fuel above the writer's, the operation's end at the writer's.
-/
import SIS.Tree.GetWriter

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's reading of a key at a fuel f. -/
def wGetAt (p : Params) (i : Time) (base : View BVal) (w : W) (f : Nat) (key : Key) : Option Nat :=
  getFromR (wNode p base w) (wValue base w) i f key w.top.rootKey

end SIS.Tree
