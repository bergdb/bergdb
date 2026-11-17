/-
The gate of bergdb 030-04, section 7.6: the axioms that the theorems rest on.
`lake env lean Axioms.lean` prints them; gate.sh checks that they are Lean's
three standard ones only.
-/
import Contract

open Contract

#print axioms inv_right
#print axioms get_right
#print axioms scan_right
#print axioms checkTx_sound
#print axioms historyOk_meets
#print axioms Contract.Example.meets
#print axioms Contract.Example3.meets
#print axioms Contract.ExampleDag.meets
#print axioms tree_right
#print axioms MeetsShape.meets
#print axioms checkShapeTx_sound
#print axioms Contract.Example3.meetsShape
#print axioms Contract.ExampleDag.not_tree
#print axioms findTop_right
#print axioms top_right
#print axioms jget_right
#print axioms jscan_right
#print axioms skip_closure
#print axioms skip_dead
#print axioms checkTopTx_sound
#print axioms Contract.Example3.meetsTop
#print axioms historyTopOk_meetsTop
#print axioms applyTx_rebuilds
#print axioms applyTx_linesOf
#print axioms java_start
#print axioms java_meetsTop
