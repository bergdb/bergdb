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
#print axioms mem_blive_entriesOf
#print axioms bridge_runOK
#print axioms bridge_rep
#print axioms bridge_recovery
#print axioms bridge_crash
#print axioms bridge_restart
#print axioms MeetsBridge.meets
#print axioms madeCheck_sound
#print axioms Contract.BridgeExample.meets
#print axioms MeetsBridge.meetsShape
#print axioms bridge_treeRunOK
#print axioms bridge_evictRunOK
#print axioms bridge_lazy_read
#print axioms bridge_lazy_restart
#print axioms bridge_handles_records
#print axioms bridge_handles_read
#print axioms bridge_handles_evict
#print axioms bridge_handles_pos
#print axioms bridge_cut_recover
#print axioms bridge_cut_restart
#print axioms bridge_cut_handles
#print axioms Contract.BridgeExample.meetsEvict
#print axioms checkBridgeTx_sound
#print axioms checkEvictTx_sound
#print axioms frame_modelD
#print axioms bridge_debt
#print axioms bridge_liveHeight
