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
#print axioms Contract.BridgeExample.w4_not_enough
#print axioms bridgeHistoryOk_meets
#print axioms MeetsBridgeTop.meetsBridge
#print axioms Contract.BridgeExample3.meetsTop
#print axioms Contract.BridgeExample3.meetsBridge
#print axioms MeetsFull.meetsBridge
#print axioms MeetsFull.meetsEvict
#print axioms Contract.BridgeExample3.meetsFull
#print axioms fullHistoryOk_meets
#print axioms MeetsFull.meetsTop
#print axioms full_recovery
#print axioms full_restart
#print axioms full_eviction
#print axioms full_cut
#print axioms writerMeets_of_opStep
#print axioms runs_meetsTop_of_opStep
#print axioms invOk_iff
#print axioms Good.ctx
#print axioms ctx_route
#print axioms ctx_reach
#print axioms lastVersion_ks
#print axioms replaceOrAdd_spec
#print axioms getNode_spec
#print axioms newSuperRoot_spec
#print axioms halves_spec
#print axioms sound_iff
#print axioms Sound.put
#print axioms Sound.timeSplit
#print axioms Sound.spaceSplit
#print axioms Sound.spaceSplitRoot
#print axioms handleFull_time
#print axioms handleFull_space
#print axioms appendKlongs_spec
#print axioms putKv_put1
#print axioms writerMeets_put1
#print axioms runs_meetsTop_put1
