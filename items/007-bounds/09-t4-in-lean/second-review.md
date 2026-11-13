- **wrong — [BoundColdDrop.lean:52](lean/SIS/BoundColdDrop.lean:52):** `lostLive.length ≤ ... c.adds ... .length` fails for Java bitmaps. One `.del [a,b,c]` entry removes three children; I evaluated this counterexample. `Dag.appendDeleteKlong` updates `node.klongs[sz - 1] = union` ([Dag.java:1155](java/src/bergdb/dag/Dag.java:1155)). Charge deleted compare values, not entries.

- **wrong — [BoundColdDrop.lean:54](lean/SIS/BoundColdDrop.lean:54):** `adopted` requires every former child of a removed node to remain reachable. Java’s `Dag.deleteUpward` instead executes `unlink(n, pd)` along an emptied chain ([Dag.java:1309](java/src/bergdb/dag/Dag.java:1309)). Parent and child can both disappear. Replace this assumption with a removal bound covering deletes and cascading replacements.

- **unclear — [BoundT4.lean:96](lean/SIS/BoundT4.lean:96):** `RecordBound` limits only `R.gd.filter (inD db.D)`. Arbitrarily many unrelated, repeated IDs outside D satisfy it. Thus 007-01 §5.1’s “cost at most a transaction plus the debt” needs more: constrain and count fresh got-dirty IDs, then supply byte weights.

- **wrong — read interpretation of [BoundColdDTheorems.lean:30](lean/SIS/BoundColdDTheorems.lean:30):** the conclusion bounds `.next`, not reads. For `runJ 8`, the section contains **22 index versions**, but its RHS is **17**; model `.next` is 13. `sectionNodes` uses `eraseDups`, whereas Java’s `StoredTrans.Parser.parse` retains every version with `nodeList.add(stored)` ([StoredTrans.java:379](java/src/bergdb/core/StoredTrans.java:379)). Count sequential versions separately.

- **wrong — [BoundCold.lean:14](lean/SIS/BoundCold.lean:14):** “rule 4 reads nothing” misses Java’s top-node fallback, `cache.liveHandle(idOf(pos))` in `NodeCollection.linkToCanonical` ([NodeCollection.java:807](java/src/bergdb/core/NodeCollection.java:807)). Assertion checks also read headers. Ordinary `followStreamPointer` calls `readNodeHeader` before finding a cached object. These reads allocate no object; add explicit header-read accounting.

- **wrong — [Phys.lean:312](lean/SIS/Phys.lean:312), underlying `rerunReach`:** `pathOf` counts ancestors of changed, touched or removed nodes. Java’s `Dag.merge` can read the left sibling, reject it, then read the right ([Dag.java:2135](java/src/bergdb/dag/Dag.java:2135)); the unused sibling stays unchanged and reachable. Count the actual operation footprint, including quiet follows.

- **unclear — [BoundT4JavaTheorems.lean:60](lean/SIS/BoundT4JavaTheorems.lean:60):** `hQ : ∀ z, ... ≤ Q` covers all historical parents, stronger than 007-01 §6’s “such nodes point to a node of D”. TREE bounds current parents only. A per-run Q exists, but no useful uniform Java Q is established. Prove/check that premise or retain an explicitly conditional result.

- **unclear — [BoundT4Theorems.lean:89](lean/SIS/BoundT4Theorems.lean:89):** `n0.level + 1` is not Java’s tree height. `TraceExport.levelOf` assigns the virtual root `keyMax + 2 + MAX_TOP_NODE_ID_VALUE` ([TraceExport.java:1608](java/stress/TraceExport.java:1608)). This can include the whole history. `PtrHeightLe` counts pointer edges correctly, but includes dead top-node chains; establish a useful height bound.

- **fine — [BoundT4.lean:42](lean/SIS/BoundT4.lean:42), [BoundCold.lean:32](lean/SIS/BoundCold.lean:32):** `spAt`, `spIter`, `levelOf`, `onAccessPath`, `changeAt`, `rerunReach` and `removedAt` have consistent time boundaries. The dated 007-01 §6 correction explicitly permits “lev(x) + 1 sections”. Touch inclusion is appropriate.

- **fine, conditional — [Assumptions.lean:88](lean/SIS/Assumptions.lean:88):** RunOK’s net-change interpretation fits `Db.setIdOfNode`, `Dag.handleFullNode`/`unlink`, `Db.endOfTrans` and `Db.touchPaths`; TREE fits `TopDs.newSuperRoot`. `javaTest` matches pointer resolution followed by `Db.handleStillDirtyNodes`’ fixpoint. `LiveAppend` is proved for `blive`. This is supporting correspondence, not a proof for every Java execution.

- **fine, limited examples — [BoundT4Example.lean:70](lean/SIS/BoundT4Example.lean:70):** all three examples’ guards passed from source under Lean 4.34.1, without a project build or file edits. Additional checks confirm TREE for X, DropRunOK for X/J, and its failure for D. J satisfies the Java/cold premises with Q = 9 at m = 8. All three use `virt = false`; none exercises Java’s virtual-root case. Exact-test theorems explicitly exclude that case.

- **unclear — [Bound.lean:107](lean/SIS/Bound.lean:107):** the abstract take always honors its deadline; Java’s `TransSeq.take` says a transaction exceeding `maxBytes` is skipped “also after the deadline” ([TransSeq.java:175](java/src/bergdb/core/TransSeq.java:175)). Establish that this cannot interrupt required progress before applying T3 to current Java.

- **unclear — 007-09 §5:** “no T4 statement covers that yet” and the missing no-D result are stale relative to `BoundT4JavaTheorems` and `BoundColdDTheorems`; update the inventory.

- **1 — wrong:** several definitions/accounting claims fall short of the intended Java bounds.
- **2 — fine/unclear:** examples establish nonvacuous abstract cases; useful Java Q/height bounds remain conditional.
- **3 — wrong:** DropStep and the allocation-to-read interpretation fail for current Java.
- **4 — unclear:** no indexing off-by-one found; revise the cost model, Java correspondence and write-up.