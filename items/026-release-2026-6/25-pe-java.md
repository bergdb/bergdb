# 026-25. Java's writer as PE, "plan, then emit"

Created 2026-11-19 by Frans Lundberg. Status: open.

Java's write half replaced by PE, the writer that 030-21 proved to meet
the writer's contract (`Contract.PE.peTx`, lean/contract/Contract/
PeWriter.lean): for each transaction, a plan over the tree from the
transaction's whole batch, then each decided node emitted once; node for
node the trees of the model on the traces. The level scripts' oracle is
then PE too. Frans, 2026-11-18, 21:42: "If you successfully prove it, feel
free to do the Java implementation too. Opus high for that." By an agent of
coord-1118, from 02:10 on 2026-11-19, on the branch `026-25-pe-java` in
/Users/f/fl/bench/2026-11-19/pej/clone.


# Result

(To be written when the work is gated.)


# 1. The plan

From 026-24's recommendation, step 2, and coord-1118's brief:

1. **Java's write half replaced by PE** (java/src/bergdb/dag/PeWriter.java,
   called by `Dag.putKvs`): the program of PeWriter.lean, rule for rule;
   the record's KVs given to the Dag as one batch (`Db.putKvs`, and the
   start's rerun, `DbStarter.rerunTransaction`). Reads, recovery, startup,
   eviction, reclaim's cut and the stream's layout stay; reclaim's own
   transactions go through the new writer. The cut size a parameter,
   `Dag.cutSize`, M / 2 (026-24, section 2.6), as PeWriter.lean's `cap`.
2. **The oracle**: the tree checker's writer (`treecheck`, the level
   scripts) is PE: lean/SIS/Tree/Pe.lean, a copy of PeWriter.lean on the
   model's P (lean/contract imports lean/SIS, so lean/SIS cannot import
   it), shown to give PeWriter.lean's trees on the traces by a tool of this
   item (`pecmp`, section 3).
3. **The record format**: decided by 027-03, section 21 (section 4).
4. **Simplify**: today's take-back, its books, the in-place splits, the
   merges at the delete, the upward unlink and the splits removed (section
   5).
5. Not touched: the creation path (028-18 waits for Frans), lean/contract.


# 2. Progress

(Kept current while the work goes on.)


# State

2026-11-19, 02:45. Started. The oracle written (lean/SIS/Tree/Pe.lean, wired
into Check/Tree.lean, Check/TreeRun.lean, TreeCheck.lean; on today's Java it
reports the expected differences). Next: PeWriter.java.


# Log

2026-11-19. Created the item; the clone at main b15f4b1b, branch
`026-25-pe-java` (02:10). The oracle, lean/SIS/Tree/Pe.lean (02:20 to
02:45).
