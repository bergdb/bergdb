001-lean-model-levels-3-4
=========================

Created 2026-10-16 by Frans Lundberg. Status: open.

Model Levels 3 (reclaim) and 4 (eviction, data larger than memory) in Lean,
and align the model with the Java code, as was done for Level 2 in the f1
repo's F1-008-11 and its report
[F1-008-12](../../../f1/b/008-bergdb-lean-model/12-level2-alignment-report-claude.md).

Decided on 2026-10-16: one plan for both levels, caching before reclaim, and
Level 4's model may change Java's Level 3.


Files
=====

* [01-plan.md](01-plan.md). 001-01, the plan: the stages, and the work
  packages, checkpoints and decisions for unattended work, to a Java
  implementation and a matching Lean model at every level.
* [02-progress.md](02-progress.md). 001-02, the progress of the plan:
  Frans's go and decisions, the status of each work package, the log.


Log
===

2026-10-16. Created the item.

2026-10-16. Frans decided the three open questions. Added 001-01, an
overview of the plan.

2026-10-16. Claude extended 001-01 into the detailed plan, on Frans's
request, and added 001-02, its progress file. Work waits for Frans's go
(G0).
