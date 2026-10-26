001-lean-model-levels-3-4
=========================

Created 2026-10-16 by Frans Lundberg. Status: done.

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
* [03-k1-review.md](03-k1-review.md). 001-03, the K1 review guide: the
  Level 4 design, what is proved and checked, the Java changes, the
  decision K1 asks of Frans.
* [04-k3-review.md](04-k3-review.md). 001-04, the K3 review guide: the
  Level 3 alignment, what is proved and checked, R9's conformance, the
  conformance step in `level3.sh`; passed by the agent on Frans's go.
* [05-k4-review.md](05-k4-review.md). 001-05, the K4 review guide: Level 4
  in Java, the evidence, the changes, eviction on by default and
  `level4.sh` a required gate; passed by the agent on Frans's go.
* [06-final-report.md](06-final-report.md). 001-06, the final report (WP
  F3): the outcome of the plan for Levels 3 and 4, what changed, the
  findings, and what Frans decides at K5.
* [07-level3-alignment.md](07-level3-alignment.md). 001-07, the Level 3
  alignment (WPs A2, R1 to R9): α for reclaim, the register (M17, M32 to
  M38, M41, M48), what makes a cut safe, the red list, conformance; its
  evidence in [07-level3-alignment/](07-level3-alignment/). Formerly
  `docs/level3-alignment.md`.
* [08-level4-alignment.md](08-level4-alignment.md). 001-08, the Level 4
  alignment (WP A2 on): α for the cache, the register (M20 to M31, M39, M40,
  M43 to M46, M49), the probes, the design of eviction and its theorems (section
  5), what Java must do, Level 4 in Java, the outcome; its evidence in
  [08-level4-alignment/](08-level4-alignment/). Formerly
  `docs/level4-alignment.md`.
* [09-level3-soak.md](09-level3-soak.md). 001-09, the Level 3 soak (WP
  P2): two hours on disk at the pilot scale, and the companion; the runs'
  output in [09-level3-soak/](09-level3-soak/). Formerly
  `docs/level3-soak.md`.
* [10-level4-evidence.md](10-level4-evidence.md). 001-10, Level 4 larger
  than memory (WPs J8 and P4). Formerly `docs/level4-evidence.md`.
* [11-level4-performance.md](11-level4-performance.md). 001-11, Level 4's
  performance against Level 3 (WP J10). Formerly
  `docs/level4-performance.md`.


Log
===

2026-10-16. Created the item.

2026-10-16. Frans decided the three open questions. Added 001-01, an
overview of the plan.

2026-10-16. Claude extended 001-01 into the detailed plan, on Frans's
request, and added 001-02, its progress file. Work waits for Frans's go
(G0).

2026-10-17. Claude added 001-03, the K1 review guide (WP E7): stage 2 is
done, and K1 waits for Frans.

2026-10-18. Claude added 001-04, the K3 review guide (WP R9): stage 3 is
done, and K3 passed (by the agent, on Frans's go of 2026-10-17 19:59).

2026-10-18. Claude added 001-05, the K4 review guide (WP J10): stage 4 is
done, and K4 passed (by the agent, on Frans's go of 2026-10-17 19:59).

2026-10-18. Claude added 001-06, the final report (WP F3): every WP is done
but R6 (partial: T-SCHEME checked, not proved); at K5 the agent accepted
the outcome, and closing the item and what comes next wait for Frans.

2026-10-19. Frans accepted the outcome (K5), with R6 as it is, and
closed the item. Status: done.

2026-10-26. 07 to 11 added: the five documents this item wrote in `docs/`,
moved here in the docs/ cleanup (006-07), each with a line on where it came
from and its links fixed, otherwise unchanged.
