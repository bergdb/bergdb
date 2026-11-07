011-docs-archive
================

Created 2026-10-26 by Frans Lundberg. Status: done.

The documents of `docs/` that no item owns, moved here on 2026-10-26 in the
docs/ cleanup (006-07): the work of 12 to 16 October, before the items
(the problem, prior art, the plans for Levels 3 and 4, the FileStream
power-loss report, the reference theory, the performance harness and
baseline, the Level 2 alignment), and `docs/levels.md` as it was until
then. History, not kept up to date; the current state is in `docs/`,
starting with [docs/levels.md](../../docs/levels.md). Each file keeps its old
name after its number.


Files
=====

* [01-problem.md](01-problem.md). 011-01, the problem statement, draft 1 of
  2026-10-12: the requirements R1 to R7, the invariants to prove, the open
  questions Q1 to Q12 and where each one went (2026-10-26), the prior art
  to check, Frans's sources. Formerly `docs/problem.md`.
* [02-prior-art.md](02-prior-art.md). 011-02, prior art and what seems
  novel, draft 2 of 2026-10-12. Formerly `docs/prior-art.md`.
* [03-startup-invariants.md](03-startup-invariants.md). 011-03, the startup
  of the 2017 code: its model, invariants and defects, 2026-10-12; the
  analysis that led to `docs/sis-model.md`, historical since 2026-10-13.
  Formerly `docs/startup-invariants.md`.
* [04-levels.md](04-levels.md). 011-04, `docs/levels.md` until 2026-10-26:
  drafts 1 to 8 and the status of each level, the measurements ("Level 3
  cost", "Level 2 under load", "Bounds, measured"), the Level 3 follow-up
  (W1 to W5), the reviews of 13 October, and the bugs found and fixed; the
  reclaim grid summaries it cites in [04-levels/](04-levels/).
* [05-level4-plan.md](05-level4-plan.md). 011-05, the Level 4 design and
  implementation plan, 2026-10-13 (Codex); implemented by item 001.
  Formerly `docs/level4-plan.md`.
* [06-level3-plan.md](06-level3-plan.md). 011-06, the Level 3 plan:
  durability, soak and performance baseline, 2026-10-14 (Codex); tasks 2
  and 3 done in item 001. Formerly `docs/level3-plan.md`.
* [07-level3-durability.md](07-level3-durability.md). 011-07, FileStream's
  power-loss ordering, 2026-10-14 (Codex). Formerly
  `docs/level3-durability.md`.
* [08-reference-theory.md](08-reference-theory.md). 011-08, references,
  deferred writes, reclaim and caching, 2026-10-14 (Codex); settled by
  Option K in item 001. Its exploratory Lean model, formerly
  `lean/References/`, is in [08-reference-theory/](08-reference-theory/README.md),
  with `check.sh`. Formerly `docs/reference-theory.md`.
* [09-performance-harness.md](09-performance-harness.md). 011-09, the
  performance harness for task 3 of 011-06, 2026-10-14. Formerly
  `docs/performance-harness.md`.
* [10-level3-performance.md](10-level3-performance.md). 011-10, the Level 3
  quick performance baseline, 2026-10-14, with the reference of item 001's
  WP P1 (2026-10-16). Formerly `docs/level3-performance.md`.
* [11-level2-alignment.md](11-level2-alignment.md). 011-11, the Level 2
  alignment of the Java code and the Lean model, from 2026-10-15, for the f1
  repo's F1-008-11, extended by item 001: α, the register (M1 to M19, M42,
  M47), the trace format (section 9, continued as
  [docs/trace-format.md](../../docs/trace-format.md)), the red list, the
  outcome; its evidence in [11-level2-alignment/](11-level2-alignment/).
  Formerly `docs/level2-alignment.md`.
* [12-lean-status-log.md](12-lean-status-log.md). 011-12, the Lean model's
  log: `lean/README.md`'s section Status until 2026-11-07, the dated
  milestones, proofs, checks and changes to the trusted part from
  2026-10-12 to 2026-10-28, with the line of its header that named its
  author as the first entry (bergdb 021-02). Formerly in `lean/README.md`.


Log
===

2026-10-26. Created the item, done from the start, in the docs/ cleanup
(006-07), at Frans's request ("Everything as recommended, except the log.
Keep log.md as is. [...] execute this plan and commit when you are
done."), by Claude (Opus 5.5, Claude Code). 01 to 11 are the documents
moved, each with a line on where it came from and its links fixed,
otherwise unchanged; 011-01 got a note on where its open questions went,
and section 9 of 011-11 a pointer to `docs/trace-format.md`.

2026-11-07. Added 011-12, `lean/README.md`'s section Status, a dated log,
moved here as it was (links fixed), with the line of its header that named
its author; `lean/README.md`'s Status keeps the current state without
dates (bergdb 021-02; Frans, 2026-11-07, 08:00: "For a., do as
recommended."). By agent f13 of coord-1107.
