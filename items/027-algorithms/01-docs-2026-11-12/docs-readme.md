docs
====

The current state of BergDB in words, kept up to date with `java/` and
`lean/`:

* [levels.md](levels.md). What works, level by level: how the Java code
  does it, what checks it, its limits, and the evidence by item ID; and
  the Pub API's objects and user indexes (its section 11). Start here.
* [sis-model.md](sis-model.md). Self-indexed streams, the model that
  `lean/` formalizes and proves.
* [trace-format.md](../02-trace-format.md). The format of the traces that connect
  the Java code with the Lean model's checker.
* [log.md](../../../docs/log.md). The development log, dated entries since 12 October
  2026.
* [sources/](sources/). Frans's documents of 2012 to 2016 that the model
  builds on.

Plans, reports, reviews, evidence and alignments are items, in
[items/](../../readme.md); a new document is a subitem there, not a file
here. Cite a document by its ID and section (`001-08, section 5.5`).


Former files
============

Until 2026-10-26 `docs/` held more; the cleanup is 006-07. Each document
went to the item that wrote it, and those that no item owns to
[011-docs-archive](../../011-docs-archive/readme.md). A file keeps its
old name after its number, and its evidence went with it.

| Former file | Now | Where |
|---|---|---|
| `docs/problem.md` | 011-01 | [items/011-docs-archive/01-problem.md](../../011-docs-archive/01-problem.md) |
| `docs/prior-art.md` | 011-02 | [items/011-docs-archive/02-prior-art.md](../../011-docs-archive/02-prior-art.md) |
| `docs/startup-invariants.md` | 011-03 | [items/011-docs-archive/03-startup-invariants.md](../../011-docs-archive/03-startup-invariants.md) |
| `docs/levels.md` until 2026-10-26 | 011-04 | [items/011-docs-archive/04-levels.md](../../011-docs-archive/04-levels.md); rewritten here as [levels.md](levels.md) |
| `docs/level4-plan.md` | 011-05 | [items/011-docs-archive/05-level4-plan.md](../../011-docs-archive/05-level4-plan.md) |
| `docs/level3-plan.md` | 011-06 | [items/011-docs-archive/06-level3-plan.md](../../011-docs-archive/06-level3-plan.md) |
| `docs/level3-durability.md` | 011-07 | [items/011-docs-archive/07-level3-durability.md](../../011-docs-archive/07-level3-durability.md) |
| `docs/reference-theory.md` | 011-08 | [items/011-docs-archive/08-reference-theory.md](../../011-docs-archive/08-reference-theory.md); its Lean model, formerly `lean/References/`, beside it |
| `docs/performance-harness.md` | 011-09 | [items/011-docs-archive/09-performance-harness.md](../../011-docs-archive/09-performance-harness.md) |
| `docs/level3-performance.md` | 011-10 | [items/011-docs-archive/10-level3-performance.md](../../011-docs-archive/10-level3-performance.md) |
| `docs/level2-alignment.md` | 011-11 | [items/011-docs-archive/11-level2-alignment.md](../../011-docs-archive/11-level2-alignment.md); its section 9 continues as [trace-format.md](../02-trace-format.md) |
| `docs/level3-alignment.md` | 001-07 | [items/001-lean-model-levels-3-4/07-level3-alignment.md](../../001-lean-model-levels-3-4/07-level3-alignment.md) |
| `docs/level4-alignment.md` | 001-08 | [items/001-lean-model-levels-3-4/08-level4-alignment.md](../../001-lean-model-levels-3-4/08-level4-alignment.md) |
| `docs/level3-soak.md` | 001-09 | [items/001-lean-model-levels-3-4/09-level3-soak.md](../../001-lean-model-levels-3-4/09-level3-soak.md) |
| `docs/level4-evidence.md` | 001-10 | [items/001-lean-model-levels-3-4/10-level4-evidence.md](../../001-lean-model-levels-3-4/10-level4-evidence.md) |
| `docs/level4-performance.md` | 001-11 | [items/001-lean-model-levels-3-4/11-level4-performance.md](../../001-lean-model-levels-3-4/11-level4-performance.md) |
| `docs/handles-alignment.md` | 009-05 | [items/009-handles/05-handles-alignment.md](../../009-handles/05-handles-alignment.md) |
| `docs/evidence/` | | with the document that cites it: `level2-*.txt` in `11-level2-alignment/` (011); `reclaimgrid-*.txt` in `04-levels/` (011); `level3-redlist-baseline.txt` and `level34-conformance.txt` in `07-level3-alignment/` (001); `level4-acopy.txt` in `08-level4-alignment/` (001); `level3-soak/` as `09-level3-soak/` (001) |
