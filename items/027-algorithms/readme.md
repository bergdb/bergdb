027-algorithms
==============

Created 2026-11-12 by Frans Lundberg. Status: open.

The algorithms of BergDB as they are, kept current with `java/` and
`lean/`, as 024-02 is for the stream format. Language-neutral: for every
implementation of BergDB (Java, C and those to come). Each algorithm with
what it does, its invariants, its cost bounds (024-04's aims 2 and 3,
024-05's bounds, 024-30's gates), its Lean counterpart (the definitions,
what is proved, what is open, the conformance checks), its Java classes,
its tests, and the principles and rules it serves (010-01, 010-04).

So far **a placeholder**: what the item is about, with no contents and
no plan of its sections yet. Its structure and contents are to be worked
out later, with Frans, carefully and without release stress (Frans,
2026-11-12, 14:45: "What I mean, was just a placeholder item really. Not
a plan for sections with names. I would like to do that later. [...] I
will have another agent do this later. Carefully without release
stress. I will be part of that work.").


Frans's words
=============

Frans, 2026-11-12, 14:17: "The release theme is solid database
algorithms. The Lean is on a good way to prove them solid. The
implementation is also about done. [...] However, I think we are missing
coherent documentation of the algorithms. Or? There are documents in
docs/, but I would like to have this as proper, maintained item."

Frans, 2026-11-12, 14:27: "Yes, create the item as a skelleton only.
Contents for later. About existing stuff in docs/. This was there before
we started with items/. We could create an item for the old-era. Nice to
keep those; what's in sources/. It can be a subitem of the new item for
"The algorithms of BergDB". I would like to remove everything from docs/
now. [...] We then have a reference to them, we don't update them, but
they are there for reference, a snapshot in time. There is one value with
them. [...] the division of functionality into "levels" was very useful to
get the old code base stability. There were bugs all over and it really
helped. Now, I don't know how important this division it."


The former docs/
================

Everything that was in `docs/` but the log moved into this item on
2026-11-12:

* `levels.md`, `sis-model.md`, `sources/` and `readme.md` (as
  `docs-readme.md`) are 027-01, a snapshot: not updated since. Until a
  part of 027 is written, 027-01's `levels.md` and `sis-model.md` are
  the best description of what they cover, as of 2026-11-12.
* **One exception, for Frans to overturn:** `trace-format.md` is 027-02
  and is **kept current**, not a snapshot. The trace exporter
  (`java/stress/TraceExport.java`) and the checkers (`lean/Check/*.lean`,
  `lake exe tracecheck`, `lake exe treecheck`) implement it, and it must
  change with them; a frozen copy would be wrong at the next format
  change. Overturning it means freezing it in 027-01 and writing the trace
  format into 027 itself.

* `log.md` stays in `docs/`, the development log, still written: Frans,
  2026-11-12, 14:32: "Some type of log is good to have. Let's keep log.md
  for now." `docs/` holds nothing else.

No script or build reads a file under `docs/` (checked: the level
scripts, `night.sh`, `conformance.sh`, `build.sh`, `before-commit.sh`).
The code's comments cite 027-01 and 027-02 by ID.


Questions for Frans
===================

* The trace format's exception (027-02 kept current, not a snapshot):
  keep it? Default: keep.
* 024-02, the stream format, is a maintained description inside a release
  item. Move it into 027 when 2026.5 is done? Default: leave it where it
  is until then.


Files
=====

* [01-docs-2026-11-12/](01-docs-2026-11-12/readme.md). 027-01, the former
  `docs/` as of 2026-11-12, a snapshot for reference, not updated:
  `levels.md`, `sis-model.md`, `sources/` and the old `docs-readme.md`.
* [02-trace-format.md](02-trace-format.md). 027-02, the format of the
  traces that connect the Java code with the Lean model's checkers, moved
  from `docs/trace-format.md`; kept current.


Log
===

2026-11-12. Created the item (Frans, 14:17 and 14:27) as a placeholder. `docs/` moved in: 027-01, a snapshot,
and 027-02, the trace format, kept current; `docs/log.md` stays where it
is (Frans, 14:32); the references in `java/`, `lean/`, the level
scripts, `AGENTS.md`, `README.md` and `items/readme.md` point here, by ID. Old items keep their
links to `../docs/` (items are history). By agent docsmv of coord-1112, on
the branch `027-algorithms`.

2026-11-12, 14:45. The planned sections and their names removed: a
placeholder only, its structure to be worked out later with Frans
(14:45).


State
=====

Done: the placeholder, 027-01 and 027-02 moved (`docs/` keeps only
`log.md`), the references changed. Next: the structure and contents,
later, with Frans.

