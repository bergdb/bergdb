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

So far **a skeleton only**: the planned sections below, each with its main
sources, none written. The contents come later (Frans, 14:27: "Contents
for later").


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
  section below is written, 027-01's `levels.md` and `sis-model.md` are
  the best description of what they cover, as of 2026-11-12.
* **One exception, for Frans to overturn:** `trace-format.md` is 027-02
  and is **kept current**, not a snapshot. The trace exporter
  (`java/stress/TraceExport.java`) and the checkers (`lean/Check/*.lean`,
  `lake exe tracecheck`, `lake exe treecheck`) implement it, and it must
  change with them; a frozen copy would be wrong at the next format
  change. Overturning it means freezing it in 027-01 and writing the trace
  format as a section of 027 (section 14 below).

* `log.md` stays in `docs/`, the development log, still written: Frans,
  2026-11-12, 14:32: "Some type of log is good to have. Let's keep log.md
  for now." `docs/` holds nothing else.

No script or build reads a file under `docs/` (checked: the level
scripts, `night.sh`, `conformance.sh`, `build.sh`, `before-commit.sh`).
The code's comments cite 027-01 and 027-02 by ID.


Planned sections
================

Each section, when written, says what the algorithm does, its invariants,
its cost bounds, its Lean counterpart, its Java classes, its tests and the
principles and rules it serves. The levels are the backbone where they fit
(Frans's note above: they helped to make the old code stable; whether they
stay the structure is open). Sources are item IDs; 027-01's files are
cited by name.

1. **Overview.** The multiversion map of byte keys and values, times,
   the self-indexed stream, the Core and what is built on it, the levels.
   Sources: 027-01's levels.md, sections 1 and 2; sis-model.md, sections 1
   to 3; 010-01; 011-01. Not written.
2. **The stream and its records.** What a transaction appends: records,
   nodes, meta blocks, the node checksum; the format itself stays 024-02.
   Sources: 024-02, 024-25, 014, sis-model.md, section 4. Not written.
3. **Transactions and the STM.** A commit from start to the go point,
   "the last operation wins", refused calls, a transaction or a read that
   fails. Sources: 024-10, 024-16, 024-27, 020-10; 027-01's levels.md,
   section 3. Not written.
4. **The key tree.** Segments and klongs; search (get, scan); put and
   delete; splits and time splits; merges at the delete; the dead-klong
   rule; root collapse; the node size. Sources: 024-02, 024-11, 024-12,
   024-14, 024-15, 024-18, 024-19, 024-21, 024-22, 024-23; 023 (023-05).
   Not written.
5. **Writing the index.** Dirty nodes, got dirty, the take, still dirty
   (Rule A), the order of writing. Sources: sis-model.md, sections 5 and
   6.1; 024-12. Not written.
6. **Restart by replay (Level 1).** Startup that reads the whole stream;
   restart invariance (T2). Sources: 027-01's levels.md, section 4;
   sis-model.md, sections 6.2 and 9. Not written.
7. **Bounded startup (Level 2).** The startup section, the startup pos
   policy, the take and its pace, Rule R, the cold start's reads, T1 and
   T3. Sources: 007 (007-01 to 007-08), 024-31; sis-model.md, sections
   6.2, 8 to 10; 027-01's levels.md, section 5. Not written.
8. **Reclaim (Level 3).** Iterations and steps, the last touch, the cut,
   the fraction, what a step reads, write amplification. Sources: 024-07,
   024-29, 024-34, 006-19, 023, 001-07; sis-model.md, section 15.3;
   027-01's levels.md, section 6. Not written.
9. **Eviction and the cache (Level 4).** Handles, eviction in bounded
   steps, the cache's tables. Sources: 009, 024-33, 001-08; sis-model.md,
   sections 15.1 and 15.2; 027-01's levels.md, section 7. Not written.
10. **Durability.** Forces, the write buffer, crashes and startup
    correction, the storage assumed. Sources: 014 (014-01), 011-07;
    027-01's levels.md, section 8. Not written.
11. **Cleanup and `maintain()`.** What the database releases when nothing
    needs it any more, and the call that drives it. Sources: 023, 024-32,
    024-30. Not written.
12. **The limits.** Of a transaction, a key, a value, a database; what is
    refused and how. Sources: 024-17, 024-24, 024-27. Not written.
13. **Costs.** The bounds of sections 3 to 12 together: operations and
    storage proportional to the work and to the KVs stored (024-04, aims 2
    and 3), what is known (024-05) and what the gates check (024-30).
    Not written.
14. **The Lean model and conformance.** What is modelled, proved and
    open, and how Java's runs are checked against the model (traces,
    027-02). Sources: sis-model.md, sections 8 to 15; 024-06, 024-09,
    024-12, 024-22; 001; 009-05. Not written.

Not in 027 for now: the Pub layer's objects and user indexes (027-01's
levels.md, section 11; 020), which are built on the Core, not part of its
algorithms.


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

2026-11-12. Created the item (Frans, 14:17 and 14:27) as a skeleton: the
planned sections and their sources. `docs/` moved in: 027-01, a snapshot,
and 027-02, the trace format, kept current; `docs/log.md` stays where it
is (Frans, 14:32); the references in `java/`, `lean/`, the level
scripts, `AGENTS.md`, `README.md` and `items/readme.md` point here, by ID. Old items keep their
links to `../docs/` (items are history). By agent docsmv of coord-1112, on
the branch `027-algorithms`.


State
=====

Done: the skeleton, 027-01 and 027-02 moved (`docs/` keeps only
`log.md`), the references changed. Not done: every section (all "not
written"). Next: write the sections one at a time, each from its sources, starting where
2026.5's work is freshest (sections 4, 7 and 8).
