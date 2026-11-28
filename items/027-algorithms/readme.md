027-algorithms
==============

Created 2026-11-12 by Frans Lundberg. Status: open.

The algorithms of BergDB as they are, kept current with `java/` and
`lean/`, as the stream format (027-03) is. Language-neutral: for every
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

Frans, 2026-11-12, 14:27: "Yes, create the item as a skeleton only.
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
* **One exception, kept** (Frans, 2026-11-13, 08:50: "Yes", to "The
  trace format's exception (027-02 kept current, not a snapshot): keep
  it?"): `trace-format.md` is 027-02 and is **kept current**, not a
  snapshot. The trace exporter (`java/stress/TraceExport.java`) and the
  checkers (`lean/Check/*.lean`, `lake exe tracecheck`, `lake exe
  treecheck`) implement it, and it must change with them; a frozen copy
  would be wrong at the next format change.

* `log.md` stays in `docs/`, the development log, still written: Frans,
  2026-11-12, 14:32: "Some type of log is good to have. Let's keep log.md
  for now." `docs/` holds nothing else.

No script or build reads a file under `docs/` (checked: the level
scripts, `night.sh`, `conformance.sh`, `build.sh`, `before-commit.sh`).
The code's comments cite 027-01 and 027-02 by ID.


The stream format
=================

The description of BergDB's stream format, written on 2026-11-11 as
024-02 in release 2026.5's item, moved into this item on 2026-11-13 as
027-03 (Frans, 08:50: "Yes", to "024-02, the stream format, is a
maintained description inside a release item. Move it into 027 when
2026.5 is done?"). 2026.5 is released; 027-03 is kept current with the
code, and release 2026.6's work on a stable format (026) edits it here.
A stub at 024-02 leads to it. Its sections kept their numbers: "024-02,
section 21" is "027-03, section 21". The code's comments cite
`bergdb 027-03`; old items keep their citations of 024-02 (items are
history).


Questions for Frans
===================

None open. The two of 2026-11-12 were answered on 2026-11-13, 08:50
(Frans: "Yes" to both): the trace format's exception is kept (section
"The former docs/"), and 024-02 moved into 027 as 027-03 (section "The
stream format").


Files
=====

* [01-docs-2026-11-12/](01-docs-2026-11-12/readme.md). 027-01, the former
  `docs/` as of 2026-11-12, a snapshot for reference, not updated:
  `levels.md`, `sis-model.md`, `sources/` and the old `docs-readme.md`.
* [02-trace-format.md](02-trace-format.md). 027-02, the format of the
  traces that connect the Java code with the Lean model's checkers, moved
  from `docs/trace-format.md`; kept current.
* [03-stream-format.md](03-stream-format.md). 027-03, the stream
  format: the structures from the files to the bits, the gaps where the
  code accepts what a specification should refuse, the open format
  questions, the options for versioning; moved from 024-02 on
  2026-11-13; kept current.
* [04-outline-proposal.md](04-outline-proposal.md). 027-04, a proposed
  outline for 027, for Frans to react to: 14 parts by mechanism in the
  levels' order, three other organisations, five questions, and how the
  writing could go on with him; decided (Frans, 2026-11-13, 11:09).


The parts, in reading order (027-04; stubs until written):

* [05-overview.md](05-overview.md). 027-05, part 1: overview, what BergDB is and what it promises.
* [06-terms.md](06-terms.md). 027-06, part 2: terms.
* [07-key-tree-reads.md](07-key-tree-reads.md). 027-07, part 3: the key tree, structure and reads.
* [08-key-tree-writer.md](08-key-tree-writer.md). 027-08, part 4: the key tree, the writer;
  written (2026-11-19), PE of record format 8, for Frans to read.
* [09-transactions.md](09-transactions.md). 027-09, part 5: transactions.
* [10-self-indexed-stream.md](10-self-indexed-stream.md). 027-10, part 6: the self-indexed stream.
* [11-startup.md](11-startup.md). 027-11, part 7: startup; reviewed, for Frans to read.
* [12-memory.md](12-memory.md). 027-12, part 8: memory, handles and eviction.
* [13-reclaim.md](13-reclaim.md). 027-13, part 9: reclaim; the pilot, reviewed
  against the code and read by Frans (2026-11-13, 12:34: "really good"): the
  template for the other parts.
* [14-storage.md](14-storage.md). 027-14, part 10: storage and durability.
* [15-failures.md](15-failures.md). 027-15, part 11: failures.
* [16-costs-and-bounds.md](16-costs-and-bounds.md). 027-16, part 12: costs and bounds, the index.
* [17-model-and-checks.md](17-model-and-checks.md). 027-17, part 13: the model and its checks, the index.
* [18-objects-and-indexes.md](18-objects-and-indexes.md). 027-18, part 14: objects and user indexes (the Pub layer).

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

2026-11-13. Frans's answers to the two questions (08:50, "Yes"): the
trace format's exception kept, 027-02 kept current; 024-02, the stream
format, moved in as 027-03, kept current (`git mv`, a stub at 024-02).
The references in `java/`, `AGENTS.md`, `README.md` and
`items/readme.md`, and in 024's and 026's readmes, point to 027-03; old
items keep 024-02. By agent sf of coord-1113, on the branch
`027-03-stream-format`.

2026-11-19. 027 brought up to date with the writer PE, record format 8
(026-25; Frans, 10:14: "Yes, good."), from the code at `b03dcea7`
(`PeWriter`, `Dag.putKvs`, `DbStarter.rerunTransaction`, `Db.putKvs`)
and the Lean writer (lean/SIS/Tree/Pe.lean): 027-02 (the TREE line's
thresholds in their roles in PE, BASE's id order, the OP lines' batch,
`treecheck`'s writer, the unreached nodes, the empty key node); 027-03
(sections 1, 3, 6, 8.1, 8.3, 8.4, 11.3, 14.2, G11, G12, Q1, Q2, Q22;
026-25 had done 5, 8.2, 11.2 and 21.1); 027-08 (a summary of PE until
the part is written); 027-11 (the cold time, the joins, `DropStep`);
027-13 (the row's dirty bytes, LIVEBELOW's premise); the stubs 027-06,
027-09 and 027-17. 027-01 (the snapshot) and 027-04 (the outline's
decision record) are history and not changed. Registered: 028-21
(`dirtyNodeBound` not argued for PE) and 028-22 (Java comments that
describe the old writer as today's). By an agent of coord-1118, on the
branch `027-pe`.

2026-11-19. 027-08 written in full (Frans, 10:54: "Write it for me."),
from the code at ba81b104 and the proved program; 028-25 registered (the
short way and the plan mark D's nodes in different orders). By an agent
of coord-1118, on the branch `027-08-writer`.

2026-11-28. 027 brought up to date with one record an action, the
documents step of 031-06's landing (its section 9, item 5), with what
landed beside it since release 2026.6 (031-04's `maintain(int budget)`,
031-05's plan from the stream, 028-67's C1, C3 and T1, 028-66's option
C, 028-62's file sizes, 028-69's removal of the crypto code), from the
code at 8a0897cf: 027-13 (a commit's and a part's maintenance planned
before the go point and applied after the record, the copies, the charge
in the record, a and the witness, the pass of `maintain(budget)`, the
warm-up), 027-03 (record format 9 in full: what a record holds, 8.5, the
copy mark, the record's cap and the take's room, the row's a and fixed
width, the padded table, the files), 027-02 (the setters' records, run
B's PROBE lines), 027-08 (the batch with the maintenance's KVs, the
record's room), 027-11 (no work of reclaim's at a start, a from the
stream, format 9, the gap and the files before it), 027-14 (028-73's
first 10 MB, the backup copies with gaps), and the stubs 027-06, 027-09,
027-15 and 027-17; with them the Javadoc of `maintain(int budget)` (`Db`,
`Database`) and the README's sentence on one stream, in the words Frans
chose (2026-11-27; 031-06, section 8). P2 in 010 is Frans's and not
changed. By agents of lead-1127, on the branch `031-06-docs`.


State
=====

Done: the placeholder, 027-01 and 027-02 moved (`docs/` keeps only
`log.md`), the references changed; 027-03 moved from 024-02
(2026-11-13). No question open. Next: the structure and contents,
later, with Frans.

2026-11-13. 027-04's outline decided (Frans, 11:09; its section 4): the
Core is the subject, the Pub layer the last part; the levels only as
the reading order; one subitem per part, 027-05 to 027-18, made as
stubs; 027 with Lean is the authority for the exact rules, and the
code's comments may repeat or summarize them, so that a reader can tell
whether the code does what it should.

2026-11-19. Up to date with PE (record format 8, 026-25). Open from it:
028-21 (`dirtyNodeBound` for PE), 028-22 (stale Java comments); part 4
(027-08) is still a stub, with a summary of PE until it is written.

2026-11-19. Part 4 (027-08) written: the writer PE, from the batch to
the dirty set, with its ways by counts, the rerun, the bounds, the model
and a worked example run on the code; not yet reviewed by a second agent
(027-04, section 5.2). Open from it: 028-25 (the order of the marks of
the short way and the plan).

2026-11-28. Up to date with one record an action (031-06) and the work
landed with it, at 8a0897cf: 027-02, 027-03, 027-08, 027-11, 027-13 and
027-14, and the stubs that name what changed.
