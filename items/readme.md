Items
=====

Well-defined pieces of work on BergDB: plans, experiments, progress logs,
reports, reviews. This file holds the rules and the index.

An item is a place to work with freedom: to try things, keep dead ends and
logs, without cluttering the current state of BergDB. The current state is
`java/`, `lean/` and the few documents in `docs/` that are kept up to date
with them, starting with [docs/levels.md](../docs/levels.md).


Names
-----

* An item has a three-digit number and a short name: `024-short-name`. In
  this repo, and wherever the context makes it clear, `024` is enough.
  Elsewhere: `bergdb:024`, or `BERGDB-024` if really needed.
* Subitems are numbered within their item with two digits: `024-01`.
* One number series. Take the number after the highest one issued, in the
  index and in the directory names. Never reuse a number and do not fill
  gaps; a deleted item or subitem keeps its number.
* Short names are lowercase kebab-case.
* Cite a document by its ID and section: `001-08, section 5.5`; in code
  comments, `bergdb 001-08, section 5.5`. A path changes when a file moves,
  an ID does not.


Layout
------

* An item is a directory `items/nnn-short-name/` with a `readme.md`.
* A subitem is a file `nn-short-name.md` or a directory `nn-short-name/`
  inside its item. The item's readme links to it in a `Files` section.
* A new item's readme has:

      024-short-name
      ==============

      Created YYYY-MM-DD by Frans Lundberg. Status: open.

      One or two sentences on purpose and scope.


      Log
      ===

      YYYY-MM-DD. Created the item.

* Status is `open`, `done` or `dropped`, in the item's readme and in its
  index line. Record a change of status in the item's log.


Small work
----------

* Small work is a subitem of the quarter's item, `nnn-yyyy-qn` (such as
  `006-2026-q4`): a single file or a small directory, finished in about a
  day. Examples: a summary, a short investigation, a note, a review.
* Work with a plan, tools or code, several files, or a status that stays
  open for a while gets an item of its own. A small subitem that grows
  moves to an item of its own and leaves a link in its place.
* The quarter's item lists its subitems in a table, one line each, with
  the ID, the date and what it is. It is done when the quarter ends; the
  next quarter's item takes the next free number.


Items and the current state
---------------------------

* Nothing outside `items/` depends on `items/`: `java/build.sh`, the level
  scripts and `lake build` never read it. Code in an item is a prototype, a
  patch or a tool for that item only.
* A result leaves an item on purpose: code moves into `java/` or `lean/`,
  passing the gates. A finding changes `docs/` only as far as the current
  state changes, usually a few lines in `docs/levels.md` that cite the item
  as evidence; the report, the alignment, the evidence and the log stay in
  the item. A new document is a subitem, not a file in `docs/`
  ([docs/readme.md](../docs/readme.md)).
* A code experiment too large for the item directory runs on a git branch
  or worktree. The item records the branch and the outcome.
* A finished item is history. It is not kept up to date, like
  [docs/log.md](../docs/log.md).
* Work on BergDB before this index (2026-10-16), including the Level 2
  alignment, is in item 011, in [docs/log.md](../docs/log.md), and in the f1
  repo's F1-007 and F1-008.


Index
=====

* **001-lean-model-levels-3-4** (done). Model Levels 3 (reclaim) and 4
  (eviction) in Lean and align the model with the Java code.
* **002-top-node-ordinal-bound** (done). The top node ordinal bound,
  2^30 − 1 over a database's life (register M46): what Java does at it, and
  what to do about it.
* **003-transaction-exception-safety** (done). A transaction that throws
  inside `Db.putKvs` is half committed (register M49); fixed in 005-01.
* **004-indirect-swizzling** (done). Indirect swizzling (handles, a mapping
  table) for BergDB: the literature, measurements, a design sketch, pros and
  cons; implemented in 009.
* **005-todo** (open). A list of things to do on BergDB: issues to fix,
  things to investigate, decisions to make; one subitem per entry.
* **006-2026-q4** (open). Small pieces of work in October to December
  2026, one subitem each; see "Small work".
* **007-bounds** (open). Bounds on BergDB's costs, the planned T3 and T4:
  first, that startup takes a bounded time, whatever the size and the age
  of the database.
* **008-release-2026-1** (done). Release 2026.1, internal: the tagged code,
  the jar and the release notes, and the baseline for performance
  measurements before handles (004) and gradual eviction.
* **009-handles** (done). Handles in BergDB, from 004's direction:
  eviction with bounded work and no stop-the-world. The plan, the work on
  `main` and on the branch `009-handles`, the measurements, the outcome.
* **010-principles** (open). BergDB's design principles, in Frans's
  words, P1 to P11: among them no stop-the-world, a deterministic stream,
  calm when not used, and maintenance proportional to the user's work.
* **011-docs-archive** (done). The documents of `docs/` that no item owns,
  moved here on 2026-10-26 (006-07): the problem statement, prior art, the
  plans for Levels 3 and 4, the Level 2 alignment and more of 12 to 16
  October, and `docs/levels.md` as it was until then.
* **012-bergdb-c** (done). BergDB's Core in C: a clone of the Core Layer
  for F53, with an API like `Db`'s public methods and the same stream as
  Java, byte for byte, so that each opens the other's databases; Levels 0
  to 4 done in 2026-10-28 and 29, the code in the item's `c/`.
* **013-ai-work** (open). How AI agents work on BergDB: ways of working
  that have worked, for Frans, Claude and other AI agents; first, the
  unattended night (013-01).
