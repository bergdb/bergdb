Items
=====

Well-defined pieces of work on BergDB: plans, experiments, progress logs,
reports, reviews. This file holds the rules and the index.

An item is a place to work with freedom: to try things, keep dead ends and
logs, without cluttering the current state of BergDB. The current state is
`java/`, `lean/` and the reviewed documents in `docs/`, starting with
[docs/levels.md](../docs/levels.md).


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
  passing the gates; findings go into `docs/`, with a link to the item as
  evidence.
* A code experiment too large for the item directory runs on a git branch
  or worktree. The item records the branch and the outcome.
* A finished item is history. It is not kept up to date, like
  [docs/log.md](../docs/log.md).
* Work on BergDB before this index (2026-10-16), including the Level 2
  alignment, is described in `docs/` and in the f1 repo's F1-007 and F1-008.


Index
=====

* **001-lean-model-levels-3-4** (done). Model Levels 3 (reclaim) and 4
  (eviction) in Lean and align the model with the Java code.
* **002-top-node-ordinal-bound** (open). The top node ordinal bound,
  2^30 − 1 over a database's life (register M46): what Java does at it, and
  what to do about it.
* **003-transaction-exception-safety** (open). A transaction that throws
  inside `Db.putKvs` is half committed (register M49); documented, to be
  fixed before item 001's J3.
* **004-indirect-swizzling** (open). Indirect swizzling (handles, a mapping
  table) for BergDB: the literature, measurements, a design sketch, pros and
  cons.
* **005-todo** (open). A list of things to do on BergDB: issues to fix,
  things to investigate, decisions to make; one subitem per entry.
* **006-2026-q4** (open). Small pieces of work in October to December
  2026, one subitem each; see "Small work".
