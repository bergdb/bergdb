Items
=====

Well-defined pieces of work on BergDB: plans, experiments, progress logs,
reports, reviews. This file holds the rules and the index.

An item is a place to work with freedom: to try things, keep dead ends and
logs, without cluttering the current state of BergDB. The current state is
`java/`, `lean/` and the few items that are kept up to date with them:
the algorithms of BergDB (027), the trace format (027-02) and the stream
format (027-03). Until 027 is written, read 027-01's
[levels.md](027-algorithms/01-docs-2026-11-12/levels.md) first, part of
the snapshot of the former `docs/`, moved into 027-01 on 2026-11-12;
`docs/` keeps only the development log, [docs/log.md](../docs/log.md).


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


Todos and release items
-----------------------

* A simple task with a clear "Done when", that one agent can finish in
  about a day, is an entry of the todo list, 028-todo since 2026-11-13.
  It names no release.
* A release item (such as 026) holds the release's plan and scope, its
  decisions and its bigger work: designs, studies, features that may or
  may not be included, work that needs Frans's thinking. It decides which
  todo entries its release takes and lists them by ID. Frans,
  2026-11-13: "I don't want the big release items hidden among 80 simple
  tasks."; "The release item itself will decided the scope of the
  release."


Items and the current state
---------------------------

* Nothing outside `items/` depends on `items/`: `java/build.sh`, the level
  scripts and `lake build` never read it. Code in an item is a prototype, a
  patch or a tool for that item only.
* A result leaves an item on purpose: code moves into `java/` or `lean/`,
  passing the gates. A finding changes a maintained description (027,
  027-02, 027-03) only as far as the current state changes, usually a few
  lines that cite the item as evidence; the report, the alignment, the
  evidence and the log stay in the item. A new document is a subitem.
* A code experiment too large for the item directory runs on a git branch
  or worktree. The item records the branch and the outcome.
* A finished item is history. It is not kept up to date, like the
  snapshot of the former `docs/`,
  [027-01](027-algorithms/01-docs-2026-11-12/readme.md), and the entries
  of [docs/log.md](../docs/log.md).
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
* **005-todo** (done). A list of things to do on BergDB: issues to fix,
  things to investigate, decisions to make; one subitem per entry. New
  entries go to 015 since 2026-11-03; every entry closed on 2026-11-05,
  the last open ones moved to 015.
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
  to 4 done in 2026-10-28 and 29, the code in the item's `c/`. A port of
  Java release 2026.2 (015-02), kept stable: it does not follow Java's
  later changes.
* **013-ai-work** (open). How AI agents work on BergDB: ways of working
  that have worked, for Frans, Claude and other AI agents; first, the
  unattended night (013-01).
* **014-stream** (open). The stream format and the contract between
  append-only storage and the database; first, startup correction and its
  historical fault model (014-01), promoted from 005-83.
* **015-todo** (done). The list of things to do on BergDB after 005, with
  a new numbering from 015-01; it took the new entries from 2026-11-03 to
  2026-11-05, and 005's last open entries (015-84 to 015-88). New entries
  go to 019 since 2026-11-05; every entry closed on 2026-11-13.
* **016-release-2026-2** (open). Release 2026.2: its scope, the work
  before it and how it is made; the first release with handles (009) and
  bounded startup (007), measured against 2026.1 in turns.
* **017-long-term** (open). The long-term topics of BergDB: open-ended
  questions and directions that need Frans's input and may never be done;
  notes, one subitem per topic, taken up one at a time with Frans.
* **018-release-2026-3** (done). Release 2026.3: a bug-free Core, with no
  known issue at the release but in DbObject and user indexes, which are
  experimental; 010's principles hold, and Frans approves any change of
  the stream format. The plan, its decisions and the work towards it.
* **019-todo** (done). Short tasks on BergDB, each done and closed in a
  day or two, mostly by an AI agent, unattended or after a decision or
  answers from Frans, and all done before the next release but Frans's
  exceptions; new todo entries from 2026-11-05 to 2026-11-13 (028 since).
  Long-term topics and ideas to consider go to 017.
* **020-release-2026-4** (open). Release 2026.4: a bug-free database,
  user indexes and the serialization of Java objects (DbObject) included;
  no backwards compatibility needed, the API may change. The plan, its
  decisions and the work towards it; first, an inventory of the non-Core
  part for Frans's keep, simplify or drop decisions.
* **021-todo** (done). Short tasks for release 2026.4, a bug-free
  database (020): each done and closed in a day or two, mostly by an AI
  agent; every open entry done before 2026.4 but Frans's exceptions. 019
  keeps 2026.3's entries until that release.
* **022-bergdb-c** (open). BergDB's Core in C, updated to Java's releases
  2026.3 and 2026.4, maybe later ones: a fresh start from 012's C clone,
  which stays the port of 2026.2.
* **023-cleanup** (open). Resource cleanup in BergDB's Core: what the
  database keeps after nothing needs it any more, and how it is released;
  from the slow scans over deleted entries (020-30) to cleanup in general.
  Release 2026.4 waits for it.
* **024-release-2026-5** (open). Release 2026.5, after 2026.4: its plan,
  its decisions and the work towards it; so far what 023 put off to later.
* **025-spare-tokens** (open). Things to do with spare AI tokens: work
  that uses many tokens and very little of Frans's time, a short dialog
  followed by long unattended work; one subitem per entry, started by
  Frans. First, a model-first rewrite of BergDB (025-01).
* **026-release-2026-6** (open). Release 2026.6, after 2026.5: its plan,
  its decisions and the work towards it. Preliminary theme: a stable
  stream.
* **027-algorithms** (open). The algorithms of BergDB as they are, kept
  current with `java/` and `lean/`, for every implementation; a skeleton
  so far. Holds the former `docs/` as a snapshot (027-01), the trace
  format (027-02) and the stream format (027-03, 024-02 until
  2026-11-13), both kept current.
* **028-todo** (open). Simple tasks on BergDB, each done in about a day,
  mostly by an AI agent, often unattended; not tied to a release (a
  release item decides which it takes). Every new todo entry since
  2026-11-13.
