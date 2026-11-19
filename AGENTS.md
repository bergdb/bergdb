# bergdb repository instructions

BergDB is an append-only database for Java with a Lean model of its
algorithm. [README.md](README.md) describes BergDB for its users and the
repository's parts; [java/readme.txt](java/readme.txt) the build and the
test scripts; [lean/README.md](lean/README.md) the model. Its algorithms are
item 027, [items/027-algorithms](items/027-algorithms/readme.md); until 027
is written, start reading at 027-01's [levels.md](items/027-algorithms/01-docs-2026-11-12/levels.md),
a snapshot of the former `docs/` of 2026-11-12.

## Public repository

- The repository is public (github.com/bergdb/bergdb, since 2026-11-17):
  a push to `main` publishes at once. Before a commit, check the change
  for private data: e-mail addresses other than frans.lundberg@gmail.com,
  phone numbers, local paths beyond the ones the scripts need, passwords
  and keys, private notes.
- Commits are Frans's, with no AI attribution: no `Co-Authored-By` or
  similar lines in commit messages.
- The history was rewritten when the repository went public (029): a
  commit hash of before 2026-11-17 cited outside this repository, in
  notes, reports or old clones, does not resolve here. The hashes cited
  in this repository's files and commit messages were mapped to the new
  ones.

## Items

- Work is organized in items. [items/readme.md](items/readme.md) holds the
  rules and the index. Read it early.
- A bare number such as `024` or `024-01` in a request means an item or a
  subitem in `items/`, unless the context says otherwise.
- Experiments, plans, progress logs and reports belong in an item, not in
  `java/` or `lean/`.
- The maintained descriptions are items, kept up to date with the code:
  027 (the algorithms of BergDB), 027-02 (the trace format) and 027-03
  (the stream format). The other former files of `docs/` are 027-01 since
  2026-11-12, a snapshot that is not updated. A new document is a subitem.
- `docs/` holds only `docs/log.md`, the development log (Frans, 2026-11-12:
  "Let's keep log.md for now").
- Cite a document by its ID and section (`001-08, section 5.5`; in code
  comments `bergdb 001-08, section 5.5`), not by its path.

## Code

- The Core Layer (`bergdb.core` and the packages it uses) is a simple
  key-value datastore: both keys and values are byte arrays. It knows
  nothing of objects or user indexes; build such features on top of it,
  not into it (010-01, P12).
- `java/before-commit.sh` must print `BEFORE COMMIT OK` before a change to
  the Java code is committed: the unit tests, the f-tests and a smoke run of
  the demos, about 2 minutes. It is the only requirement. The level scripts
  (`java/stress/level1.sh` to `level4.sh`) are deeper checks, not commit
  gates; `level2.sh`, `level3.sh` and `level4.sh` need Lean (elan) for their
  conformance steps, but not Mathlib: `level2.sh` builds the contract
  checkers in `lean/contractcheck/`, without Mathlib (028-24). Only the
  contract package's proofs, `lean/contract/` and its `gate.sh`, need
  Mathlib (030-04).
- Some tasks need more testing than that, depending on the job: work on
  performance runs the performance tests (`java/stress/performance.sh` with
  a suite, or `java/perf.sh`); a change to a level's mechanism runs that
  level's script. The task's item says what it needs.
- `java/night.sh` runs on a clone of the committed code: the level scripts,
  the night tests and more; its reports are in `java/build/night/`. It has
  no fixed time: the day's coordinator (013-02) starts it as a step of its
  plan when the machine has room for it, or Frans by hand (the command is
  in its header). `java/night.sh large` adds the large conformance set and
  is started by hand.
- Do not edit a shell script while it runs; `sh` reads it as it goes.

## News

- `news.md` (not tracked by Git; it stays local and is never committed) is
  Frans's morning news of background work: `night.sh`, scheduled runs,
  unattended sessions. Add an entry with `tools/news.sh STATUS SOURCE TEXT`
  when such work finishes, fails, or stops for Frans's decision; STATUS is `OK`, `FAILED` or `needs a look`. One or two
  lines and a reference (an item such as `012-03`, a file, a commit): the
  details belong in the item. An unattended session ends its night with a
  summary entry. The helper drops `OK` entries after 3 weekdays.

## Markdown tables

- Make tables readable in source/text view as well as when rendered.
- Align the data rows using the widths of their contents. Do not pad short
  data rows to match long headers; the header and separator may remain
  unaligned with the data rows.
- Aim for data rows of at most 100 characters, with 120 as the maximum.
  If the contents need more space, split the table or use a list.
- When asked to format selected lines, change only those lines.

## General

- Preserve unrelated worktree changes.
- Frans's private notes are kept outside this repository and are never
  cited; `frans/` at the root is ignored by Git. Their IDs (F1-007,
  F1-008) appear in older items and comments as a record
  (items/readme.md); do not add new citations.
