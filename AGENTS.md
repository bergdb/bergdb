# bergdb repository instructions

BergDB is an append-only database for Java with a Lean model of its
algorithm. [README.md](README.md) describes the repo; start reading at
[docs/levels.md](docs/levels.md).

## Items

- Work is organized in items. [items/readme.md](items/readme.md) holds the
  rules and the index. Read it early.
- A bare number such as `024` or `024-01` in a request means an item or a
  subitem in `items/`, unless the context says otherwise.
- Experiments, plans, progress logs and reports belong in an item, not in
  `java/`, `lean/` or `docs/`.

## Code

- All three level scripts (`java/stress/level1.sh`, `level2.sh`, `level3.sh`)
  must print `LEVEL n OK` before a change to the Java code is committed.
  `level2.sh` needs Lean (elan) for its step 7.
- Do not edit a shell script while it runs; `sh` reads it as it goes.

## General

- Preserve unrelated worktree changes.
- Frans commits himself; do not commit unless asked.
