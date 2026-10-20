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

- `java/before-commit.sh` must print `BEFORE COMMIT OK` before a change to
  the Java code is committed: the unit tests and the f-tests, about 2
  minutes. It is the only requirement. The level scripts
  (`java/stress/level1.sh` to `level4.sh`) are deeper checks, not commit
  gates; `level2.sh`, `level3.sh` and `level4.sh` need Lean (elan) for their
  conformance steps.
- Some tasks need more testing than that, depending on the job: work on
  performance runs the performance tests (`java/stress/performance.sh` with
  a suite, or `java/perf.sh`); a change to a level's mechanism runs that
  level's script. The task's item says what it needs.
- `java/night.sh` runs at 02:00 (launchd), on a clone of the committed
  code: the level scripts, the night tests and more; its reports are in
  `java/build/night/`. `java/night.sh large` adds the large conformance set
  and is started by hand.
- Do not edit a shell script while it runs; `sh` reads it as it goes.

## General

- Preserve unrelated worktree changes.
- Preserve files in `frans/`.
