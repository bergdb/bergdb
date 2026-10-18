BergDB
======

BergDB is an in-process, append-only database for Java: a multiversion
ordered map from (key, time) to value, kept in one append-only stream. Its
central idea is the **self-indexed stream**: the stream is the only durable
storage, index nodes are written lazily into it, and startup reads only the
tail of the stream, so startup time does not grow with the size of the
database.

This repository holds three things that belong together, and the work on
them:

* `docs/`. The theory: the problem statement, the model of self-indexed
  streams, prior art, the feature levels with their test evidence, and the
  plans for the next levels. Start with [docs/levels.md](docs/levels.md).
* `lean/`. The abstract model in Lean 4 and machine-checked proofs of
  recovery (T1) and restart invariance (T2). See [lean/README.md](lean/README.md).
* `java/`. The Java implementation, its build script and the regression and
  stress tests.
* `items/`. Work items: plans, experiments, progress logs and reports, kept
  apart from the current state. See [items/readme.md](items/readme.md).

BergDB was developed 2012 to 2017 (until July 2013 under the name KissDB).
This repository continues from the 2017 source; the work since October 2026
fixed the bugs that stopped it, formalized the algorithm, and added reclaim.


Status
------

| Level | Features | Status |
|---|---|---|
| 0 | Multiversion map in memory | Passes the tests run |
| 1 | + restart by replaying the whole stream | Passes the tests run |
| 2 | + bounded startup (self-indexed stream) | Passes the tests run, under load and with crashes |
| 3 | + reclaim: cut the front of the stream | FileStream power-loss ordering implemented and audited on tested macOS/Linux VM paths; a long disk soak and performance reference remain planned |
| 4 | + eviction: data larger than memory | Not implemented; design in [docs/level4-plan.md](docs/level4-plan.md) |

Evidence and limits are in [docs/levels.md](docs/levels.md), including the
[FileStream durability report](docs/level3-durability.md). The Lean proofs
concern the abstract model, not the Java code, reclaim, eviction,
concurrency or resource bounds. Whether the concept is novel is open; see
[docs/prior-art.md](docs/prior-art.md).


Build and test
--------------

Needs a JDK (the code is compiled with `--release 8`) and, for the proofs
and `level2.sh`, [elan](https://github.com/leanprover/elan).

    java/build.sh                  # builds java/build/bergdb.jar and the stress tests
    java/stress/level1.sh          # full replay          (about 80 s)
    java/stress/level2.sh          # bounded startup      (about 17 minutes; quick: 2)
    java/stress/level3.sh          # reclaim              (about 8 minutes)
    cd lean && lake build          # checks all proofs

Each level script prints `LEVEL n OK` when it passes. All three must pass
before a change to the Java code is committed. Set `JAVAC` and `JAR` if the
JDK tools are not on the path.


Notes
-----

* Much of the 2026 documentation, the tests and the Lean development were
  written by Frans Lundberg together with AI assistants (Claude, Codex); the
  documents say which.
* Commit ids in the documents (`49aa48d`, `ebe5f77`, ...) name commits in
  Frans's earlier repositories, where the history up to this repository's
  first commit is kept. Frans: see F1-007, repo f1.
* The original 2012 to 2017 design notes and the git history of the 2017
  source are not part of this repository. The four documents that the theory
  builds on are in `docs/sources/`.


License
-------

Apache License 2.0, see `LICENSE` and `NOTICE`.
