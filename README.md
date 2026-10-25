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
* `releases/`. The releases: each one's jar, source, release notes and
  baseline measurements. The latest is
  [2026.1](releases/2026.1/readme.md), internal, of 2026-10-25.

BergDB was developed 2012 to 2017. This repository continues from the 2017 source; the work since October 2026 fixed the bugs that stopped it, formalized the algorithm, and added reclaim and eviction.



Build and test
--------------

Needs a JDK (the code is compiled with `--release 8`) and, for the proofs
and `level2.sh` to `level4.sh`, [elan](https://github.com/leanprover/elan).

    
    java/build.sh                  # builds java/build/bergdb.jar and the stress tests
    java/before-commit.sh          # the check before a commit: unit and f-tests (about 2 minutes)
    java/unit.sh                   # runs the unit tests
    java/f.sh                      # runs the f-tests
    java/perf.sh                   # runs the perf-tests
    java/props.sh                  # runs the Props tests: MEM, CORE, SS (about 50 s)
    java/night.sh                  # the night run, at 02:10: all of the below (about 50 minutes)
    java/night.sh large            # the same and the large conformance set (about 6 hours)
    java/night.sh tests            # only the night-tests (about 4.5 minutes)
    java/stress/level1.sh          # full replay          (about 80 s)
    java/stress/level2.sh          # bounded startup      (about 17 minutes; quick: 2)
    java/stress/level3.sh          # reclaim              (about 8 minutes)
    java/stress/level4.sh          # eviction             (about 16 minutes; quick: 4)
    cd lean && lake build          # checks all proofs

`java/before-commit.sh` must print `BEFORE COMMIT OK` before a change to
the Java code is committed; it is the only requirement. Each level script
prints `LEVEL n OK` when it passes; they are deeper checks of their levels,
run after larger changes, not commit gates. Some tasks need more testing,
depending on the job; work on performance, for example, runs the
performance tests. `java/night.sh`, the night run, is not a gate either:
on a clean clone of the committed code, the check before a commit, the four
level scripts, the night tests (the long-running tests of 2013 to 2015) and
the medium conformance set; launchd starts it at 02:10, and its report is in
`java/build/night/`. `java/night.sh large` adds the large conformance set;
it is started by hand. Set `JAVAC` and `JAR` if the JDK tools are not on the
path.



Status
------

| Level | Features | Status |
|---|---|---|
| 0 | Multiversion map in memory | Passes the tests run |
| 1 | + restart by replaying the whole stream | Passes the tests run |
| 2 | + bounded startup (self-indexed stream) | Passes the tests run, under load and with crashes |
| 3 | + reclaim: cut the front of the stream | Passes the tests run, a two-hour disk soak and the power-loss ordering checks; aligned with the proved Lean model of reclaim |
| 4 | + eviction: data larger than memory | Passes the tests run, on by default; a database six times its memory budget runs on disk; aligned with the proved Lean model of eviction |

Evidence and limits are in [docs/levels.md](docs/levels.md), including the
[FileStream durability report](docs/level3-durability.md). The Lean proofs
concern the abstract model, which since bergdb item 001 includes reclaim and
eviction; Java's runs are checked against it, not proved, and concurrency and
resource bounds are not in it. Whether the concept is novel is open; see
[docs/prior-art.md](docs/prior-art.md).

Two known limits (2026-10-25). Replication (`DatabaseBuilder.replica`,
`Database.addReplica`) is experimental, with known faults, and not for data
that matters ([005-11](items/005-todo/11-replication.md)). And bounded
startup is not yet proved for BergDB's own startup pos policy: the startup
section reached 2.21 times the startup distance in a test, and the deadline
that bounds it is planned ([007-03](items/007-bounds/03-plan.md)).


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
