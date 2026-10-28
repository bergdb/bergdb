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

* `docs/`. The current state in words: the feature levels, what works
  and where the evidence is (start with [docs/levels.md](docs/levels.md)),
  the model of self-indexed streams, the trace format, and the development
  log. See [docs/readme.md](docs/readme.md).
* `lean/`. The abstract model in Lean 4 and machine-checked proofs of
  recovery (T1) and restart invariance (T2). See [lean/README.md](lean/README.md).
* `java/`. The Java implementation, its build script and the regression and
  stress tests.
* `items/`. Work items: plans, experiments, progress logs and reports, kept
  apart from the current state. See [items/readme.md](items/readme.md).
* `releases/`. The releases: each one's jar, source, release notes and
  baseline measurements. The latest is
  [2026.1](releases/2026.1/readme.md), internal, of 2026-10-25. What the
  next release's notes must say is collected in
  [releases/next.md](releases/next.md).

BergDB was developed 2012 to 2017. This repository continues from the 2017 source; the work since October 2026 fixed the bugs that stopped it, formalized the algorithm, and added reclaim and eviction.



Build and test
--------------

Needs a JDK 17 or later (the code is compiled with `--release 17`, since
2026-10-25, bergdb 009; before, `--release 8`) and, for the proofs
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
    java/stress/core-build.sh      # the Core Layer built alone, its tests on it (about 15 s; unit f: 50 s)
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
on a clean clone of the committed code, the check before a commit, the Core
Layer built alone (`core-build.sh`), the four level scripts, the night tests
(the long-running tests of 2013 to 2015) and the medium conformance set;
launchd starts it at 02:10, and its report is in
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
| 4 | + eviction: data larger than memory | Passes the tests run, on by default; with handles since 2026-10-26, eviction in bounded steps, without a stop-the-world of its own (bergdb item 009); a database six times its memory budget runs on disk; aligned with the proved Lean model of eviction, with handles |

Evidence and limits are in [docs/levels.md](docs/levels.md), including the
FileStream durability report,
[011-07](items/011-docs-archive/07-level3-durability.md). The Lean proofs
concern the abstract model, which since bergdb item 001 includes reclaim and
eviction; Java's runs are checked against it, not proved, and concurrency and
resource bounds are not in it. Whether the concept is novel is open; see
the study of prior art, [011-02](items/011-docs-archive/02-prior-art.md).

Two known limits (2026-10-25). Replication (`DatabaseBuilder.replica`,
`Database.addReplica`) is experimental, with known faults, and not for data
that matters ([005-11](items/005-todo/11-replication.md)). And bounded
startup is not yet proved for BergDB's own startup pos policy: its take
keeps up with twice the startup distance by a deadline, which
[007-03](items/007-bounds/03-plan.md)'s step 4 is to prove; before the
deadline, the startup section reached 2.6 times the startup distance at
50 MB in a test ([005-38](items/005-todo/38-writes-at-scale.md)).

Pauses (2026-10-28). In the runs of bergdb item 009, no get or commit
waits more than about 20 ms for BergDB's own work: eviction works in
bounded steps (009), and no read waits for the stream's writer, its forces
or reclaim's cuts ([005-46](items/005-todo/46-stream-file-lock.md)). One
case is open: with 8 readers on F53's 8 performance cores, from the OS's
cache under eviction, gets of up to 36 ms
([005-65](items/005-todo/65-gets-with-8-readers.md)). The collector's pauses
come on top: use ZGC, or Shenandoah in its default mode, without
generations; with G1 they reach hundreds of milliseconds under eviction. A
slow disk shows through too, in reads that miss the caches and in a writer
that fills the write buffer. Details in docs/levels.md, section 7.


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
