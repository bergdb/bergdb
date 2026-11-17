019-06. Fix: performance.sh's harness does not compile against 2026.2's jar
=========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-05 by Frans Lundberg.

What: `java/stress/performance.sh` compiles its harness (`PerfUtil.java`,
`Perf.java`, `PerfTool.java`) against each build's jar. `Perf.openDb()`
calls `new FileStream(dir, !noForce)`, a constructor that 005-47 added on
2026-11-04 (`9b67a82`), after release 2026.2. 2026.2's jar has no such
constructor, so javac fails ("incompatible types: boolean cannot be
converted to FileStreamIo") and `performance.sh ab 2026.2 current` stops
at "the harness does not compile". Found 2026-11-05 by the agent of
019-04, which kept a `seekFirstPos` without `@Override` in `Perf.java`'s
`CountingStream` for the same reason.

Why: 2026.2's notes (section on the performance comparison) require it:
"The harness of the later tree must compile against 2026.2's jar". The
comparison of 2026.3 with 2026.2 depends on it.

Frans: none.

Done when: the three harness files compile, with `performance.sh`'s
javac flags, against 2026.2's jar, against 2026.1's jar if it is at hand,
and against main's `java/build/bergdb.jar`; `performance.sh`'s behaviour
on main is unchanged (`perf.noforce=1` still gives a stream without
per-append forces); `before-commit.sh` prints `BEFORE COMMIT OK`.

First step: compare `FileStream`'s and `FileStreamIo`'s constructors and
methods in 2026.2's jar and on main (`javap`), and see how the harness
opened its stream before `9b67a82`.


Log
---

2026-11-05. Registered by session bergdb-e8, from 019-04's agent's
finding, and taken by session bergdb-e8's agent: in progress.

2026-11-05. Done. `Perf.openDb()` opens `new FileStream(dir)`, in every
jar, and with `perf.noforce=1` calls `fileStreamWithoutForces(dir)`,
which finds `FileStream(File, boolean)` by reflection and calls it with
`false`. No constructor or method of both jars gives a stream without
per-append forces: 2026.2's `FileStreamIo` has only
`forceFile(File, RandomAccessFile)`, and a subclass that skips it would
also skip the forces that keep the database whole (a new file, a cut,
close). So with a jar without that constructor (2026.2 and earlier),
`perf.noforce=1` cannot be honoured: the run fails with a `PerfFailure`
that says so, rather than force every append unannounced. Without
`perf.noforce`, nothing changed on main or on 2026.2: `FileStream(dir)`
forces every append in both.

Compiled with `performance.sh`'s javac flags (`--release 17
-Xlint:-options -encoding UTF-8`): against 2026.2's jar, OK; against
main's `java/build/bergdb.jar` (after `build.sh`), OK; against 2026.1's
jar (`releases/2026.1/`), one error, which is not this fault and is
left: `bergdb.pub.util.SyncLevel` is not in 2026.1 (`SyncLevel` moved from
`bergdb.core` in 005-56, `8752cf0`, a known change that 2026.2's notes
list; only 2026.2's jar is required). A probe (in the scratchpad, not
kept) called `fileStreamWithoutForces`: on main's jar the stream's
`forcesAppends()` is `false`; on 2026.2's jar it throws `PerfFailure:
perf.noforce=1 cannot be honoured with this jar: its FileStream has no
FileStream(File, boolean) (bergdb 005-47, after 2026.2) and forces every
append`. No performance runs. `before-commit.sh`: BEFORE COMMIT OK
(104 s; unit 1167, f-tests 81).
