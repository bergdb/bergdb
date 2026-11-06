015-19. Fix: tools in items still use what 005-79 removed
=========================================================

Status: done 2026-11-06, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2. 005-79 (`f04cefe`) removed `Eviction.LOW` and
`TransSeq.dither`. Some tools in items, outside `java/` and so outside
`before-commit.sh`, still use them and no longer compile against `main`:

* `items/005-todo/65-gets-with-8-readers/night/ScaleBench-065.diff`
  (005-65's `night/prep.sh`) uses `Eviction.LOW`. 016-10's
  `prep-tools.sh` (`/Users/f/fl/bench/016/numbers/`) puts
  `Eviction.lowOf` in that line for a jar without it.
* `items/007-bounds/08-step4-take-in-lean/TakeCheck.java` calls
  `TransSeq.dither` (Lean's side: 015-03).
* `items/012-bergdb-c/c/test/cross/java/Vectors.java` calls
  `TransSeq.dither` (C's side: 015-02).

Done when: each tool compiles against `main` and gives the values of
005-79's integer take, or its item says that it is kept for the code
before 005-79 only.

First step: give `ScaleBench-065.diff` the line of `prep-tools.sh`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05, in 015-02's work: `items/012-bergdb-c/c/test/cross/java/Vectors.java`
writes `TransSeq.ditherFp` and `shareFp` (and `Math.multiplyHigh` and
`Math.round`) in place of `dither`, and compiles against release 2026.2,
whose Java the cross harness now compiles by default (015-02). The other two
tools are as they were.

2026-11-05. 019-04 removed `AppendOnlyStream.seekFirstPos()`. As with
005-79's removals, the item tools that call it on an `AppendOnlyStream`
no longer compile against `main`: 005-57's `StartBench`, 005-64's
`TrickleProbe` and `MixedProbe`, 005-81's `RetryBench`, 007-05's
`StartupBench`, 006-11's `RwBench`, 004-02's `ScaleBench`, 016-06's
`R7WarmupExpiryProbe`, 005-01's `M49Probe`, 005-33's
`CreationCrashProbe`, 005-35's `StopCloseProbe` and 005-11's
`ReplicaProbe`. The same fix works for each: a `seekFirstPos(long)`
without `@Override` that does not call the inner stream, as `Perf.java`
has, so that the tool compiles against `main` and against older jars.

2026-11-05, night 006-12. The item tools that are run again now compile
against `main` (checked with `javac` against this night's `main` jar and
against release 2026.2's jar, `releases/2026.2/bergdb-2026.2.jar`, both
without errors):

* `seekFirstPos(long)` without the inner call, as `Perf.java` has (throws
  `UnsupportedOperationException`; no layer of BergDB calls it):
  005-57's `StartBench`, 007-05's `StartupBench`, 006-11's `RwBench`,
  005-81's `RetryBench` (now 017-06's), 005-64's `TrickleProbe` and
  `MixedProbe`.
* `retainForever()` dropped (forever is the default, also in older jars):
  those but `TrickleProbe`, and the `WriteBench` of 005-38, 005-49 and
  007-06, 005-38's `NodeSizeBench`, 005-52's `BudgetBench`, 006-02's
  `Probe006`.
* `SyncLevel.STRONG` (gone with replication, 005-11; it was `ORDINARY`
  without a replica) is `ORDINARY` in `StartBench`, `StartupBench` and
  `MixedProbe`; `StartBench`, `StartupBench` and `Probe006` take `SyncLevel`
  from `bergdb.pub.util`, where 005-56 moved it. So these four no longer
  compile against a jar before 005-56 (2026-10-27); for one, take the tool
  from Git's history.
* 006-11's `eviction-startup.patch` was applied to `RwBench` long ago and is
  not changed; `finish-runs.py`, which applies it, was a one-off.

Kept for the code of their time, with a note in their items (one paragraph
each, "2026-11-05 (015-19)"): 005-01's `M49Probe`, 005-11's `ReplicaProbe`,
005-32's `FailedStartProbe`, 005-33's `CreationCrashProbe`, 005-35's
`StopCloseProbe`, 005-42's `TransactionInfoProbe`, 005-46's
`InterruptCutProbe`, 005-83's `PowerLossTailProbe`, 016-06's R6 probes and
R7's `R7WarmupExpiryProbe`, 006-08's `CoreSame`, and 007-08's `TakeCheck`
(the double take of 005-79's base, as 007-08's Lean model; 015-03 brings
both to the integer take). Besides 005-79's, 019-04's and 015-87's removals,
015-05's removal of `DatabaseBuilder.dir` breaks some of them.

Left as they are:

* 004-02's `ScaleBench` and 005-65's `ScaleBench-065.diff`: tonight's quiet
  blocks build them (006-12, W2), against jars before 019-04 and 005-79, as
  005-65's `prep.sh` does; not changed tonight. What is left of this entry:
  `ScaleBench`'s `seekFirstPos` as above and its `retainForever()` dropped,
  and the `-065.diff` line of 016-10's `prep-tools.sh` (`Eviction.lowOf`)
  for a jar without `Eviction.LOW`, after the night.
* 012's Java (`c/test/cross/java/`, `c/test/func/java/`, `c/bench/`):
  the C clone follows release 2026.2 (015-02, bergdb-2c), and its harness
  compiles its Java against 2026.2's jar by default.
* Patches and diffs of closed work (005-10's `edits.patch`, 016-06's
  `R5-F*.diff` and `R6-F1.diff`): records of a change, not tools.

Status stays open for `ScaleBench` and its `-065.diff`.

2026-11-06, night 006-12. The rest: 004-02's `ScaleBench` and 005-65's
`ScaleBench-065.diff`.

* `ScaleBench`: `seekFirstPos(long)` without the inner call (throws
  `UnsupportedOperationException`, as `Perf.java`), `retainForever()`
  dropped, and `SyncLevel.STRONG` is `ORDINARY` (STRONG is gone with
  005-11; it was `ORDINARY` without a replica).
* `ScaleBench` again: 005-52 (after 2026.2) changed what its timed load
  listener uses, `NodeCollection.LoadListener.loaded()` to `loaded(OpData)`
  and `Eviction.afterLoad(Db)` to `afterLoad(Db, boolean paced)`. The
  listener now has both `loaded` methods (no `@Override`), and calls
  `afterLoad` through a `MethodHandle` found once, with `paced` false for a
  transaction's warmup (`Trans.WarmupGetData`, tested by its class name), as
  Db's own listener; before 005-52 it is the old call. 009-03's
  `ScaleBench-009.diff` still applies, at an offset (`patch -s` says
  nothing).
* `ScaleBench-065.diff`: the one line that used `Eviction.LOW` now calls a
  new `lowWatermark(budget)` in the diff, which takes `Eviction.lowOf` by
  reflection in a jar that has it (005-79's integer take, the line that
  016-10's `prep-tools.sh` puts in) and the budget times `LOW` in a jar
  before 005-79. So one diff compiles against all of them, and 2026.1, which
  016's W7 runs compare with 2026.2, keeps working: `lowOf` alone (as
  `prep-tools.sh` writes it) would not compile against 2026.1, which has no
  `lowOf`. `prep-tools.sh`'s change of that line now finds nothing to
  change, and its check that `Eviction.LOW` is gone passes; it is not
  changed. Regenerated against `ScaleBench` with the `-009.diff`, as
  005-65's `prep.sh` and `prep-tools.sh` apply them; else as before.

Compile checks (2026-11-06, `javac --release 17`, JDK of
`/opt/homebrew/opt/openjdk`): 016-10's `prep-tools.sh` itself, run with
this branch's tree as TREE and the output in a scratch directory
(`ScaleBench` with the `-009.diff` and the `-065.diff`, the `SyncLevel`
import where the jar has it, `PauseProbe`, `StreamDigest`, `pidio`), prints
`PREP TOOLS OK` against each of

* the `main` jar of this branch (`java/build.sh`; `lowOf 1`);
* `releases/2026.2/bergdb-2026.2.jar` (`lowOf 1`);
* `releases/2026.1/bergdb-2026.1.jar` (`lowOf 0`: it has `LOW`).

Against each, `lowWatermark` gives 0.75 times the budget (750,000,000 for
10^9; 9,259,259,175 for 12,345,678,901), as `budget * LOW` and `lowOf` do.
`ScaleBench` alone, without the `-009.diff`, still does not compile with
`--release 17` against any of the three (`Thread.threadId()`, Java 19; and
`KeyNode.setPointerAccessData`, gone with 009): as before, it is used only
with that diff (005-65's `prep.sh`, `prep-tools.sh`). 005-65's `prep.sh`
applies the same diffs; its default builds (`bf19075`, `eaec93e`,
`4f7cd60`) are before 005-79, 005-52 and 019-04, as 2026.1 is, and were not
compiled again.

The Done when holds: each tool compiles against `main`, and `ScaleBench`
gives 005-79's integer low watermark there; the tools that do not are
kept, with a note in their items, for the code of their time (above).
