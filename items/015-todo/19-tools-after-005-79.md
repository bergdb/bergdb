015-19. Fix: tools in items still use what 005-79 removed
=========================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

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



State (night 006-12)
--------------------

Clone `/Users/f/fl/bench/006-12/g5a`, branch `w1-g5a`. Done: the tools
above, committed (items only, compiled with `javac` against the branch's
jar and 2026.2's). Next step, after the night's quiet blocks (not before
06:20 on 2026-11-06): `ScaleBench` (004-02) and `ScaleBench-065.diff`
(005-65), then this entry is done.
