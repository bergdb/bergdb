006-05. The TODO markers in java/: a review
==========================================

Created 2026-10-25 by Claude (Opus 5.5, Claude Code) for Frans Lundberg.

At Frans's request: "Go through all Java code, find all locations with
TODO, XXX, or FIXME flags in the code. For each one, propose what to do
with it: remove the comment, add an item to 005, or some other proposed
action." To the proposal, his answer: "as proposed".


The markers
-----------

15 in `java/` on `67bcc02`, all `TODO`, in 13 files; no `XXX` or `FIXME`,
and none in the Java of `items/`. 13 are from 2013 to 2017, and two are
Frans's idea of 2026-10-13. His rule for them, in
`java/src-dev/bergdb/dev/package.html` (2013): "Use NOTE in addition to
TODO and XXX. NOTE is used for something we may want to modify at in the
future. Possible improvements, considerations. NOTEs can be kept in the
code indefinitely, while XXX are temporary and should be gone before each
commit. Most TODOs should be gone before a release. Use backlog for
future tasks." The backlog is now 005.

| ID | Where, on `67bcc02` | The marker | What was found | Done |
|---|---|---|---|---|
| T1 | `src-dev/bergdb/dev/Dev.java:4` | Call `Db.possiblyEvict()` several times from `getMany()` (2015) | Obsolete: there is no such method (`Cache2`'s evictor had one, never wired in; removed in 005-10). Since item 001 (WP J7) the capacity controller sweeps after every load from the stream once the budget is passed (`Eviction.afterLoad`), so a large `getMany` is held in check load by load | Removed |
| T2 | `src-dev/bergdb/test/StartupDistanceTester.java:19` | "We need more startupDistance testing. See payTillStreamSize(3.0e6)", with `//payTillStreamSize(3.0e6); // NOTE result in problems` (2015) | The problems were an assertion, removed in 2015; see below | Both lines removed |
| T3 | `src-dev/bergdb/test/java/MyLongMap.java:20` | A bare "TODO A." on the fixed table size (2017) | A benchmark of Java, kept in 005-10 (D1); the next line says the size is fixed for the test. A table that grows is 004-03's open question (section 3) | Removed; MyLongMap named in 004-03, section 3 |
| T4 | `src/bergdb/core/Db.java:1278` | "DbException or something else?", in `getTrans` (2016) | Thrown only for a position at or past the end of the stream | Fixed in 005-43 |
| T5 | `src/bergdb/core/DbHelper.java:93` | "Make sure this class is tested", `AddReplicaClass` (2014) | Still true: only the ID check is tested (`DbTester.testBadReplica1`). For 005-11 to decide; its report quotes the line | Removed; 005-11's option B names the tests |
| T6 | `src/bergdb/core/DbStarter.java:590` | Check the stream format version (2015; 005-40 has its history) | The parsers check it | Done in 005-40, which found a fault there |
| T7 | `src/bergdb/core/TransSeq.java:112` | Raise the node count limit when the startup pos falls behind, by more than 2 × sd (2015) | The origin of 007's D1, decided on 2026-10-24: a deadline at 2 × sd, 007-03's step 3, not started | Kept; step 3 removes it, and the comment's claim that the startup pos "should never fall exceedingly behind" (007-01, 4.1: up to 2.21 d) |
| T8 | `src/bergdb/dag/Dag.java:166` | "We need to set g.pointerFollower somehow, I suppose." (2017) | Written in the last commit of 2017 (`50786b2`), which moved the follower from `Dag` into `OpData`; done there: every caller sets it, and `OpData.followPointer` asserts that it is set | Removed; the Javadoc of `newGetData` and `newPutData` says that the caller sets it |
| T9 | `src/bergdb/dag/Dag.java:1053` | The time split's `replaceKlong`, "A bit of a hack ... Consider other solution" (2013 and 2015) | A refactoring idea; the time split is tested (`DagTester.testTimeSplit1a`) and checked by DagFuzz, A2A3Check2 and the level scripts with StreamDigest | A NOTE; the test's old name, `Graph.testTimeSplit1a`, corrected |
| T10, T11 | `src/bergdb/pub/Connection.java:266`, `src/bergdb/pub/Transaction.java:53` | Frans's idea: `isDurable()` and `isDurable(SyncLevel)` (2026-10-13) | Not started | Removed; 005-41 (decide) |
| T12 | `src/bergdb/pubimp/ConnectionImp.java:125` | "we cannot in general convert keys to ukey (strings). How to handle in Pub Layer?" (2016) | A fault, with a probe: `transactionInfo()` gives internal KVs, whose `key()` throws, and for a value that reclaim has rewritten, reclaim's transaction | 005-42 (decide); the TODO is now a comment that points there |
| T13 | `src/bergdb/pubimp/PubKeys.java:8` | "Review what exception to throw? Make it consistent." (2014) | A bad directory gave `BadFormatException`, a bad key `IllegalArgumentException` | Fixed in 005-43 |
| T14 | `src/bergdb/storage/RecoverableStream.java:15` | "Remove reference to core.StoredTrans, ref storage -> core not allowed." (2015) | The only use: `StoredTrans.CURRENT_FORMAT_VERSION`, 4, the filler of a torn header | Done in 005-40: `RecoverableStream.TORN_HEADER_FILLER`, the same 4 |
| T15 | `src/bergdb/storage/RecoverableStream.java:516` | "This doc is not true, or we have a bug." (2013) | Both | Done in 005-39 |

After it, one marker is left in `java/`, T7's. Two comments name former
TODOs, so a search for TODO finds them: 005-39's in
`RecoverableStream.getPosOfTransCompletedBefore` ("as a TODO here said")
and 005-40's in `DbStarter.validateTransactions`.


T2: the 3.0e6 that "result in problems"
---------------------------------------

`StartupDistanceTester` changes the startup distance of a running database
four times while it pays between 100 accounts, then starts from copies of
its stream cut at random lengths and checks the sum. It is the only test
that changes the distance at runtime; 007-03's step 2 plans a workload
that does.

On 2015-05-31 (`2d5c2a3`, in F1-007's history: the f1 repository's
`a/007-bergdb-261012/bergdb-git.bundle`) the second phase went from 2.5e6
to 4.0e6, with 3.0e6 commented out, "NOTE result in problems", and the
TODO came; the log of that day: "Status: U0 F0 CORE:0.76. Nice :-)
(cheated a bit with StartupDistanceTester, but... well, well...)". A
bisect with 3.0e6, in [05-todo-markers/](05-todo-markers/):

* On `2d5c2a3` it fails at a start from a cut copy, `AssertionError:
  trying to read node at bad spos, 502073, mod8: 1`, in
  `NodeStream.readNode`.
* From `c08e4ce` (2015-07-23, "ZERO BUGS :-) u0f0n0") it passes. That
  commit removed `readNode`'s assertion that a node starts at a multiple
  of 8, which holds for index nodes only: `Spos`'s note of 2015-05-15 says
  that value nodes "can start at any mod8 value" (they are 4-aligned since
  2015-11-14). The log of that day: "DONE! fix f-test:
  bergdb.test.StartupDistanceTester". The 4.0e6 and the TODO stayed.

On `67bcc02`, with the seed and the second phase made properties: 10
seeds × 9 sizes from 1.6e6 to 5.4e6, 90 runs, none failed. The 2017
baseline, `0257e0b`, passes with 3.0e6 too.


What changed
------------

* `java/`: the comments of T1 to T3, T5, T8 to T12, with a sentence of
  Javadoc in `Dag` (T8); 005-43's fix (T4, T13).
* `items/`: 005-41 to 005-43; a line in 005-11 (option B), in 007-03
  (step 3) and in 004-03 (section 3); this subitem.
* `before-commit.sh` passes; see 005-43's outcome.


Files
-----

[05-todo-markers/](05-todo-markers/): `bisect-step.sh`, the step of T2's
bisect, with its usage; `bisect-log.txt`, its steps; `fail-2015.txt`, the
failure on `2d5c2a3`.
