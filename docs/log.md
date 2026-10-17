BergDB development log, 2026
============================

Dated entries from 12 October 2026 of intermediate results while the code and
the theory were developed. They are history. [levels.md](levels.md) gives the
reviewed status. References to the former `docs/level2-design.md` and
`docs/level2-review.md` are historical: both were consolidated into
`levels.md` on 13 October. Commit ids in this log and in the other documents
(`49aa48d`, `be61ed6`, `ebe5f77`, ...) name commits in Frans's earlier
repositories, not in this one.

2026-10-12. Studied the theory documents. Wrote `docs/problem.md` (the
problem statement) and `docs/startup-invariants.md` (the startup
formalized, with test results). Wrote `java/stress/RestartInvariance.java`, and
tested invariants with experimental patches
(`java/stress/restart-experiments.diff`).

2026-10-12. Read Lomet and Salzberg 1989 (the TSB-tree). Wrote
`docs/prior-art.md`: BergDB's index is in the WOBT, TSB-tree and MVBT
family; self-indexed streams is the candidate novel concept.

2026-10-12. Tested feature by feature what works (`docs/levels.md`):
without restarts, and with restarts by full replay (stream below the
startup distance), everything passes, except deleting a missing key of 7 or
more bytes, which breaks the next restart (`java/stress/DeleteRepro.java`).

2026-10-12. Fixed the delete bug in the 2017 source. A delete of a key that
does not exist created a key node when the key was 7 bytes or longer; a
restart did not, so node ids differed and a later restart failed. Now
`Dag.putKv()` creates no nodes for a delete. Added two unit tests, both
failing before the fix: `DagTester.testDeleteMissingKey` and
`DbTesterRestart.testDeleteMissingLongKey`. All 857 unit tests pass. In
`RestartStress`, restarts by full replay with deletes and 7-byte keys now
pass 100 of 100 rounds (before: 100 of 100 failed). With patches E1, E4 and
E6, the "Key node with size 0" failures are gone. See `docs/levels.md`.

2026-10-12. Added `java/stress/level1.sh`, the level 1 regression check (about
70 s; `quick`, about 20 s). It passes. It uses the default node size, 14
and 62. Node size 8 is left out: with restarts by full replay, 5 of 200
rounds give a wrong historical lookup (1 of 200 without restarts).

2026-10-12. Decided to formalize self-indexed streams from theory, without
the Java code, and to prove them in Lean 4. Chose Rule A: a node that is
still dirty after it is written gets the current transaction as its
got-dirty index, so it is written only once per startup section, at the
cost of reconciliation at startup. Wrote `docs/sis-model.md`.

2026-10-12. Installed Lean 4 (elan, toolchain 4.34.1). Wrote `lean/`:
milestone 1, the model's definitions, assumptions and the statements of T1
and T2, with the example of sis-model.md section 7 and a random test on a
four-level structure with splits. All checks pass. The random test found a
gap in sis-model.md: Rule R must also follow vpos pointers. Fixed.

2026-10-12. Fixed the second level 1 bug, found as "the node size 8 bug".
A transaction that replaced the space root twice (a time split, then a
space split) created two top nodes with the same time, and
`TopDs.findSuperRootAtTime()` could later return the first one, so a
historical lookup missed part of the transaction. It affects every node
size: with the default size 30, a transaction of about 20 keys is enough.
Now `TopDs.newSuperRoot()` updates the top node created earlier in the same
transaction instead of adding one. Wrote `java/stress/DagFuzz.java`, which found
the cause, and the unit test `DagTester.testTwoNewRootsInOneTransaction`,
failing before the fix for node sizes 8, 14 and 30. All 858 unit tests
pass; node size 8 passes 200 of 200 level 1 rounds (before: 5 of 200
failed). Added node size 8, small trees and `DagFuzz` to `level1.sh`, which
passes. See `docs/levels.md`.

2026-10-12. Proved T1 and T2 in Lean (`lean/SIS/Proof/`, about 3,500
lines): for any structure with A1 to A4, any startup pos policy and the
exact still-dirty test, startup from the stream gives back every node and
D, and a run with restarts appends the same records as one without. No
`sorry`; only Lean's standard axioms. While proving: A2 had to be stronger
(entries only to nodes reachable after the change), "no resurrection" is
not needed, and two invariants were missing from the sketch.
`docs/sis-model.md` is now draft 2, with the changes in its section 14.

2026-10-12. 15:50. Fixed a bug. See DagTester.testTwoNewRootsInOneTransaction.
It replays one failing case each for sizes 8, 14 and 30. All three failed 
before the fix and pass after it.

2026-10-12. Wrote `docs/level2-design.md`: how to get level 2 working
while reads of nodes in memory follow Java references as today. All extra
work is at startup, at the first touch of a node and in the internal
transaction. A new lemma, that a newer version of a node is good whenever an
older one is, makes it safe to swizzle a pointer once. Measured today's read
speed for comparison: 265 ns per get with 100,000 keys, 540 ns with
1,000,000 keys. Nothing implemented yet.

2026-10-12. Level 2, step 1 of `docs/level2-design.md`: four small fixes,
each with a unit test that failed before it.
* A top node written again lost the times of skip pointers read from the
  stream (`docs/level2-review.md`, defect 7;
  `StoredTopNode.testStreamPointerTimesKept`).
* A new top node took a skip pointer read from the stream as no pointer
  (defect 8; `TopTester.testNewSuperRootFromStreamPointers`).
* The alignment padding of value nodes was not written, so the same
  transaction could give other bytes and checksums
  (`StoredTrans.testSameBytesFromReusedSerializer`).
* `DbStarter.checkStreamPointers()` checked the node's own position instead
  of its pointers, so it never rejected anything
  (`DbStarter.testCheckStreamPointersOfKeyNode`).

All 862 unit tests, the night tests and `level1.sh` pass. With the padding
written, level 1 streams are byte for byte the same with and without
restarts, in 6 of 6 runs; `level1.sh` now requires it. Level 2 random
configurations: 60 of 100 fail (63 before); steps 2 and 3 are the main
repairs. `build.sh` and `level1.sh` now delete files, not directories, since
Finder can add a `.DS_Store` to a directory while it is being removed.

2026-10-12. Level 2, step 2 of `docs/level2-design.md`: one node table, and
Rule R by node id.
* Found: `Db` and `NodeCollection` had a node table (`Cache3`) each. Nodes
  created in memory were in one, nodes read from the stream in the other, so
  after a restart a stream pointer to a node in memory read a second copy.
  That is how D came to hold copies (`docs/level2-review.md`, defect 1).
  Now there is one table.
* `NodeCollection` follows a stream pointer by node id: the table's
  canonical object if there is one; else the newest of the version the
  pointer names and the node's newest version in the startup section (Rule
  R, also for a vpos), cut back to the startup time. It calls the pointer
  listener on every follow and swizzles the pointer (defects 2, 3, 4). Puts
  and the rerun use a writer follower, which makes every node it reaches
  canonical. A reader's memory-pointer path is unchanged.
* `DbStarter` builds Rule R by id for all index nodes, top nodes included,
  instead of prevPos chains, registers the section's nodes, and looks up
  got-dirty nodes by id. Found and fixed: a node created and written in the
  section got its vpos as spos at startup, so a parent written later named
  the vpos, which a later startup could not resolve.

Tests that failed before: `NodeCollection.testFollowNewerVersion`,
`NodeCollection.testFollowRuleR`,
`DbTesterRestart.testOneObjectPerNodeAfterRestarts`. All 865 unit tests,
the night tests and `level1.sh` pass. Read speed is unchanged within the
noise (`bergdb.test.Get`, 100,000 and 1,000,000 keys, alternating with the
step 1 build). Level 2: random configurations fail 37 of 100 (60 before);
the default case on disk past 20 MB, without deletes, passes 5 of 5 (5 of 5
failed); in RestartInvariance with restarts every 250 transactions, node
identity and lookups are correct (3 of 3 seeds), but the stream differs from
the one without restarts. Most remaining failures, and all 10 of the default
case with deletes, stop at startup: a got-dirty node is not found, where
before a copy was read. (The cause, found in step 3: a delete of a key that
does not exist; see the next entry.)

2026-10-12. Discussed publishing a paper on self-indexed streams.
`docs/prior-art.md` is now draft 2: Berkeley DB JE is purely append-only
too, so the candidate claim is the combination of four properties, P1 to
P4 (section 5.3), with new relatives (LogFS aliases, LeanStore, ForestDB,
OrioleDB) and what to check next.

2026-10-12. Level 2, step 3 of `docs/level2-design.md`: the write path,
and two more startup bugs. Level 2 now passes every test run.
* Before index nodes are written, `NodeCollection.resolvePointers()`
  resolves their pointers to index nodes by node id: a pointer to a node
  that has a canonical object becomes a memory pointer to it, so a node
  written in the same record is named by its new position, and the
  still-dirty test sees every node in D (`docs/level2-review.md`,
  defects 5 and 6). Otherwise the pointer names the newest version known.
* Found: a delete of a key that does not exist makes the nodes on its path
  dirty, but it is not stored, so the rerun does not reach them. Startup
  now takes such a node in D from the position stored with its got-dirty
  id, as the model rebuilds D from the stored ids. This, not defects 5 and
  6, was the "got-dirty node not found" after step 2.
* Found: after a restart, the meta block held the position of the last
  transaction as of the last meta block on disk. Startup now sets it to the
  last transaction, so later meta blocks are the same as without restarts.

Tests that failed before: `NodeCollection.testResolvePointers`,
`DbTesterRestart.testLastTransPosAfterRestart`,
`DbTesterRestart.testLevel2RestartsKeepAllValues` (every key checked at
the latest and earlier times after each of 60 restarts, node sizes 30 and
8, deletes, long keys, transactions of up to 20 keys) and
`DbTesterRestart.testLevel2SameStreamWithRestarts` (the stream is the same,
byte for byte, with and without restarts: T2). All 869 unit tests, the
night tests and `level1.sh` pass.

Level 2 results: `RestartStress` random configurations 0 of 200 fail (37 of
100 after step 2); the default case on disk past 20 MB with deletes 0 of 10
(10 of 10), without deletes 0 of 5. `RestartInvariance` gives the same
stream byte for byte, with node identity and all lookups correct, in all 20
runs: startup distances from 100 bytes to the default 20 MB, node sizes 8
to 62, long keys, transactions of up to 40 keys, a restart after every
transaction, and the 100 MB case. Reads and writes are as fast as with step
1 (`bergdb.test.Get`, and its puts, alternating builds). New options in
`RestartInvariance`: `long=1`, `bigtrans=N`; and it reports whether the
stream was the same up to a failed restart.

2026-10-13. Test times and the failing f-test. Frans wrote the time rules
into `Unit.java` (normally at most 100 ms per test) and `F.java` (at most
10 s). `CreateIndexTester.testRestart`, the one failing f-test since 2015,
failed on timing, not on a bug: the index job was done before the restart,
first within the 100 ms sleep, and with 10,000 employees during the sync
before the stop. It now uses 100,000 employees and a 20 ms sleep (about 2
s), and passes: the job is resumed after the restart. Made the two level 2
unit tests small (under 100 ms each; the unit tests now take 5.5 s, from 6.5
s) and checked that each still fails without the fix it is for; their
earlier sizes are now f-tests. All 869 unit tests and all 28 f-tests pass.
`Concurrency2.test1` takes 10.2 s, just over the f-test rule.

2026-10-13. Level 2, step 4 of `docs/level2-design.md`: `java/stress/level2.sh`,
the level 2 regression check, like `level1.sh` (about 2 minutes; `quick`,
about 30 s). It runs the unit tests; `RestartStress` with 200 random
configurations, with startup distance 1000 bytes for each node size, and
with the default settings on disk past 20 MB; and `RestartInvariance` in 6
configurations, from a 100-byte startup distance and a restart after every
transaction to the 100 MB case, each requiring the same stream byte for
byte. It prints `LEVEL 2 OK`. Checked that it fails when the got-dirty fix
of step 3 is undone (the small level 2 unit tests catch it).

2026-10-13. Level 2 under load and crashes (`docs/levels.md`, "Level 2
under load"). Wrote `java/stress/LoadTest.java`: load, updates, restart and
reads on disk, with 1M and 10M keys. Startup is 0.6 to 0.7 s with the
default 20 MB startup distance, for an 18.5 GB stream as for a 1.6 GB
one (15.7 s by full replay of 0.5 GB); the startup section stays within
1.0 to 2.2 times the startup distance; about 100,000 single-put
transactions per second and 1 us per get. The costs: 6 to 10 bytes
appended per user byte with uniform random updates (1.65 without index
writes), all history in the heap (7.3 GB for 10M keys after 10M updates),
and commit pauses of 120 to 260 ms, which are G1 pauses (4.75 ms max with
ZGC). Wrote `java/stress/CrashTest.java`: the stream cut at random positions,
startup checked against a model, work on, restart. Now step 5 of
`level2.sh`. Fixed four bugs of the 2017 code, each with a unit test that
fails without the fix:
* `Cache3`: streams longer than 2.1 GB failed (a negative map index for
  node ids of 2^31 and more).
* `BufferedStream`: after a restart, reads of bytes still in the write
  buffer returned other bytes.
* `RecoverableStream`: a crash within a transaction's size bytes could
  make startup fail ("Bad transaction size").
* `BufferedStream` and `StorageManager`: a sync returned normally when the
  write to disk had failed. Also a one-byte flush wrote the wrong bytes.

All 874 unit tests, `level1.sh` and `level2.sh` pass. Decided with Frans:
a working, performant database is the first goal; next are reclaim (level
3) and eviction (level 4).

2026-10-13. Claude had changed sync to flush the write buffer at once
(9 to about 15,000 synced transactions per second for a single writer
that syncs every transaction). Frans: keep the 2017 design, where a sync
waits for the next buffer write (about 100 ms), so that many transactions
share one durable write, and the application chooses when and how to sync.
Reverted; the bug fixes in `BufferedStream` and `StorageManager` stay.

2026-10-13. Level 3, reclaim (`docs/levels.md`, "Level 3: reclaim"). The
2017 reclaim had never been tested with restarts after a cut. Wrote
`CutStream` (refuses reads below the cut) and `java/stress/ReclaimStress.java`:
20 of 20 random configurations failed. Fixed ten bugs, each with a test
that fails without the fix, and reworked `Reclaim.java` so that all its
state is in its stored table or follows from stream positions:
* Old values were skipped: the rewrite test used the value's time, which
  after a time split of its key node is the split time. Now its position.
* Q6: the first available lookup time was the iteration's start, not its
  end.
* Q7: nodes with deleted keys only, and subtrees of deleted long keys, were
  never rewritten. Now each step also "touches" its key range
  (`Trans.touch`): every index node on the way gets dirty.
* Startup after a cut read below it (meta block search, and the scan of
  transactions from a meta block).
* After a restart, the first available lookup time came from the last
  iteration, cut or not. The table now marks the cut.
* `NodeCollection.resolvePointers` (level 2) read headers of dead pointers
  below the cut.
* The cut ignored that recovery starts at the transaction the last meta
  block names, ignored the startup pos, and did not wait until the
  rewritten nodes were written.
* `BufferedStream` passed on a cut still in its buffer.
* Reclaim starved with small startup distances (its own table writes used
  the allowance).
The cut now also waits until the table is durable. `RestartInvariance`,
`CrashTest` and `LoadTest` got a `retain` option. Results: `ReclaimStress`
0 of 200, the same stream with and without restarts (also a restart after
every transaction), `CrashTest` 0 of 50, and `LoadTest` with a restart and
a full check at every cut. New check `java/stress/level3.sh` (about 3 minutes).
All 882 unit tests, the f-tests, `level1.sh`, `level2.sh` and `level3.sh`
pass. Under load (1M keys, retain 1 s) reclaim costs much: the stream after
the cut is 8 to 12 times the live data, throughput falls from 102,000 to
56,000 updates per second, and commits during reclaim write up to 4019
index nodes. The touch was initially blamed; later measurements counted
few additional dirty nodes after the value rewrites, without establishing
the cause of the bursts. Next at that point: reduce reclaim's cost and
spread its writes, then level 4. Q9 (`Kv.time()` after a rewrite) is left
for later; found that
`Kv.time()` is already wrong after a time split.

2026-10-13. The cost of reclaim (`docs/levels.md`, "Level 3 cost").
Frans: with a long retention, little is gained by reclaiming often; how
should reclaim work? Added statistics to `Reclaim` (in memory, off by
default: per iteration the KVs scanned and rewritten, the nodes the touch
makes dirty, and the cuts) and wrote `java/stress/ReclaimCost.java` and
`java/stress/reclaimgrid.sh`: three workloads (uniform, hot, cold) and H = W_R /
L from 0.14 to 158, in simulated time. Results: iterations run back to back
whatever the retention, each rewriting 69 to 96% of the KVs; reclaim adds
20 to 36% to the bytes written, and the stream is 9 to 13 times the live
data with a short retention, 1.05 times the retention window with a long
one. At H = 158 the share rises to 39 to 51%, because the reclaim table
grows by a row per iteration and every step stores all of it. The touch
adds few dirty nodes after the rewrites; that count does not isolate total
maintenance index cost or explain the large commits, whose cause is open.
internalFraction 0.5 instead of 0.25 makes the stream about a quarter
smaller and reclaim's extra writes 3 to 5 times larger. Next: pace
iterations by the retention, and store the table per row. Also fixed a
race found by `level1.sh`: the unit test
`BufferedStream.testPretruncateBeyondFlushed` (bug 8 of the reclaim work)
failed now and then, because a pending cut was made after the flush was
published, so `close()` could return first. Now it is made before: 53 of
40,000 runs of the test failed before, 0 after.

2026-10-13. Frans defined the measures WE (write efficiency: user bytes
written / stream bytes appended) and SE (store efficiency: user bytes
accessible / stream kept), and asked for values of 100, 1000 and 10,000
bytes. `ReclaimCost` now reports both, takes the retention as K (updates
per key within R) and keeps the live user data at 30 MB. The grid
(`reclaimgrid.sh`, 45 runs) with the initial repair: reclaim lowers WE by
about 20 to 35% at K up to 1, up to 39% at K = 10; SE is 0.09 to 0.31
at K = 0.01, reaching 0.46 at K = 1, and 0.45 to 0.62 at K = 10 for
values of 1000 bytes and more. Table in
`docs/levels.md`, "Level 3 cost". This is the baseline for step 3,
pacing by the retention and the table per row.

2026-10-13. Step 3 of the reclaim cost work: an iteration starts only when
a quarter of the retain duration has passed since the last one
(`Reclaim.ITERATION_SPACING`), and a step stores only its own row (key
`dreclaim/-current.txt`), not the whole table. Two new unit tests fail
without the change; all three level checks pass (884 unit tests). The grid
again: the extra loss at K = 10 is gone (uniform, 1000-byte values: WE 0.45
to 0.62, SE 0.45 to 0.55; 10 kB: WE 0.67 to 0.81); elsewhere little change,
since iterations that take R/4 or longer still run back to back at the
rate f allows, copying unchanged data. Options left in `docs/levels.md`.

2026-10-13. The older cut point (option 3) was implemented in the earlier
`b70fe6b` baseline: values are rewritten only if stored before the previous
iteration's start, and the cut uses that position. The recorded level
checks pass (885 unit tests, 29 f-tests). At K = 10, uniform 1000-byte
values: WE 0.623 to 0.716, SE 0.547 to 0.573; uniform 10 kB: WE 0.814 to
0.940, SE 0.710 to 0.752. Other workloads and shorter retention have
different tradeoffs; see `docs/levels.md`, "Level 3 cost". The subsequent
index-aware budget and scan target are recorded below.

2026-10-13. Documentation closure: reviewed all eight Markdown documents
authored for this item, checked source and recorded results, and corrected
current summaries, measurement ranges, proof boundaries and historical
references. The seven recovered historical Markdown files are unchanged.

2026-10-13. Items 2 and 3 of the reclaim cost work, now committed in
`ebe5f77`. The allowance of a
step now counts the index nodes it makes dirty (their stream size), not 100
bytes per value; the row is stored by a value transformation, and the
touch comes before the puts. The large commits came from large steps: the
allowance is a budget for the whole iteration, so a step could make 800
index nodes dirty, and a user commit later wrote them all, with the parents
the still-dirty test kept dirty (up to 1100 index nodes). Steps now use a
16 KB scan target (the final KV can exceed it); user commits in the grid
write at most 125 index nodes (31 without reclaim across workloads, 18 for
uniform). WE changes by -0.013 to +0.012. New test
`testAllowanceCountsIndexNodes`; all three level checks pass (886 unit
tests). These changes are included in the updated end-of-day snapshot;
numerical and source consistency were checked, without independently
rerunning the Java gates.

2026-10-13. Updated the documentation snapshot to `ebe5f77` (18:02 CEST):
886 unit tests, 29 f-tests, index-aware reclaim budgeting and the 16 KB scan
target. Earlier algorithm versions and measurements remain historical.

2026-10-13. Default startup distance 50 MB (was 20 MB; `DbBuilder`,
`DatabaseBuilderImp`), Frans's decision after measuring: startup 0.63 s
with 1000-byte values (0.30 s before), 1.4 s with 100-byte values (0.78 s),
0.36 s with 10 kB values; WE up 9% (1000 bytes) to 35% (100 bytes).
Existing databases keep the distance stored in their stream. `level2.sh`
runs its default case on disk to 920 MB (was past 20 MB); `level3.sh` keeps
20 MB for its LoadTest, which otherwise reaches one cut instead of six. All
three level checks pass. Table in `docs/levels.md`, "Level 2 under load".

2026-10-13 (evening). Level 3 follow-up carried out, with Frans's decisions
(a read may expire; no exact value time; f stays 0.25). Reader safety:
`ReadBelowFirstPosException`, not remembered by
`FileStream` or `StorageManager`; `Db` turns it into
`LookupTimeNotAvailableException`; tests `ReclaimReaderTester`, the stress
`ReclaimReaders` in `level3.sh`. Retention changes: `ReclaimRetentionTester`,
random changes in `ReclaimStress`, which also checks every key at every
transaction time for up to 50 keys. `Kv.time()` and `Connection.time()`
removed. `Reclaim.Stats` counts the records by writer and content;
`ReclaimCost` prints where the bytes go. GetMany inclusive start key fixed.
Documentation of the Pub API (expiry, cost of a finite retain duration).
896 unit tests, 35 f-tests; the three level checks pass (level3.sh now takes
about 4 minutes).

2026-10-14. Replaced the completed Level 3 plan with the next three validation
tasks. Consolidated the independent review results into `docs/levels.md`;
the detailed old plan and review remain in Git at `5650ed7`. Level 4
implementation awaits the durability checks, soak and performance reference.

2026-10-15. Level 2 alignment of the Java code and the Lean model (F1-008-11,
repository f1): `docs/level2-alignment.md` (the mapping, the register, the
red list), the trace exporter `java/stress/TraceExport.java` and
`conformance.sh`, the trace checker `lean/` `lake exe tracecheck`. Found and
fixed a startup bug (M18): transactions that change nothing could move the
startup pos past every top node version, after which the database could not
start ("Could not find super node in startup section"); reproduced with 10
empty transactions at a startup distance of 100 bytes. Every record now
stores topPos, the position of the latest version of the newest written top
node, and startup starts there; the record format byte is 5 (it was 2; the
constant `CURRENT_FORMAT_VERSION = 4` was never the stored byte), and older
streams are refused. Tests: `DbTesterRestart.testRestartAfterTransactionsThatChangeNothing`,
`StoredTrans` tests for topPos and the old format. The three level checks
pass. Performance, quick suite against `a116ec7`: no alerts, throughput
unchanged within noise, the stream 0.7 percent larger (8 bytes per record).
In Lean: marking the access path in step 3 (`Algo.mark`), A5 as an
assumption, T13 (marking is exact), and BergDB's still-dirty test
(`javaTest`); T1, T2 and T13 hold for it and for the exact test.

2026-10-16. Level 2 alignment, the model (F1-008-11, WP E3, repository f1):
`lean/` gets the virtual root of option (a) (`Spec.virt`, docs
`level2-alignment.md` 8.6): the root is never in D and never written, top(i)
names the root's child at s(i), and startup reads the root children through
their pointers (BergDB's skip pointers) and rebuilds the root. New
assumptions R1 to R4, and older top nodes are dead. T1, T2 and T13 are proven
with and without a virtual root; with one they need BergDB's still-dirty
test, Rule A over all pointers, which keeps the references between top nodes
fresh. Also Rule R from R(s) on (M7) and a startup pos policy that sees the
transaction (M10). The trace checker now runs the model's own `init` and
`step` and checks R1 to R4 on Java's traces; the exporter writes the node of
top(i) on the `REC` line.

2026-10-16. A Java transaction is one transaction of the Lean model
(F1-008-11, WP D1; F1-008-10's prototype in production quality;
`docs/level2-alignment.md`, M1, M2, 10.4). A transaction applies its keys
one at a time, and a later key could split a node that an earlier key had
created or changed: the created node was never reachable, the changed one
kept klongs no lookup sees. Now a node that the transaction created is split
in place (`Dag.handleFullNode`), and a node that existed before is replaced
and then loses its klongs of the transaction (`KeyNode.toPreviousState`; the
class comment of `KeyNode` says why readers are safe). Marking (step 3)
happens when an operation ends, and only if it changed something, so a
delete of a missing key marks nothing; a node that the transaction replaced
leaves D. Java's step 3 is then the model's marking (T13). Tests:
`DagTester.testTransactionLeavesNoUnreachableNode` (40 sorted puts, two root
changes in one transaction), `DbTester.testDeleteOfMissingKeyMarksNothing`,
`testReplacedNodeLeavesD`; `testPointerCreationListener` follows the new
contract. `ReclaimReaderTester` now takes the first seed whose held reader
reaches the cut: whether it does depends on where the versions lie, and with
the change seed 1 no longer does (seeds 2, 8 and 11 did not before); a reader
that does not reach the cut must end with every KV. The three level checks
pass; 1.4 to 13.7 percent fewer stream bytes in five workloads.

2026-10-16. Level 2 alignment finished (F1-008-11, WPs D2, F1 and F2;
`docs/level2-alignment.md`, 10.5, 11 and 12). D2 had nothing left to change.
F1, the conformance campaign on `d5c56dd`: the trace checker on 50 small
and 9 medium traces, every transaction a step of the model, every restart
invisible (`CONFORMANCE OK`); the Java tier (`A2A3Check2`) on 68,901
transactions up to the gate's sizes, no failure, Java's marking the model's;
the gates in full. Raw summaries: `docs/evidence/level2-conformance.txt`.
`RestartInvariance` has two new options, `empty` and `nodel`, for
transactions that change nothing (off by default; the gate's runs are
unchanged): mostly idle runs fail on `a116ec7` (M18) and pass now.
`conformance.sh` records the time and memory of each run and gives its
verdict only for the sets it ran. F2: the outcome of the plan's 1.2 point by
point (all six met; T15 not proven, as the proofs did not need it), the
Level 2 status in `levels.md`, the model changes in `sis-model.md`, and a
proposal for a conformance step in `level2.sh`, for Frans's checkpoint K4.

2026-10-16. `level2.sh` checks the alignment with the Lean model (Frans's
decision at K4, `docs/level2-alignment.md`, 12): step 4 also runs
`RestartInvariance` on mostly idle transactions (seeds 1 and 2), which
catches M18; a new step 7 runs `A2A3Check2` on three configurations and the
trace checker on `conformance.sh`'s small set (2 seeds quick, 10 full). The
gate now needs Lean; it builds the checker with lake.

2026-10-16. Bergdb item 001 started: Levels 3 and 4 in the Lean model and in
Java (`items/001-lean-model-levels-3-4/`). WP A1: the baseline, and
`java/stress/StreamDigest.java`, which compares the stream bytes of a build
with those of the preserved build `l34-base`. WP A3: the top node ordinal
bug of F1-008-13 (levels.md, "Bugs found by the alignment of Levels 3 and
4") is fixed, with round-trip and restart tests and two parser checks;
startup checks the super root without `-ea`. Streams with top node ordinals
below 32,768 are unchanged, byte for byte.

2026-10-17. Bergdb item 001, WP R8, change 6 (R7's red list, register M17 of
`docs/level3-alignment.md`): in a reclaim step, a transaction with a touch,
`Db.endOfTrans` takes out of D the nodes that the step's puts marked and
replaced, as in every other transaction, and keeps those that the touch
marked; before, a touch transaction kept every mark. New test
`DbTester.testTouchTransactionReplacedNodes`, failing before the change. Only
runs with reclaim get other records: StreamDigest against `l34-base` finds
the 24 digests of the Level 2 configurations the same, byte for byte, and 10
of the 12 of the Level 3 ones (reclaim on) different. The trace checker on
R2's small reclaim set made again with the change: 25 of 25 traces TRACECHECK OK (14,448 transactions, 288 cuts; C-CUT and C-CUT+ without a failure), every transaction
a step of the model.

2026-10-17. Bergdb item 001, WP R8, change 2 (E7's list, register M22 of
`docs/level4-alignment.md`): a version that a pointer leads to is cut back to
the startup time only while `DbStarter` reconstructs the database
(`NodeCollection.endReconstruction`); a load at runtime never is, as the Level
4 loader of the Lean model has it (`Mem.follow4`). Not reachable today, since
every node with a version in the startup section has a canonical object, so
no record changes (StreamDigest: the same as with change 6). New test
`NodeCollection.testNoCutBackAfterReconstruction` (a runtime load of a section
version after `endReconstruction`, not cut back).

2026-10-17. Bergdb item 001, WP R8, change 1 (E7's list, rows 1 and 4;
register M20, M21, M26 and M44 of `docs/level4-alignment.md`): before index
nodes are written, `NodeCollection.resolvePointers` resolves by node id only
the pointees in the pinned set (the canonical objects of D's nodes and of the
record being written, which are dirty: `Db.store` now resolves before it
cleans the record's nodes), and every other pointee from its slot (a memory
pointer's object, or a stream pointer's version after Rule R); no snapshot
or clean canonical object from the node table. At startup, rule 4
(`DbStarter.linkD`, `NodeCollection.linkToCanonical`) links the stream
pointers of D's canonical objects to canonical objects by node id, as the
model's `Mem.linkD`. Without rule 4 the change gave other records after
restarts (StreamDigest: 3 of the 36 digests, all of runs with restarts);
with it, the same records as before (36 of 36). New tests
`NodeCollection.testResolvePointersUnpinned` and `testLinkToCanonical`.

2026-10-17. Bergdb item 001, WP R8, change 3 (E7's list, row 3; register
M27 of `docs/level4-alignment.md`, plan Q7): the loader
(`NodeCollection.followStreamPointer`) takes a node's canonical object if it
has one, else reads exactly the version the pointer names after Rule R, as a
snapshot that the node table does not get (no `register`, and
`pointerCreated` only for a canonical object); it never takes a snapshot
from the table. This is the Level 4 loader, `Mem.follow4`. Records: the same
(StreamDigest, 36 of 36). The trace checker has a new diagnostic, C-L4: the
FIRST lines against the Level 4 loader (none takes a snapshot since the
change); test trace `snapfirst.trace`. New test
`NodeCollection.testLoaderReadsTheVersionNamed`; `testFollowRuleR` now
checks that a second pointer reads the version again.

2026-10-17. Bergdb item 001, WP R8, change 5 (E7's list, row 6; register
M28 of `docs/level4-alignment.md`): reclaim's scan and its reads of each KV
(`Reclaim.step`) are maintenance reads, through a follower of the step's own
(`NodeCollection.maintenance`): it loads as the readers' follower does (the
canonical object, or the version the slot names after Rule R), but swizzles
nothing into the slots, enters nothing in the node table, leaves the slots'
access data as they are, and keeps what it read for the step, so a version
is read once per step. Before, both reads swizzled what they read, the
values too, which then stayed in memory for good. Records: the same
(StreamDigest, 36 of 36). New test `NodeCollection.testMaintenanceFollower`.
