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

2026-10-17. Bergdb item 001, WP R6, part 1 (register M48 of
`docs/level3-alignment.md`, option (a), Frans): `CutOK`'s part 2 now covers
the versions that a physical read in the running process may follow
(`ReadsPhys`, `lean/SIS/Reclaim.lean`): through a pointer to a live child,
every version of the child at or after the record that the pointer names, as
well as what a lookup reads with Rule R. A trusted change; T8 holds as
before. The trace checker's C-CUT checks the stronger part (R4's diagnostic
C-CUT+ is part of it now); test trace `physcut.trace`. Example 4:
`cutReadWitness`'s cut is no longer safe.

2026-10-17. Bergdb item 001, WP R8, change 4 (E7's list, row 5; register
M23 and M24 of `docs/level4-alignment.md`, and M40's clock): slots for
eviction. `TopNode.getPointer` reads the reference once and decides on it
(before, it tested the reference and read it again), as `KeyNode.getPointer`
did. `KeyNode`'s and `TopNode`'s `setPointerAccessData` write access data
only into a memory pointer (the caller holds the pointer's lock, as for every
change of a pointer), so that a position written by an unswizzle (stage 4)
survives a reader that saw a memory pointer; their `getPointerAccessData`
give `Spos.NULL` for a stream pointer (`TopNode`'s asserted a memory pointer).
The access clock is a field of its own, `Cache3.accessClock`, which starts at
10,000 (the old constant, minus `putSize`, which nothing advanced) and
advances by one at every node read from the stream and every node the writer
makes; `Db.getAccessData` is minus it and takes no lock (before, the node
table's lock). Records: the same (StreamDigest, 36 of 36). New test
`NodeCollection.testAccessData`.

2026-10-17. Bergdb item 001, WP R6, part 1b: T-SCHEME tried by running
before proving (scratch probes of example 4's random runs, about 1.2 million
states):
with `CutOK`'s part 2 over every pointer (part 1), Java's scheme does not
always give it; witness `schemeWitness` (`lean/SIS/ReclaimExample.lean`): a
stale chain of versions that Rule A put back during the settling, still in D
at the decision, leads below the cut, while the running memory reads through
the pinned canonical objects and is right. `ReadsPhys` now takes D and does
not extend through such versions (a trusted change); the checker's C-CUT
likewise. With it the scheme gives part 2 in every state checked.

2026-10-17. Bergdb item 001, WP R5, the logical half: T12 proved
(`T12_restartCut`, `lean/SIS/ReclaimTheorems.lean`). A run that restarts from
safe cut streams appends the records of the run without restarts, cut at the
largest cut, with its D and its lookups from the first available time on;
for marking and `javaTest`, with T8's assumptions and `PolicyCutOK`. The
nodes of D that no lookup from f on reaches (M33, M34, the plan's delicate
case): their ancestors at a time they were reachable stay in D by Rule A,
put back with versions in the startup section, and startup reads them
through these with Rule R, so they are written again with the run's content.
New proofs `lean/SIS/Proof/CutRestart.lean`, `CutHist.lean`,
`CutHistRead.lean`, `CutRuns.lean`; `step_closed` needs only D closed upward
(`DClosed`), not A6'. T12 with eviction follows T9.

2026-10-17. Bergdb item 001, WP R4: T9 proved (`T9_readCut`,
`lean/SIS/ReclaimTheorems.lean`). In a run with eviction, any cache
schedules and restarts, after a safe cut, a read through the Level 4 loader
in the running process at any time from the first available time on gives
the same on the cut stream as on the whole stream, and gives P at that time.
The proof is the invariant on the slots of register M48's option (a)
(`CInv`, `lean/SIS/Proof/CutPhys.lean` to `CutPhysRun.lean`): a read from f
on follows only canonical objects and versions that `CutOK`'s part 2 covers
(`ReadsPhys`). On R2's medium reclaim set, now checked in full (22,448
transactions, 174 cuts): `CutOK` holds at every cut Java decided, and so
does the diagnostic C-CUT+; C-S fails only in register M17's pattern, which
R8's change 6 fixed.

2026-10-17. Bergdb item 001, WP R8: the performance comparison of changes 1,
3 and 4 (`SUITE=quick java/stress/performance.sh ab l34-base current`, two
matched runs on a quiet machine): no regression. The first run's two alerts
on warm single-thread gets (-5.8 and -6.4 percent) were not confirmed by the
second (-0.8 and +1.9 percent) nor by the comparison of the second
reference with both candidates. Gets with 4 threads +8 to +25 percent;
startup +6 to +8 percent (no threshold). R8 is done. Frans kept R6 part 1b's
refinement of `CutOK` (no second wait in Java's reclaim).

2026-10-17. Bergdb item 001, WP R5: T12 with eviction proved
(`T12_evictCut`, `lean/SIS/ReclaimTheorems.lean`). The run with eviction
that restarts from safe cut streams, with the Level 4 startup at each restart
and any cache schedules whose reads are from the first available time on,
appends the records of the run without restarts, with its D and its lookups
from f on: it has the states of the run without eviction that restarts from
the same cut streams. The proof compares it with the run with eviction that
restarts from the whole streams at the same points (T2-C covers it, with
extra unswizzles of its root's slots before each release): the memories
differ only in a virtual root's object, rebuilt from the root children that
the cut stream still has, and where it is in the list of objects; reads from
f on follow no version before the cut (an invariant on the slots after a
restart, `NInv`). New proofs `lean/SIS/Proof/CutLater.lean` to
`CutLaterRun.lean`. Register M34 closed. R5 is done.

2026-10-18. Bergdb item 001, WP R9 and checkpoint K3: Level 3 conformance on
the current Java. R2's small and medium reclaim sets made again with the
Java of R8's last change and checked by the Lean checker: every trace
`TRACECHECK OK`; every record, D and cut the model's, every cut Java
decided safe (`CutOK`), no failing probe after restarts from the cut stream.
K3's conditions for an automatic pass hold, so K3 passed (by the agent, on
Frans's go of 2026-10-17 19:59), with the recommended option: `level3.sh`
checks conformance with reclaim (its step 8, `conformance.sh reclaim`).
The outcome for Level 3: `level3-alignment.md`, sections 7 and 8.

2026-10-18. Bergdb item 001, WP J1: Java knows what it holds in memory and
what it must keep (`core/Residents.java`: the resident objects and their
bytes; the pins), and a test-only audit checks the model's invariants on
its state (`core/Audit.java`: INV-CAN, the pins, INV-SLOT against an oracle
of latest positions). The audit found that the node table could name a
snapshot (a split's copied slot); fixed. No record changes.

2026-10-18. Bergdb item 001, WPs J2 and J3: eviction of values and of index
nodes at transaction boundaries (`core/Eviction.java`): a memory slot to an
object that is not pinned and has been written becomes a stream slot naming
its position, and an object no resident slot names is released; a later
read loads it again. With every schedule (none, values, every, random) the
records are byte for byte those without eviction (`EvictionInvariance`).

2026-10-18. Bergdb item 001, WP J4: conformance with eviction. The exporter's
run E (a forced eviction schedule) writes SLOT lines, and the checker's C-P
checks INV-SLOT on Java's physical states: `conformance.sh evict`, no
failure.

2026-10-18. Bergdb item 001, WP J5: readers under eviction (the plan's Q8):
eviction under the write lock, each slot under its pointer lock, which a
reader holds for a whole follow; tested step by step and under stress. The
writer's own checks now read a pointer under the node's monitor.

2026-10-18. Bergdb item 001, WP J6: reclaim under eviction. A reclaim step
pins the index nodes it makes dirty; a reserve (4 MiB by default) splits a
step that would pin more. No record changes with the default.

2026-10-18. Bergdb item 001, WP J7: the capacity controller, and eviction on
by default (Frans's decision, Q10). `cacheSizeInMb` is the cache's budget:
when the resident bytes pass it, a sweep evicts the least recently used
objects, values first, down to three quarters of it; pinned state is never
taken. A larger-than-memory run (J8) found that a sweep counted only what it
released, not what left memory with it, and could empty the cache down to
the pinned state; fixed. The gates pass with eviction on.

2026-10-18. Bergdb item 001, WP J8: larger than memory. 20 million keys, an
index of 1.5 GB and 2 GB of values, on disk in a JVM capped at 2 GB with a
budget of 500 MB: load, updates, gets, scans, reclaim, two cold restarts and
every key checked, all right; the live heap at most 646 MB
([level4-evidence.md](../items/001-lean-model-levels-3-4/10-level4-evidence.md)).

2026-10-18. Bergdb item 001, WP J9: `java/stress/level4.sh`, the Level 4
check (eviction invariance with every schedule, stress with eviction and
the audit, conformance with eviction, a larger-than-memory run). It passes,
full and quick.

2026-10-18. Bergdb item 001, WP J10: Level 4 against Level 3's code, the quick
performance suite in matched runs: with eviction off and with a budget
larger than the data, warm gets and scans within 5 percent, commits within
1.2 percent, startup 7 to 10 percent slower, no alert (the plan's Q13
targets); under pressure (a budget of a fifth of the data) reads are 30 to
90 times slower ([level4-performance.md](../items/001-lean-model-levels-3-4/11-level4-performance.md)).

2026-10-18. Bergdb item 001, checkpoint K4: Level 4 in Java accepted (by the
agent, on Frans's go), with eviction on by default and `level4.sh` a
required gate: all four level scripts must pass before a Java change is
committed (`AGENTS.md`, `README.md`).

2026-10-18. Bergdb item 001, WP P4: the Level 3 soak (P2's main run) with
eviction on, an 8 GB heap and a budget of 1.6 GB: `SOAK OK`, two hours,
every read right, the live heap bounded at 1.5 to 1.9 GB (without eviction
it grew to 15 GB). But the paced writer reached 123.5 of its 200 commits a
second: a sweep walks every resident object under the write lock, 35
percent of the time with the readers' loads; and G1 needed 81 full
collections ([level4-evidence.md](../items/001-lean-model-levels-3-4/10-level4-evidence.md)).

2026-10-18. Bergdb item 001, WP F1: the conformance campaign on the final code
and model, all levels: the Level 2 sets (81 traces), the reclaim sets (31
traces, 463 cuts), the eviction set (30 traces, C-P), every trace
`TRACECHECK OK`; the Java tier (68,901 transactions); `EvictionInvariance`
with every schedule (24 runs); the four gates, full, and every record R8's
([../items/001-lean-model-levels-3-4/07-level3-alignment/level34-conformance.txt](../items/001-lean-model-levels-3-4/07-level3-alignment/level34-conformance.txt)).

2026-10-18. Bergdb item 001, WP F2: the documents for Levels 3 and 4: the
outcome of the plan's 1.2 for Level 4 point by point
([level4-alignment.md](../items/001-lean-model-levels-3-4/08-level4-alignment.md), section 8), Level 4 in
[levels.md](../items/011-docs-archive/04-levels.md), the status in `README.md`, `problem.md` (R5, R6,
Q10), [sis-model.md](sis-model.md) (section 15) and `lean/README.md`.

2026-10-18. Bergdb item 001, WP F3: the final report
([../items/001-lean-model-levels-3-4/06-final-report.md](../items/001-lean-model-levels-3-4/06-final-report.md)).
Levels 3 and 4 are in the Lean model, with proofs, and in Java, aligned with
it; eviction is on by default. Open for Frans: closing the item (T-SCHEME is
checked, not proved) and what comes next (the sweep's cost first).

2026-10-19. Bergdb item 001 closed (done): Frans accepted the outcome at
K5, with T-SCHEME checked, not proved (R6).

2026-10-19. `level1.sh` step 6, Props (bergdb item 006-02): MEM, heap bytes
per KV, and SS, stream bytes per user byte, are checked against limits (MEM
at most 228, SS at most 1.51 (1.11, 1.20, 1.63, 2.38): the values of
`11ea2f6` on JDK 27 plus one step); CORE is printed, not checked, in the full
run only. A change that improves MEM or SS lowers the limit; one that needs a
higher limit needs a reason here. Full run 2 min 43 s, quick 75 s, both
`LEVEL 1 OK`, on a scratch copy of `java/`.

2026-10-19. Bergdb 005-02 (register M46; item 002 closed): top node ordinals
are longs below 2^48, in the 48 bits the stream already had for them (bytes
10 to 15 of a top node), of which the reader read 32. No format change: every
record the same (StreamDigest, 36 of 36 R8's). Near the end, a user
transaction is refused before it changes anything, 1,024 below the bound;
reclaim's internal transactions are not. New tests cross 2^30, 2^31, 2^32
and 2^47 with restarts, eviction and reclaim, and reach the end; the
test-only `DbBuilder.secondTopOrdinal` starts the ordinals near a boundary.
The four gates pass, full; `level3.sh` on its second run: the first failed a
test of item 001's eviction that fails on today's code too, now and then (see
005-02).

2026-10-19. Bergdb 005-04 (register M43), Frans's decision: A6 is not a
target; the assumption stays A6', with TREE and A-COPY, as K1 accepted. A
look at the code found one kind of A6 failure only, the in-place split of a
segment root made by the same transaction, which keeps A6'
(level4-alignment.md, section 4). The Java tier's 61 A6 failures, on its 21
configurations and seven larger ones at node sizes 8 to 62, are all that
kind; 21 traces that contain it pass the checker, with eviction too. No
change to `java/` or `lean/`. Not done, proposed in 005-04: TREE, A6' and
A-COPY as gate checks, and A6' as the checker's diagnostic.

2026-10-20. Bergdb 005-10, unused code, as Frans decided: 3,071 lines
removed in 103 files. Deleted: seven files that nothing reached (among
them `NextMap`, `NoReclaim`, `Triplet`, `JavaCollator`), `Cache2` (the cache
of 2012 to 2017, replaced by `Cache3`), `DagChecksum` and the unregistered
`Concurrency` test. Removed: 165 unused methods, fields and nested classes
in files that stay, 20 unused Lean lemmas, three unit tests that never ran
(one failed on today's code), and eight class methods of the Pub API that
nothing called (`Duration.add`, `days`, `hours`, `minutes`;
`Time.substract`, `getDate`; `Factory.printHello`; `CryptoKey.main`).
`DbDouble`'s two unit tests, never registered, now run. New:
`java/stress/night.sh`, the night tests (2013 to 2015), not a gate. Unit
tests 948 to 942, f-tests 37 to 36; the four gates, `lake build` and
`night.sh` pass. The rest of the Pub API that nothing in the repository
calls waits for Frans (005-10).

2026-10-20. Bergdb 005-04's follow-up: TREE, A6' and A-COPY, the model's
assumptions of stage 2, are gate checks. `A2A3Check2` reports them as
assumptions, each with its failures, and A6's failures, the adoptions below
the old parent, as information; `level2.sh` step 7 requires them. The
checker's C-A checks them (`EvictRunOK`, R(0) included), with A6' (the new
`adoptFailures`) in place of the diagnostic A6, and counts the adoptions
below the old parent; a new test trace, `adopt2.trace`, has one from outside
the old parent's subtree, which fails A6'. conformance.sh's small and evict
sets have a configuration with A6's kind, `a6` and `e-a6`; a trace of them
without it fails. The four gates pass, full, on `0597329` with the change
and on `c6ca623`, where Frans committed it with 005-10's removal.

2026-10-20. Bergdb 005-10, the end: the Pub API's
`Database.getFirstAvailableLookupTime` returned the current time, not the
first available lookup time (since the 2017 source; nothing called it). It
returns the core's now, with two unit tests in `PubTester`. Removed, as
Frans decided: `Connection.put(Object)` (the demo `GetStarted4` uses
`put(key, object)` instead), the repeated `RwEnvironment.exists`, and
`NoFieldsSetException`, which nothing threw; `Connection.get`'s Javadoc
says that it returns null for a missing key. Replication and transaction
outputs wait for 005-11 and 005-12. Unit tests 944, f-tests 36; the four
gates and `lake build` pass.

2026-10-20. The night tests run with `java/night.sh` (Frans's, beside
`unit.sh`, `f.sh` and `perf.sh`); 005-10's `java/stress/night.sh` is
removed, at Frans's request.

2026-10-20. Bergdb 006-03, fast unit tests: the unit tests from 41.5 s to
10 s (942 tests to 933 on today's code), each changed one under 100 ms warm.
The slow ones waited for the storage thread: a sync waits for
`BufferedStream`'s poll, and after a storage failure for `StorageManager`'s
500 ms poll, as nothing wakes it; or they ran fixed windows or much work.
Seven Eviction twin cases, two reader tests, two CapacityTester tests and
`testCutIsMadeAfterDecisionIsDurable` have a small unit test and the full
version as an f-test (name ending in F); eleven tests moved to the f-tests.
The Java of BergDB is unchanged. `level3.sh quick` and `level4.sh` run the
f-tests of their classes. New `java/before-commit.sh`: the unit and f-tests
in parallel, about 2 minutes, now the only requirement before a commit; the
level scripts are deeper checks. The four level scripts pass, full, with the
change on `39ab4a8`; `before-commit.sh` on `9d909cc`.

2026-10-20. Bergdb 006-03: the night run. `java/night.sh` runs, on a clone
of HEAD, `before-commit.sh`, the four level scripts (full), the night tests
and `conformance.sh medium`, and writes a report to `java/build/night/`;
launchd starts it at 02:00. `night.sh large` adds `conformance.sh large`
(about 5 hours more) and is started by hand; `night.sh tests` runs only the
night tests, as `night.sh` did before.

2026-10-20. Bergdb 005-13, the buffer time: the default of the main
stream is 20 ms, was 100 ms (2012, for rotating drives). A sweep of 10 to
200 ms on F53 (SSD, `F_FULLFSYNC`): a sync after each commit waits for the
timer, about the buffer time plus 20 to 50 percent, so one syncing thread
gets 29 commits a second instead of 8, and 64 threads 1,800 instead of 530;
writers that do not sync are as fast from 10 to 100 ms (260,000 puts a
second with 100-byte values, 100,000 with 1 KB). One `F_FULLFSYNC` costs
about 5 ms. At 200 ms bulk writes lose a third, as the consumer wakes only
on its timer. `Perf` has `bufftime=` and counts the forces; the suite is
`java/stress/performance-bufftime.suite`.

2026-10-20. Bergdb 005-09, the race of a reader's entry and a release
(register M31): a reader that follows a stream pointer to a canonical
object enters it in the node table (`Cache3.pointerCreated`); it read the
canonical flag before it took the table's lock, so a sweep's release in
between left the released object in the table, a snapshot, and the audit
failed (INV-CAN). Records and reads were not affected. Now the flag is read
again under the lock, and `Cache3.released` clears it under the same lock.
New test `EvictionReaderTester.testReleaseBeforeTheTableEntry`, which fails
without the fix; `testReaderPausedInsideAFollow`'s f-test under load failed
1 in 2,000 runs before, 0 in 2,000 after. StreamDigest identical to R8's;
Props and `performance.sh`'s quick suite unchanged; `before-commit.sh` and
`level4.sh quick` pass.

2026-10-21. Bergdb 005-14, calm when idle: an idle database's storage
thread woke every bufferTime / 4, 160 times a second at 20 ms (0.3 percent
of a core, 0.14 mW on F53, against the JVM's own 25 wakes). Now
`BufferedStream`'s consumer waits without a timeout when nothing has been
buffered for a buffer time, and an append, `stop()` or `close()` wakes it:
an idle database wakes as often as the JVM alone, at any buffer time; no
change under load. Two faults fixed with it: the wake count overflowed
after 2^31 wakes without a write (about half a year at 20 ms), after which
the timer stopped flushing; and a close could flush 0 bytes, which
appended the whole ring buffer, so that the database failed to start (34
of 24,000 closes in a test). Unit tests in `BufferedStream`;
`before-commit.sh` passes.

2026-10-21. 005-15 done, by Claude (Opus 5.5, Claude Code): a long index
scan's start key (`UseIndexBuilderImp.plusOne`) kept the `0xff` bytes it
carried past, so a scan after a value whose low byte is `0xff` (255, -1)
skipped or added entries: `startAt(255).inclusive(false)` missed 256 to
510. Now they become 0. Two tests; `before-commit.sh` passes.

2026-10-21. 005-16 done, by Claude (Opus 5.5, Claude Code):
`MemoryStream`'s first position was a product of two `int`s and went
negative after a cut past 2^31 bytes, so an in-memory database with a
retain duration treated a read below the cut as a storage failure and
stopped taking transactions. Now in `long`; an f-test; `before-commit.sh`
passes.

2026-10-21. 005-17 done, by Claude (Opus 5.5, Claude Code): a transaction of
1.79 GB or more was half committed and blocked the writer, since the
record's size was added up in an `int` after the go point. Now a
transaction whose value nodes pass 7/8 of the record limit (2^31 − 9
bytes) is refused before it changes anything, `TransSeq.take` keeps the
index nodes within the limit, and the serializer computes in `long`. Four
tests; streams unchanged (StreamDigest), Props unchanged;
`before-commit.sh` passes.

2026-10-21. 005-18 done, by Claude (Opus 5.5, Claude Code): a clock time of
2^56 or more (a clock in nanoseconds, say) was taken, and the database
then could not start again ("Time too large"). Now `DbClock` refuses it
with a `DbException` before the transaction begins. Two tests; streams
unchanged; `before-commit.sh` passes.

2026-10-21. 005-19 done, by Claude (Opus 5.5, Claude Code): `FileStream`
parsed its file names as `int`s, so a stream past 214.7 TB of positions
could not be opened again. Now `long`; a test; `before-commit.sh` passes.

2026-10-21. 005-20 done, by Claude (Opus 5.5, Claude Code): Jmx's
`setRetainDurationInDays` computed in `int`, so 99,999 days set a retention
of 578.5 days. Now in `long`; a test; `before-commit.sh` passes.

2026-10-21. 005-21 done, by Claude (Opus 5.5, Claude Code): smaller
overflows fixed: `Time.millis` (unchecked product), `TimeResolver`
(seconds cast to `int`, NaN), `TransSeq.take`'s node count limit, negative
key hashes (`Keys.hash` for `Long.MIN_VALUE`, `KeyModSet`'s index,
`Trans.Builder`), a `DbObject` field name over 32,767 UTF-8 bytes, and
corrupt counts that gave `NegativeArraySizeException`. Seven tests;
streams unchanged; `before-commit.sh` passes.

2026-10-21. 005-22 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: reading an object into its class, a stored value that does not fit
its Java field (a long of 3,000,000,000 into an `int`, a NaN into a `long`)
was cast silently; now it is a `DataFormatException` that names the field.
Two tests; `before-commit.sh` passes.

2026-10-21. 005-23 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: a put of an object with a reference cycle, or nested 20,000 deep,
threw `StackOverflowError`. Now `DbObject.toDbObject` refuses a cycle, and
nesting deeper than 1,000 objects, with an `IllegalArgumentException` that
names the field path. Three tests, one changed; `before-commit.sh` passes.

2026-10-21. 005-24 done, by Claude (Opus 5.5, Claude Code): a `FileStream`
read at the end of the stream looped forever, since a bound check compared
`spos` with `spos + fileLength`; one past it threw
`IndexOutOfBoundsException`. Now both throw `EOFException` and the stream
stays usable. A test; `before-commit.sh` passes.

2026-10-21. 005-25 done, by Claude (Opus 5.5, Claude Code):
`BufferedStream.read` let a read end one byte past the end of the stream,
and gave a stale byte of the ring buffer; now it throws. A test;
`before-commit.sh` passes.

2026-10-21. 005-26 done, by Claude (Opus 5.5, Claude Code):
`StringUtil.utf8Size` counted a lone surrogate as 3 or 4 bytes, where the
encoder writes 1, so an object with such a string in an array could not be
stored ("Bad type"). Now it counts as the encoder writes. Tests;
`before-commit.sh` passes. With it, 005-15 to 005-26, the findings of the
review of the Java code for overflow, are done.

2026-10-22. 005-01 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: a transaction that threw after its go point was half committed
(M49): its time became readable with its first puts, and the next
transaction wrote its nodes as its own. Now a `Throwable` after the go
point in `Db.executeInner` fails the database: the call gets a
`DbFailedException` with the cause (an `Error` is thrown as it is), the
time of a transaction whose puts threw never becomes a lookup time, and
every later transaction and read is refused until a restart, which
rebuilds the state from the stream. The state is checked again under the
write lock. No rollback; transformations stay where they are and must not
throw. No model change ([levels.md](../items/011-docs-archive/04-levels.md), "A transaction that
fails"). Seven tests; streams unchanged (StreamDigest); `before-commit.sh`
and the four gates pass.

2026-10-23. 005-28 done, by Claude (Opus 5.5, Claude Code): startup looped
for ever when the transaction at its start position was a failed one,
zero-filled by recovery: in a stream that mixes two histories (005-11, P9),
and after a crash in a new database's first transaction.
`NodeStream.TransIterator` went back to that position and read the same
transaction again. Now a failed transaction at an exact start position
throws a `StreamFormatException` that names it, and the iterator from the
last transaction before a position steps on. Three tests;
`before-commit.sh` passes.

2026-10-23. Bergdb item 007, bounds, by Claude (Opus 5.5, Claude Code), at
Frans's request. T3 in Lean (`lean/SIS/Bound.lean`, `BoundTheorems.lean`):
with any cost of a record, and a startup pos policy that keeps up with a
startup distance d, the startup section without its last record costs less
than d after every run, also with restarts; no other assumption. BergDB's
take does not keep up (its node limit); 007-02, found with a probe: a
transaction whose dirty nodes do not fit in one record stops the startup
pos for good. `lake build` passes.

2026-10-23. 005-29 done, by Claude (Opus 5.5, Claude Code):
`MemoryStream.assertOk` expected one array too many for an empty stream
and at a length that is a multiple of 1,000,000 bytes, so `copy()`, which
the crash and reclaim tests use through `CutStream`, failed its assertion
under `-ea`. Now `assertOk`, `truncate` and an append of 0 bytes agree:
the arrays are exactly those that hold bytes. A test; `before-commit.sh`
passes.

2026-10-23. 005-27 done, by Claude (Opus 5.5, Claude Code): a crash that
ended the stream exactly at a meta block's position, after a transaction
that ended there, left a database that did not start ("spos >=
streamSize"). The transaction's bytes and the meta block are two appends,
and a flush can come between them; recovery filled out a meta block that
was partly written, not one that had not begun, and then stepped past it.
Now `RecoverableStream.fixMetaBlockIfNeeded` fills out that block too; it
is invalid, and recovery takes the one before it. Two unit tests;
`CrashTest` also cuts at and next to meta block positions, and at the end
of each transaction that ends at one. Streams unchanged (StreamDigest);
`before-commit.sh` and the four gates pass.

2026-10-23. 005-30 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: a read that failed on the storage (an I/O error, corrupt data)
threw, and the database stayed active, half dead, as the storage below
refuses all I/O after an I/O error. Now such a read (`Db.getOne`,
`getMany`, the warm-up of a transaction, `getTrans`), and a sync that
fails, fail the database as a transaction does since 005-01
([levels.md](../items/011-docs-archive/04-levels.md), "A transaction or a read that fails"). A read
that a cut has overtaken still expires; a read while the database stops,
and an interrupted sync, throw as before. Ten tests; streams unchanged
(StreamDigest); `before-commit.sh`, `level3.sh` and `level4.sh` pass. Found
on the way, 005-34: `Connection.transactionInfo()` reads at a wrong
position for a value after a meta block in its record.

2026-10-24. 005-36 done, by Claude (Opus 5.5, Claude Code):
`DbTester.testCrash3` truncated a copy of its stream and started on the
original, so it had tested no truncation since 2017. Now it syncs the new
database before it takes its first length, and starts on each truncated
copy; its cuts come after the creation (a cut in the creation is 005-33's
case). Test code only; `before-commit.sh` passes.

2026-10-24. 005-37 done, by Claude (Opus 5.5, Claude Code): `MemoryStream`,
the in-memory stream of the tests and of `DatabaseBuilder.memory()`, took
a negative length to `append` and a `pretruncate` past its length, where
`AppendOnlyStream` says otherwise; after some of them it took no more
appends. Now it refuses both with an `IllegalArgumentException`, as
`FileStream` refuses such a cut, and the Javadoc of
`AppendOnlyStream.pretruncate` says what the streams do. A test;
`before-commit.sh` passes.

2026-10-24. 005-34 done, by Claude (Opus 5.5, Claude Code): a get gave a
transaction position 128 bytes too far for a value after a meta block in
its record, as the value node's offset counted the record's bytes, without
the meta block; and, after a restart, a value that startup had rerun gave
its own position. `Connection.transactionInfo()` read the middle of a
record there. Now the value node keeps the distance in the stream (the
stored field is unchanged), the rerun copies it, `getTrans` refuses a
position that cannot start a transaction, and a format error there fails
the database, as in the other reads ([levels.md](../items/011-docs-archive/04-levels.md), "A
transaction or a read that fails"). Tests; streams unchanged
(StreamDigest); `before-commit.sh` passes.

2026-10-24. 005-32 done, by Claude (Opus 5.5, Claude Code): a start that
threw left its storage running, its threads and open files, until the
garbage collector finalized the `Db`, and its threads then wrote what the
start had appended, also into a database started after it on the same
files; `BufferedStream.close()` waited for ever after a failed flush, and
an `Error` in a flush ended the storage thread without a word, so syncs
waited for ever. Now `Db.start` closes the storage when the start throws
(what it appended is written, the streams are closed and their threads
have ended) and stops the database; the Pub API closes the `Db`, or the
builder's streams, on a failure after or before the `Db` is built;
`BufferedStream.close()` waits for its thread and throws the failure; any
failure of a flush stops the stream and tells the listener. Tests;
`before-commit.sh` passes.

2026-10-24. 005-35 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: `Db.stop()` dropped what was still in the write buffer (all of a
quick run's transactions, unless a sync came first), `close()` returned at
once after `stop()` or beside another `close()`, and a writer that waited
for room in the buffer waited for ever when the stream stopped or failed,
so a failing disk hung the database. Now `stop()` starts one close, in a
thread of its own that is not a daemon, and returns at once; `close()`
runs or waits for the same close. The close takes the write lock, so a
transaction that runs completes and is written, then writes what is
buffered, closes the streams and ends their threads; a program that
returns from `main` after `stop()` keeps all its transactions. A waiting
writer gets an `IOException` when the stream stops or fails. The Pub API's
`Database.stop()` does the same; it has no `close()`. Tests;
`before-commit.sh` and the four level scripts pass.

2026-10-24. 005-31 done, by Claude (Opus 5.5, Claude Code), option A as
Frans decided: a transaction whose index nodes did not fit in one record
was never taken by `TransSeq.take`, which takes transactions whole, so the
startup pos stayed before it for good (007-02). Now `Db.checkDirtyNodes`
refuses such a transaction before its go point, under the write lock: a
cheap test from its keys, then, for a large transaction, a bound from a
walk of the paths of its keys (`Dag.dirtyNodeBound`: the distinct key
nodes on them, the splits from each node's room, new segment trees), each
node at the largest size, against 15/16 of the record limit
([levels.md](../items/011-docs-archive/04-levels.md), Level 2, "Bounds, one transaction"). Streams
unchanged (StreamDigest); a test; `before-commit.sh` passes.

2026-10-25. 005-39 done, by Claude (Opus 5.5, Claude Code), from the TODO
under the Javadoc of `RecoverableStream.getPosOfTransCompletedBefore`,
where the iterators that do not start at an exact position start. The
Javadoc promised the last transaction completed before the position;
the method gives the one that the last meta block before it names, up
to 200,000 bytes earlier. In a stream whose front is cut, it threw
`NullPointerException` for a position before the first meta block after
the cut, and could give a transaction before the cut for one after it,
so `NodeStream.createTransIterator` and `print()` failed on a database
that reclaim had cut. Startup does not use it. Now the Javadoc says what
the method gives, and in a cut stream it gives the first transaction
after the cut that a meta block names. Tests; `before-commit.sh`
passes.

2026-10-25. 005-40 done, by Claude (Opus 5.5, Claude Code), at Frans's
request, from the TODO in `DbStarter.validateTransactions` that asked for
a check of the stream format version. The parsers have made that check
since 2015; what was wrong was the order of recovery, which wrote to the
stream before it checked it. After a crash that ended the stream at or
just inside a meta block, a start with a wrong crypto key, or with none,
filled out that meta block through the key, and the right key could then
not start the database either. Now `RecoverableStream.recover()` reads the
meta blocks first, and a stream whose key or version it cannot read is
refused as it is ([levels.md](../items/011-docs-archive/04-levels.md), "Bugs found by the load and
crash tests", 8). The versions of records and nodes are refused with a
`VersioningStreamException` (now a `StreamFormatException`), whose
message says whether an older or a newer BergDB wrote the stream; a newer
format got the message of format 2 before. The rule for the next format
change is in the Javadoc of `MetaBlock` and `StoredTrans.RECORD_FORMAT`.
`StoredTrans.CURRENT_FORMAT_VERSION`, never the stored byte, is gone, and
`RecoverableStream` no longer refers to `bergdb.core`. Streams unchanged
(StreamDigest); tests; `before-commit.sh` and `level2.sh` pass.

2026-10-25. The TODO markers in `java/` reviewed, at Frans's request, by
Claude (Opus 5.5, Claude Code): 15, of 2013 to 2017, but two of 2026-10-13
(bergdb 006-05). Seven are gone from the code: five that were obsolete or
done, among them the startup distance test's 3.0e6 that "result in
problems" (an assertion removed in 2015, found by a bisect in F1-007's
history), and the two of Frans's `isDurable()`, now 005-41. One is a NOTE.
One points to 005-42: `Connection.transactionInfo()` gives internal KVs
whose `key()` throws, and for a value that reclaim has rewritten,
reclaim's transaction. 005-43 fixes two: `Db.getTrans` refuses a position
at or past the end of the stream with an `IllegalArgumentException` (it
was a `DbException`), and the Pub API's `IndexBuilder.dir` and
`UsePrimaryBuilder.dir` refuse a bad directory with one (it was a
`BadFormatException`). Three were done in 005-39 and 005-40; the one in
`TransSeq.take` waits for 007-03's step 3. Two tests; `before-commit.sh`
passes.

2026-10-25. 005-44 done, by Claude (Opus 5.5, Claude Code), found in
005-41: a sync waited until the durable length reached the position of
the transaction's last byte, its commit byte, so it returned while that
byte could still be in the write buffer. It was right only while the
buffer wrote in parts that end at even positions, as with the Pub API's
buffer sizes, multiples of 4; with a buffer of 2 S − 2 bytes, for a
record of S bytes, a crash right after the sync lost the transaction in
10 runs of 10 of a probe. Now `Db.sync` waits until that byte is durable
too, and `Db` keeps the end of the last transaction
(`endOfLastTrans`), not its last byte ([levels.md](../items/011-docs-archive/04-levels.md), "Bugs found
by the load and crash tests", 9). An f-test that fails without the fix;
`before-commit.sh` passes. 005-41 itself is decided: no
`isDurable()` for now (Frans).

2026-10-25. 005-33 done, by Claude (Opus 5.5, Claude Code), option A as
Frans decided: a database whose creation did not complete, as after a
power loss in the first write of its stream, never started: one of three
`StreamFormatException`s that did not say why ("Cannot recover stream
without complete first meta block", "No transactions in startup
transaction set.", "Transaction at start pos 128 is not committed"), after
recovery had zero-filled a cut first transaction. Now `Db.startInner`
refuses such a stream before recovery, with a `DatabaseNotCreatedException`
(in `bergdb.pub.util`, for the application to catch) that says what
happened and what to do (remove the files, start again), and it writes
nothing. `RecoverableStream.isIncompleteCreation` recognizes it, and only
in a stream no longer than a creation, 264 bytes, which holds no data
whatever its first transaction's size field says. Without a crypto key, a
`BadCryptoKey` for bad magic bytes no longer says that the wrong key was
used. Tests; `before-commit.sh` and `level2.sh quick` pass. Found on the
way, for 005-11: with a replica, a stream that ends inside its first meta
block fails the start earlier, in the check of the streams' IDs.

2026-10-25. Before release 2026.1 (bergdb 008), the known faults that were
left, at Frans's request ("Are there any known bugs in BergDB? If so, we
should fix them before the release."), by Claude (Opus 5.5, Claude Code).
005-42 done, A1 and B2 as Frans decided: `Connection.transactionInfo()`
also gave the KVs under the internal prefix, an index's entries, whose
`key()` threw, and for a value that reclaim had rewritten it described
reclaim's step, with its time and its row. Now it gives the user's KVs
only, and throws `LookupTimeNotAvailableException` for a value that
reclaim has rewritten. 005-45, two faults found on the way in 005-40 and
005-41: `SalsaStream.getLength()` did not count what it appended, and
`WTransaction.sync(SyncLevel)` waited for the database's last transaction,
not for its own. Replication is kept as it is for the release, documented
as experimental in the Javadoc of the Pub API's replica methods, README.md
and levels.md (005-11), and the deadline in `TransSeq.take` comes after the
release (007-03), which README.md and levels.md say too. Tests that fail
without the changes; `before-commit.sh` passes.

2026-10-25. Release 2026.1, internal, by Claude (Opus 5.5, Claude Code) at
Frans's request, as planned in item 008: the tag `release-2026.1` on
`a42947c`, where `BuildInfo` says 2026.1 (it said 2017.1). The night run
passed on it, and the tests again on the jar itself. `releases/2026.1/`
holds the jar, the source, the release notes with the baseline before
handles (Props: MEM 191, CORE 0.29, SS 1.50; the quick suite; ScaleBench at
10M keys on F53 with G1 and ZGC, and on s1 from the disk), and the outputs
of the runs. After the tag, `BuildInfo` says 2026.2-dev.

2026-10-26. Handles (bergdb item 009), merged into `main` (`178a0d4`), by Claude
(Opus 5.5, Claude Code) in Frans's unattended run ("I want you to work on the
009 implementation until completion."). A memory pointer of a key node or a
top node holds its pointee's handle, the handle the node's one object;
eviction kills a handle, with nothing to find, in batches of CLOCK steps
bounded to 2 ms; readers follow pointers without a lock, with the barriers
of 009-02, section 3.4, tested by jcstress; the pointer locks, the stamp,
the readers' `readSync` monitor and the sweep are gone; the build is
`--release 17`. Records unchanged: StreamDigest gives 2026.1's digests after
every step. Lean: T-CACHE, T-READ, T2-C and T-PIN over handles proved
(`tc_handles`, `tr_handles`, `t2_handles`, `tr_handles_restarts`,
`tp_handles`; docs/handles-alignment.md maps Java to the model). Against
2026.1 (items/009-handles/03-measurements.md): with ZGC on F53 the longest
get from the OS cache at 10M keys 3.45 ms (7.3 s); gets in memory on one
thread 3 and 11 percent fewer (G1, ZGC), with 8 threads 101 and 61 percent
more; MEM 130 bytes per KV (191); the 10M load on s1 with a 600 MB budget
767 s (3,015 s). Found on the way: 005-46, a reader's read of the stream's
last file waits for the writer's `fsync`. docs/levels.md's Level 4 and
docs/handles-alignment.md describe it.

2026-10-26. `docs/` cleaned up, at Frans's request (006-07), by Claude (Opus
5.5, Claude Code). `docs/` keeps what is kept up to date with the code:
`levels.md`, rewritten from 1,805 lines to 390 (the current state, level by
level, with the evidence by item ID), `sis-model.md`, `trace-format.md` (new:
section 9 of the Level 2 alignment), this log and `sources/`;
[readme.md](readme.md) says where the other documents went. Those written in
an item went to it (001-07 to 001-11, 009-05); those that no item owns went
to the new item 011-docs-archive (011-01 to 011-11), with `levels.md` as it
was until today as 011-04, and `lean/References/` beside 011-08. The code and
the items cite documents by ID now (`bergdb 001-08, section 5.5`), and every
link to a moved file is fixed. The open questions of the problem statement
that had no home are 005-54.

2026-10-27. 005-50 done, by Claude (Opus 5.5, Claude Code), at Frans's
request. A database starts only with the maximum node size it was written
with (`DbBuilder.maxNodeSize8()` to `62()`; 30 by default, and always in
the Pub API), and the size was not in the stream: a start with another
size failed with what looked like a corrupt stream ("startup error, node
... not found"), or it started, and could then leave a stream that no
start opened, with either size (005-50's `MixedNodeSize`: written with
62, started with 8, 14 or 30). Now the size is in every meta block, two
bytes at offset 44 that were reserved, so the meta block's version stays
154 and release 2026.1 still starts a new database. A start reads it with
the last valid meta block, before recovery writes, and refuses another
size with a `StreamFormatException` that names both sizes and what to do,
and a meta block without a size, as every database written before has,
with a `VersioningStreamException`. Records unchanged (StreamDigest with
its new `metamask=44:2`); tests; `before-commit.sh` and `level2.sh quick`
pass.

2026-10-27. 005-46 done in the code, by Claude (Opus 5.5, Claude Code), at
Frans's request: no read waits for the stream's writer. A read of
`FileStream` takes no lock: positional reads (`pread`) on a read channel of
the file's own, and a list of files that the writer replaces, never
changes. Before, a read of the last file waited for the writer's append and
its force (seconds on s1's disk, the longest waits left there with handles,
009-03), and every read for a new file's forces and a physical cut's
deletes (up to 171 ms in P4's soak, 009-04). A new file is made outside the
stream's monitor; a cut only takes its files off the list, and a thread of
its own deletes them in the same order as before, a directory force after
each; a failed delete fails the stream at its next operation (Frans).
`SalsaStream` reads before its lock, so an encrypted database's reads no
longer wait for each other. And interrupts, by Frans's rule A: none fails
the database or hangs it; `sync()`, a job's `join()` and the Pub API's
wait before a rerun end on one, every other call ignores it, and the
thread's interrupt flag is kept. Before, an interrupt failed the database
in a commit that made a cut or waited for room in the write buffer, hung it
when it reached the storage thread, made `close()` return before the
storage was closed, a new `FileStream` throw, and a job's `join()` throw an
`Error`. The test reports (`PauseProbe`, `Soak`) give the writer's waits
for room in the write buffer and the disk's forces; such waits are the
disk's and do not count against item 009's pause target (Frans). Tests,
`InterruptStress` (level 3); `before-commit.sh`, `level3.sh` full and
`flush-order.sh` pass. The measurements on s1 and P4's soak are still to
run.

2026-10-27. 005-55 done, by Claude (Opus 5.5, Claude Code), at Frans's
request, after his decision ("I think no safety net is reasonable. [...]
Calling close() is a reasonable requirement. And the database is
crash-tolerant anyways."): `Db.finalize()` is gone, with nothing in its
place. `stop()` or `close()` is required, as `Db`'s class Javadoc and
`Database.stop()`'s now say; a database that is not stopped keeps its
storage threads, open files and memory until the JVM exits, and what it
has committed is still written within the buffer time. The 188 unit and
f-tests that left a database running stop it, and so do two night tests
and two stress programs (`RestartStress`, `ReclaimStress`), which without
`finalize()` ran out of memory. `bergdb.dev.Unit`, `F` and `Night` fail
when a test leaves a database running
(`NanotestForBergDB.checkDatabasesStopped()`, a last test
`databasesStopped`). `ValueNodeTotalMem` deleted, `Class.newInstance()`
replaced: `build.sh` prints no note of deprecated API. `before-commit.sh`
(1,040 unit tests, 73 f-tests) and `level1.sh` pass.

2026-10-27. 005-57 done, part 1, by Claude (Opus 5.5, Claude Code), at
Frans's request: rule 4 reads nothing from the stream. Rule 4
(`DbStarter.linkD`, `NodeCollection.linkToCanonical`) gives each stream
pointer of D's nodes the handle of its node's canonical object, if it has
one; it used to read the header at the pointer's position to learn the
node's id, one random read a pointer: 864,000 and 1.25 million reads at
10M keys and startup distances of 50 and 200 MB, about 197 s of a cold
start of 214 s on s1 (007-05). It now finds the node by the position: a
vpos is the id; the startup section's `posToId` gives the ids of the
section's versions and of the version before each key node version there;
the canonical objects give their own positions. A pointer in neither names
no node with a canonical object, by the argument of the old reconciliation
(Frans: a node that stays dirty is written at least once every startup
section; 005-57's report, section 2). A top node's pointer that neither
resolves reads the header, as before (top node versions have no
`prevPos`). With assertions on, every startup also runs rule 4 by node id
and fails on a difference. In the prototype, a cold start on s1 at 10M
keys took about 46 and 51 s at 50 and 200 MB. Not done: the writer's reads
of the same headers (part 2) and the rerun's loads. Tests;
`before-commit.sh`, `level2.sh` (full, and quick on the tree committed on)
and `level4.sh quick` pass.

2026-10-27. 005-51 done, by Claude (Opus 5.5, Claude Code), at Frans's
request (006-09, W4): the eviction thread wakes only for the calls. Idle,
it waits with no timeout; it woke once a second to see whether the
database had stopped, against 010-P3. The database's close wakes it
(`Eviction.endThread`, from `Db.closeStorage`), and `close()` returns
after it has ended, also after `stop()`. A unit test,
`Eviction.testEvictionThreadIdleUntilClose`, fails on the code before.
`before-commit.sh` (1,044 unit tests, 73 f-tests) and `level4.sh` (full)
pass.

2026-10-27. 005-58 done, by Claude (Opus 5.5, Claude Code), at Frans's
request (006-09, W3; reviewed and finished at max effort): Java's rule 4
by position (005-57) is in the Lean model, as new trusted definitions in
`SIS/Handle.lean` (`inPosToId`, `HMem.byPos`, `HMem.linkDPos`,
`handleStartupPos`, `runHandlesPos`), and proved to link what rule 4 by
node id links: `Rule4_positions`, `Rule4Pos_handles` and `RunPos_handles`
(`SIS/HandleTheorems.lean`, proofs in `SIS/Proof/HandleLinkPos.lean`), with
no new assumption; the proof adds two facts to E5's rerun invariant. On the
model's example runs every pointer that rule 4 links is at its canonical
object's position: the model's startup links by node id where Java can
only use `posToId`, so those branches are covered by the theorem but not
exercised in the model; the check under assertions in `linkToCanonical`
compares the two rules on Java's own states (005-58, Outcome). `lake
build` clean (163 jobs), `test-traces/run.sh` OK, axioms standard
(`7c1ce2f`).

2026-10-27. 005-48, group commit, in the code, by Claude (Opus 5.5, Claude
Code), as Frans decided (006-09, W5, reviewed at max effort): a sync that
waits starts the flush (`BufferedStream.flushSoon`, called by
`StorageManager.sync` and `syncStrong` before they wait), instead of
waiting for the buffer time's timer; transactions that arrive during a
force go out together in the next flush. No new thread, timer or setting
(010-P3, P10); the stream's bytes unchanged (StreamDigest, with and without
syncs). On s1, 20 ms buffer time: durable commits a second 38 to 213 with
one thread, 2,364 to 6,429 with 64; the sync's median 24.8 to 3.8 ms.
`ReclaimReaders.awaitModel` reads `lastCompleted` again before it fails:
a race in the check, seen with and without the change. Tests;
`before-commit.sh` and `level3.sh` (full) pass. F53's runs tonight.

2026-10-27. 005-61 done, by Claude (Opus 5.5, Claude Code), at Frans's
request (006-09): Reclaim spaces its iterations by the database's live
startup distance (`db.getStartupDistance()` in `transactionCompleted`). It
used a copy of the builder's, made before `start()` read the stream's and
blind to `setStartupDistance`, so a database opened with another distance
than its own reclaimed too seldom or too often (005-53, question 3; no
wrong cut: the cuts check the live positions). Two unit tests that fail on
the code before; StreamDigest identical; `before-commit.sh` and `level3.sh`
(full) pass.

2026-10-27. 005-59 done, by Claude (Opus 5.5, Claude Code), as Frans
decided (option A, 006-09): `Db` and `Database` implement `AutoCloseable`;
`Database` has a `close()` that waits until the database is closed, as
`Db.close()` does, so try-with-resources closes it, also when the block
throws; `close()` is safe after `stop()`, twice and from several threads.
Two tests each in `DbTester` and `PubTester`; a line in `releases/next.md`;
`before-commit.sh` passes.

2026-10-27. level2.sh's step 6, `BryanRepro`, failed on `main` from
`eaec93e` (005-46) on, found and fixed by Claude (Opus 5.5, Claude Code) in
006-09: each cycle ended with `stop()` and the next started a database on
the same directory at once, while the old one's `FileStream-cut` thread
still deleted the files of a cut; the new database took them as its own,
cut them again at start, and failed when a delete found the file gone. No
data at risk (all below the durable cut). The test now ends each cycle
with `close()` (`b0661ba`); `level2.sh` full passes. The API question is
005-63.

2026-10-27. 005-62, by Claude (Opus 5.5, Claude Code, at max effort), at
Frans's request (006-09): Level 3's reclaim theorems with eviction over
handles' runs, `T9_handles` (a read through the handles from the first
available time on gives the same on a safely cut stream, and gives P) and
`T12_handles` (the run that restarts from safe cut streams appends the
records of the run without restarts, with its D and lookups), in the new
trusted file `SIS/HandleReclaimTheorems.lean`, proved (`bba91dd` to
`a506b34`); T12's proofs are 3,364 lines, against 8,100 over Evict.lean.
Reviewed independently: the statements are the old ones with the handle
model in place of Evict.lean's, hypothesis for hypothesis. `lake build`
clean (173 jobs), trace tests OK, axioms standard. The design before
handles can now be removed; how far is for Frans.

2026-10-28. 005-63 done, by Claude (Opus 5.5, Claude Code), as Frans
decided (option C): one database per directory. `FileStream` holds an
operating-system lock on a file of its own in the directory,
`bergdb.lock` (on one byte far beyond its end, so the file's text stays
readable on Windows), from before it reads the directory until its
`close()` has ended. A second `FileStream` on the directory, in the JVM or
in another process, is refused at once with the new
`DirectoryInUseException`, and so is a database started right after
`stop()` while the first still closes (`BryanRepro`'s case, 006-09). A
crash leaves no lock. Within the JVM a set of the locked directories
refuses first: closing a refused channel of the file released the first
stream's lock for other processes (POSIX record locks; seen on macOS), a
deviation from 010-P9 that Frans chose. `stop()`'s Javadoc says to start
again after `close()`; `FileStream`'s says what holds on network file
systems. Tests in `FileStream`, one across processes, and in `PubTester`;
six tests and stress programs that restarted right after `stop()` now call
`close()`; a line in `releases/next.md`. `before-commit.sh`, `level3.sh`,
`level2.sh` and `level4.sh quick` pass.

2026-10-28. 005-48 closed by Frans, with the buffer time kept at 20 ms:
group commit is in `main` since 2026-10-27 (`e611709`). Now that a sync
no longer waits for the timer, whether 50 or 100 ms is better is a new
entry, 005-64 (fewer forces and wake-ups for writers that do not sync,
against more unsynced data lost on a power loss).

2026-10-28. 005-56 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: the packages of `java/src` use only what their `package.html`
lists, and `java/before-commit.sh` checks it with `java/deps.py`. The
lists are in one form, `Depends on: a, b, c.`; `pub`'s now has `common`,
`nanotest` (its tests) and `pubimp` (`Factory`'s designed cycle, and
`Time`'s `TimeResolver`, which stays), and `pubimp`'s `dag`, `pub.util`
and `storage`. `SyncLevel`, a Core class in the Pub API's `sync` methods,
moved from `bergdb.core` to `bergdb.pub.util`, an API change against
2026.1 (`releases/next.md`); `Database.PRIMARY` is defined in `pub`, and
`TestClock` checks against `Time`'s range instead of `pubimp`'s
`ClockConstants`, which is gone. `before-commit.sh` and `level2.sh quick` pass.

2026-10-28. Item 009, handles, done at Frans's decision on its target 2,
by Claude (Opus 5.5, Claude Code): no get or commit waits more than about
20 ms for BergDB's own work in P4's soak (the longest commit 5.1 ms, read
3.6 ms, on `main` with 005-46) and the pause probe; s1's get of 2,760 ms is
the machine's (the kernel's memory reclaim). Open as 005-65: with 8
readers from the OS's cache at 665 MB under ZGC on F53, gets of 27 and 36
ms, with loads waiting for the eviction thread. 005-46's Props in the
quiet block had measured CORE after all (the same as before 005-46); its
parser is fixed. README.md's pauses, docs/levels.md's Level 4 limits.

2026-10-28. 005-66 done, by Claude (Opus 5.5, Claude Code), at Frans's
request: the Pub API's `DatabaseBuilder.dir()` and `replica()` only
record their directories, and `start()` opens them, the database's first,
and closes them again if it fails. Since 005-63 a builder that was never
started, the first of two `dir()` calls and a replica given before `dir()`
held a directory's lock until the JVM ended; now a builder holds nothing
before `start()`, a replica given before `dir()` is kept, and a bad or busy
directory is reported by `start()`. Javadoc, two tests in `PubTester`, a
line in `releases/next.md`; `before-commit.sh` and `level2.sh quick` pass.

2026-10-28. 005-56's follow-ups, by Claude (Opus 5.5, Claude Code), as
Frans decided: the Core Layer is built alone every night, with an empty
class path, and its unit and f-tests run on it: 006-08's `core-build.sh`
is `java/stress/core-build.sh`, step 2 of `java/night.sh`, not a commit
gate. `java/deps.py --layer core` lists the Core Layer's packages. Three
stale `package.html` titles corrected, three `src-dev` packages got one,
and `Factory`'s comment names `Time`'s use of `pubimp` too. P12 (010-01)
has its measures: `deps.py` in `before-commit.sh`, and this.

2026-10-28. 005-62 done, by Claude (Opus 5.5, Claude Code), as Frans
decided ("as proposed, all steps"; "Prove it!"; a cut without a restart:
"No, not for now"). The design before handles is gone from lean/:
SIS/Evict.lean and every proof file of it, SIS/EvictExample.lean's runs,
and the seven theorems over it with a counterpart over handles
(`TC_records`, `TR_view`, `T2_cache`, `TR_view_restarts`, `TP_pins`,
`T9_readCut`, `T12_evictCut`). The startup with handles is now proved over
handles (SIS/Proof/HandleStart.lean), from the lazy startup's memory
directly; the assumptions of stage 2 (`EvictRunOK`) and `Mem.sectionPos`
moved word for word to SIS/Phys.lean; what the proofs over handles still
used of the old proof files is in files of neutral names. And rule 4 by
position after a cut: `HMem.linkDPosFrom` is Java's rule with its skip of
the pointers below the stream's first position; after a safe cut it links
what rule 4 by node id links (`rule4PosCut_handles`), so the run with cuts
and rule 4 by position is `runHandlesCut` (`runPosCut_handles`) and T12
over handles holds for Java's startup; no new assumption. By running, at
744 restarts, 1,920 pointers below the cut, none to a node with a canonical
object. lean/ from 144 files and 66,452 lines to 119 and 51,539.
`lake build` from scratch with no warnings and no `sorry`, axioms standard,
the trace tests, `reclaimtest`, `phystest`, `sistest` and
`before-commit.sh` pass.

2026-10-28. 005-67 done, by Claude (Opus 5.5, Claude Code), at Frans's
request: `StorageManagerTester.testAddReplica2`, which failed about one
gate run in twelve on a busy machine ("Expected 700, got 200") and since
2026-10-28 runs twice a night, was wrong, not the code. It asserted the
lengths of the main and the replica right after an append, but an active
replica only means that the sync's last bytes are in the replica's
buffer, which writes them a little later, and both buffers write an
append within milliseconds. It now waits for the confirmed lengths. The
writer of `testAddReplicaWhileAppending` appended without the write lock
that `StorageManager.append` requires, which could hang that test; it
takes it now. Forced interleavings made each failure certain before and
none after; 0 failures in 400,000 runs after the fix, 4 in 40,000 before.
Frans's note of 2015 in the test, "Expected 800, got 1200", was a fault
of the code then: `BufferedStream`'s flush of nothing at a close, fixed by
005-14. Test code only; `before-commit.sh`, `core-build.sh unit f` and
`level2.sh quick` pass.

2026-10-28. 005-53 and 005-52 done, by Claude (Opus 5.5, Claude Code),
for 006-10, as Frans decided ("53 and 52. Yes, do this as recommended."):
the startup distance and the cache size change while the database runs,
through the Pub API (010-P6). `Database.setStartupDistanceInMb(int)` and
`getStartupDistanceInMb()`, clamped to 5 to 1000 MB as the builder, kept in
the stream as before through `Db.setStartupDistance`, one call since D4:B;
that method now writes nothing for the value in force, and checks the
state before it changes the setting, which it puts back if the
transaction is refused. `Database.setCacheSizeInMb(int)` and
`getCacheSizeInMb()`, clamped to 4 to 100,000 MB as the builder, for the
run only, through the new `Db.setCacheSizeIndicator` and
`getCacheSizeIndicator` (Db's public methods from 43 to 45), which JMX now
uses instead of `internal()`; after a decrease the setter wakes the
eviction thread (`Eviction.setBudget(Db, long)`), so that an idle database
gives the memory back too (010-P3: work the call starts). The rule, in
both Javadocs: a setting that changes the stream's bytes is kept in the
stream (P2), one that does not lasts for the run. New tests in
`PubTester`, `DbTester` and `CapacityTester`, each failing on a mutation
of the change; StreamDigest identical (36 of 36); `before-commit.sh`, `level3.sh` and `level4.sh` (full) and `level2.sh quick` pass.

2026-10-28. 007-08's review followed up, by Claude (Opus 5.5, Claude
Code), for 006-10, as Frans decided ("as recommended"): the wrong comment
of `T3_take_decrease` corrected, README.md and levels.md say that T3, the
startup section's bound, is proved (T4 and a cold start's reads through
references open), `share`, `dither` and `javaPace` marked as used by no
theorem. The review's code finding became 005-68 and was dropped: it does
not hold. `Db.store` passes the stream's `getLength()` to `TransSeq.take`,
and the review held that after a record ending on a 200,000-byte boundary
this is 128 bytes before where the next record begins (`getNextPos()`),
the model's argument; but `RecoverableStream.append` writes the meta block
together with such a record, and recovery fills out one that a crash cut,
so the two are equal whenever `take` is called (an instrumented copy: 0 of
5,524,901 calls differ, 229 after a record that ended exactly on
a boundary). No change to `java/`.

2026-10-29. `level1.sh`'s SS limits raised to 1.52 1.11 1.21 1.66 2.41
(from 1.51 1.11 1.20 1.63 2.38), as Frans decided on 29 October (option A
of bergdb 007-07, section 12.3), by Claude (Opus 5.5, Claude Code), for
006-10. The reason, as step 6's rule asks: after 007-07's paced take
(`f89846d`) SS went from 1.50 to 1.51, SS2 from 1.19 to 1.20, SS3 from 1.62
to 1.65 and SS4 from 2.37 to 2.40, SS1 unchanged, so SS3 and SS4 failed
their limits. The startup distance setting is now the startup section's
target (005-49): the paced take holds the section at about the setting,
where the old take let it grow past it, so at Props' default 50 MB it
writes index nodes more often. That is 0 to 2 percent in the SS workloads,
where the user's data are most of the stream, and 24 percent at 10M small
keys (32-byte puts, docs/levels.md, section 5): the expected cost of the
bound, not a regression. The limits keep one step of 0.01 above the new
values; MEM's limit is unchanged.

2026-10-29. `level1.sh`'s MEM limit lowered from 228 to 131 bytes per KV,
as Frans decided on 29 October, by Claude (Opus 5.5, Claude Code), for
006-10, as step 6's rule asks when a change improves MEM. The limit was
still that of 2026-10-19 (MEM 226 to 227); 005-08's fix gave 191 (2026.1),
and the handles work (bergdb item 009: 174 after its phase 1 on 25 October,
then handles, `178a0d4`, 26 October) 129 to 130. MEM has been 129 to 130
since: level1 in the nights of 27 and 28 October 129, 130 and 129, 007-07's
Props in turns 130 before it and 129 after (four rounds each, its section
12.2), and level1 129 today. The limit is 130, the highest, plus one step
for MEM's noise. LEVEL 1 OK (MEM:129).

2026-10-29. The main stream's default buffer time is 50 ms, where it was
20 ms (bergdb 005-64), as Frans decided on 29 October ("Use 50 ms."), by
Claude (Opus 5.5, Claude Code), for 006-10. Since group commit (005-48) a
sync has the buffer written at once, so the buffer time only bounds how
long bytes nobody syncs on stay buffered. In 005-64's runs of 28 October
on F53 and s1, 50 ms gave writers that do not sync 11 to 35 percent fewer
forces (fewer rewrites of the stream's last, partly filled page) with the
same throughput, latency and CPU, at the cost of about twice the unsynced
data a power loss can take (about 82 against 40 ms of writes on macOS,
never more than the 10 MB buffer). `StorageManager.DEFAULT_BUFFER_TIME`
and its comment, `Db`'s Javadoc, levels.md, `releases/next.md`. No test
changed. StreamDigest identical (36 of 36), and also with the tests' buffer
time at 50 ms instead of 10 (P2); `before-commit.sh`, `level1.sh`,
`level2.sh quick` and `level3.sh` pass. 100 ms lost 13 to 16 percent of
the throughput at 1 KB values, because the quarter-full rule is seen only
when the storage thread wakes; that is 005-76, registered.

2026-10-29. 007-08's fourth counterexample is a `#guard` in
`lean/SIS/BoundExample.lean`, as Frans decided on 006-10's point 9, by
Claude (Opus 5.5, Claude Code): R(s+1), ..., R(k) cost less than 2 sd plus
the last record counted whole (`T3_take_rerun`), but not less than 2 sd
plus the last transaction's own bytes; with the deadline alone at a
setting of 200, after T(6) they cost 552, at least 2 · 200 + 72. README.md,
levels.md, sis-model.md and lean/README.md now say that the meta blocks,
not modelled, make no difference to the take (bergdb 005-68), while the
record limit is still left out. `lake build` clean (148 jobs, no
warnings, no `sorry`); trace tests OK.
