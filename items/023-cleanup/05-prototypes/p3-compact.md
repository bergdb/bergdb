# 023-05 P3. Reclaim rebuilds what it rewrites, with maintain()

Created 2026-11-10 by Frans Lundberg. Status: open.

Prototype P3 of 023-05: reclaim's touch rebuilds the nodes it passes, with
replacement nodes (023-04, RB with TU and RC, merges included), the record
stores the touch's range so that a start reruns it (format 6), and an
explicit `maintain()` (023-04, MT). P3 works on `main`'s Dag, without the
upward unlink of P1 and P2, so that the pieces can be combined.

In short: T1 converges to the twin at N = 1,000, 100,000 and 1,000,000,
with the user's writes and with repeated `maintain()` calls: 6 reachable
key nodes as the twin's, the stream kept 2.2 MB against `main`'s 40.4 MB at
100,000 and 2.1 MB against 319 MB at 1M, the first available time 1.1 s
behind against 6 and 13 s. T4's queue keeps cutting (165 cuts, 1.7 MB kept,
against 9 cuts and 53 MB). T3 fails as expected: with R forever nothing
changes, and between touches the scans pay. The costs: two to three times
the bytes written while the deletes run (the other prototype saw about
twice), about twice the objects in memory then, D above the twin's in some
shapes, and the Lean checker's C-S check differs in each step with a
rebuild, as the touch no longer marks the nodes it replaces; with the marks
kept (a switch) the checker passes every check.

The clone `/Users/f/fl/bench/2026-11-10/p3/clone`, branch `023-p3-compact`
(on `main`'s `1901394c` with 023-03's `CleanupRule`, `251c4b65`). Code
places below are file:line at the branch's head, in `java/src/bergdb/`.


## 1. The mechanism as built

### 1.1 The touch and its rebuild

**When and by whom.** In every reclaim step, inside its internal
transaction, before the step's puts, as today's touch (`Reclaim.step`
sets `Trans.touch`, `touchFrom`, `touchTo`; `Db.putKvs` calls
`touchRange`, core/Db.java:3056). Only with a finite R, so only where
reclaim runs; each node of the range once an iteration.

**What.** `Dag.touchAndRebuild` (dag/Dag.java:1385):

1. **The walk** is today's touch: a scan at the step's time ts from
   `touchFrom` to the first live key after `touchTo`, as the writer, whose
   listener makes every index node it follows dirty. Two changes: it reads
   keys only (`GetMany.keysOnly`, dag/GetMany.java:93), so neither the
   walk nor its rerun at a start reads a value; and a listener of its own
   (`TouchWalk`, Dag.java:1426) records the space root and, for each key
   node, the children it followed, by their klongs' compare values.
2. **The plan** (`Rebuild.plan`, Dag.java:1556), children first. For each
   node n the walk reached: its live klongs at ts, as a time split's last
   version takes them (`KeyNode.lastVersionGivenDel`). Then:
   * a child that the walk followed and that has nothing live below it is
     **unlinked**: its klong is left out (020-30-01's B1; 023-04's TU);
   * a child that the walk did not follow is **kept** as it is, assumed
     live (it lies outside the step's range, and another step passes it);
   * if n's first children are unlinked, the first one kept takes their
     **lower bound** (the old first klong's compare value), and so down its
     left edge: every inner node there is planned with that bound as its
     first klong (`Dag.checkFound` needs a klong at or below every key
     routed to an inner node; 023-04's LE-a, done in the replacement nodes,
     so nothing is deleted);
   * adjacent children that the walk followed are **merged** while their
     live klongs and a time klong fit in half a node (`merge`,
     Dag.java:1652): the second one's first klong takes its bound in n;
   * a root, the space root or a segment root, that is an inner node with
     one live child is **replaced by that child** (root collapse, 023-04's
     RC), again while the new root is so.
3. **The build** (`build`, Dag.java:1692), children first: a node whose plan
   changes anything (a klong not live at ts, an unlinked, relabeled, merged
   or replaced child) gets a **replacement node**: a new key node with one
   time klong, ts, and its entries, sorted. The new nodes are reported
   created in this order (`keyNodeCreated`, so they get their ids), the old
   ones replaced (`keyNodeReplaced`). A new space root gets a new super
   root at ts (`TopDs.newSuperRoot`). A node that needs nothing is left as
   it is, and made dirty by the walk, as today.

**Never in place.** The replaced nodes keep their klongs and serve every
time before ts, through the old versions of their parents and the old
super root (`TopDs.findSuperRootAtTime`). So readers at earlier times read
what they read before, and lemma M (a newer version serves every time an
older one serves) holds, as for a time split. The new nodes are reachable
only from the new super root at ts, which readers use only after the
step's commit (their lookup times are before ts until then).

**D.** The walk's marks stay on the nodes it keeps. A node that the rebuild
replaces, unlinks, merges away or collapses leaves D again at once, if the
touch made it dirty (`Db.unmarkReplacedByTouch`, Db.java:2990), as
`endOfTrans` does for a node a put replaces: from ts on no lookup reaches
it. The new nodes are dirty, as every new node is. A switch,
`bergdb.p3.keepTouchMarks` (Db.java:2981, off), keeps the marks, as the
Lean model's touch step does (section 3.2).

### 1.2 The rerun at a start (format 6)

Designed first, as it decides whether P3 is possible. A start reruns the
startup section's records through the Dag (`DbStarter.rerunTransaction`)
and checks the node ids it makes against the stored got-dirty ids. The
rebuild makes nodes whose ids later records name, so a start must make
them too, the same ones, in the same order.

* **What the record stores.** A step's record has bit 0 of header byte 5
  set (`StoredTrans.FLAG_TOUCH`, core/StoredTrans.java:65; byte 5 was the
  first of three unused bytes, all zero), and after the got-dirty list the
  touch's range: `touchFrom` and `touchTo`, each an int (its segments, or
  -1 for null) and its segments as longs (`serializeKey`, :902;
  `parseKey`, :456). Other records are as in format 5, byte for byte, but
  for the format byte. `RECORD_FORMAT` is 6 (:53), so a stream of format 5
  is refused, as Frans decided (023-02, F9 (a) and F10).
* **Why the range.** The range is all that the rebuild needs besides the
  tree at ts, which the rerun has rebuilt from the section and the earlier
  records: ts is the record's time, and the rebuild reads nothing else
  (not the first available time, not what is resident, not D). `touchFrom`
  is the previous step's `lastKey`, in an earlier record that may lie
  before the section, so it cannot be derived; 020-30-04, section 2, came
  to the same field.
* **The rerun.** `DbStarter.rerunTransaction` (core/DbStarter.java:384 to
  445) runs `touchAndRebuild` over the stored range at the record's time,
  before the record's puts, with the listener that numbers the nodes the
  rerun makes (one listener for the touch and the puts now, made once per
  record). So the walk, the plan and the build are the same function of
  the same tree, and the new nodes get the same vpos ids in the same order.
  The rerun reads the nodes of the range, which are mostly in D and read at
  the start anyway; no value (keys only).
* **Checked by** RestartInvariance with reclaim (level3.sh step 3: the
  same stream byte for byte, the same cut, D and node ids with a restart
  after every transaction), CrashTest with reclaim, LoadTest's restarts at
  every cut, and T1's restart (section 4). No start failed.

### 1.3 The cut's safety

Reclaim's argument (Reclaim's class comment): when an iteration is done,
every node reachable at times from tEnd on is stored at pStart or later, or
is dirty. With the rebuild, each node that a step's walk reaches at ts is
kept and dirty (as today), or replaced by a new node (dirty, written at or
after the step's record, so after pStart), or unlinked (reachable from no
time at or after ts). A replaced or unlinked node is reachable only at
times before ts, and ts is at most tEnd. Nodes made after ts are new. The
walk does not follow children outside its range; they lie in another
step's range of the same iteration. So the argument holds as before, and
pEnd and pSafe are unchanged: the still-dirty test (Rule A) keeps a new
node dirty while a child it points to is dirty, as for any node.

A replaced node that leaves D is not written again. A lookup at a time
before ts, but at or after the first available time f, may still reach it:
then f is the tEnd of an earlier iteration, before ts, whose argument says
that the node is stored at or after that iteration's pStart, so in the
kept stream. Once a cut moves f past ts, nothing reaches it. The trace
checker agrees: C-CUT, CutOK at every cut of level3's traces (251 and 254
in two runs), has no failure (section 3.2).

Readers admitted before a cut that reach a cut byte expire with
`LookupTimeNotAvailableException`, as today (D1 = A): no node is changed in
place. ReclaimReaders (level3.sh step 5) passed: 31.7 million gets and 10.8
million scans right, 67 expired.

### 1.4 maintain()

* **Core.** `Db.maintain()` (core/Db.java:643), under the write lock,
  refused on a database that is not active. It returns whether more is
  due. Its parts:
  1. `Reclaim.maintain` (core/Reclaim.java:504): with no iteration in
     progress, one starts when a quarter of R has passed since the last
     one started, without today's condition of a stream grown by twice the
     startup distance, which an idle database never meets; tStart is the
     database's current time (`DbClock.currentTime`). With one in
     progress, one step of at most `MAX_STEP_SIZE` bytes of KVs, with its
     touch and rebuild, whatever its allowance. Then the safe positions and
     the cut, as after a user transaction.
  2. If D is not empty, or a done iteration waits for the startup pos to
     pass its pEnd or pSafe (`waitsForStartupPos`, :534): an internal
     transaction with no keys whose record's take is forced
     (`Trans.maintainTake`; `TransSeq.take` with `forced`, oldest first,
     at most `FORCED_TAKE_BYTES`, 1 MiB, but always the first
     transaction): the startup pos moves on without user writes. Then the
     cut again (`afterMaintain`, :527).
* **Pub API.** `Database.maintain()` (pub/Database.java:501), which calls
  the Core's (pubimp/DatabaseImp.java:231). Small: one line and its
  Javadoc. Both are new API methods, which P12 of 010 leaves to Frans; his
  words of 10:49 allow it for the tests.
* **Calm when not used** (010, P3): nothing calls it. Each call's work is
  bounded by one step, one take of at most about 1 MiB, and the tables.
* **What it cannot do.** A cut needs the last valid meta block to name a
  transaction at or after pCut (`pretruncateIfPossible`). Meta blocks lie
  every 200,000 bytes of stream (`META_BLOCK_DISTANCE`), and `maintain()`
  writes about 25 to 80 bytes a call on average, so a small database waits
  for its stream to pass the next meta block (section 4.3). Not changed
  here: the meta blocks are the framing (014-01).


## 2. What changed, and why

On the branch, after 023-03's test (`git diff 2ae7fdd0 HEAD`; the head in
section 8):

| File                           | Change                                                   |
|---|---|
| dag/Dag.java                   | `touchAndRebuild`, its walk, plan, merge and build       |
| dag/GetMany.java               | `keysOnly`: a scan that reads no value                   |
| core/Db.java                   | the touch calls the rebuild; unmarking; `maintain()`     |
| core/DbStarter.java            | the rerun of a step's touch, before its puts             |
| core/StoredTrans.java          | format 6: the flag and the touch's range                 |
| core/NodeStream.java           | gives the serializer the transaction's touch             |
| core/Trans.java                | `maintainTake`; comments                                 |
| core/TransSeq.java             | the forced take; `dirtyCount()`                          |
| core/Reclaim.java              | `maintain`, `afterMaintain`, `waitsForStartupPos`        |
| core/Reclaim.java, its Tester  | `testRebuildReleasesDeletedKeys`, an f-test (below)      |
| pub/Database.java, DatabaseImp | `maintain()`                                             |
| pubimp/PubTester.java          | one test runs 5,000 puts instead of 2,500 (section 3.1)  |
| stress/CleanupRule.java        | `maintain()` drive; bytes, records, D; `keep=K`          |

Two knobs for experiments, both off: `bergdb.p3.keepTouchMarks` (1.1) and
`bergdb.p3.minDeadDivisor` (compact a node for its own klongs only when at
least B / divisor of them are not live; section 4.5). No Lean change, no
change of the expected digests. One fault found and fixed on the way: a
segment root that collapsed to an unchanged child stayed linked itself,
and left D (commit `66273fc9`); no test had met it.

The new f-test (0.3 s): 300 short and 300 long keys at node size 8, all but
every 50th deleted, 400 overwrites with a restart every 100; every key read
right before and after a restart; the key nodes reachable at the end within
20 of a twin's (46 against 36), with nodes made, unlinked and relabeled
across the sessions.


## 3. The gates

Run in the clone, in this order; the commits are on the branch.

| Gate                     | Commit     | Result                                                 |
|---|---|---|
| before-commit.sh         | `04d30fca` | BEFORE COMMIT OK, after the test change of 3.1         |
| level3.sh                | `5f786851` | steps 1 to 7 OK; step 8, conformance: C-S only (3.2)   |
| level1.sh full           | `5f786851` | LEVEL 1 OK; MEM 129 (at most 131), SS 1.51 (1.52)      |
| level2.sh quick          | `5f786851` | LEVEL 2 OK; conformance small, 14 traces OK            |
| before-commit.sh         | `8c5eee3f` | BEFORE COMMIT OK (merges and plans in)                 |
| level3.sh                | `8c5eee3f` | as at `5f786851`: C-S in 507 steps, all else OK        |
| level1.sh, level2.sh quick | `66273fc9` | LEVEL 1 OK, LEVEL 2 OK                               |
| level2.sh full           | `66273fc9` | LEVEL 2 OK, its conformance 70 traces OK               |
| conformance.sh reclaim 1 | `66273fc9` | with `keepTouchMarks`: CONFORMANCE OK, C-S too         |
| before-commit.sh         | `7b2cf1ec` | BEFORE COMMIT OK, the new f-test in                    |
| level3.sh                | `7b2cf1ec` | steps 1 to 7 OK; conformance: C-S in 507 steps only    |
| level4.sh quick          | `7b2cf1ec` | steps 1 to 4 OK; conformance: C-S in 45 steps only     |

### 3.1 before-commit.sh

One unit test changed: `PubTester.testTransactionInfoAgainstOracle` asserts
at least 30 reads of a reclaim copy, to be sure that it checks
`transactionInfo()` on copies. With P3 it found 13 in 2,500 puts: reclaim
made 33 iterations instead of 48. Its records are smaller (the rebuilt
nodes hold only live klongs), and reclaim's pace is a fraction of the
stream's growth, so iterations come later in that small run (node size 8,
startup distance 2,000 bytes). With 5,000 puts it finds 34 copies, still in
0.2 s; every correctness assertion passed in both runs. A changed test,
for Frans's approval (023-02, R27).

### 3.2 level3.sh

Steps 1 to 7 pass: the unit and f-tests, ReclaimStress (200 rounds, all
with a cut, 3,528 exhaustive verifications), RestartInvariance with reclaim
(stream identical, same cut, in all four configurations), CrashTest with
reclaim, ReclaimReaders (at `8c5eee3f`: 58.9 million gets and 19.9 million
scans right, 76 expired), LoadTest (a restart at every cut), PowerLossTest.
Step 8, the conformance with the Lean model with reclaim, fails in one
check:

* **C-S, the steps' D and got-dirty sets**: 507 transactions of 25 traces,
  each a reclaim step whose rebuild replaced nodes. Every difference is
  "model only": the model's touch step (`touchOf`) marks every node the
  touch reaches, and P3 takes the marks off the nodes it replaces (1.1).
  No "Java only" node in any trace. An expected new behaviour, not a fault:
  the model has no touch that replaces.
* Every other check passes: C-A (A2 to A5, TREE, A6', A-COPY: the
  replacement nodes are accepted as a time split's are), C-V, C-CUT (0 of
  254 cuts fail), C-L, C-R, no exporter error.

To pass C-S unchanged, either the model's touch step leaves unmarked what
the touch replaces (a change of `touchOf` in the model, for Frans), or Java
keeps the marks (`bergdb.p3.keepTouchMarks`): measured at N = 100,000, the
replaced nodes are then written once more, D in the window reaches 164
instead of 102, and the first cut after the deletes comes later (the most
kept in the window 50.3 MB instead of 2.2 MB). With the switch the checker
passes every check, C-S too (`conformance.sh reclaim 1`: 5 traces, 45
cuts): the replacement nodes, the unlinks and the new super roots are steps
of the model as it is; only the unmarking is not.

### 3.3 level4.sh quick

Steps 1 to 4 pass: the eviction unit and f-tests, EvictionInvariance in
each schedule with the audit (the same stream with and without eviction),
RestartInvariance, CrashTest and ReclaimStress under forced schedules (0 of
some 66,000 audits failed), ReclaimReaders under eviction. Step 5, the
conformance with eviction: the 4 traces with reclaim (`e-r-*`) fail C-S
only, in 45 steps, all "model only", as in level3; C-P, C-H (the handles),
C-V, C-L, C-R pass; the other 11 traces pass.

### 3.4 Not run

level4.sh full, `night.sh`, `cross.sh` (the C port follows Java after the
release), performance.sh. StreamDigest: section 4.6.


## 4. The measurements

With 023-03's `CleanupRule` and the settings of its section 2.1 (R = 1 s,
startup distance 100 kB, a test clock 1 ms a transaction, `CutStream`, no
eviction), counts only. "Main" is 023-03's section 8 and, for the bytes,
`main`'s jar run here the same way. The twin is each build's own (P3's twin
writes less: M1 1.94 MB against 2.13, M5 13 against 35, M8 56 against 79).

### 4.1 T1, the drive of overwrites, shape "after"

| Measure                 | P3 twin | P3 1,000 | P3 100,000 | P3 1M     | main 100,000 | main 1M   |
|---|---|---|---|---|---|---|
| M1, MB, most in window  | 1.94    | 1.90     | 2.23       | 2.05      | 40.42        | 319.02    |
| M3, ms                  | 1,035   | 1,220    | 1,131      | 1,106     | 5,951        | 12,956    |
| M4, reachable nodes     | 6       | 6        | 6          | 6         | 7,902        | 78,999    |
| M5, dead KEY klongs     | 13      | 13       | 10         | 10        | 102,918      | 1,028,078 |
| M6, M7                  | 1, 6    | 1, 6     | 1, 6       | 1, 6      | 1, 6         | 1, 6      |
| M8, D, most in window   | 56      | 47       | 102        | 65        | 26           | 31        |
| M9, largest record, B   | 2,488   | 2,488    | 3,248      | 2,928     | 1,729,720    | 2,224     |
| M10, touch visited      | 7       | 7        | 7          | 7         | 34,629       | 76,480    |
| M11, after the probe    | 58      | 45       | 106        | 70        | 7,927        | 79,033    |
| M12, start's loads      | 3       | 7        | 2          | 2         |              |           |
| cuts in the run         | 11      | 11       | 15         | 15        | 1            | 4         |

Against 023-03's criteria, P3's twin and allowances (bounded a_n = 10 + 4
h_fill; strict 10):

* N = 1,000 and 1M: C1, C2, C3, C4, C5, C7, C8, C10 pass, strict too; C6
  and C9 pass bounded (1M: M11 70 against the strict 68, by 2).
* N = 100,000: C1 to C5, C7, C8, C10 pass, strict too; **C6 and C9 fail**,
  bounded: D 102 against 90, M11 106 against 92. The excess is top nodes
  in D (section 5.2). C11 (M14) was not measured: 023-03's H2 is not built.

### 4.2 T2's rows at N = 100,000 (long: 10,000), drive of overwrites

| Row               | M1, MB | M3, ms | M4 | M5 | M6 | M7 | M8  | M9, B | M11 |
|---|---|---|---|---|---|---|---|---|---|
| after, ascending  | 2.23   | 1,131  | 6  | 10 | 1  | 6  | 102 | 3,248 | 106 |
| after, descending | 2.45   | 1,129  | 6  | 7  | 1  | 6  | 131 | 2,984 | 129 |
| after, random     | 2.06   | 1,070  | 6  | 4  | 1  | 6  | 73  | 3,000 | 79  |
| after, 3 versions | 1.92   | 1,208  | 6  | 17 | 1  | 6  | 48  | 2,600 | 45  |
| before            | 2.35   | 1,116  | 6  | 9  | 1  | 6  | 112 | 3,232 | 120 |
| around            | 1.99   | 1,000  | 6  | 5  | 1  | 6  | 63  | 3,248 | 75  |
| inter             | 2.11   | 1,088  | 6  | 6  | 1  | 6  | 84  | 2,800 | 91  |
| hashed, ascending | 1.94   | 1,008  | 6  | 14 | 1  | 6  | 53  | 3,016 | 53  |
| long, 10,000      | 1.89   | 1,163  | 6  | 14 | 1  | 6  | 48  | 2,488 | 56  |

Every row ends with the twin's 6 nodes, a get of one node and the twin's
head. "inter", keys in "/a.txt"'s own segment tree, needed the merges:
without them it ended with 14 nodes and a get of 5 (a root with two live
children over underfull leaves). M8 and M11 exceed the bounded allowance
in "after" ascending and descending and in "before" (section 5.2).

"Sparse" (every 30th key of "after" kept, `keep=30`, 3,334 live keys): 377
reachable nodes, about 9 live keys a node, and 1,603 dead klongs (the
shadowed klongs of reclaim's own rewrites since the last touch of each
leaf); no twin was run for it. Every 300th kept: 45 nodes for 334 keys.
"Long" with every 30th, 300th and 1,000th key kept, N = 20,000: lookups
right before and after a restart, 1 and 2 segment roots collapsed.

### 4.3 T1, the drive of maintain() calls

4,000 calls of `maintain()`, the clock 1 ms between calls, instead of the
overwrites; the same for the twin.

| Measure                | twin    | N = 1,000 | N = 1,000, 16,000 calls | N = 100,000 |
|---|---|---|---|---|
| M1, kept at the end, B | 106,840 | 361,552   | 71,704                  | 45,752      |
| M3, ms                 | 14,001  | 14,021    | 1,001                   | 1,159       |
| M4, M6                 | 6, 1    | 6, 1      | 6, 1                    | 6, 1        |
| M5                     | 3       | 5         | 6                       | 4           |
| M11, after the probe   | 7       | 7         | 7                       | 7           |
| cuts                   | 0       | 0         | 14                      | 10          |

* The index converges at once: 6 nodes and 7 resident objects after a
  restart, as the twin's, at every N.
* The stream converges once a cut can come. The twin and N = 1,000 never
  cut in 4,000 calls: their streams, 107 and 362 kB, have no meta block
  after their pCut (1.4). With 16,000 calls N = 1,000 cuts 14 times and
  keeps 72 kB; N = 100,000 cuts in 4,000 calls and keeps 46 kB, less than
  the twin, which has never cut. So "about as much as a fresh hello-world
  database" holds after enough calls, measured by the twin under the same
  calls; how many depends on the meta blocks.
* A call writes about 25 to 80 bytes on average: a step's record when an
  iteration runs (one every R/4 of the clock), the forced take while D or a
  done iteration waits, nothing otherwise.

### 4.4 T4, the queue, keys in time order, 100,000 transactions

| Checkpoint | M1, MB | M3, ms | M4  | M5 | head | M8  | M9, B  | cuts | main: M1, M4, head  |
|---|---|---|---|---|---|---|---|---|---|
| 10,000     | 1.49   | 1,072  | 156 | 91 | 43   | 153 | 37,632 | 12   | 2.4, 1,119, 1,006   |
| 50,000     | 1.77   | 1,485  | 141 | 61 | 28   | 135 | 20,544 | 79   | 25.0, 5,576, 5,463  |
| 100,000    | 1.70   | 1,413  | 134 | 47 | 21   | 156 | 30,056 | 165  | 53.2, 11,147, 11,033 |

Steady: cuts go on (165 against `main`'s 9), M1, M3, M4 and M9 stay flat.
The queue's head varies from 12 to 44 key nodes between the touches of the
head's range (`main`: one node per 9 keys ever deleted), more than T4's
4 H (about 20): the deletes since the last touch are passed (T3).

Hashed keys, 100,000 transactions: M4 2,470 to 2,535 at every checkpoint
(`main` 112,782 at the end), M1 4.3 to 5.0 MB (`main` 112.5), M3 1.0 to
1.4 s, 259 cuts, the head 5 nodes, M9 at most 34 kB (`main` 391 kB).

### 4.5 The costs: bytes written and memory

Stream bytes written in each phase, P3 against `main` (the same runs):

| Phase, N              | main, MB | P3, MB | P3 / main | index nodes in user records |
|---|---|---|---|---|
| fill, 100,000         | 23.2     | 28.3   | 1.22      | 34,512 against 17,580       |
| deletes, 100,000      | 10.9     | 22.8   | 2.09      | 75,714 against 19,434       |
| drive, 100,000        | 6.5      | 6.4    | 0.99      |                             |
| fill, 1M              | 247.9    | 353.6  | 1.43      | 588,501 against 182,581     |
| deletes, 1M           | 109.2    | 329.4  | 3.02      | 1,054,263 against 173,361   |
| drive, 1M             | 4.7      | 9.2    | 1.96      |                             |
| twin's drive          | 5.4      | 5.0    | 0.92      | 2,378 against 3,825         |
| queue, 100,000 trans. | 56.8     | 67.1   | 1.18      |                             |
| hashed queue, 100,000 | 306.2    | 239.2  | 0.78      |                             |

* `main`'s reclaim stalls once the deletes begin at 100,000 and 1M (no cut
  in the drive), so it writes less there; P3's keeps up (15 cuts). In the
  steady state, the twins' drives and 100,000's, P3 writes less than
  `main`: the rebuilt nodes hold only live klongs.
* The extra bytes are mostly not the new nodes: the rebuild made 113,976
  nodes at 1M, and 105,083 of them replaced a node in D. Such a node must
  still be written once, for the times before ts, and the still-dirty test
  (Rule A) keeps it dirty while a child it points to is dirty, which in a
  busy range is again and again: it is written many times.
* Memory, without eviction, after the deletes: 19,460 resident objects
  against 10,953 at 100,000 (1.8 times), 242,078 against 110,257 at 1M
  (2.2 times); the hashed queue 291,029 against 117,571 (2.5 times). They
  are the replaced versions, which nothing frees without eviction (023-02,
  K15: CLOCK takes them under a budget). After a restart 106 against 7,927.
* Compacting a node only when at least B / 4 or B / 2 of its klongs are
  not live (`bergdb.p3.minDeadDivisor`) wrote 45.6 and 45.2 MB to the end
  of the deletes at 100,000, against 51.1; it raised the twin's D to 93 and
  83 and its dead klongs to 21 and 35. Left off.

### 4.6 Determinism

* StreamDigest, quick (11 configurations, 4 modes): "the modes give the
  same stream" in every configuration. Against `main` all 44 digests differ:
  `l2-*` by the format byte only (the same lengths), `l3-*` also in length,
  as the rebuild writes other nodes: l3-every1 1.88 to 1.51 MB, l3-node8
  7.20 to 5.49 MB, l3-node14 1.65 to 1.39 MB, l3-node62 10.34 to 10.07 MB.
* A probe of `maintain()` (20,000 and 3,000 keys put and deleted, then
  4,000 calls with an overwrite every 7th): the same stream, byte for byte
  (SHA-256 from the decided cut), the same cut and first available time,
  without restarts, with a restart every 37 or 500 calls and every third
  delete transaction, and with a restart after every call.
* Eviction: T1 at N = 100,000 with the capacity controller at a budget of
  1 MB gives the same measures as without, on a `CutStream` and on a
  `FileStream` (M1 most 2,230,336 bytes in each); M13, resident bytes at
  the end, 0.97 MB against the twin's 0.93 MB. On the `FileStream` the files
  lag far behind the decided cut: 57.1 MB in 42 files after the restart,
  against 2.0 MB from the decided cut (the twin 4.8 MB in 20 files); the
  physical cut's lag that 023-03, 2.4, describes, not looked into here.

### 4.7 T3, scans at every time

As expected, P3 alone fails T3. With R forever there is no reclaim, so
nothing changes: right after deleting 100,000 keys a scan for one KV
follows 7,897 key nodes, and "before"'s head scan 7,897, `main`'s numbers
(023-03, 8.3). With R finite, scans between two touches of a range pass
the deletes since the last one: T4's head, 12 to 44 nodes against 4 H.


## 5. Faults and limits found

### 5.1 Requirements and tests

* **Met** (023-02): R1 (T6 found nothing in any run), R2 and R3 for nodes
  and klongs of ended versions within one or two iterations of their end
  (every row of T2 ends at the twin's index; M5 is the shadowed klongs of
  the last iteration's own puts, F1, F2, R7), R6 (cuts keep up: T1 at 1M,
  T4), R12 (a) and (b) in the end state, R13, R15 (the rerun reads the
  nodes of each step's range in the section, mostly in D anyway, and no
  value; M12 2 to 7 loads), R16 to R19 (level3.sh steps 2 to 7), R20
  (level4.sh steps 1 to 4; T1 under a budget, 4.6), R17 also for
  `maintain()` (4.6), R10's wish in the end state (the twin's height
  after root collapse).
* **Not met**: R9 at every available time (F3; T3), R26 in the delete
  phase (the bytes of 4.5), R14 in part (D, 5.2), R24 (C-S, 3.2), R22 and
  R27 for Frans's approval (format 6, the changed test).
* 023-03: T1 passes bounded at N = 1,000 and 1M, and fails C6 and C9 at
  100,000; strict, C3 to C5 pass at every N. T2's index converges in every
  row; C6 and C9 fail in three rows. T3 fails. T4 passes M1, M3, M4, M9 and
  the cuts, fails the head's 4 H. The `maintain()` drive converges the
  index at once and the stream after enough calls.

### 5.2 D keeps top nodes

At N = 100,000 D holds about 100 nodes in the drive against the twin's
45; it is stable over 16,000 transactions, so bounded. Of the 107 at the
end, 97 are top nodes, 96 of them with a dirty skip target at that moment:
the still-dirty test keeps a written top node dirty while a node it points
to is dirty. Runs of 10 to 25 consecutive top nodes stay dirty for 1,000 to
2,000 transactions, then clean; at a print, the oldest of them pointed to
no dirty node: it waits for its next write, and each write so far met a
child that was dirty at that moment. Not explained yet. Not the ordinals: a
twin with 15,000 more overwrites first, so as high ordinals, keeps 35 top
nodes, as the twin. At 1M D is 65 against 56. It is what fails C6 and C9 at
100,000. My guess: 5.3, through the old roots.

### 5.3 Replaced while dirty

A node in D that the rebuild replaces must still be written once, for the
times before ts, and the still-dirty test (Rule A) then keeps it dirty
while a child is dirty: in a range under writes, it is written again and
again until its children are quiet. This is the write amplification of
4.5. `main` has the same with time splits, and every top node is replaced
while dirty. A deterministic remedy is needed, and the easy ones are not:

* "Do not rebuild a node in D" cannot be decided at a start: the rerun
  does not rerun the takes, so it does not know which nodes were dirty when
  a record ran, and the ids would differ.
* Rule A for a replaced node only up to its replacement time (it needs a
  written version of each child from that time on, not a clean child)
  needs the replacement time of every node in D after a restart too; the
  rerun knows it for the section's replacements only.
* Compacting a node only when many of its klongs are dead (4.5) helps the
  delete phase a little and hurts the twin's D.

Options for phase 2: a stream-derived criterion for "quiet" (from klong
times, which the rerun has), or the replacement time stored with a node's
version.

### 5.4 Other limits

* Merges only between children that the walk followed, so within a step's
  range; an underfull node at a step's edge waits for an iteration whose
  steps fall otherwise. Root collapse at each rebuild of a root.
* The walk still runs to the first live key after `touchTo` (021-25, part
  2), but only once: the next iteration finds the deleted subtrees gone.
* A step charges its new nodes to the iteration (`dirtiedBytes`), and the
  replaced ones are taken off; the step reserve counts the nodes followed.
* `maintain()` cannot force a meta block (1.4), and its forced take writes
  up to 1 MiB of D in one record.
* With R forever nothing is rebuilt: no reclaim (R8, as F8 recommends).


## 6. What is left for a production version

1. A deterministic way to avoid rewriting replaced nodes again and again
   (5.3), then the bytes of 4.5 again, at 1M and 10M, and `performance.sh`
   (T10).
2. The top nodes of 5.2, explained and bounded by the twin's.
3. The Lean model: a touch step that leaves the nodes it replaces
   unmarked (C-S), or the marks kept, at their cost (3.2); with the marks
   kept the checker accepts P3's traces as they are.
4. The format change approved (018-01, section 2): StreamDigest's new
   digests (4.6), `night.sh`, the C port (022: the walk, the plan and
   build, the rerun, the record's range; 200 to 400 lines by 020-30-04).
5. The scan bound at every time needs the upward unlink at the delete (P1
   or P2); with it the walk passes no deleted subtree, and P3's rebuild
   keeps the compaction, merges and collapse (023-04's option C).
6. Tests: unit tests of each case of the rebuild (merge, collapse of the
   space root and of a segment root) beside the f-test of section 2;
   023-03's H2 (M14); T7 with restarts at the drive's cuts and crashes
   inside a step's record; the "sparse" row against its twin; `maintain()`
   in a unit test.


## 7. Questions for Frans

* **Q1. maintain() in the API.** `Db.maintain()` and
  `Database.maintain()`, bounded per call, returning whether more is due:
  keep them in 2026.4 (P12 leaves a new API method to Frans)? Recommended:
  yes, as a documented call for databases that idle; the tests need it.
* **Q2. The touch's marks.** Leave the replaced nodes unmarked (fewer
  bytes, earlier cuts; C-S then fails until the model's touch step changes)
  or keep the marks as the model has them (the checker passes today)?
  Recommended: unmarked, with the model's change, which the cut's
  argument of 1.3 supports.
* **Q3. The changed unit test** (3.1): 5,000 puts instead of 2,500 in
  `testTransactionInfoAgainstOracle`, as reclaim's pace follows the smaller
  records. Recommended: approve.
* **Q4. The cost in the delete phase** (4.5): about twice `main`'s bytes at
  100,000 and three times at 1M while reclaim keeps up (`main`'s stalls
  there), before 5.3's remedy. Is that within "near current performance"
  for a prototype to continue, or must 5.3 come first? Recommended: 5.3
  first.


## 8. State

2026-11-10, 12:20 (the machine's clock): done for this prototype. The
clone `/Users/f/fl/bench/2026-11-10/p3/clone`, branch `023-p3-compact`,
head `7b2cf1ec`, 8 commits after 023-03's `2ae7fdd0`; the worktree is
clean. At the head: before-commit.sh OK; level3.sh and level4.sh quick
pass every step but the Lean conformance, which fails C-S only (3.2, 3.3);
level1.sh and level2.sh (full) passed at `66273fc9`, before the f-test. The
runs' output is in the agent's scratch directory, not kept; the numbers are
in this report. Next, for whoever continues: section 6, first 5.3.
