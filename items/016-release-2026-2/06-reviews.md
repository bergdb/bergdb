016-06. Plan: the reviews, H1 and H2
=====================================

Created 2026-11-03 by Frans Lundberg.

**Status: planned, not started.** The detailed plan of 016-01, section 6's
H1 (the changes since 2026.1) and H2 (the Pub API's promises). H3 is 016-07,
H4 is 016-08. Frans's answers of 15:27 apply: the reviews run at xhigh, no
higher (Q3). His change of 15:31 (D7) applies too: only Java is in the
release; Lean and the C clone are tools, not outputs.


## 1. In short

Frans, 15:40: "try your best to finish this work by 07:00 tomorrow in the
morning ... instead of in three days or so. Note, you only need
before-commit.sh to be successful to commit your work." So the search runs
tonight, 2026-11-03, and this plan is cut to fit:

* **Eight reviews tonight**, each by one fresh subagent at xhigh with a
  hard stop of 2.5 hours, in two rounds from about 16:50; the last starts by
  19:40, so that every report is in by about 22:00 (section 6).
* **The priority order** (section 6): handles and the node table (R1);
  FileStream (R2); the threads and the lifecycle, H3 (R3, planned in
  016-07); eviction (R4); BufferedStream and StorageManager (R5); startup
  and the take (R6); Db and reclaim (R7); the Pub API, its lifecycle and
  the promises of the database and connections (R8, H1d with H2a).
* **Two reviews on stand-by** (S1: rw-transactions, encryption and JMX; S2:
  indexes and objects): they start only if a slot frees before 19:40.
  Otherwise they are after the release, by section 7's decision.
* **Each finding is verified** (section 2.4) by about 23:00: a failing test,
  which the coordinator reruns, or an interleaving, which a verifier agent
  checks (section 2.6). The fixes run from about 22:00 to 01:00 (section 8),
  with `before-commit.sh` as their gate (Frans, 15:40).
* **Reports**: `06-reviews/ID.md` (ID: R1 to R8, S1, S2), with tests and
  probes in `06-reviews/ID/`. Section 2.5 gives the form.
* The reviews of the concurrency-heavy areas (R1, R2, R4, R5) also list
  their shared fields (section 2.5, "Shared fields"); 016-07 builds H3 on
  them.


## 2. Rules for every review

### 2.1. The base commit

* What: each review reads one commit of `main`, its BASE, and the diff
  `release-2026.1..BASE`.
* When: the coordinator takes BASE as `git rev-parse main` at the moment it
  starts the agent, after the commits that the review waits for (section
  6).
* By whom: the coordinator; it writes BASE into the brief and into
  section 9's table.
* Checked: the report's header names BASE; the verifier checks out the same
  commit.
* A change committed after BASE in the review's files is not in its scope:
  it gets its own review under H5 (016-01, section 6).

### 2.2. The clone

Each agent works in a scratch clone of its own, never in the main tree:

```
mkdir -p /Users/f/fl/bench/016/ID
cd /Users/f/fl/bench/016/ID
git clone -q /Users/f/fl/repos/bergdb repo
cd repo && git checkout -q BASE
sh java/build.sh > ../build.txt 2>&1     # about 30 s; needed for tests and probes
git diff release-2026.1..BASE -- FILES > ../diff.txt
git log --format='%h %ad %s' --date=short release-2026.1..BASE -- FILES > ../log.txt
```

FILES is the review's list of section 3, as paths from the repository's
root. The agent writes in the main tree only its report and its attachment
directory (section 2.5).

### 2.3. What the reviewer gets, and what not

* It gets: the code at BASE; its files (section 3); the diff and the log;
  the entries and sections that define the intended behaviour (section 3);
  the existing tests of its area; `AGENTS.md`, `docs/levels.md` and
  `items/readme.md`.
* It does not get, and its brief tells it not to read:
  * 016-01 and the other files of `items/016-release-2026-2/`, except its
    own brief, which the coordinator pastes into the prompt;
  * `items/015-todo/`, where the search's findings are registered;
  * the other reviews' reports, and 016-07's reading.
* Why: 016-01, section 6. A reviewer with no stake and no hints finds what
  the others missed, and does not confirm what it was told.
* Checked: the verifier and the coordinator look at the report's sources
  (the report's section 7, "Read", in section 2.5's form); a finding that
  rests on a forbidden file goes back to its reviewer, or becomes a doubt
  if there is no time.

### 2.4. The rule for findings

This is 016-01, section 6, "The rule for findings", made concrete.

* **A fault is verified** in one of three ways:
  1. a failing test: a test added to the area's Nano tester (or a new
     tester), which fails on BASE for the reason the finding gives;
  2. a probe: a small program, kept in the attachment directory, whose
     output shows the wrong behaviour;
  3. for a race: the interleaving written out, step by step (section 2.5),
     and checked by a second agent, the verifier (section 2.6). A test that
     forces the interleaving (a latch, a hook in a test subclass) is better
     still, when it can be written in the time.
* **Not verified**: the finding goes into the report's "Doubts", with what
  would verify it. A doubt is not registered as a fault. The coordinator
  lists the doubts in 016-02, and Frans sees them in the notes' review.
* **A statement of the Javadoc that the code does not keep** is a fault of
  one or the other, verified the same way (H2). Which side to change is the
  fix's question, not the finding's.
* **Out of scope**, and not reported as faults: replication
  (`DatabaseBuilder.replica`, `Database.addReplica`, `removeReplica`,
  `getStorageInfos`, the replica rules in `storage/`), by Frans's decision; the
  holes of an unforced tail at a start (014-01, out of this release); speed,
  unless it breaks a stated bound. A fault met in replication on the way goes
  into the report's section 5, "Met outside the scope", one line each.
* **Tests and probes stay small**: a unit test of up to about a second, a
  probe of up to a minute. No gate, no level script, no `night.sh`, no timed
  run: other agents use the machine (013-01, section 4).
* **Test gotchas**: every test stops its databases (`close()` waits,
  `stop()` closes in the background); a probe in `bergdb.core` goes before
  `build/bergdb.jar` on the class path. A single test runs with
  `java -ea -cp build/bergdb.jar bergdb.dev.Unit -c CLASS -m METHOD` (or
  `bergdb.dev.F`).

### 2.5. The report

* Where: `items/016-release-2026-2/06-reviews/ID.md`, written by the agent
  in the main tree. Attachments in `06-reviews/ID/`: each test as a patch
  against BASE (`git diff > ../ID-F1.diff`, then copied), each probe as a
  `.java` file, and a few lines of output each. No raw logs (013-01,
  section 4, "Raw output").
* The form:

```
016-06/ID. Review: TITLE
========================

Created YYYY-MM-DD by Frans Lundberg. Base: COMMIT. Started HH:MM, ended
HH:MM (from date). Effort: xhigh.

## 1. Scope
Files read whole; files read as a diff; entries read. Anything left out,
and why.

## 2. Faults
### ID-F1. One line: what is wrong
* Where: FILE, METHOD, lines at BASE.
* Intended: what the entry or the Javadoc says (cited by ID and section).
* Actual: what the code does.
* Effect: what a user or the stream sees: a wrong answer, lost or extra
  data, a hang, a database that does not fail when it should, or fails
  when it should not, a refused start.
* Evidence: the test or probe (file in ID/, the command, the line that
  shows the failure), or the interleaving (numbered steps, each naming
  the thread, the code line, the lock held, and the happens-before edge
  that is missing).
* In 2026.1: yes, no or unknown, from `git show release-2026.1:FILE`.
* A fix touches the stream format, a Pub API signature, or needs a
  design choice: yes or no, and which.
* A fix, proposed in a few lines; not made.

## 3. Doubts
Each: what may be wrong, why it is not verified, and what would verify it.

## 4. Checked and right
A short list of what was checked and holds, so that the coverage shows.

## 5. Met outside the scope
One line each (replication, 014-01's tails, speed).

## 6. Shared fields (R1, R2, R4 and R5; 016-07, section 3)
One item per field or object that more than one thread uses:
* FIELD (CLASS): written by THREAD under LOCK (or: a volatile write, a
  CAS, final, before publication); read by THREAD under LOCK (or: plain,
  acquire); the happens-before edge that orders them; why a stale or
  torn value is harmless, if it can be seen; the test that checks it
  (jcstress, a tester), or "none".

## 7. Read
The files and sections that the agent read besides its code.
```

* The agent's final message to the coordinator: the report's path, the
  number of faults and doubts, each fault's one-line title, and the time.

### 2.6. The verifier

* What: a second agent at xhigh, which checks the faults of one or more
  reports. It has not seen the reviewer's reasoning beyond the finding.
* It gets, per finding: the section `ID-Fn` copied from the report, its
  attachments, BASE, and the entries the finding cites. Not the rest of the
  report, not 016-01.
* It does, in a clone at BASE (`/Users/f/fl/bench/016/verify-N/`):
  * a test or probe: applies it, runs it, and checks that it fails for the
    stated reason (the assertion, the stack), that the test uses BergDB as
    its contract allows (not a misuse of an internal method, not a test's
    own bug), and that the behaviour is against the cited entry or
    Javadoc;
  * an interleaving: walks each step against the code at BASE: that each
    step is reachable, that the locks named are and are not held, that the
    happens-before edges are as claimed under the Java Memory Model, and
    that the end state is wrong. If it can, it writes a test that forces the
    interleaving.
* Its verdict per finding: **confirmed**, **refuted** (with the step or the
  reason) or **unclear**. Confirmed counts as verified; refuted or unclear
  moves the finding to the report's doubts.
* Where: `06-reviews/verify-N.md`, one section per finding, with the verdict
  first. The coordinator adds the verdict to the finding's title in the
  report (`ID-F1 (confirmed, verify-2)`).
* Size: about 20 to 40 minutes a finding; one verifier takes up to about
  six findings.
* Tonight, to save slots (section 6):
  * a fault with a failing test or a probe: the coordinator reruns it in its
    own clone at BASE (one command, under a minute), and reads the failure
    against the cited entry or Javadoc. That rerun is the verification. A
    test whose premise the coordinator doubts (a misuse of an internal
    method, a test's own bug) goes to a verifier;
  * a fault that is an interleaving only: always a verifier agent, as
    016-01, section 6 asks.
* Who chooses: the coordinator, after each report. A report without faults
  needs no verifier.

### 2.7. After a review

* The coordinator registers each confirmed fault as a 015 entry, Kind: Fix,
  with the report's section as its source (016-01, section 6, rule 2).
* A fault that affects 2026.1 gets a line in 2026.1's post-release notes
  (W2).
* The fix follows W4's way, with H5's review, unless it changes the stream
  format or a Pub API signature or needs a design choice: then it stops for
  Frans (section 8).
* A doubt is listed in 016-02, with the report's ID. A doubt that a later
  test settles becomes a fault or is closed there.


## 3. The reviews

Tonight's reviews (section 6) are made of these areas:

| ID | Areas                 | ID | Areas                 |
|---|---|---|---|
| R1 | 3.1, H1a1             | R6 | 3.5, H1c1             |
| R2 | 3.3, H1b1             | R7 | 3.6, H1c2             |
| R3 | H3, 016-07            | R8 | 3.7 and 3.8, H1d, H2a |
| R4 | 3.2, H1a2             | S1 | 3.9, H2b              |
| R5 | 3.4, H1b2             | S2 | 3.10 and 3.11, H2c, H2d |

S2 is two areas in one review: it reads the Javadoc and the code of each
promise, not the whole of the files.

Sizes are at `df6ad50` (`git diff --numstat release-2026.1..`, lines added
plus removed). The whole of `java/src` changed in 120 files, 7,441 lines
added and 2,084 removed; about 2,250 of the 9,525 changed lines are in the
testers, which the reviews use but do not review. Paths are under
`java/src/bergdb/`. Each review reads its tests as well: `grep -rln CLASS
java/src java/src-dev java/stress` finds them.

### 3.1. H1a1: handles and the node table

* Read whole:
  * `dag/Handle.java` (146 lines, new), `dag/Node.java` (168),
    `dag/KeyNode.java` (1,886), `dag/TopNode.java` (417),
    `dag/ValueNode.java` (339), `dag/TopDs.java` (244), `dag/Pointee.java`,
    `dag/Spos.java` (144);
  * `core/NodeCollection.java` (1,263), `core/Cache3.java` (563),
    `core/Cache.java`, `core/CacheStats.java` (41, new).
* As a diff: `dag/Klong.java`, `dag/GetMany.java`, `dag/GetData.java`,
  `dag/Dag.java`, `dag/DagNodeIterator.java`, `core/StoredKeyNode.java`,
  `core/StoredTopNode.java`, `core/StoredValueNode.java`,
  `core/NodeStream.java`, `core/DagComparison.java`, and the removed
  `core/PointerLocks.java`.
* Diff: about 2,250 lines (NodeCollection 879, Cache3 529, KeyNode 204,
  Handle 146, TopNode 139).
* Intended behaviour: 009-02, sections 2 to 4 (the design; 3.3's table of
  fields and barriers; 3.4's argument for a plain read of a pointer);
  009-05, the alignment of handles with the model; `docs/levels.md`,
  section 7; 005-65's change (a reader's load does not take the eviction
  monitor); 005-08 and 005-09, the node table's earlier faults.
* Tests: `dag/DagTester`, `dag/TopTester`, `core/NodeStreamTester`,
  `core/EvictionReaderTester`, `core/DbTesterGetMany`,
  `java/stress/jcstress/*.java`.
* The reviewer's scope, in the brief: every write of a pointer, a handle's
  object and its state, and under which lock or barrier; the fast and slow
  paths of a read; a load, two loads of one node, and a load against an
  eviction; the node table's maps (insert, remove, lookup, growth); a
  stored node made into an in-memory node and back; CacheStats' counts.
* Size: L; 2.5 hours, the hard stop.

### 3.2. H1a2: eviction

* Read whole: `core/Eviction.java` (1,480), `core/Residents.java` (295),
  `core/Audit.java` (384).
* Read in part:
  * `core/Db.java`, the calls into eviction and the budget (`grep -n
    'viction\|udget\|CacheSize' core/Db.java`, 22 lines today), with
    `setCacheSizeIndicator`;
  * `pubimp/DatabaseImp.java`'s `setCacheSizeInMb`; `core/Jmx.java`'s
    cache setter.
* Context, read as needed: `dag/Handle.java`, `core/Cache3.java` (H1a1
  reviews them).
* Diff: about 1,340 lines (Eviction 1,011, Residents 255, Audit 77).
* Intended behaviour: 009-02, sections 4.7 and 4.10; 009-01's targets;
  005-51 (an idle eviction thread does not wake); 005-52 (the cache size
  while running); 005-65; 005-80 (`setBudget`'s race); `docs/levels.md`,
  section 7; 010-01, P1 (no stop-the-world) and P3 (calm when not used).
* Tests: `core/CapacityTester`, `core/EvictionReaderTester`, the eviction
  twins in `core/DbTester`, `java/stress/EvictionInvariance.java`,
  `java/stress/PauseProbe.java`.
* Scope: the eviction thread's life (start, wake, sleep, stop, failure);
  each batch and its bound; the budget's changes while it runs; the
  interplay with the writer, the readers' loads and reclaim; the resident
  lists; the audit's checks; what happens when eviction throws.
* Size: M to L; 2.5 hours, the hard stop.

### 3.3. H1b1: FileStream

* Read whole: `stream/FileStream.java` (2,180), `stream/FileStreamIo.java`
  (57), `stream/DirectoryInUseException.java` (new),
  `stream/AppendOnlyStream.java` (123),
  `stream/ReadBelowFirstPosException.java`.
* Diff: about 1,320 lines (FileStream 1,205).
* Intended behaviour: 005-46 (reads that do not wait for the writer;
  interrupts); 005-63 (one database per directory); 005-72 (the files after
  a cut); 005-19 and 005-24 (earlier faults); `docs/levels.md`, section 8;
  011-07 (Level 3's durability).
* Tests: `core/FileStreamPowerLossTester.java` (moved from `stream/`),
  `core/InterruptTester.java` (new), `java/stress/PowerLossTest.java`,
  `java/stress/InterruptStress.java`, and FileStream's own tests.
* Scope: appends, forces and the order of forces against the directory;
  new files and their names; positional reads beside appends, without a
  lock; the file list and its publication; the physical cut and the delete
  thread; the directory lock, a second process, a second database in one
  JVM, a close while another opens; interrupts during each I/O call; what is
  left after each failure.
* Size: L; 2.5 hours, the hard stop.

### 3.4. H1b2: BufferedStream and StorageManager

* Read whole: `storage/BufferedStream.java` (1,386),
  `storage/StorageManager.java` (1,296, without the replica paths),
  `storage/Constants.java`.
* Read in part: `core/Db.java`'s sync and flush paths (`grep -n
  'sync\|flush\|SyncLevel' core/Db.java`); `pub/util/SyncLevel.java` (moved
  from `core/`); the rules in `storage/` that StorageManager calls
  (`DurabilityRule`, `ErrorRule`, `MainConfirmedRule`, `MainErrorRule`), as
  needed.
* Diff: about 470 lines (BufferedStream 425, StorageManager 43), and 106 of
  `StorageManagerTester`.
* Intended behaviour: 005-48 (group commit); 005-64 (the buffer time);
  005-76 (the wake at a quarter); 005-13; 005-44 (a sync and its last
  byte); 005-35 (stop and close); 005-41 (`isDurable`); `docs/levels.md`,
  section 8; 010-01, P3.
* Tests: `storage/StorageManagerTester`, `core/DbTesterStream`,
  `core/DbTesterFailure`, `core/InterruptTester`.
* Scope: the producer and the consumer of the buffer; every wait and every
  wake; a sync that waits, and group commit; a full buffer; a failure of the
  stream under the buffer, and how it reaches the writer and the readers;
  stop and close with bytes in the buffer; interrupts.
* Size: M; 2.5 hours, the hard stop.

### 3.5. H1c1: startup and the take

* Read whole: `core/TransSeq.java` (754), `core/DbStarter.java` (915),
  `core/StartupPos.java` (45), `storage/MetaBlock.java` (314),
  `core/StoredTrans.java` (1,295).
* As a diff: `storage/RecoverableStream.java` (41 of 1,656 lines),
  `core/Trans.java`, `core/KvComparison.java`.
* Diff: about 720 lines (TransSeq 395, StoredTrans 129, DbStarter 115,
  MetaBlock 42, RecoverableStream 41), more after 005-79.
* Intended behaviour: 007-01 (the startup bound); 007-03; 007-07 (the
  paced take); 007-08 (T3 for the take, with Lean's statement `T3_take` as
  the definition); 005-49; 005-50; 005-53; 005-57 (rule 4 by position);
  005-58; 005-68; 005-74 and 005-75; 005-79 (after its commit);
  `docs/levels.md`, section 5; `docs/sis-model.md`.
* Tests: `core/DbTesterRestart`, `core/DbTester`, TransSeq's tests,
  `java/stress/RestartStress.java`, `java/stress/CrashTest.java`,
  `java/stress/RestartInvariance.java`.
* Scope: the take's decisions and their inputs; the meta blocks, the node
  size and the version checks at a start; a start's reads and the deadline;
  the records' parsers and corrupt sizes; a start after a crash at each kind
  of position. The holes of an unforced tail (014-01) are out.
* Size: L; 2.5 hours, the hard stop.

### 3.6. H1c2: Db and reclaim

* Read: the changed methods of `core/Db.java` (2,802) and
  `core/Reclaim.java` (2,212), whole, with their callers; the rest of the
  files as needed.
* As a diff: `core/KeyModSet.java`, `core/DbUtil.java`,
  `core/DbBuilder.java`, `core/DbHelper.java`, `core/DbScan.java`.
* Diff: about 620 lines (Db 376, Reclaim 156, KeyModSet 33, DbUtil 19,
  DbBuilder 19), more after 005-79 and 005-82.
* Intended behaviour: `docs/levels.md`, sections 3 and 6; 005-61; 005-70;
  005-73; 005-75; 005-82, 005-69 and 005-71 (after their commits); 005-79's
  fraction and watermark (after its commit); 011-06 (Level 3's plan).
* Tests: `core/DbTester`, `core/DbTesterFailure`, Reclaim's tester,
  `core/ReclaimReaderTester`, `core/ReclaimRetentionTester`,
  `java/stress/ReclaimStress.java`, `java/stress/ReclaimReaders.java`.
* Scope: a transaction from `execute` to its listeners; the STM check
  against KeyModSet after a start; the read paths and how a failure fails
  the database; reclaim's iterations, its spacing, its cut and the readers it
  overtakes; the retain duration and the first available lookup time; the
  setters.
* Size: L; 2.5 hours, the hard stop.

### 3.7. H1d: the Pub API and the lifecycle

* Read whole: `pub/Database.java` (350), `pub/DatabaseBuilder.java` (152),
  `pubimp/DatabaseImp.java` (374), `pubimp/DatabaseBuilderImp.java` (312),
  `pubimp/ConnectionImp.java` (333), `core/Jmx.java` (349).
* Read in part: `core/Db.java`'s start, stop, close, failure and interrupt
  handling (`grep -n 'void start\|void stop\|void close\|fail(\|nterrupt'
  core/Db.java`); `core/DbBuilder.java`.
* As a diff: `pub/Connection.java`, `pub/Transaction.java`,
  `pub/TransactionInfo.java`, `pub/ReadInterface.java`, `pub/TestClock.java`,
  `pub/Time.java`, `pub/CryptoKey.java`, `pub/Factory.java`,
  `pub/IndexBuilder.java`, `pub/Kv.java`, `pub/RwEnvironment.java`,
  `pub/package.html`, `pub/util/*.java` and `pub/util/package.html`,
  `pubimp/RwTransaction.java`, `pubimp/WTransaction.java`,
  `pubimp/IndexManager.java`, `pubimp/IndexBuilderImp.java`,
  `pubimp/OptionalIcuCollatorFactory.java`, `pubimp/Pack.java`, the
  removed `pubimp/ClockConstants.java`, `common/Util.java`,
  `stream/SalsaStream.java`.
* Diff: about 560 lines (Database 143, DatabaseBuilderImp 86, DatabaseImp
  37, Jmx 35, SalsaStream 35, DatabaseBuilder 34), and 474 of
  `PubTester` and `PubInterruptTester`.
* Intended behaviour: 005-35; 005-46 (interrupts); 005-52; 005-53; 005-55;
  005-56; 005-59 (AutoCloseable); 005-63; 005-66 (the builder opens at
  start); 005-73; `docs/levels.md`, section 3.
* Tests: `pubimp/PubTester`, `pubimp/PubInterruptTester`.
* Scope: start, stop, close and their order with the storage threads and the
  index jobs; a start that fails half-way; a second start on one directory;
  interrupts in each public call; the setters while the database runs;
  what each public method does on a failed, stopped or closed database.
* Size: M; tonight together with H2a as R8 (section 6), 2.5 hours. Best
  after A1's change of replication's Javadoc is committed (016-01, section
  4.1, item 9); if that is not in by 19:40, R8 reads the Javadoc as it is.

### 3.8. H2a: the database, connections, transactions and time

* The promises, read whole: the Javadoc of `pub/package.html`,
  `pub/Database.java`, `pub/DatabaseBuilder.java`, `pub/Connection.java`,
  `pub/Transaction.java`, `pub/TransactionInfo.java`,
  `pub/StartupInfo.java`, `pub/ReadInterface.java`, `pub/Kv.java`,
  `pub/WBuilder.java`, `pub/Action.java`, `pub/Time.java`,
  `pub/Duration.java`, `pub/TestClock.java`; `pub/util/package.html`,
  `DbException` and its subclasses, `SyncLevel`, `Clock`, `Job`,
  `JobStatus`. Not replication's methods, `StorageInfo` or
  `BadReplicaException`.
* The code: `pubimp/DatabaseImp.java`, `DatabaseBuilderImp.java`,
  `ConnectionImp.java`, `ConnectionInitializer.java`, `WBuilderImp.java`,
  `WTransaction.java`, `StartInfoImp.java`, `TimeResolver.java` (646), and
  `core/Db.java` where they call it.
* Size of the promises: about 1,700 lines of API; of the code, about 2,500
  lines and Db's parts.
* Intended behaviour: the Javadoc itself; `docs/levels.md`, sections 3 and
  8; 005-34; 005-41; 005-42; 005-43; 005-69; 005-71.
* Tonight it is part of R8, with H1d: R8 reads H1d's code and this
  Javadoc together, in 2.5 hours, and gives the Javadoc's statements of
  `Database`, `DatabaseBuilder` and `Connection` first.
* Method: each statement of the Javadoc (a return value, an exception and
  when it is thrown, a state, a time, a guarantee of durability or order)
  is a line in the report's section 4 or a finding. For each, the code that
  keeps it, and a test that checks it, if one exists (`PubTester` and its
  siblings). A statement with no test gets a small test when it is cheap;
  the report lists those tests, which can be added to the suite later.
* Size: L; 2.5 hours, the hard stop.

### 3.9. H2b: rw-transactions, encryption and JMX

These are parts that the C clone did not port (012), so no second
implementation has checked them.

* The promises: `pub/RwEnvironment.java`, `pub/Action.java`,
  `pub/Connection.java`'s rw-methods, `pub/CryptoKey.java` (225),
  `pub/util/BadCryptoKey.java`; the operations of `core/Jmx.java` and their
  descriptions.
* The code: `pubimp/RwEnvironmentImp.java` (711), `pubimp/RwTransaction.java`
  (163), `stream/SalsaStream.java` (348), `core/Jmx.java` (349); the crypto
  key's path in `DatabaseBuilderImp` and `core/DbStarter.java`; the STM
  check in `core/Db.java` (`stmCheckConflicts`, `KeyModSet`).
* Intended behaviour: the Javadoc; 005-12 (transaction outputs); 005-40 (a
  start checks the key before it writes); 005-45; 005-70; 005-81 as a
  description of today's retries (its proposals are not for 2026.2); 005-20.
* Scope: an Action's reruns, its read set, a conflict, the retry and its
  sleeps, an exception from the Action, an Action that never ends; the
  cipher's key, nonce and position for each byte, a wrong key, a stream cut
  at any byte, `getLength`; each JMX operation on a running, stopped and
  failed database.
* Size: M to L; 2.5 hours, the hard stop.

### 3.10. H2c: indexes

* The promises: `pub/IndexBuilder.java` (236), `pub/UseIndexBuilder.java`
  (160), `pub/UsePrimaryBuilder.java` (124),
  `pub/IndexAlreadyExistsException.java`, `pub/NoSuchIndexException.java`,
  `pub/MissingKeyFieldException.java`; `Connection`'s index methods;
  `pub/util/Job.java` and `JobStatus.java` for index jobs.
* The code: `pubimp/IndexManager.java` (1,024), `IndexBuilderImp.java` (604),
  `UseIndexBuilderImp.java` (807), `UsePrimaryBuilderImp.java`,
  `FieldIndexFunction.java` (239), `IndexFunction.java`,
  `IndexEntryBuilder.java` (202), `PubKeys.java` (242), `Entries.java`,
  `KCollator.java`, `PrimaryKeyCollator.java`, `UnicodeCollator.java`,
  `CollatorFactory.java`, `BergCollatorFactory.java`,
  `OptionalIcuCollatorFactory.java`, `IcuInfo.java`.
* Intended behaviour: the Javadoc; 005-15 (range scans); 005-21; 005-26
  (lone surrogates).
* Tests: `pubimp/PubTesterIndex` (2,157), `PubTesterPrimary`,
  `PubTesterComposite`, `PubTesterNestedFields`.
* Scope: an index built while writes go on, and its job; a restart during a
  build; range scans at the ends and across key types; collation with and
  without ICU; an index and its primary data after an rw-transaction rerun;
  an index removed and made again.
* Size: L; 2.5 hours, the hard stop.

### 3.11. H2d: objects and values

* The promises: `pub/Factory.java`, `pub/Kv.java`,
  `pub/ObjectCreationException.java`, `pub/DataFormatException.java`, and
  what `pub/package.html` and `Connection` say of objects.
* The code: `pubimp/DbObject.java` (1,085), `DbValue.java` (517),
  `DbArray.java` (344), `DbString.java`, `DbByteArray.java`, `DbInt.java`,
  `DbLong.java`, `DbDouble.java`, `DbBoolean.java`, `Data.java` (219),
  `ClassToObject.java`, `ObjectFactory.java`, `BlankConstructorFactory.java`,
  `KvToObjectImp.java` (218), `KvToObjectConverter.java`, `FieldRef.java`,
  `PubUtil.java` (232), `PackForPub.java`.
* Intended behaviour: the Javadoc; 005-22 (narrowing); 005-23 (deep
  objects); 005-26.
* Tests: `pubimp/DbObjectTester` (1,257), `PubTesterOutput`, `PubTester`.
* Scope: each Java type to bytes and back, at its limits; null, empty,
  nested, cyclic and very large values; a stored value read into another
  field type; a class changed between a write and a read.
* Size: M to L; 2.5 hours, the hard stop.


## 4. The reviewer's brief

The coordinator gives this text, with ID, TITLE, BASE, FILES and the
section of section 3 filled in, as the agent's prompt, at effort xhigh:

```
You review BergDB's code for faults: review ID, TITLE, of bergdb item 016
(release 2026.2). Repo /Users/f/fl/repos/bergdb (the main tree, shared;
do not build or test there). Read AGENTS.md, items/readme.md and
docs/levels.md first.

The code: commit BASE. Work in /Users/f/fl/bench/016/ID/ as below
(clone, checkout, build, diff). Your area, files and entries:
[the section of 016-06, section 3, pasted here]

Find faults: places where the code does not do what the entries, the
Javadoc or docs/levels.md say, or where it can lose or invent data,
return a wrong answer, hang, fail the database when it should not, or
not fail it when it should. Read the diff and the whole files; follow
calls out of your files as far as you need.

Do not read items/016-release-2026-2/ (this brief is all you need from
it), items/015-todo/, or other reviews. Replication and the holes of an
unforced tail at a start (014-01) are out of scope; note a fault met
there in one line.

Each fault must be verified: a test that fails on BASE, a probe, or,
for a race, the interleaving written out step by step with the locks
and the happens-before edges. Anything not verified is a doubt.
Tests up to about a second, probes up to a minute; no gates, no level
scripts, no timed runs: other agents use the machine.

Write your report to items/016-release-2026-2/06-reviews/ID.md in the
main tree, in the form of 016-06, section 2.5 (read only that section
of 016-06), and its tests and probes to 06-reviews/ID/. Write nothing
else in the main tree. Do not stage or commit. The header says
"Created YYYY-MM-DD by Frans Lundberg."

For R1, R2, R4 and R5: also the report's section 6, "Shared fields":
every field or object of your files that more than one thread uses.

Hard stop: HH:MM by date. Write the report as you go; before the stop,
it is complete, with what is unchecked in its section 1. Your final
message: the report's path, the faults (one line each), the number of
doubts, the times.
```

The brief names section 2.5 of 016-06 as the one part of 016 the agent
reads. The hard stop is the start plus 2.5 hours, and never later than
22:10.


## 5. The verifier's brief

```
You verify findings of a code review of BergDB, bergdb item 016. Repo
/Users/f/fl/repos/bergdb (shared; do not build or test there). Read
AGENTS.md and items/readme.md first.

The code: commit BASE. Clone it to /Users/f/fl/bench/016/verify-N/repo
and build it (sh java/build.sh). The findings, each with its
attachments in items/016-release-2026-2/06-reviews/ID/:
[each finding's section, pasted here]

For each finding: if it has a test or probe, apply and run it; check
that it fails for the stated reason, that it uses BergDB as its
contract allows, and that the behaviour is against the cited entry or
Javadoc (read them). If it is an interleaving, walk each step against
the code at BASE: is the step reachable, are the locks as stated, are
the happens-before edges as stated under the Java Memory Model, is
the end state wrong? Write a test that forces it if you can.

Verdict per finding: confirmed, refuted (with the step or reason) or
unclear. Do not read items/016-release-2026-2/ beyond the findings
above, nor items/015-todo/. Tests up to about a second; no gates.

Write items/016-release-2026-2/06-reviews/verify-N.md: one section per
finding, the verdict first, then the reasons and the commands. Write
nothing else in the main tree; do not stage or commit. Header:
"Created YYYY-MM-DD by Frans Lundberg." Hard stop: HH:MM by date.
Final message: each finding's verdict in one line.
```


## 6. Tonight's schedule

At most 4 agents at a time for all of the release's work, the fixes
included (016-01, section 8). The reviews take the slots in this order, as
they free:

| Order | ID | Area                                    | Why here                              |
|---|---|---|---|
| 1     | R1 | handles and the node table              | the largest new mechanism (009)       |
| 2     | R2 | FileStream                              | the largest diff, 1,205 lines         |
| 3     | R3 | threads and lifecycle (016-07)          | its jcstress tests must run by 01:30  |
| 4     | R4 | eviction                                | 1,011 changed lines, a thread of its own |
| 5     | R5 | BufferedStream and StorageManager       | 005-76 is not yet in a night run      |
| 6     | R6 | startup and the take                    | after 005-79's Java commit, if in     |
| 7     | R7 | Db and reclaim                          | after 005-82's commit, if in          |
| 8     | R8 | the Pub API, the lifecycle, H2a         | after A1's replication Javadoc, if in |
| 9     | S1 | rw-transactions, encryption, JMX        | stand-by                              |
| 10    | S2 | indexes and objects                     | stand-by                              |

The times, from `date`:

* **16:50**: R1 to R4 start, as far as slots are free. A slot that a W4
  fix holds goes to the next review when the fix ends.
* **About 19:20**: R1 to R4 end (hard stop 2.5 hours). R5 to R8 start in
  their slots.
* **19:40, the last start.** A review not started by 19:40 is not started
  tonight: it would end after 22:10. It goes to section 7's list.
* **From about 19:20**: the coordinator reruns round 1's failing tests
  (section 2.6). A confirmed fault that loses data, invents data or hangs
  gets its fix at once, in the next free slot, before S1 and S2.
* **About 22:00**: every report is in. One verifier takes all the faults
  that are interleavings, and the tests that the coordinator doubts, about
  22:00 to 23:00.
* **22:00 to 01:00**: the fixes, in up to 4 slots (section 8, step 6).
* **01:00**: no new fix starts. A confirmed fault that is not fixed by then
  goes to Frans: a known issue of 2026.2, or the release waits (section 8,
  step 5).
* **About 01:45**: the release commit (016-01, section 8; 016-02).

The sizes: 8 reviews of 2.5 hours, 20 agent-hours, in 16:50 to 22:10, with
4 slots: about 21 slot-hours. It fits only if W4's fixes hold few slots
after 16:50. The coordinator keeps the order above; what does not start by
19:40 is listed, not squeezed.


## 7. Decision for Frans: what of the search is left out tonight

Tonight's schedule has no room for all of 016-01, section 6's reviews.

* **A. Eight reviews tonight, S1 and S2 after the release** (recommended).
  The changes since 2026.1 (H1) and the concurrency (H3) are reviewed in
  full; of H2, the promises of `Database`, `DatabaseBuilder` and
  `Connection` (in R8). Left for after the release: rw-transactions and
  their retries, encryption, JMX, the indexes and the objects. These are
  the parts that the C clone did not port, but they changed little since
  2026.1 (about 90 lines of the diff). The notes say "not reviewed for
  2026.2" in their known issues.
* **B. Ten reviews tonight**: S1 and S2 start at 16:50 in place of the
  fixes, and the fixes start later. Fewer of tonight's faults are then
  fixed by 01:00.
* **C. The release a day later**, with all eleven areas of section 3 as
  separate reviews (about 38 agent-hours), and their fixes.

The coordinator goes on with A unless Frans says otherwise; the choice is
a line in 016-02's "For Frans to decide". If a slot frees before 19:40,
S1 starts, then S2.


## 8. Steps

Each step: what; the files; the commands; the check; who; when; the size;
the stop for Frans.

1. **Prepare.** Create `06-reviews/` with a `readme.md` that lists the
   reports as they come: one line each with the ID, BASE, the faults, the
   doubts and the verdicts. Files: `06-reviews/readme.md`. Check: the file
   exists. Who: the coordinator. When: before 16:50. Size: 5 minutes. No
   stop.
2. **Start a review.** For each ID of section 6, in order: take BASE
   (section 2.1), fill in the brief (section 4) with the area of section 3
   and a hard stop of the start plus 2.5 hours, start the agent at xhigh,
   and write the row in section 9. Files: section 9; 016-02's agent list.
   Check: `git -C /Users/f/fl/bench/016/ID/repo rev-parse HEAD` is BASE.
   Who: the coordinator. When: 16:50, then as slots free, never after
   19:40. Size: 10 minutes each. No stop.
3. **Take the report.** When the agent ends: the report has section 2.5's
   form; every fault has evidence (a file in `ID/`, or an interleaving); its
   section 7 cites no forbidden file. A report that misses these goes back
   to the same agent once (SendMessage), if its time allows. Files:
   `06-reviews/ID.md`. Check: by reading. Who: the coordinator. Size: 15
   minutes. No stop.
4. **Verify.** A failing test or probe: rerun it in the coordinator's own
   clone at BASE and read the failure (section 2.6). An interleaving, or a
   doubted test: the verifier at about 22:00 (section 5). Copy each verdict
   into the finding's title. Files: `06-reviews/verify-N.md`,
   `06-reviews/ID.md`. Check: each fault has a verdict. Who: the
   coordinator, and the verifier agent. When: a test at once; the verifier
   at 22:00, earlier if a slot is free. Size: 5 minutes a test; about 1
   hour for the verifier. No stop.
5. **Register.** Each confirmed fault: a 015 entry, Kind: Fix, citing
   `016-06/ID, ID-Fn`; a line in W2's list if it affects 2026.1. Files:
   `items/015-todo/`. Check: the entry is in 015's table. Who: the
   coordinator. When: at once after the verdict. Size: 10 minutes each.
   **Stop for Frans** if the fix changes the stream format or a Pub API
   signature or needs a design choice (016-01, section 6, rule 3), or if
   it is not fixed by 01:00: `news.sh "needs a look"`, and a line in
   016-02's "For Frans to decide".
6. **Fix.** W4's way: a scratch clone, the fix and its test (the finding's
   test, which now passes), `before-commit.sh` (`BEFORE COMMIT OK`, the
   only gate needed, Frans 15:40), H5's review by another agent, the
   commit by the coordinator. Files: as the fix needs, and the 015 entry.
   Check: `BEFORE COMMIT OK` on the combined tree; the review's answers in
   the entry. Who: an agent; the coordinator commits. When: 22:00 to 01:00,
   a fault that loses data or hangs earlier. Size: by the fault.
7. **Close.** At about 01:00: the counts in `06-reviews/readme.md`; the
   doubts and the unfixed faults in 016-02; this file's State. Check:
   section 10. Who: the coordinator. Size: 20 minutes.


## 9. State

2026-11-03, 19:50. R1 by a Claude agent; R2 to R6 on Codex (GPT-6.1 Sol,
effort max), at Frans's suggestion at 18:04, with this plan's brief and in
clones of their own; R3's first session was ended at 18:27 by the
service's content filter and continued from its report in a second one.
Codex reached its usage limit at 19:20, so R4, R5 and R6 stopped early and
continue after 23:06; R7 and R8 follow if its quota allows. The last start
of 19:40 (section 6) holds for Claude's reviews; a review on Codex ends
within about an hour.

| ID | Base | Agent | Started | Report | Faults | Doubts | Verified by |
|---|---|---|---|---|---|---|---|
| R1 | `6f932f0` | Claude | 15:59 | [R1](06-reviews/R1.md) | 4 | 2 | R1-F1, F2, F4 by test; F3 pending |
| R2 | `b9ba427` | Codex | 18:06 | [R2](06-reviews/R2.md) | 5 | 1 | verify-1 (F1, F5); F2 to F4 pending |
| R3 | `b9ba427` | Codex | 18:06 | [r3](07-concurrency/r3.md) | 12 | 4 | verify-1 (F1 to F3, F8, F9, F12) |
| R4 | `b9ba427` | Codex | 19:15 | stopped 19:20, continues 23:09 |  |  |  |
| R5 | `b9ba427` | Codex | 19:15 | stopped 19:21, continues 23:09 |  |  |  |
| R6 | `b9ba427` | Codex | 19:15 | stopped 19:20, continues 23:09 |  |  |  |
| R7 |      |       |         |        |        |        |             |
| R8 |      |       |         |        |        |        |             |
| S1 |      |       |         |        |        |        |             |
| S2 |      |       |         |        |        |        |             |

Unfinished in this plan: nothing that blocks R1. Section 7 waits for Frans;
the coordinator goes on with A meanwhile.


## 10. Done when

* R1 to R8 are in `06-reviews/`, in section 2.5's form, each on a recorded
  BASE; S1 and S2 too, or listed as left out by section 7's decision.
* Each fault has a verdict; each confirmed fault has a 015 entry and is
  fixed, or is a known issue or a wait by Frans's decision.
* Each doubt is listed in 016-02.
* `06-reviews/readme.md` lists the reports with their counts, and this
  file's status is done.
