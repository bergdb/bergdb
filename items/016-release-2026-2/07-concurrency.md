016-07. Plan: concurrency, H3
=============================

Created 2026-11-03 by Frans Lundberg.

**Status: planned, not started.** The detailed plan of 016-01, section 6's
H3: 005-07's questions 1 and 2 for today's code. Cut to fit tonight's run
(Frans, 15:40: "try your best to finish this work by 07:00 tomorrow in the
morning"); the reviews' schedule is 016-06, section 6.


## 1. In short

* **The question** (005-07, questions 1 and 2): write down the
  synchronization as it is (the threads, the locks and monitors, what each
  protects, the publication points, the go point of a transaction), and
  check it: is each shared field accessed under the right lock or
  published correctly, under the Java Memory Model?
* **The split** (section 3):
  * the fields inside an area are read by the area's review: R1 (handles
    and the node table), R2 (FileStream), R4 (eviction) and R5
    (BufferedStream and StorageManager) each write a "Shared fields"
    section (016-06, section 2.5);
  * one review of its own, **R3**, reads what lies between the areas: the
    writer's and the readers' protocol in `Db`, every thread's life from
    start to close and failure, the locks' order, and the setters. It
    starts at 16:50 with the first round (016-06, section 6).
* **The start**: 009-02's reading of the fast path (sections 2.5 and 3),
  which R1 and R3 both read first.
* **The output**: R3's report `07-concurrency/r3.md`, with the map of
  threads, locks and publication points; the fields in R1's, R2's, R4's
  and R5's reports. The merged design document is after the release
  (section 6, step 7).
* **jcstress** (section 5): tests for the publications that have none,
  written in the fix window by one agent, and run by 016-08 on F53 and s1
  by about 01:30.
* **Findings** follow 016-06, sections 2.4 and 2.6: a race is an
  interleaving written out and checked by a verifier; a deadlock is the
  cycle of locks written out with its code lines, or a test that hangs.


## 2. What there is to read

The threads of today's code (`grep -n 'new Thread' java/src`, without the
testers), at `df6ad50`:

* **The callers**: any number of reader threads (`Db.getOne`, `getMany`,
  `getTrans`, the scans) and the writer (`Db.execute`, under the write
  lock).
* **The buffer's consumer**: `storage/BufferedStream.java`, the
  `consumer` thread, which writes the buffer to the stream below.
* **The cut's delete thread**: `stream/FileStream.java`, `cutThread`, which
  deletes the files below reclaim's physical cut.
* **The evictor**: `core/Eviction.java`, `bergdb-evictor`.
* **The closer**: `core/Db.java`, the thread that `stop()` starts to close
  in the background (005-35).
* **The index jobs**: `pubimp/IndexBuilderImp.java` (a build) and
  `pubimp/DatabaseImp.java` (a removal of an index's entries).
* **JMX's monitor**: `core/Jmx.java`, `DBMonitor.MThread`.
* **Out of scope**: replication's sync thread (`core/DbHelper.java`),
  by Frans's decision (016-01, section 3).
* No finalizers since 005-55.

The constructs per file (`synchronized`, `volatile`, atomics and CAS),
counted at `df6ad50`, without the testers:

* the most: `core/Db.java` (49 synchronized, 12 volatile),
  `core/Eviction.java` (25, 5), `stream/FileStream.java` (20, 14, 6
  atomics), `storage/BufferedStream.java` (18, 3), `core/Cache3.java` (15,
  0, 4), `storage/StorageManager.java` (11, 5, 14), `dag/KeyNode.java` (13,
  5, 2), `pubimp/IndexManager.java` (13), `core/NodeCollection.java` (9, 5,
  2);
* also: `core/Reclaim.java`, `core/DbClock.java`, `core/Residents.java`,
  `core/Audit.java`, `core/Jmx.java`, `core/StartupPos.java`,
  `core/StoredTrans.java`, `dag/Handle.java`, `dag/TopNode.java`,
  `dag/TopDs.java`, `dag/ValueNode.java`, `pubimp/DatabaseImp.java`,
  `pubimp/IndexBuilderImp.java`, `stream/SalsaStream.java`,
  `stream/MemoryStream.java`, `stream/CutStream.java`,
  `common/EventToWaitFor.java`.


## 3. The split

### 3.1. Inside the areas: the "Shared fields" sections

* What: every field or object of the area's files that more than one
  thread uses, one item each, in the form of 016-06, section 2.5, report
  section 6.
* Who: the area's reviewer, as part of its review: R1 (`dag/`,
  `NodeCollection`, `Cache3`), R2 (`FileStream`), R4 (`Eviction`,
  `Residents`), R5 (`BufferedStream`, `StorageManager`).
* When: in the review's 2.5 hours; the brief asks for it (016-06, section
  4).
* Checked: the coordinator checks that the section exists and names a test
  or "none" for each item.

### 3.2. Between the areas: R3

* **The area**, in R3's brief in place of 016-06, section 3:
  1. The writer's and the readers' protocol: `Db.execute`, `executeInner`,
     the warm-up, the write lock, `readSync`, `DbClock`, `KeyModSet`, the
     go point; `getOne`, `getMany`, `getTrans` and the scans; reclaim's
     admission of readers and their expiry; `StartupPos` and the setters
     of 005-53 on the fly.
  2. Every thread of section 2, from its start to its end: who starts it,
     what it touches, how it waits and wakes, what it does when the
     database fails, stops or closes under it, and how `close()` waits for
     it. Interrupts in each (005-46).
  3. The boundaries: how a failure in one thread reaches the others; the
     order in which the locks and monitors are taken, and any cycle; the
     setters (cache size, startup distance, retain duration, reclaim's
     fraction) called from any thread while the others run.
* **The files**:
  * read for their concurrency: `core/Db.java`, `core/DbClock.java`,
    `core/KeyModSet.java`, `core/StartupPos.java`, `core/Reclaim.java` (the
    admission and the cut's publication), `core/Jmx.java`,
    `pubimp/DatabaseImp.java`, `pubimp/IndexBuilderImp.java`,
    `pubimp/IndexManager.java`, `common/EventToWaitFor.java`;
  * read for their threads' start, stop and failure only (their fields are
    R2's, R4's and R5's): `core/Eviction.java`, `storage/BufferedStream.java`,
    `storage/StorageManager.java`, `stream/FileStream.java`;
  * the promises: what `pub/Database.java`, `pub/Connection.java` and
    `pub/package.html` say of threads.
* **The entries**: 009-02, sections 2.5, 3.1 to 3.4 and 4.4 (read first);
  005-07 (the design so far, from F1-007 and the code); 005-35, 005-46,
  005-48, 005-51, 005-53, 005-55, 005-65, 005-76, 005-80; `docs/levels.md`,
  section 3; 010-01, P1 and P3.
* **Not given**: 016-01, the other reviews' reports, 015 (016-06, section
  2.3).
* **The report**: `items/016-release-2026-2/07-concurrency/r3.md`, in the
  form of 016-06, section 2.5, with four sections added after its section
  2, "Faults":
  * **Threads**: one item per thread: who starts it and when; what it
    reads and writes; how it waits and is woken; how it ends; what it does
    on a failure, a stop, a close, an interrupt.
  * **Locks and monitors**: one item each: what it protects; who takes it;
    which others are taken inside it (the order); whether any path takes
    them in another order.
  * **Publication points**: one item each: the writes before it, the reads
    after it, the happens-before edge (a monitor's release and acquire, a
    volatile write and read, a CAS, a thread's start or join, a final
    field).
  * **The go point**: where a transaction can no longer fail without
    failing the database, and what is checked before it.
  * And, last, **Tests to add**: the publications and waits of R3's area
    that no test checks, each in section 5's form.
* **Size**: L; 2.5 hours, the hard stop (016-06, section 6).


## 4. The rule for findings

As 016-06, sections 2.4 and 2.6:

* A race is an interleaving written out, each step naming the thread, the
  code line, the locks held and the edge that is missing, and checked by
  the verifier agent at about 22:00. A test that forces it is better.
* A deadlock is the cycle written out (thread A holds L1 at line x and
  waits for L2 at line y; thread B the reverse), checked the same way, or a
  test that hangs within a timeout.
* A lost wake is the interleaving of the check, the wait and the notify,
  with the timeout that ends it (a wait with a timeout loses time, not
  liveness: the report says which).
* Not verified: a doubt.


## 5. The jcstress tests

### 5.1. What there is

* `java/stress/jcstress/`: `HandlePublication`, `InstallPublication`,
  `EvictionRace`, `ValuePublication` (009-02, sections 3.4 and 3.5), and
  the control `PlainPublication`; `run.sh JCSTRESS_DIR [MODE [JAR]]`.
* They ran in default mode on step 3c on F53 and on s1 (2026-10-25; s1 from
  22:16 to 22:32), and on F53 on the branch's final `fb0c770` (2026-10-26,
  01:25), with no forbidden outcome (009-03, section 2). Not since: not
  after 005-65's change of the eviction thread's wake (`988fe1a`), nor
  005-76's change of `BufferedStream`.
* 009-02, section 3.5 planned two more that were not made: a re-resolve
  against an eviction, and two loaders of one node.
* 016-08 runs the five on today's code at once (its step F1).

### 5.2. The candidates

To be confirmed or dropped by the readings (R1 to R5); each needs a
publication that rests on a volatile, a final field, a monitor or a CAS
between two threads, and that can be built from a few BergDB objects
without a `Db`:

1. **The file list** (005-46, item 3): FileStream's immutable list of files
   in a `volatile` field, which `findFile` and `getFirstPos` read without a
   lock. A writer installs a new list with a new file; a reader sees either
   the old list, or the new one with the new file's fields set. Forbidden:
   the new file with a field unset.
2. **The length a read may read** (005-46, item 1): a file's `volatile`
   length, which `append` sets after its write. If a read is ever served
   from memory (a write buffer), the test: a length that covers bytes that
   the reader then does not see is forbidden. If every read goes through
   the file channel, the OS's page cache orders it and jcstress cannot
   isolate it: R2 says which, and the case stays with `InterruptStress` and
   the unit tests.
3. **The wake at a quarter** (005-76): a `Mode.Termination` test: the
   consumer waits with a long buffer time; an append takes the buffer past
   a quarter; the consumer must wake (the test ends), and a stale run is
   forbidden. If a `BufferedStream` per jcstress instance is too dear (a
   thread each), a unit test instead, with a buffer time of 10 s and a
   limit of 1 s, that places the append between the consumer's check and
   its wait.
4. **The evictor's wake** (005-51, 005-65): the same, for the eviction
   thread.
5. **A re-resolve against an eviction**, and **two loaders** (009-02,
   section 3.5).
6. Each item of R1's, R2's, R3's, R4's and R5's reports marked "test: none"
   that meets the condition above.

### 5.3. The rule

* What: one jcstress test per confirmed candidate, at most four tonight,
  in the order of section 5.2; the rest are listed in 016-02 for after the
  release.
* Each test's header says what it checks and cites the entry (`bergdb
  005-46, item 3`), as the five do; each outcome has its reason.
* When: 22:00 to 23:30, in the fix window (016-06, section 6).
* Who: one agent, the jcstress agent (section 5.4), in
  `/Users/f/fl/bench/016/jcstress/`. It is not a reviewer: it gets the
  readings' "Tests to add" and "test: none" items, copied by the
  coordinator.
* Checked:
  * `stress/jcstress/run.sh DIR sanity` passes and lists every new test (a
    few minutes; DIR in 016-08, section 4);
  * then 016-08's default runs on F53 and s1 (about 30 and 20 minutes);
  * a forbidden outcome is a fault, verified by jcstress's own count; the
    verifier checks that the outcome is rightly forbidden.
* The tests are code in `java/stress/jcstress/`. `build.sh` does not compile
  them, so they cannot break `before-commit.sh`; the coordinator commits
  them after the sanity run and H5's review, with the fixes.

### 5.4. The jcstress agent's brief

```
You write jcstress tests for BergDB, bergdb item 016 (release 2026.2).
Repo /Users/f/fl/repos/bergdb (shared; do not build or test there).
Read AGENTS.md, items/readme.md, items/009-handles/02-implementation-
plan.md sections 3.3 to 3.5, items/016-release-2026-2/07-concurrency.md
section 5, and the five tests and run.sh in java/stress/jcstress/.

Work in /Users/f/fl/bench/016/jcstress/: clone the repo, check out
BASE, build (sh java/build.sh). The jcstress jars are in JDIR.

The publications to test, from tonight's readings:
[the "Tests to add" and "test: none" items, pasted here]

Write at most four tests, in the order of 016-07, section 5.2, in the
style of the five (header comment with the entry, @Outcome with a
reason each), against BergDB's real classes. Run
"sh stress/jcstress/run.sh JDIR sanity" from java/; it must list each
new test with no forbidden outcome. Do not run the default or tough
mode: 016-08 does.

Copy the tests to items/016-release-2026-2/07-concurrency/jcstress/
in the main tree, and write 07-concurrency/jcstress.md: each test, what
it checks, the sanity run's lines. Nothing else in the main tree; do
not stage or commit. Header: "Created YYYY-MM-DD by Frans Lundberg."
Hard stop: 23:30 by date. Final message: the tests, the sanity result,
and the publications left without a test.
```


## 6. Steps

Each step: what; the files; the commands; the check; who; when; the size;
the stop for Frans.

1. **R3 starts.** The coordinator fills in 016-06, section 4's brief, with
   section 3.2 above pasted as the area, ID `R3`, the clone
   `/Users/f/fl/bench/016/R3/`, and, in place of the brief's paths, the
   report `items/016-release-2026-2/07-concurrency/r3.md` and its
   attachments in `07-concurrency/r3/`; the report's added sections are
   those of section 3.2. Effort xhigh; hard stop 2.5 hours. Files:
   `07-concurrency/` (made by the agent). Check: the clone is at BASE.
   When: 16:50, third in order (016-06, section 6). Size: 2.5 hours. No
   stop.
2. **The briefs of R1, R2, R4 and R5** ask for their "Shared fields"
   (016-06, section 4). Who: the coordinator. When: as each starts. Check:
   each report has its section 6.
3. **R3's report.** The coordinator takes it as 016-06, section 8, steps 3
   to 5; the interleavings go to the verifier at 22:00. When: about 19:20.
   Stop for Frans: as 016-06, step 5.
4. **The jcstress agent.** The coordinator copies the "Tests to add" of R3
   and the "test: none" items of R1, R2, R4 and R5 into section 5.4's
   brief, with BASE (`main` at 22:00) and JDIR. Files:
   `07-concurrency/jcstress/`, `07-concurrency/jcstress.md`. Check: the
   sanity run's lines in `jcstress.md`. When: 22:00, in a fix slot. Size:
   1.5 hours. No stop.
5. **The default runs.** 016-08, steps F6 and L5: the new tests with the
   five, on F53 and on s1. When: 23:30 to 00:30. Check: no forbidden
   outcome; the control sees its race on F53.
6. **The commit.** The new tests into `java/stress/jcstress/`, after H5's
   review, with a fix commit or one of their own; `before-commit.sh` on the
   combined tree. Who: the coordinator. When: by 01:00. A forbidden outcome
   is a fault: fixed by 01:00, or a stop for Frans (016-06, section 8,
   step 5).
7. **After the release, not in its path**: `07-concurrency/design.md`, the
   map of today's synchronization, merged from R3's sections and the four
   "Shared fields" sections; 005-07's log gets a line that its questions 1
   and 2 are answered for 2026.2's code here, and that questions 3 and 4
   stay open. A new document is a subitem, not a file in `docs/`
   (AGENTS.md), so 005-07's "a document in `docs/`" becomes this file.
   Who: one agent. Size: about 1.5 hours.


## 7. State

**Not started** (2026-11-03, when this plan was written). A fresh agent
resumes here:

| Step | What                         | Status      | Output                       |
|---|---|---|---|
| 1    | R3                           | not started | `07-concurrency/r3.md`       |
| 2    | Shared fields of R1, R2, R4, R5 | not started | 016-06's reports, section 6 |
| 3    | R3's findings verified       | not started | `06-reviews/verify-N.md`     |
| 4    | jcstress tests written       | not started | `07-concurrency/jcstress.md` |
| 5    | default runs, F53 and s1     | not started | 016-08's State               |
| 6    | tests committed              | not started | the commit                   |
| 7    | design.md, after the release | not started | `07-concurrency/design.md`   |

Unfinished in this plan: section 5.2's candidates are a guess until the
readings confirm them.


## 8. Done when

* R3's report is in, with its sections on threads, locks, publication
  points and the go point; R1, R2, R4 and R5 have their "Shared fields".
* Each fault of them has a verdict, and each confirmed one is fixed or with
  Frans (016-06, section 8).
* The new jcstress tests ran in default mode on F53 and s1 with no
  forbidden outcome, or their fault is fixed or with Frans; they are
  committed.
* For after the release: `design.md`, and 005-07's log line.
