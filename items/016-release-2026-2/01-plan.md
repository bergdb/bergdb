016-01. Plan: release 2026.2
============================

Created 2026-11-03 by Frans Lundberg, from his request: "Create bergdb
item 016-release-2026-2. This is for planning
the 2026-2 release. The scope of it and the work needed." Revised the same
day, at max effort (14:50 and 15:01): "Create item 016-01.
This collects known bugs and other issues that should be resolved before
the release. Create the item, then create a list of all unsolved issues
that should potentially be resolved before release. We do not want unknown
bugs in the release. Make a proposal for items to fix before the release.
Read 005 for open items to fix." Then: "You are one step ahead of me, you
created a plan already. In subitem 01. Great! Now, review your plan. You
now have Max effort level.", with his decisions (section 10).

**Status: decided, in progress.** Frans decided D1 to D6 on 2026-11-03
(section 10), answered Q1 to Q4 at 15:27 and limited the release to Java
at 15:31 (section 10). The coordinator started the work at 15:27; its run
is 016-02.


## 1. The goal

BergDB 2026.2 is an internal release (D1). It is the first release with
handles (009) and with bounded startup for BergDB's own take (007-07,
007-08). It is made as 2026.1 was (008-01): a tag, the jar, the source,
the Pub API's Javadoc, release notes, the gates and tests on the final jar,
and numbers against 2026.1, with both jars run in turns.

"We do not want unknown bugs in the release" (Frans). So before the
release:

* every known fault is fixed, or listed as a known issue by decision
  (section 4);
* the code gets a search for unknown faults, and each fault found is
  fixed or listed (section 6).

A search cannot prove that no faults are left. Section 6 says what it
covers and what it does not.

The work is done unattended. One coordinator session (013-02) of Claude
(Opus 5.5) does it, through subagents (D5; section 8).

Done when:

* the tag `release-2026.2` is set and `releases/2026.2/` is committed;
* `releases/next.md` is folded into the release notes and emptied;
* 2026.1's post-release notes list the faults found since that affect
  2026.1;
* every issue of section 4.1 is closed, and every issue of 4.2 is in the
  notes' known issues;
* section 6's search is done, and each of its findings is closed or in
  the notes with Frans's agreement;
* the stream format is unchanged, or changed only with Frans's explicit
  approval (section 3).


## 2. Where main stands, 2026-11-03

* There are 245 commits since `release-2026.1` (2026-10-25), up to
  `9d34ac1` (15:08), Frans's commit of the open work. `main` is clean and
  pushed. 43 of those commits touch `java/src`: 120 files, 7,441 lines
  added and 2,084 removed.
* `night.sh` passed every scheduled night since 2026-10-30. The last run
  was on `afc3d20` (2026-11-03). No night has run yet on `9d34ac1`, which
  adds 005-76's change to `BufferedStream`.
* Props, 2026-10-28 (007-07, section 12):
  * MEM: about 130 bytes per KV, against 191 at 2026.1. `level1.sh`'s
    limit was lowered to 131 (`5dda08b`).
  * CORE: about 0.24, against 0.29.
  * SS: 1.51, against 1.50. The limits were raised after 007-07
    (`b68bb55`).
* Databases of 2026.1 are refused (005-50), with no migration (Frans:
  "No need to consider "today's databases". There are none.").
* Tested on JDK 27, on macOS (F53):
  * F53 and s1 have no JDK 17 (checked 2026-11-03), though README.md says
    that BergDB needs JDK 17 or later.
  * s1 (Linux) has run benchmarks and probes. No run of the unit tests,
    the f-tests or the level scripts on Linux is recorded. 011-07 audited
    `fsync` in a Linux VM.

2026.1's known issues (its readme, "Known issues and limits"):

* **The sweep's stop-the-world**: gone with handles (009). Eviction runs in
  batches of at most 2 ms. 009's target 2 is met in P4's soak and in the
  pause probe. 005-65's case with 8 readers has a fix in `main`
  (`52aeb04`). Frans accepted the rest of it as a full machine. Its rerun
  is still to be made (section 4.1).
* **The read path's cap at about 2 million gets a second**: gone. In
  memory, 4.2 million gets a second with 8 threads, where 2026.1 stops at
  2.1 (009-03, on the branch at step 3d).
* **Writes at scale**:
  * The stream's growth came from the startup distance of 10 MB (005-38).
    Index writes are now in proportion to each commit (005-49, 007-07).
  * The default of 50 MB suits up to about 10M keys; from there, 200 to
    1000 MB do (010-01, P10, a deviation).
  * The collapse of loads on s1's disk when the index is larger than the
    budget (under 100 puts a second at 30M keys) was measured with the
    sweep, and has not been measured again. W7 runs the 10M load in
    turns.
* **A cold start of minutes at 10M keys on s1**: rule 4 by position
  (005-57, part 1) took it from 214 s to 46 s in the prototype. Part 2 was
  not made, by Frans's choice.
* **Startup not bounded for BergDB's own take**: 007-07 put the deadline
  into the code. T3 for the take is proved (`T3_take`, 007-08); T4 is not.
* **`BufferedStream` did not wake its consumer**: 005-76, in `main` since
  `9d34ac1`.
* **Replication**: unchanged, and out of this release (section 3).
* **Power loss on real hardware**: not established. A new fault class was
  found since: holes in an unforced tail can refuse a start or fail a
  later read (005-83, moved to 014-01). It is out of this release.
* **Tested on JDK 27 only**: still true, now with Java 17 as the stated
  minimum (`bb7e189`).
* **The documentation is not reviewed for users**: still true. This is an
  internal release.


## 3. Rules for the release work

* **The stream format stays.** Frans: "Keep the stream format the same,
  unless I (Frans) explicitely approve changes."
  * The format is the layout and meaning of what a start reads: the meta
    blocks, record headers and records, the node encodings, reclaim's
    table, the version numbers and the reserved internal keys.
  * Changing which bytes a workload writes within the format is not a
    format change. 005-79's take is an example. Such a change is recorded:
    StreamDigest gets a new reference, and the notes say it.
  * A proposal that changes the format, from an entry or from the search,
    waits for Frans's explicit approval before anything is made.
* **Replication is out.** Frans: "leave this out of this release. This
  should be considered experimental in 2026.2, known issues are allowed
  for this, the API will change. Should absolutely not be used in
  production."
  * The only work on it is wording. The release notes and the Javadoc of
    `DatabaseBuilder.replica`, `Database.addReplica`, `removeReplica` and
    `getStorageInfos` say four things: it is experimental, it has known
    faults, its API will change, and it must not be used in production.
  * The search does not look for its faults. A fault met in it on the way
    goes to 005-11 and the notes, and is not fixed.
* **014-01 is out.** Frans: "014-01, not in this release." The holes of an
  unforced tail are a known issue of 2026.2.
* **Doubles only at an API.** Frans, on 005-79: "The Pub API can use
  doubles at the interface, then immediately convert to integers (int,
  long) internally."
  * A public method may keep a `double` parameter. It converts the value
    to an `int` or a `long` at once, and no `double` decides the stream's
    bytes or the memory.
  * The plan applies this to `Db.setReclaimInternalFraction(double)` and
    JMX's setter as well, the only double setters of the Core. Both keep
    005-73's checks.
  * This replaces 005-79's decision 2 of 2026-10-29 (an integer setter).
    The coordinator copies Frans's words into 005-79 when it starts the
    entry.
* **One change, one entry, gated.**
  * Each change is made in its 005 or 015 entry, in a scratch clone.
  * The gates: `java/before-commit.sh` (`BEFORE COMMIT OK`) and the level
    script of the mechanism the change touches; for Lean, `lake build`
    with no `sorry` and no new axiom; the combined tree gated before a
    commit.
  * Each change is reviewed before it is committed (section 6, H5).
* **Commits.**
  * By the coordinator, in Frans's name, with no AI attribution, as for
    2026.1 and as 013-02 says.
  * Before each commit, the coordinator checks that `java/` and `lean/` in
    `main` are still what it gated, since Frans may commit meanwhile
    (013-01, section 4).
  * Staged right before the commit, with a path list.
  * Nothing is pushed, and the tag stays local; Frans pushes.
* **One owner of `main`.** During the release, other sessions and agents
  hand finished, gated files to the coordinator instead of committing
  them (013-02).
* **Timing.** Timed runs happen only in quiet blocks (013-01, section 7).
  Byte counts and other deterministic measurements may run at any time.
  s1 is checked with `ps` before each run there.
* **Principles.** Each change is checked against 010-01, above all P2, P9,
  P10 and P11. A departure is written under its principle.
* **News.** `tools/news.sh` when something finishes, fails or stops for
  Frans, and a summary each morning.


## 4. The issues

This section lists every unsolved issue known on 2026-11-03, each with a
proposal. The sources:

* the Open tables of 005 and 015 (015 is empty);
* 014, and 007's open points;
* 010-01's "To check" lines;
* the limits in docs/levels.md;
* 012's findings in Java;
* 009's leftovers;
* this review.

### 4.1. To fix or settle before the release

1. **005-82, Fix.**
   * The fault: `Db.getTrans` parses a record outside its failure
     handling. A corrupt record makes it throw a `StreamChecksumException`
     or a parser's bounds exception, and the database stays active. This
     is against docs/levels.md, section 3: a read that fails fails the
     database.
   * Its log of 2026-11-02 says that Frans asked first to tell expected
     incomplete crash tails from unexpected corruption. 005-83's
     experiment showed that the lazy hole case reaches `getTrans` this
     way.
   * Proposed, now that 014-01 is out: only the part for live reads.
     `getTrans` fails the database as every other read does, and keeps the
     cause. How startup handles damaged tails stays as it is (014-01).
     This is question Q1.
   * Size: S.
2. **005-79, Implement.**
   * What: integers in the Core's four decisions:
     * the take, in fixed point (option B);
     * the iteration spacing;
     * the internal fraction;
     * the low watermark.
   * Also: a check in the gates that keeps doubles out of the Core, Lean's
     `share` and `dither` in integers, and the C clone following, as its
     "Done when" says.
   * The setter keeps its double (section 3). The number of bits (16 is
     proposed) and the fraction's unit are for the entry's first step.
   * It changes the take's bytes once; the format does not change.
   * Size: M, about two days with Lean and C.
3. **005-78, Investigate, then change.**
   * What: keep the retain duration in the stream.
   * First the study and the probe (about half a day), then a design for
     Frans that sets the three forms side by side.
   * Each form adds something that a start reads, so each is a format
     question under section 3's rule:
     * A puts 8 bytes into the meta blocks' reserved bytes, as 005-50 did;
     * B adds an internal KV under a new key, and changes no layout;
     * C adds a field to reclaim's table, whose text the C clone parses.

     Frans's choice of a form is the explicit approval that the rule asks
     for.
   * The study's question 9, the internal fraction and the step reserve,
     is answered together with 005-79's fraction.
   * It comes after 005-79. Both change the iteration rule; each is done
     on its own, and the later one builds on the earlier.
   * It is a stop for Frans (section 8).
   * Size: M, a day and a half after his choice, more if C must follow.
4. **005-69, Fix: option A**, the entry's recommendation, taken under D2.
   `SystemClock` keeps its promise: one line and a test. C follows. S.
5. **005-71, Fix: option A**, recommended, under D2. A note in 010-01's P2
   and in 012-05's workload rules; no code. S.
6. **005-80, Decide: option B**, recommended, under D2. A line in 005-52's
   Outcome, and a test that forces the interleaving and fails on the code
   before `52aeb04`. S.
7. **005-52, the point that is left.**
   * `PauseProbe` gets two properties, `lower` and `lowerAt`.
   * Four runs in a quiet block, about 15 minutes, and the table.
   * The entry closes if no wait in the runs is longer than with a fixed
     budget.
   * Size: S, plus a night.
8. **005-65, the rerun.**
   * `threads.sh` with the fix, in a quiet block, about 21 minutes. Its
     four builds are ready in `/Users/f/fl/bench/006-10/e65-builds`.
   * Then the explanation and the recommendation, and the entry closes.
   * It changes nothing, but the fix it tests is in the release.
9. **Replication's wording** (section 3), in the Javadoc and the notes. S.
10. **The documents** (W3). These statements are out of date:
    * docs/levels.md's status date, 2026-10-26;
    * docs/levels.md, section 7: 005-65 "not yet explained";
    * docs/levels.md, section 8: "Open: group commit (005-48)", which has
      been in `main` since `d8ed1aa`, and its citation of 005-83, now
      014-01;
    * README.md's latest release;
    * lean/README.md's list of the theorems whose axioms the release
      checks.
11. **The notes, 2026.2's and 2026.1's** (W1, W2).
12. **015-01, Fix: the empty directory** (Q4, section 10). A database
    directory whose stream files are gone, or whose only file is empty,
    starts as a new, empty database without a word (005-33, the first row
    of its table; 012-14, section 6.4). Fixed before the release; the
    coordinator chooses the design from 015-01's options.

### 4.2. Known issues of 2026.2, not fixed

These go into the notes' "Known issues and limits", with their IDs:

* **Replication**: experimental, with known faults (005-11; docs/levels.md,
  section 9). Its API will change. It must not be used in production.
* **Power loss**:
  * Holes in an unforced tail can refuse a start or fail a later read
    (005-83, 014-01).
  * Physical power cycling, other storage and Windows are not established
    (docs/levels.md, section 8).
* **Collectors**: G1 pauses and runs full collections under eviction, and
  generational Shenandoah stops. Use ZGC, or Shenandoah without
  generations (docs/levels.md, section 7; 004-04, 009-04).
* **As many readers as cores**: gets of up to 39 ms with 8 readers and
  ZGC's workers on F53's 10 cores (005-65; Frans accepted these as a full
  machine).
* **A decrease of the startup distance at 50M keys**: from 1000 to 100 MB,
  the largest records are 13 to 15 MB (005-77, open).
* **A small commit after a large transaction** can write that transaction
  whole (007-07, sections 7.1 and 7.2; accepted).
* **D's bound is loose**: 1.6 to 2.9 times the startup distance (005-38).
* **The default startup distance** (50 MB) suits up to about 10M keys;
  beyond that, use 200 to 1000 MB (005-38; 010-01, P10).
* **Loads in memory** are 8 to 20 percent slower than before handles
  (docs/levels.md, section 7).
* **Bounded startup**: T3 is proved for the take. T4, and a cold start's
  reads, are not proved (007).
* **The files after a physical cut** depend on timing. The bytes from the
  decided cut do not (005-72).
* **Overload**: there is no admission control, and rw-transactions retry
  with hard-coded exponential sleeps from 10 ms (005-81).
* **Concurrency** is outside the Lean model, and is checked by tests and
  reviews only (005-07; section 6).
* **JDKs and systems**: tested on JDK 27, and on 17 if Q2 allows; on macOS,
  and on Linux after section 6's runs.
* **The documentation** is not reviewed for users.

### 4.3. Not for 2026.2

* **The 005 entries:**
  * 005-05 and 005-06, publication;
  * 005-07, though section 6 uses its questions 1 and 2;
  * 005-47, a feature;
  * 005-54, theory;
  * 005-60;
  * 005-72's option B;
  * 005-77;
  * 005-81.
* **Other items:** 007's T4; 014, with 014-01.
* **The C clone**, beyond what the entries' own "Done when" asks (D6).
* **009's leftovers**, which are not faults: LargerThanMemory's report
  with handles, and the test schedules' walks (006-09's 009-closure
  notes, section 3).
* **New 015 entries**, unless they are faults (section 6's rule).


## 5. The work

**W1. The release notes complete.** `releases/next.md` was begun on
2026-10-27 (`74bc2dc`, 005-55). It lacks most changes of the two days
before, and some after. Found in this review:

* **Java 17 or later is required**: `--release 17` since `bb7e189`, where
  2026.1 ran on Java 8. This is the incompatible change, so it goes first
  in the notes.
* **Handles (009)**: eviction without the sweep, in batches of at most
  2 ms; the lock-free fast path of reads; no stop-the-world of BergDB's
  own. Level 4's status as in docs/levels.md.
* **Group commit** (005-48, `d8ed1aa`): a sync that waits starts the
  flush.
* **An idle eviction thread does not wake** (005-51, `043a09c`).
* **Reclaim spaces its iterations by the live startup distance** (005-61,
  `4085e2e`).
* **A reader's load skips the eviction monitor** (005-65, `52aeb04`), and
  `setBudget`'s race was fixed there (005-80).
* **The Pub API's Javadoc** is built by `java/javadoc-pub.sh` (`f342bd4`).
* **Lean**:
  * the theorems over handles: T-CACHE, T-READ, T2-C, T-PIN, T9 and T12
    (009, 005-62);
  * the model before handles removed (005-62);
  * rule 4 by position (005-58);
  * T3 for BergDB's take (007-08).
* **Props** and `level1.sh`'s limits (section 2).
* **Replication's wording** (section 3).
* **The changes of section 4.1** as they are made.

The method: walk `git log release-2026.1..` against `next.md`, commit by
commit, and add each change with its ID and date, as `next.md`'s own rule
says. Then `next.md`, sorted, becomes the notes' "Changes since 2026.1".

**W2. 2026.1's post-release notes.** Its readme says that "a fault found
later that affects 2026.1 ... is recorded here", and still says "None
yet". Each fault fixed or found since is checked against 2026.1's code,
and gets a line: what it is, its effect, and where it was fixed. To check:

* 005-46 (an interrupt could fail the database);
* 005-50 (a start with another node size);
* 005-61;
* 005-63 (two databases on one directory);
* 005-70 (an rw-transaction accepted after a reopen despite a conflicting
  write);
* 005-73 (close discarded I/O failures);
* 005-74 and 005-75 (corrupt sizes and times);
* 005-82, and 005-83 with 014-01;
* any fault that section 6 finds.

**W3. The documents current.**

* Section 4.1's list, item 10. Only what is out of date with the code
  changes.
* docs/log.md's entry for the release, as for 2026.1.

**W4. The entries of section 4.1**, in the order of section 8.

* Each entry is done by its own "Done when", with C and Lean where it
  names them.
* The coordinator sets each entry's status in 005's table when it starts
  and when it ends.

**W5. The search for unknown faults** (section 6).

**W6. The release, by 008-01's steps**, with these changes:

* **The version.** 2026.2, version int 262, build `2026.2.YYMMDD.HHMM` in
  `BuildInfo`. The commit after the tag sets `2026.3-dev` and 263.
* **The commits and the tag.**
  * The tag `release-2026.2` goes on commit A, the release commit.
  * Commit B holds `releases/2026.2/`, the folded `next.md`, README's
    line and docs/log.md.
* **Files** (D6): 2026.1's five, and the Pub API's Javadoc as a zip
  (`javadoc-pub.sh`).
* **The tests on the jar itself** (`bergdb.dev.Unit`, `F` and `Night`, with
  `-ea`):
  * on F53 with JDK 27;
  * on s1 with JDK 27;
  * on JDK 17, if Q2 allows.
* **A user's program**, built against the jar and the Javadoc only: it
  creates a database, writes, restarts, reads and closes. It shows that
  the jar works as shipped.
* **2026.1's lessons**:
  * The F53 script hung for an hour on a `wait` that also waited for its
    own `caffeinate`. Wait for each child by its PID.
  * The quiet check waited half an hour for other work.
  * It took three hours, not two.

**W7. The numbers, against 2026.1.**

* **The runs**: 2026.1's runs (its readme, "Baseline"), each with both jars
  in turns:
  * Props;
  * `performance.sh ab 2026.1 2026.2` (the quick suite);
  * on F53, ScaleBench at 10M keys: M and C at 665 and 133 MB, with G1 and
    ZGC, and gets from 1, 4 and 8 threads;
  * on s1, the 10M load and D at 133 MB with a cold start, and 1M.
* **The startup distance**: ScaleBench runs at 2026.1's 10 MB, to compare.
  On F53 it also runs at 200 MB, for the figures that the notes and docs
  cite; only distances of 50 MB or more are cited.
* **Pauses**: the pause probe (009-03) beside the runs, with each version's
  longest waits.
* **StreamDigest**: new digests, which become 2026.2's reference.
  005-50, 007-07 and 005-79 change the bytes, and 005-78 may.
* **Time**: 2026.1's F53 block took 32 minutes. In turns, with the 200 MB
  runs, it is about 100 minutes. s1 needs about 2.5 hours, from
  `/opt/bergdb-bench/2026.1/`, where 2026.1's jar and scripts are.
* **First**: check that today's tools still run on 2026.1's jar.
  ScaleBench and the pause probe read internals that handles changed;
  009-03 ran both jars, so they likely do.


## 6. The search for unknown faults

What is done, by whom, and how each result is checked. Each reviewer is a
subagent with no stake in the code it reads. It gets:

* the code and its area;
* the entries that define the intended behaviour;
* not this plan's conclusions, nor earlier reviews' findings.

**H1. Reviews of what changed since 2026.1** (`git diff release-2026.1..`
of `java/src`, with the files whole), in four areas:

* **(a) Handles and eviction**: `dag/Handle`, `KeyNode`, `TopNode`,
  `NodeCollection`, `Cache3`, `Eviction` and `Residents` (009; 005-51,
  005-52, 005-65, 005-80).
* **(b) Storage**: `FileStream`, `BufferedStream` and `StorageManager`
  (005-46, 005-48, 005-63, 005-64, 005-76).
* **(c) Startup, the take and reclaim**: `TransSeq`, `DbStarter`, `Db`,
  `Reclaim`, `StoredTrans`, `RecoverableStream` and `MetaBlock` (005-49,
  005-50, 005-53, 005-57, 005-61, 007-07; 005-70, 005-73 to 005-75).
* **(d) The Pub API and the lifecycle**: `pub` and `pubimp`, start, stop,
  close, interrupts and the setters (005-46, 005-52, 005-53, 005-55,
  005-56, 005-59, 005-63, 005-66).

**H2. The Pub API's promises.**

* Each statement in the Javadoc of `bergdb.pub` and `bergdb.pub.util` is
  checked against the code, and against a test where one exists.
* The parts that the C clone did not port get the same reading: the
  connections, the rw-transactions and their retries, the indexes, the
  builder, encryption (`SalsaStream`) and JMX.
* Not replication.

**H3. Concurrency.**

* What: 005-07's questions 1 and 2, for today's code. The reading covers
  every thread (the callers, the storage threads, the cut's delete thread,
  the eviction thread, the index jobs, the close), every lock and monitor,
  and each shared field and how it is published, all against the Java
  Memory Model.
* The start: 009-02's reading of the fast path.
* The output: a subitem of 016. Each problem found is registered.

**H4. Tests beyond the gates**, on the candidate:

* **`night.sh large`**, about 6 hours. No run with handles is recorded.
* **jcstress** (`java/stress/jcstress`): its tests cover handles'
  publication and the eviction race. It last ran on 009's branch
  (`7d325b3`), before 005-65 changed the eviction thread's wake. H3 adds a
  test wherever it finds a publication that has none, such as 005-46's
  reads without a lock or 005-76's wake.
* **The stress programs, with fresh seeds, for some hours**: RestartStress,
  DagFuzz, CrashTest, ReclaimStress, ReclaimReaders, EvictionInvariance,
  InterruptStress, PowerLossTest and LargerThanMemory; also `soak.sh`'s
  soak of Level 3 on disk, two hours.
* **On Linux** (s1, JDK 27): `before-commit.sh`, `level1.sh` and the night
  tests. s1 has no Lean, so `level2.sh` to `level4.sh` cannot run their
  conformance steps there.
* **On JDK 17**, if Q2 allows: `before-commit.sh` and the night tests.
* **The C clone's cross tests**, where an entry makes C follow (005-79): a
  second implementation of the Core, compared byte for byte.

None of these runs is timed. They run by day, or in a night without a
quiet block, one heavy run at a time (013-02).

**H5. A review of each change made for the release.**

* Every change of W4, and every fix of a finding, is reviewed before it
  is committed, by an agent other than its author.
* The reviewer gets the entry, the diff and the tests. The findings are
  answered in the entry.

**The rule for findings:**

1. **Each finding is verified**: by a failing test or a probe; for a race,
   by the interleaving written out and checked by a second agent. A
   finding that is not verified goes into its area's report as a doubt.
2. **A verified fault gets an entry**: the coordinator registers it in 015,
   Kind: Fix.
3. **It is fixed before the release**, W4's way, when its fix changes
   neither the stream format nor the Pub API's signatures and needs no
   design choice. Otherwise it stops for Frans: `news.sh` "needs a look",
   and a line in 016-02's "For Frans to decide". The other work goes on.
4. **A fault in replication** goes to 005-11 and the notes, and is not
   fixed.
5. **A fault that affects 2026.1** also goes into 2026.1's post-release
   notes.

**The exit**, which is the freeze of section 8:

* H1 to H4 are done, with their reports in 016;
* every verified fault is fixed, or deferred by Frans;
* no Fix entry is open in 005 or 015 that Frans has not deferred.

**Not covered**: physical power loss on real hardware; proofs of
concurrency; Windows; network file systems; JDKs other than 27 (and 17);
replication.


## 7. Risks

* **The length depends on Frans**: his decisions during the run (005-78's
  design, and findings that need him) set when the release can be made.
  Each stop adds its waiting time.
* **The search may find faults that take longer to fix** than these days.
  Finding them is the purpose of the search; Frans decides which of them
  wait.
* **Every byte change has a cost**: 005-79 and 005-78 each change the
  bytes, and StreamDigest's reference and the C clone's cross tests follow
  each. A third change, from the search, repeats that.
* **Usage limits**: 013-02's check-ins resume the work after a usage
  limit. A weekly limit stops it until its reset.
* **Shared machines**: other sessions may time on s1; the coordinator
  checks with `ps`. `night.sh large` and the 02:10 `night.sh` do not
  overlap.
* **A gate that fails on the release commit** stops the release, and
  Frans decides, as for 2026.1.


## 8. How the work runs

**The coordinator.**

* One coordinator session (013-02) of Claude (Opus 5.5), unattended (D5).
* Frans starts it with `/coordinator start`, then `/coordinator unattended
  UNTIL`, and tells it to run 016-01.
* It is the only coordinator until the tag. If the work takes more than a
  day, the same session goes on (Frans: "one Coordinator session"), with
  013-02's check-ins and watchdog.

**Subagents.**

* Background agents (the Agent tool), at most 4 at a time, as in 006-09.
* Each agent works in a scratch clone of its own, under
  `/Users/f/fl/bench/016/`.
* Effort: xhigh, or high when the usage is tight (013-02, "Effort"). The
  reviews of section 6 run at the effort of Q3.

**The log.** A subitem 016-02, the run: progress with times, the agents,
the stops and the outcome. It takes the place of a 006 subitem for the
days of the release.

**Stops for Frans:**

* 005-78's design;
* any change of the stream format;
* a fault that needs a choice;
* a gate that fails on the release commit.

Each stop gets a `news.sh` "needs a look" and a line in 016-02's "For
Frans to decide". The other work goes on.

**The order.** Times are from 013-01's windows: window 1 from 22:30 to
02:05, and window 2 from the end of `night.sh` to 06:15.

* **Day 1.** Four agents:
  * A1: W1, W2 and W3, the documents and replication's wording;
  * A2: 005-79, Java first, then Lean, then C;
  * A3: 005-78's study and probe, then the design for Frans (a stop);
  * A4: 005-82 (after Q1), 005-69, 005-71, 005-80, and `PauseProbe`'s
    properties for 005-52.

  Each change is reviewed (H5) and committed when it is gated.
* **Night 1.**
  * The quiet block: 005-65's `threads.sh` (21 minutes) and 005-52's four
    runs (15 minutes).
  * `night.sh` at 02:10, on the day's `main`.
  * On s1: the gates on Linux (H4).
* **Day 2.**
  * H1, in four areas, and H2 and H3, in two waves of agents. The
    verified findings are fixed.
  * 005-78's change, after Frans's choice.
  * What is left of 005-79's Lean and C.
* **Night 2.** No quiet block. `night.sh large`, from about 18:00 so that
  it ends before the 02:10 run. jcstress, and the stress programs with
  fresh seeds.
* **Day 3.**
  * The last fixes; W1 to W3 brought up to date.
  * The freeze: section 6's exit is met, `main` is clean, and every entry
    of 4.1 is closed.
  * In the evening: commit A, the release commit, and its jar, built in a
    clean clone of A.
* **Night 3.**
  * In window 1, the quiet block: W7's F53 block in turns, about 100
    minutes.
  * From window 1's start, s1's runs in turns, about 2.5 hours.
  * At 02:10, `night.sh` on A: the release's gate.
* **Day 4, the morning.** If `night.sh` printed `NIGHT OK` on A:
  * the tests on the jar (W6);
  * the numbers, the notes, `baseline.zip` and `SHA256SUMS`;
  * commit B, the tag, and `BuildInfo` set to 2026.3-dev;
  * the summary in `news.md`.

**The size**: about four days and nights of the coordinator's time. That
holds if Frans answers 005-78's design within a day and the search finds
nothing that needs him.


## 9. What is not made

As for 2026.1: no Maven coordinates, no website, no .NET (gone since
2026-10-29), and none of the 2017 build's other jars.


## 10. Decisions (Frans, 2026-11-03, 15:01)

* **D1, internal or published: A, internal.** "D1. Internal." The
  alternative was a public release with 005-05's decision, a review of
  the documents for users and Maven.
* **D2, what must be done before the release: A, section 4.1.** "D2. As
  you recommend unless I say otherwise here."
  * With it, the entries' own recommendations: 005-69 A, 005-71 A and
    005-80 B.
  * Added by this review: 005-65's rerun, the documents, and the search of
    section 6, from "We do not want unknown bugs in the release".
  * The alternative was 005-82 and the documents only.
* **D3, 005-79: A, before the release.** "005-79, yes implement this
  internally. The Pub API can use doubles at the interface, then
  immediately convert to integers (int, long) internally." and "D3. See
  above."
* **D4, replication: A, kept, experimental, with no work on it.** "D4. As
  you recommend." and "Replication: leave this out of this release. This
  should be considered experimental in 2026.2, known issues are allowed
  for this, the API will change. Should absolutely not be used in
  production." The alternative was its removal.
* **D5, how the work runs: unattended, for all of the work, not only the
  release night.** "D5. Yes, the work will be unattended AI work by you
  (Opus 5.5) as one Coordinator session that starts subagents."
* **D6, the release's files: A.** "D6. As you propose." 2026.1's five
  files and the Javadoc zip; the C clone is not built or tested for the
  release.
* **014-01: out.** "014-01, not in this release. Keep the stream format
  the same, unless I (Frans) explicitely approve changes."
* **The answers to section 11** (15:27): "Q1: as recommended. Q2. Yes on
  both as recommended. Q3. Use xhigh, no higher. Q4. Fix before. You
  decide how to."
  * Q1: 005-82's live-read fix only.
  * Q2: a JDK 17 on F53 and on s1.
  * Q3: every review at xhigh, none at max.
  * Q4: the empty directory is fixed before the release, as 015-01; the
    coordinator chooses the design. It moves from section 4.2 to 4.1.
* **D7, Java only** (15:31): "The C code does not need to be updated for
  2026.2 in this work. Only Java code will be included in the release. It
  is not a requirement to update the Lean code either. If this is needed to
  develop Java or to ensure it works well, then do it. See it as a tool,
  not an output artifact for the release."
  * This replaces the C and Lean steps of the entries' "Done when" for
    2026.2 (005-69, 005-79 and others): the C clone does not follow, and
    Lean changes only where it helps to develop or check the Java change.
  * The level scripts' Lean conformance steps still run: they check Java
    against the model.


## 11. Questions before the start

Answered by Frans at 15:27 (section 10): Q1 and Q2 as recommended, Q3
xhigh, Q4 a fix before the release.

* **Q1. 005-82 without 014-01.** Make the live-read fix (`getTrans` fails
  the database on a corrupt record, as every other read does), and leave
  startup's handling of damaged tails to 014-01?
  * Recommended: yes. The fix makes the read contract of docs/levels.md,
    section 3, hold, and it decides nothing about recovery.
  * Without it, 005-82 is a known issue.
* **Q2. A JDK 17.** May the coordinator install one: Homebrew's
  `openjdk@17` on F53, and a JDK 17 in `/opt/bergdb-bench/` on s1, beside
  its JDK 27?
  * Recommended: yes, on both.
  * Without it, the notes say "tested on JDK 27 only", against README's
    "JDK 17 or later".
* **Q3. The reviews' effort.** xhigh, the standing rule, or max, as for
  the reviews of 005-62, 007-08 and 012-02?
  * Recommended: max for H1 to H3, about six agents, and xhigh for
    everything else.
  * The cost: 013-02's effort cost index puts max at 3.44 and xhigh at
    1.66.
* **Q4. The empty directory** (section 4.2): a 015 Decide entry for after
  the release, or a fix before it?
  * Recommended: after the release. A fix changes the API (for example, a
    start that refuses to create a database unless told to); 2026.2 is
    internal; and there are no users who could lose data.
