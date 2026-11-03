016-03. Plan: the release notes
===============================

Created 2026-11-03 by Frans Lundberg. Status: planned, not started.

The plan for W1 and W2 of 016-01 (section 5; section 4.1, item 11): the
release notes of 2026.2 complete, from `releases/next.md` and `git log
release-2026.1..`, and 2026.1's post-release notes. It fits the one
night of the coordinator's timeline (Frans, 15:40): the notes are written
in the evening, and get the numbers in the morning.

Who: a notes agent, in a scratch clone `/Users/f/fl/bench/016/notes/`
(N below), in the evening; the coordinator commits, and fills in the
numbers in the morning. 016-01 gives A1 W1 to W3 together. Recommended:
one agent for this plan and 016-04, in this order: 016-04's D1 and D2
(17:00 to 18:15), this plan's N1 to N3 (18:15 to 23:00), 016-04's D4, D6
and D3 (23:00 to 01:00), and N4 (01:00 to 01:20). About 8 agent-hours;
the coordinator may hand the second half to a fresh agent at 23:00, with
the two plans' State sections.


## 1. What next.md has, and what it lacks

`releases/next.md` (2026-11-03) has 23 entries in four sections:
Reliability (005-73 twice, 005-75, 005-74), API changes (005-73, 005-70,
005-55, 005-59, 005-46, 005-63, 005-56, 005-66, 005-53, 005-52, the
`Factory` constructor, no .NET), Format (005-50) and Performance (005-46,
005-57, 005-49 with 007-07, 005-76, 005-64).

A walk of `git log release-2026.1..df6ad50` (245 commits; the 49 that
touch `java/` read one by one, with the diff of `bergdb.pub` and
`bergdb.pub.util`, and the 32 that touch `lean/`) found these changes
missing. Each goes into next.md with its ID and date, as next.md's own
rule says, in the section named.

**Requirements** (a new section, first in the notes):

* Java 17 or later is required: `build.sh` and `performance.sh` compile
  with `javac --release 17`, where 2026.1 had `--release 8` (`b10e072`,
  2026-10-25, 009 step 1-0). The incompatible change, so it goes first.
* The collector: ZGC, or Shenandoah without generations. G1 pauses for
  hundreds of milliseconds and runs full collections under eviction, and
  generational Shenandoah stopped for 821 ms (docs/levels.md, section 7;
  004-04; 009-04; `62ad470`, `3c02f11`, `45c5e43`, 2026-10-26 and 27).

**Performance**:

* Handles (009), merged in `178a0d4` (2026-10-26; branch tip `a04a418`):
  * eviction without the sweep: CLOCK over the node table, in batches
    that end after 2 ms (`Eviction.BATCH_NANOS`), and a reader's load over
    the trigger waits up to 2 ms (`LOAD_WAIT_NANOS`) (`4a1fc5e`,
    `66c8f3a`, `a04a418`);
  * reads of resident nodes without a lock (`19a8c58`); the pointer locks
    gone (`7831909`);
  * the node table in 4,096 maps with a lock each: a resize stops one map
    for 0.23 ms, where it took 11.6 ms (`be4534a`); reads no longer
    synchronize on `readSync` (`463d6ee`);
  * figures (009-03; docs/levels.md): the longest get from the OS cache at
    10M keys under ZGC 3.45 ms, against 7.3 s in 2026.1; gets in memory
    from 8 threads 101 and 61 percent more (G1, ZGC), from one thread 3
    and 11 percent fewer; loads in memory 8 to 20 percent slower; P4's
    soak: the longest commit 5.1 ms, the longest read 3.6 ms. The
    figures the notes cite are tonight's (016-10), with these as context.
* MEM 129 to 130 bytes per KV since handles, against 191; `level1.sh`'s
  limit from 228 to 131 (`f648f96`, 2026-10-29). SS limits raised after
  007-07 (`f6fc56b`, 2026-10-29).
* Group commit (005-48, `e611709`, 2026-10-27): a sync that waits has the
  buffer written at once (`BufferedStream.flushSoon`), and transactions
  that arrive during a force go out together. On s1 one thread's durable
  commits went from 38 to 213 a second (`3950a96`). next.md names it only
  inside 005-64's entry.
* An idle eviction thread waits with no timeout, where it woke once a
  second; `close()` returns after it has ended, also after `stop()`
  (005-51, `c2aab10`, 2026-10-27; 1.4 ms of CPU a minute before, none
  after, `78a6723`).
* A reader's load skips the eviction monitor when a request to the
  eviction thread is pending (005-65, `988fe1a`, 2026-10-29).

**Reliability**:

* Reclaim spaces its iterations by the live startup distance (005-61,
  `a175840`, 2026-10-27). Before, it used the builder's value, taken
  before `start()` read the stream's, so a database made with a small
  distance and opened with the default builder nearly stopped reclaiming.
  A fault of 2026.1 (W2).

**API changes**:

* `Database.PRIMARY` is `Util.identity("primary")`: the same value, but no
  longer a compile-time constant, so a `case` label with it no longer
  compiles (005-56, `04f1546`, 2026-10-28).
* `Db.setCacheSizeIndicator(long)` and `getCacheSizeIndicator()`, the Core's
  side of 005-52 (`fd8f513`, 2026-10-28).
* Internal only, a line at most: `PointerLocks` and
  `Db.Internal.getPointerLocks()` gone (`7831909`); `Db.Internal.cacheStats()`,
  `writersWaiting()` and `takeWriteBufferWaits()` added (`e23c96e`);
  `bergdb.stream.FileStreamIo` and `FileStream(File, FileStreamIo)` public,
  for the power-loss tester (`3c807f1`).

**Documentation** (a new section, or under API changes):

* The Javadoc of `Database.stop()` and `Db.stop()` corrected: 2026.1 said
  that the files are not forced and that only `sync(STRONG)` forces them;
  `FileStream` forces every append, so `sync()` waits until the data is on
  the device, and `STRONG` adds the replicas (`a515af3`, 2026-10-26).
* `DatabaseBuilder.startupDistanceInMb`'s Javadoc said 5 to 100 MB; the
  code has always clamped to 5 to 1000 (`fd8f513`).
* Replication's wording (016-04).

**Build and tools**:

* `java/javadoc-pub.sh`: the Pub API's Javadoc, with doclint, failing on
  any warning (`216fc8b`, 2026-10-29).
* `java/deps.py`: `before-commit.sh` checks the package dependencies
  against each `package.html` (005-56, `04f1546`).
* `java/stress/core-build.sh`: the Core Layer built alone, `night.sh`'s
  step 2 (005-56, `43e631f`, 2026-10-28).
* `java/stress/PauseProbe.java` (`e23c96e`); jcstress tests in
  `java/stress/jcstress/` (`19a8c58`, `a04a418`).

**The Lean model** (a new section; Frans, 15:31: Lean is a tool, not an
output of the release):

* the model of handles, `SIS/Handle.lean` (`74af34c`, 2026-10-25);
  T-CACHE, T-READ, T2-C, T-READ with restarts and T-PIN over handles
  (`38586b3`, `059d741`, 2026-10-26); the checker's C-H compares Java's
  handle state with the model (`851acdf`, `e712874`);
* rule 4 by position proved to link what rule 4 by node id links (005-58,
  `7c1ce2f`, `0965377`), also after a cut (`96e371a`, `8ce4f12`);
* T9 and T12 over handles (005-62, `bba91dd`, `a506b34`); the model before
  handles removed, and startup with handles proved (005-62, `bee5065`,
  `7f81169`, `073366a`, 2026-10-28);
* T3 for BergDB's take (007-08, `db1eca8`, `8b6669f`, `3d21792`,
  `9cf8a82`).

**Not for the notes**: `52d1e1f` (news.sh), `27ec238` (a suite comment),
`899c5e6` (`BuildInfo` 2026.2-dev), the tests only (`b0661ba`, `dad6bd2`,
the test parts of `cec0032`), and comments only (`df6ad50`'s `Reclaim`
and `AppendOnlyStream`).

**Rightly absent so far** (no code since the tag): 005-69, 005-71,
005-72, 005-79, 005-82, 014-01. Those made tonight bring their own lines
(step N4).

**Entries of next.md to correct:**

* No date, against its rule: 005-59 (`f9c3b09`, 2026-10-27), 005-46's two
  entries (`eaec93e`, 2026-10-27), 005-50 (`bf19075`, 2026-10-27), 005-57
  (`07b6375`, 2026-10-27).
* No ID: "`Factory` has no public constructor" and "No .NET" (`216fc8b`,
  2026-10-29); the commit names none, so they keep the date only.
* 005-64: "the same throughput, latency and CPU; a sync is not slower".
  The entry's own conclusion says that 50 ms "costs up to 22 % on a rare
  sync beside a plain writer (s1)", and "11 to 35 percent fewer forces" is
  11 to 14 on F53 and 18 to 35 on s1. Say both. Replicas added through
  the Pub API also went from 20 to 50 ms (`DatabaseBuilderImp` gives
  them `DEFAULT_BUFFER_TIME`); the Core's replicas keep 2,000 ms.
* 005-52: "in batches of at most 2 ms" is the limit (`BATCH_NANOS`), not
  a measured bound: 009-03, section 0, measured 3 to 4 ms on s1, and up to
  17 ms with 8 readers on F53 before `988fe1a`. Say "batches that end
  after 2 ms". 005-80's race, in the same setter, was fixed in `988fe1a`;
  it never was in a release, so it is a line in this entry, not a fault
  of 2026.1.
* 005-76: dated 2026-11-02, but its code is in `df6ad50` (2026-11-03).
* 005-70 is a fault fixed; it belongs under Reliability.
* 005-49: "the largest record of a run is 2 to 10 times smaller" is not
  what docs/levels.md says (0.34 to 1.9 MB against 2.6 to 4.6 MB). Take
  docs/levels.md's figures. Its 24, 36 and 13 percent agree.

Checked and right: the four hashes cited (`cec0032`, `eaec93e`, `bf19075`,
`07b6375`); 005-57's 214 to 46 s and 210 to 51 s; the clamps (5 to 1000
MB, 4 to 100,000 MB); `FileStream-cut`, `bergdb.lock`,
`DirectoryInUseException`, `VersioningStreamException` and the 200 kB
transaction; 005-73 to 005-75.


## 2. The notes' layout

`releases/2026.2/readme.md`, as 2026.1's, section by section:

1. **The title and status**: "Released 2026-11-04 by Frans Lundberg.
   Internal: not published, not for production." As planned in 016-01.
2. **Files**: the six files of 016-09, section 2.
3. **Identity**: the tag, commit A, the build id, the JDK and `--release
   17`, F53, the jar's SHA-256 (016-09, R3).
4. **What it is**: the levels' table from docs/levels.md as it is at A;
   the defaults that matter: startup distance 50 MB (200 to 1000 MB from
   about 10M keys), buffer time 50 ms, infinite retention, eviction on
   with handles; the collector (ZGC).
5. **Requirements**: Java 17; the JDKs tested (016-09).
6. **Changes since 2026.1**: next.md, sorted into Requirements,
   Reliability, API changes, Format, Performance, Documentation, Build and
   tools. "Every stream differs from what 2026.1 wrote; databases of
   2026.1 are refused (005-50)" stays prominent.
7. **The Lean model and the C clone** (Frans, 15:31): what the Lean model
   covers (the section 1 list), and where this release's Java changes are
   not in it. For example 005-79's integers: the model's `share` and
   `dither` are not changed, unless 005-79's entry changed them. The C
   clone (012) is not updated: it writes the bytes of the Java it last
   ported (012's log), and its cross tests would differ on 005-79's take.
   The coordinator gives the list of tonight's changes that touched
   neither (from each entry's outcome).
8. **Verification**: `night.sh` on A (each step, its result and time),
   the tests on the jar (F53 and s1, JDK 27 and 17, the counts), the
   user's program, `lake build` in the level scripts and the axioms
   (016-09, R8), StreamDigest (016-10, N8), H1 to H5's reviews and
   findings (016-01, section 6) by their subitems.
9. **Release Props**: 2015.4, 2026.1 and 2026.2 side by side, the medians
   of tonight's runs in turns (016-10); the line counts as 2026.1's table
   (`git ls-files` at A, `wc -l`; Java, Lean, docs).
10. **Baseline**: 016-10's tables, both versions in each row, with the
    machine, the JDK, the flags, the startup distance (200 MB), and which
    runs were cut or skipped.
11. **How to compare a later version**: one compiled copy of each tool per
    jar (016-10, section 1); `performance.sh ab` with 2026.2's preserved
    build; StreamDigest's reference in `baseline.zip`.
12. **Known issues and limits**: 016-01, section 4.2, with the changes of
    the night: 005-82 and the empty directory (015-01, Q4) are fixed, so
    they leave the list and are in the changes; replication with the four
    statements (016-04); each finding of section 6 that Frans deferred;
    the JDKs and systems tested.
13. **Post-release notes**: "None yet."


## 3. The steps

### N1. Next.md complete (notes agent, 18:15 to 19:45; 1.5 hours)

* In `N/` (`git clone /Users/f/fl/repos/bergdb N`): add section 1's missing
  entries to `releases/next.md`, in its style (a bold lead, what changed
  for a user, the ID, the date, the commit), and correct the entries
  listed there.
* Check, by a walk that the agent writes as `N/walk.sh`: for each commit of
  `git log --format=%h release-2026.1..HEAD -- java/src java/src-dev
  java/src-icu java/stress java/*.sh`, its hash or its ID is in
  `next.md`, or the hash is in section 1's "Not for the notes" or
  "Internal only" lists. It prints the commits that are neither; the list
  must be empty, or each commit left gets a line in section 1.
* Hand-over: the patch of `next.md` to the coordinator, who commits it
  (no Java gate is needed for `releases/`).

### N2. The draft notes (notes agent, 19:45 to 21:30; 1.75 hours)

* `N/out/readme.md`, the layout of section 2, with every section written
  but the numbers. Each number to come is a marker `[[NAME]]`, with NAME
  the label of the table or figure that fills it (016-09's R3, R4, R6;
  016-10's `tables.md`).
* The changes from next.md as it is then, sorted; the known issues from
  016-01, section 4.2, as amended in section 2, item 12.
* Check: `grep -c '\[\[' N/out/readme.md` lists only the markers that
  section 2's numbers explain; each table follows AGENTS.md (rows of at
  most 100 characters, aligned by their contents).
* The draft stays in `N/out/` until the morning; the coordinator copies
  it into the release (016-09, R8).

### N3. 2026.1's post-release notes (notes agent, 21:30 to 23:00; 1.5 hours)

Each fault fixed or found since 2026.1 is checked against 2026.1's code:
`git show release-2026.1:PATH` of the code the fix changed (`git show
--stat` of the fix gives the paths), read beside the fix. Expected, from
the entries; the agent confirms or corrects each:

* 005-46: an interrupt of a caller or the storage thread could fail or
  stop the database. Affects 2026.1.
* 005-50: a start with another node size looked like a corrupt stream, or
  started and could leave a stream that no start opened. Affects 2026.1.
* 005-61: reclaim nearly stopped for a database opened with another
  startup distance than it was made with. Affects 2026.1.
* 005-63: nothing refused a second database on one directory. Affects
  2026.1.
* 005-70: an rw-transaction accepted after a reopen despite a conflicting
  write before the close. Affects 2026.1.
* 005-73: `close()` discarded I/O failures; NaN accepted as a reclaim
  fraction; broken diagnostics. Affects 2026.1.
* 005-74 and 005-75: corrupt sizes and times looped, exhausted the heap,
  or were replayed. Affects 2026.1.
* 005-76: 2026.1 listed it (005-13) as a known issue; a line that it is
  fixed.
* 005-82: `getTrans` on a corrupt record left the database active.
  Affects 2026.1 (checked 2026-11-03): at the tag, `Db.getTrans` returns
  `ti.getStoredTrans()` after its `try`, so the parse's exceptions pass
  its failure handling.
* 005-83 and 014-01: holes in an unforced tail can refuse a start or fail
  a later read. Affects 2026.1 (power loss); not fixed in 2026.2.
* 005-69: `SystemClock` does not keep its promise of strictly increasing
  times. Affects 2026.1 (checked 2026-11-03): `SystemClock.getTime()` is
  the same code at the tag.
* 005-72: the files after a physical cut depend on timing. A property, not
  a fault, and the same in 2026.1: no post-release line, unless Frans's
  decision on it makes it a fault.
* 005-80: in 005-52's setter, which 2026.1 does not have: not a fault of
  2026.1.
* 015-01, the empty directory: by the 2012 rule, also in 2026.1.
* Each fault that 016-01, section 6 finds (rule 5): the coordinator gives
  the list at 01:00.

Also a post-release note on 2026.1's own "How to compare a later
version": since 005-56 (`04f1546`) moved `SyncLevel` and 005-46
(`eaec93e`) made `PauseProbe` use `FileStreamIo`, one compiled copy of
StreamDigest, PauseProbe or `performance.sh`'s harness no longer runs on
both 2026.1 and later jars; 016-10, section 1 says what does.

Each line: what the fault is, its effect on 2026.1, where it was fixed
(ID, commit), and "not fixed" where it is not. In
`releases/2026.1/readme.md`, "Post-release notes", replacing "None yet."

* Check: every fault above has a line or a reason in this plan's State
  why it does not affect 2026.1; the coordinator commits the section
  (no Java gate).

### N4. The night's changes (notes agent, 01:00 to 01:20; 20 minutes)

* Each entry made tonight (005-79, 005-78, 005-82, 005-69, 005-71, 005-80,
  005-52, 015-01, the findings' fixes) adds its own line to `next.md`, as
  next.md's rule says. This step checks that they did: `N/walk.sh` again,
  on `main` as it is then, and a line added where one is missing.
* The draft's changes and known issues brought up to date from `next.md`
  and from 016-01, section 6's findings.
* Check: `walk.sh` prints nothing.

### N5. The freeze (coordinator, 01:25)

* `next.md` and the draft complete for every commit up to the freeze. A
  commit after it, before A, is A itself (016-09, R2).

### N6. The numbers and the fold (coordinator, 06:05 to 06:35; 30 minutes)

* The markers filled: the identity (016-09, R3), `night.sh`'s report (R6),
  the tests on the jar (R4, R5), the axioms (R8), StreamDigest (016-10,
  N8), Props and the baseline (016-10's `tables.md`).
* Check: `grep -c '\[\[' releases/2026.2/readme.md` prints 0.
* `releases/next.md` emptied: its title and first paragraph kept, with
  "after 2026.2" for "after 2026.1" and the link to 2026.2's readme; no
  entries.
* Both into commit B (016-09, R9).


## 4. What is a stop for Frans

* A fault of 2026.1 that is found in N3 and not fixed in 2026.2, other
  than the ones known (014-01, replication): it goes into the notes'
  known issues only with his agreement (016-01, section 1); until then,
  `news.sh "needs a look"`. The tag can wait for him; the notes are ready.
* None for the wording: the release is internal.


## 5. Done when

* `releases/2026.2/readme.md` has every section of section 2, with no
  marker left;
* `next.md` is folded and emptied, and `walk.sh` printed nothing at the
  freeze;
* 2026.1's post-release notes list each fault of N3 that affects 2026.1;
* the known issues hold every issue of 016-01, section 4.2 that is still
  open, and each deferred finding.


## 6. State

2026-11-03, 16:05: the plan is written; section 1's walk is done (up to
`df6ad50`); nothing of N1 to N6 is done. Open: N3's checks against
2026.1's code; 005-82 and 005-69 are checked, the others' expectations
are from their entries.

2026-11-03, 20:10, the notes agent (in `/Users/f/fl/bench/016/docs/repo`,
with 016-04): **N1 done**, on `main` at `5c9d0f6`. `releases/next.md` has
section 1's entries, in new sections Requirements, Documentation, Build
and tools and The Lean model; the corrections of section 1 (the dates and
commits, `Factory` and .NET with `216fc8b`, 005-64's figures and replicas,
005-52's batches with 005-80's line, 005-76's date and commit, 005-70
under Reliability, 005-49's figures from docs/levels.md); and the commits
of tonight up to `c72a02b`: 005-82, 015-07, 015-12, 015-01 with 015-06's
part, 005-69 under Reliability; 015-17 in 005-73's close entry, 015-24 in
005-63's, 015-10 in 005-52's and with 015-15 in Handles' (faults of the
development, never in a release); 005-79 under Format; `DatabaseMissingException`
and `Database.PRIMARY` under API changes; `doubles.py`, PauseProbe's
`lower` and the growth's jcstress test under Build and tools. The walk is
`/Users/f/fl/bench/016/docs/walk.sh` (outside the repository; `walk.sh
REPO`); its list of commits not for the notes, with reasons, adds to
section 1's: `7f3dab4` (a `@throws` line), `cc8effb`, `b348922`,
`413f72c`, `6180a32` (comments and citations), `d91b619` and `cf6c8e7`
(tests only, 015-09 and 015-16). `27ec238` is 005-64's code, not only a
suite comment, and is cited. It printed nothing at 20:10. Hand-off:
`/Users/f/fl/bench/016/docs/handoff-N1/`.
