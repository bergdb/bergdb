016-01. Plan: release 2026.2
============================

Created 2026-11-03 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "Create bergdb item 016-release-2026-2. This is for planning
the 2026-2 release. The scope of it and the work needed."

**Status: draft, for Frans's decisions (section 8).** Nothing done yet. The
release procedure itself is 008-01's, with the changes in section 4, W5;
this plan does not repeat it.


## 1. The goal

BergDB 2026.2: the first release with handles (009) and bounded startup
for BergDB's own take (007-07, 007-08), made as 2026.1 was: a tag, the jar,
the source, release notes, the gates and the tests on the final jar, and
the numbers. 2026.1 was the baseline before handles; 2026.2 shows what they
and the work since changed, by running both jars in turns on the same
machines, and is the baseline for what comes next.

Whether 2026.2 is internal, as 2026.1, or published is D1.

Done when: the tag `release-2026.2` and `releases/2026.2/` are committed,
`releases/next.md` is folded into the release notes and emptied, and
2026.1's post-release notes list the faults found since that affect it.


## 2. Where main stands, 2026-11-03

* 244 commits since `release-2026.1` (2026-10-25), the last `3ad171d`.
  `night.sh` has passed every night since 2026-10-31 (`NIGHT OK` on
  `3ad171d`, 2026-11-03). The main tree has uncommitted changes of other
  sessions, among them 005-76's code in `BufferedStream`, which
  `releases/next.md` already lists.
* Props, 2026-10-28 (007-07, section 12): MEM about 130 bytes per KV (191
  at 2026.1; `level1.sh`'s limit lowered to 131, `f648f96`), CORE about
  0.24 (0.29), SS 1.51 (1.50; the limits raised after 007-07, `f6fc56b`).
* Databases of 2026.1 are refused (005-50), with no migration (Frans: "No
  need to consider "today's databases". There are none.").

2026.1's known issues (its readme, "Known issues and limits"), one by one:

* The sweep's stop-the-world: gone with handles (009). Eviction runs in
  batches of at most 2 ms; 009's target 2 met in P4's soak, the rest of
  005-65 accepted by Frans.
* The read path's cap of about 2 million gets a second: `readSync` gone
  (009, step 1c) and a lock-free fast path (step 3c). The new figure is to
  be measured, in the baseline (W6).
* Writes at scale (005-38): the cause was the startup distance of 10 MB;
  index writes in proportion to each commit since 005-49 and 007-07.
* A cold start of minutes at 10M keys on s1: rule 4 by position (005-57,
  part 1), 214 s to 46 s in the prototype.
* Startup not bounded for BergDB's own take: the deadline at 2 sd in the
  code (007-07), T3 for BergDB's take proved (007-08).
* `BufferedStream` did not wake its consumer when full: 005-76.
* Replication experimental with known faults: unchanged (005-11, D4).
* Power loss on real hardware not established: unchanged; and a fault
  class found since, holes in an unforced tail, can refuse a start (005-83,
  moved to 014-01, not fixed).
* Tested on JDK 27 only: unchanged; compiled for Java 17 since `b10e072`.


## 3. Scope

2026.2 is what is on `main` at Frans's command. The question is which open
entries are done before it, and which become known issues in its notes.

### 3.1. Before the release

Proposed (D2): faults that break a stated contract, and changes whose
behaviour a database made with 2026.2 would otherwise keep.

* **005-82**, Fix: a corrupt record that `Db.getTrans` parses throws past
  the failure handling and leaves the database active, against
  docs/levels.md, section 3. Small: the parse moves inside the handler,
  with a test.
* **005-78**, Investigate, then a change: the retain duration is not kept
  in the stream, though it decides reclaim's cuts, so a restart takes the
  builder's value (default forever). The entry asks for it before the next
  release, "since it changes what a restart does with a database that
  reclaims". S to M, about a day and a half, with Frans's choice among its
  options A to C in between.
* **005-69**, Fix: `SystemClock` promises strictly increasing times and
  does not keep the promise. One line and a test, or the comment.
* **005-71**, Fix: a note in 010-01, P2, no code (the entry's
  recommendation).
* **005-80**, Decide: record `setBudget`'s race, fixed inside `988fe1a`;
  no code.
* **005-52**, what is left: the pause probe with a lowered budget, a
  measurement on F53 or s1, about half a day; the API is done and in
  `releases/next.md`. If it is not done, the notes say the comparison is
  not made.
* The notes and the documents: W1 to W3.

### 3.2. Candidates, for Frans

* **005-79**, integers instead of doubles in the Core's decisions: decided
  in direction, "not to be implemented until Frans says so". It changes
  the stream's bytes, not the format. M: about a day for the take, with
  its tests and measurements, plus C and Lean. D3.
* **005-11**, replication: kept as experimental, or removed. D4.
* **014-01** (from 005-83), recovery of holes in an unforced tail: the
  recovery contract is not decided, and 014 does not yet adopt a change.
  Proposed: a known issue of 2026.2, with docs/levels.md, section 8's
  wording.
* **005-77**, a cap of the pace's factor: the largest record after a
  large decrease of the startup distance grows with the keys (13 to 15 MB
  at 50M keys). About a day of F53 runs. Proposed: a known issue;
  decreases are rare.

### 3.3. Not for 2026.2

No effect on what the release is or says: 005-05 (what to do with BergDB,
unless D1 is B), 005-06, 005-07, 005-47, 005-54, 005-60, 005-65's accepted
rest, 005-72, 005-81; 007's T4; 015's entries as they come, unless Frans
adds one; the C clone (012), a separate project (D6).


## 4. The work

**W1. The release notes complete.** `releases/next.md` was begun on
2026-10-27 (`565499f`, 005-55) and lacks most changes of the two days
before, and some after. Found on a first pass over the log:

* Handles (009): eviction without the sweep, in batches of at most 2 ms;
  the lock-free fast path of reads; no stop-the-world of BergDB's own.
  Level 4's status as in docs/levels.md.
* Java 17 or later required: `--release 17` since `b10e072`, where 2026.1
  ran on Java 8. An incompatible change; it belongs first in the notes.
* Group commit (005-48, `e611709`): a sync that waits starts the flush.
* An idle eviction thread does not wake (005-51, `c2aab10`).
* Reclaim spaces its iterations by the live startup distance (005-61,
  `a175840`).
* A reader's load skips the eviction monitor (005-65, `988fe1a`), and
  `setBudget`'s race fixed there (005-80).
* The Pub API's Javadoc, built by `java/javadoc-pub.sh` (`216fc8b`).
* Lean: the theorems over handles (T-CACHE, T-READ, T2-C, T-PIN, T9,
  T12; 009, 005-62), the model before handles removed (005-62), rule 4 by
  position (005-58), T3 for BergDB's take (007-08).
* Props and `level1.sh`'s limits (section 2).

The method: walk `git log release-2026.1..` against `next.md`, commit by
commit, and add each change with its ID and date, as `next.md`'s own rule
says. Then the release notes' "Changes since 2026.1" are `next.md`, sorted.

**W2. 2026.1's post-release notes.** Its readme says that "a fault found
later that affects 2026.1 ... is recorded here", and says "None yet".
Faults fixed or found since, to check against 2026.1's code, a line each
(what, the effect, fixed in): 005-46 (an interrupt could fail the
database), 005-61, 005-63 (two databases on one directory), 005-70 (an
rw-transaction accepted after a reopen despite a conflicting write),
005-73 (close discarded I/O failures), 005-74, 005-75, 005-82, 005-83.
Into `releases/2026.1/readme.md`, before or with the release.

**W3. The documents current.** docs/levels.md: the status column's date
(2026-10-26), and section 8's "Open: group commit (005-48)", done since
`e611709`. README.md: the status table, the latest release. lean/README.md:
the list of theorems whose axioms the release checks. Only where they are
out of date with the code; the other sessions' uncommitted edits of
docs/levels.md first.

**W4. The entries of section 3.1**, and those of 3.2 that Frans takes, each
by its own entry, with its gates.

**W5. The release, by 008-01's steps**, with:

* Version 2026.2, version int 262, build `2026.2.YYMMDD.HHMM` in
  `BuildInfo`; the commit after the tag sets 2026.3-dev and 263.
* The tag `release-2026.2` on commit A; commit B holds `releases/2026.2/`,
  the folded `next.md` and README's line; commits in Frans's name without
  AI attribution, as for 2026.1.
* 2026.1's lessons: the F53 script hung for an hour on a `wait` that also
  waited for its own `caffeinate` (wait for the PIDs by name); the quiet
  check waited half an hour for other work, so the other sessions are told
  in advance; it took three hours, not two.
* The tests on the jar itself (`Unit`, `F`, `Night` with `-ea`) on JDK 17
  as well as 27, as Java 17 is now the stated minimum (a JDK 17 on
  F53 or s1 first).
* The Pub API's Javadoc as a zip, if D6 says so.

**W6. The numbers, against 2026.1.** 2026.1's runs (its readme,
"Baseline"), each with both jars in turns: Props; `performance.sh ab
2026.1 2026.2` (quick); ScaleBench at 10M keys on F53, M and C at 665 and
133 MB, G1 and ZGC, with gets from 1, 4 and 8 threads; on s1 the 10M load
and D at 133 MB with a cold start, and 1M. ScaleBench runs at 2026.1's
startup distance of 10 MB to compare, and at 200 MB for the figures the
notes and docs cite (only distances of 50 MB or more are cited). The
pause probe (009-03) beside them: 2026.1's longest waits against 2026.2's.
StreamDigest: new digests, since 007-07 and 005-50 change the bytes; they
are 2026.2's reference. In turns, the F53 block is about twice 2026.1's,
some 80 minutes; s1's 10M load alone is about 50 minutes per jar.

**W7. The C clone (012).** Its cross tests compare with Java's bytes,
which 005-76 changed (one physical-cut digest) and 005-79 would change.
012 is a separate project, tested by hand; D6 says whether the release
runs them.


## 5. Order and size

1. W1 to W3: about half a day, documents only, in a session of their own.
   Can start at once; W1 and W2 are needed whatever is decided.
2. W4: 005-82, 005-69, 005-71 and 005-80 in about a day together;
   005-78 a day and a half, with Frans's choice in between; 005-52's probe
   half a day. With 005-79 (D3, A), a day or two more.
3. The freeze: everything meant for 2026.2 committed, `main` clean, the
   other sessions told, `night.sh` OK on the freeze commit.
4. W5 and W6, by D5: one attended block of about four hours, or a
   night.

So about three to four working days of sessions from Frans's decisions to
the tag, with 005-79 out; five or six with it. The coordinator (013-02)
schedules them around F53's other work.


## 6. Risks

* The other sessions' work: the release takes a quiet F53 and a clean
  `main`. A session that commits during the freeze moves the release
  commit; the coordinator holds new work for the day.
* A gate that fails on the release commit stops the release, and Frans
  decides, as for 2026.1.
* 005-78 may find more than its size says (the C clone follows it, and
  its interplay with 005-79's iteration rule).
* The in-turn runs need 2026.1's jar to run today's tools: ScaleBench and
  the pause probe read internals that handles changed. 009-03 ran both
  jars in turns, so this is likely done; it is checked first in W6.


## 7. What is not made

As for 2026.1: no Maven coordinates, no website, no .NET (gone since
2026-10-29), none of the 2017 build's other jars. With D1 as B, the list
changes: see D1.


## 8. Decisions for Frans

**D1. Internal or published.**

* A (recommended): internal, as 2026.1: not published, not for
  production; the release is the record and the baseline. Publication
  stays with 005-05.
* B: published, as the first public release since 2015.4. It adds 005-05's
  decision (license, where, how), a review of the documentation for users
  (2026.1: "not reviewed for users"), a public repository or Maven
  coordinates, and a release without `items/` in the source zip, or with
  it. Days to weeks more, and it moves 005-05 into this item.

**D2. What must be done before the release.**

* A (recommended): section 3.1 as proposed: 005-82, 005-78, 005-69,
  005-71, 005-80, 005-52's probe, and W1 to W3.
* B: smaller: 005-82 and W1 to W3 only; 005-78 a known issue. Saves about
  two days. Databases of 2026.2 that reclaim then take the builder's
  retain duration at a start, and a later fix changes what they do.

**D3. 005-79, integers instead of doubles.**

* A: before the release. 2026.2's stream bytes are then those that a port
  reproduces exactly, and they change once, not twice. A day or two more;
  StreamDigest's new reference follows it; the C clone must follow for
  its cross tests.
* B (recommended): after, in 2026.3. The format does not change, so
  2026.2's databases open in later versions; 2026.2 stays the measurement
  of handles and bounded startup, without a change of the take beside
  them.

**D4. Replication (005-11).**

* A (recommended unless 005-11 is decided by then): kept, experimental, as
  in 2026.1; the notes list its known faults as docs/levels.md, section 9,
  does.
* B: removed before the release (005-11's option): the Pub API's
  `replica()` and `addReplica()` go, and the notes say so. About a day,
  with its own entry.

**D5. How the release runs.**

* A: one attended block, as 2026.1, now about four hours from the command
  to the tag, with the in-turn runs.
* B (recommended): over a night. In the evening, commit A and `night.sh`
  on it; in the night, W6's runs unattended on F53 and s1, as in 013-01;
  in the morning, the numbers, the notes, commit B and the tag. F53 is
  quiet at night, and nobody waits for it.

**D6. What goes in `releases/2026.2/`.**

* A (recommended): 2026.1's five files (the readme, the jar, the source
  zip, `baseline.zip`, `SHA256SUMS`) and the Pub API's Javadoc as a zip
  (`javadoc-pub.sh`, small). The C clone is in the source zip, as `items/`
  is, and not built or tested for the release.
* B: as A, and the C clone's cross tests run against the release jar, with
  their result in the notes. Hours more, and a failure there (005-76's
  digest, 005-79) is C's to fix, not the release's.
