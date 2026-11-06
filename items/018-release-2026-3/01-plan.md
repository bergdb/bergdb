018-01. Plan: release 2026.3, a bug-free Core
=============================================

Created 2026-11-05 by Frans Lundberg, from his request: "Create item
nnn-release-2026-3 with this plan for working towards 2026.3." The plan
answers a strategy that Claude proposed the same morning (section 4).

**Status: the goal, the rules and Frans's decisions made (2026-11-05,
09:28 and 09:43).** The way of working is worked out step by step with
Frans, and this plan is updated with it.


## 1. The goal

Frans, 2026-11-05, 09:28: "let's make the goal of [Release] 2026.3 "a
bug-free Core". DbObject and user indexes is experimental. For the Core,
we aim for no known issues at all. All A, B, C, and D are fixed. That is
the goal; while working we may make exceptions."

* **The Core**, in this plan, is everything that is not experimental:
  * the Core Layer (010-01, P12): `Db`'s public methods and what is under
    them, the packages `bergdb.core`, `dag`, `storage`, `stream`,
    `common`, `pub.util` and `nanotest`, as `java/stress/core-build.sh`
    builds them;
  * the Pub API, but DbObject and user indexes (D4);
  * their tests and tools.

  Where the Core Layer alone is meant, the plan says "the Core Layer".
* **No known issue of the Core** at the release: every known fault of the
  Core is fixed, whatever its severity, A to D (D1).
* **Experimental** in 2026.3: DbObject and user indexes (D2; the methods
  are D6's). Their faults stay open, outside the goal.
* **Exceptions**: while the work goes on, Frans may leave a fault of the
  Core as a known issue of 2026.3. Each exception goes into section 5 with
  his words and the date. An agent makes none.

**Ready** (D7), when all of these hold:

1. No known fault of the Core is open: section 3.1's list is closed, and
   no open entry of 015 or 019 is a fault of the Core, but Frans's
   exceptions.
2. All tests pass, on the release's commit: `night.sh` (with
   `before-commit.sh`, `core-build.sh`, the four level scripts, the night
   tests and the medium conformance set), `night.sh large`, and the
   harnesses of section 6; and the jar's tests on F53 and s1 with JDK 27
   and 17, as for 2026.2 (016-09).
3. The stream's bytes are explained: StreamDigest's digests of the
   release's commit are compared with 2026.2's, the reference of its
   notes' "Verification" (`baseline.zip`, `f53/digests.txt`), and every
   configuration whose decided digests differ is named by a line of
   `releases/next.md` (section 2). The release's digests then become the
   reference for the next release, as 2026.2's did.
4. The documentation is up to date with the code: the Javadoc, README.md,
   docs/levels.md and lean/README.md, with the experimental parts marked
   (W1), and the release notes.
5. The release notes' known issues are all of the experimental code, but
   Frans's exceptions.
6. Frans says that it is ready. The release is made at his command.


## 2. Rules for the work

Frans, 2026-11-05, 09:43: "The principles 010 must hold unless Frans makes
an exception. All changes to the stream format must be approved by
Frans."

* **010's principles hold**, P1 to P12 (010-01), unless Frans makes an
  exception.
  * Before a commit, the agent that makes a change checks it against P1
    to P12. If the change would break one, the agent stops and asks
    Frans, and commits nothing until he answers. His exception goes into
    section 5.
  * The principles most likely to meet this work: P7 (a failed database
    stops), which the failure paths of section 6.2 must keep; P10 (few
    settings), met by 015-05's `createIfMissing()`; P12 (a small Core
    Layer), met by any new method of `Db`; P2 (a deterministic stream),
    met by 015-87.
* **Every change to the stream format is approved by Frans** before it is
  made.
  * The format is, as in 016-01, section 3, the layout and meaning of
    what a start reads: the meta blocks, record headers and records, the
    node encodings, reclaim's table, the version numbers and the reserved
    internal keys.
  * A change of which bytes a workload writes, within the format, is not
    a change of the format (005-79's take was one). It is recorded in the
    change's own entry (or item): its folder keeps StreamDigest's digests
    before and after the change, and its line in `releases/next.md` names
    the configurations whose digests changed and the entry that holds
    them, as 015-54's does (`digests-base.txt`, `digests-new.txt`). No
    file holds a reference between releases: the reference stays 2026.2's
    digests, and the release explains every difference from them (section
    1, "Ready", 3). Frans, 2026-11-05, 12:46, option (a).
  * A proposal that changes the format is written in its entry, with what
    changes and why, and waits for Frans's explicit approval; his words go
    into the entry's log. Likely: 015-87 (the retain duration in the
    stream). 014-01 needs none for 2026.3: Frans decided its contract,
    prefix interruption, at 14:36 (section 3.1).


## 3. Where we start

On 2026-11-05, 015 has 70 open entries. Most come from one search for
unknown faults: the reviews of release 2026.2 on the evening of 2026-11-03
(016-06). Of the 60 open Fix entries, 50 are in 2026.1 too, and 6 are new
in 2026.2. The lists below are as of 2026-11-05; the entries' own
`Status:` lines and 015's tables are the source. 015 takes no new
entries: since 2026-11-05, 09:38, they go to 019 (D3).


### 3.1. The Core's known faults

52 entries of 015, S2-F24 of 015-49, and the fault of 014-01: 54 faults.
This is the goal's list.

| Area | Entries | Count |
|---|---|---|
| FileStream                                | 015-06 (its rest), 26, 31, 32, 33; 014-01 | 6 |
| BufferedStream, StorageManager, MetaBlock | 015-34, 35, 74, 78, 79, 80, 81, 82, 83    | 9 |
| Startup                                   | 015-72, 75, 76, 77, 87                    | 5 |
| Db and reclaim                            | 015-27, 50, 52, 53, 54, 55                | 6 |
| Eviction                                  | 015-66, 67, 68, 69, 70, 71                | 6 |
| JMX                                       | 015-38                                    | 1 |
| The Core Layer's tests and tools          | 015-04, 08, 11                            | 3 |
| Pub API: rw-transactions, connections     | 015-41, 42, 47, 48, 59, 60, 62, 64        | 8 |
| Pub API: builder, keys, Time, CryptoKey   | 015-05, 44, 45, 57, 58, 63, 65; S2-F24    | 8 |

Of these:

* New in 2026.2: 015-52, 66, 68, 70, 71 and 76.
* Javadoc and comments only: 015-54, 74 and 77.
* A decision by Frans comes first: 015-05 (a start on an empty or missing
  directory), 015-27 (a failed append's transaction was visible; decided
  2026-11-05: intended, not a fault), 015-87 (his answers to F1 to F7)
  and 014-01 (the recovery of holes in an unforced tail; decided
  2026-11-05: outside the crash contract, not a fault).
* Checked by a second agent: R2's and R3's faults (015-26, 27, 31 to 35,
  38). The others have the reviewer's own test or probe. Each fix starts
  with its failing test anyway, by its entry's "Done when".

Changed since, 2026-11-05: 015-27 left the list (intended, not a fault);
019-01 joined (a meta block's version read as 2 bytes, from 015-74), and
019-02 (the streams' refusals of a bad length, found by harness 6.3,
018-02). 014-01's fault left the list (Frans, 14:30 and 14:36): the crash
contract is prefix interruption, under which a hole in an unforced tail
is damage outside the contract, not a fault; 014-01 stays open in 014 for
the broader model (014-01, section 7). 015-73 left the list (Frans, 15:35;
the table's row "Startup" follows): a last record's startupPos changed to
an earlier record's start is outside the fault model for 2026.3, option
(a); 015-75's checks stay, and a checksum of the record header waits for
the next change of the record format (019-07). 015-51 left the list
(Frans, 21:03; the table's row "Db and reclaim" follows): a value
transformation's result above the value limit is the caller's fault, as
an exception from it is, and fails the database (P7); a refusal is
017-07, section 3, to consider. 2026-11-06: 019-20, 019-21 and 019-22
joined and left, fixed the night they were found by harness 6.5
(018-05).

Changed since, 2026-11-06: 019-10 joined (an unchecked exception or
`Error` from a read of the storage leaves the database going on, found by
harness 6.2, 018-03), and was fixed the same night.


### 3.2. Outside the goal

| Group | Entries |
|---|---|
| Experimental: objects, user indexes | 015-23, 28, 29, 30, 36, 37, 39, 43, 46, 61; 49 but S2-F24 |
| Limits (D5)                         | 015-84, 86, 88                                             |
| Not the Java code                   | 015-02 (C clone), 03 (Lean), 18 (a night run), 19 (items)  |

015-49 holds review S2's 27 faults. All but S2-F24 (keys with a lone
surrogate, in the goal's list) are in the objects, the user indexes and
their scans. 015-18, `night.sh large` on 2026.2, is a run, not a fault;
`night.sh large` on 2026.3 is part of "Ready" (section 1).


## 4. The strategy and the decisions

Claude proposed six points in the morning of 2026-11-05, in a chat; they
are summed up here with Frans's answers of 09:28. His words on 3 to 6:
"About 3-6, let's gradually work on this strategy, it will be updated."

1. **Define "bug-free" so that it can be checked**, with severities A to
   D, and a fresh review of each area that finds nothing. Answered by D1.
2. **Decide the supported surface**: DbObject and user indexes
   experimental. Answered by D2.
3. **Triage once**: a second agent checks each fault that has none, each
   fault gets a severity, 015-49 is split, and entries are made only
   after triage. Frans: "3. is not required right now." With D3.
4. **Fix by fault class**, with a harness that finds the whole class,
   including faults nobody has reviewed. Frans: "I like 4, it seems like
   a good idea." Section 6.
5. **An order**: A first, then the harnesses, B, and C in batches; a fresh
   review of each area after its fixes. Frans: "No, no particular order
   needs to be enforced, we will fix everything."
6. **A stopping rule and tracking**: a weekly table of faults found, fixed
   and open by severity; the release when A and B are zero and a fresh
   round of reviews finds none. Frans: "No, not as stated." Replaced by
   D7.

The decisions:

* **D1.** "1. as above, A, B, C, and D, but only for Core." Every known
  fault of the Core is fixed, whatever its severity:
  * A: committed data lost or wrong, or a database that cannot run again;
  * B: the database fails, or gives wrong answers, in ordinary use;
  * C: misuse, edge cases, a wrong exception, a leak;
  * D: Javadoc, comments, tests, tools.

  The severities matter only for exceptions (section 5).
* **D2.** "2. Yes, experimental." DbObject and user indexes are
  experimental in 2026.3 (W1).
* **D3.** "3. No changes now." The existing entries stay as they are: no
  triage, no split of 015-49. A new fault is registered by 019's rules:
  since 2026-11-05, 09:38, every new entry goes to 019, and 015 takes no
  new entries (Frans, through session bergdb-34).

Frans answered the plan's first questions at 09:43:

* **D4.** The rest of the Pub API is in the goal: "1. Yes, included."
  That is: `String` and `byte[]` puts, gets and deletes, rw-transactions,
  connections, `Time`, `TestClock`, `CryptoKey`, `DatabaseBuilder`.
* **D5.** The limits: "2. As default." A limit of 2026.2's notes (the
  collectors, gets with 8 readers, a decrease of the startup distance at
  50M keys, D's loose bound, T4 not proved, overload and more) is not a
  known issue. It stays in the notes' limits, and 015-84, 86 and 88 go on
  as Frans decides, outside the goal.
* **D6.** What is experimental: "3. OK." `Database.indexBuilder` and
  `deleteIndex`, `Connection.useIndex` and `usePrimary`, the classes
  `IndexBuilder`, `UseIndexBuilder` and `UsePrimaryBuilder`, and a value
  that is neither a `String` nor a `byte[]`: `put(Object)`, a put of an
  object at a key, and a get into another class.
* **D7.** When 2026.3 is ready: "4. When we have no known Core bugs. When
  all tests pass, when documentation is updated. When the list of known
  issues are all for experimental code. When Frans say it is ready."
  Section 1, "Ready".


## 5. Exceptions

None yet. Two kinds, each made by Frans only:

* a fault of the Core left as a known issue of 2026.3: its ID, his words,
  the date, and what the release notes say of it;
* a change that breaks one of 010's principles (section 2): the change,
  the principle, his words and the date.


## 6. Harnesses by fault class

The known faults of the Core fall into a few classes. A harness that
finds a class finds the faults of it that no review has met yet. Each
harness below is a proposal. They are worked out one at a time with
Frans, and this section is updated.

A harness is shown to work when it fails on each known fault of its class,
on the code before that fault's fix; the fixes then make it pass. Where it
runs (`before-commit.sh`, a level script, `night.sh`) is decided for each
harness; `before-commit.sh` stays at about 2 minutes.

The differential test of the user indexes, proposed with point 4, is not
for 2026.3: they are experimental (D2).


### 6.1. Corrupt streams at a start

* Known faults: 015-72, 75 (and 015-07, 005-74 and 005-75, fixed).
* What it does: takes streams written by real runs and makes damaged
  copies of them: a byte flipped, a range cut out, the tail cut at every
  byte, a record's size or `startupPos` changed with its checksum made
  right again, as R6's probes did.
* What it checks: its core is the crash contract (014-01, section 7), a
  hard requirement: a copy truncated at any byte starts with exactly the
  transactions of its committed prefix and passes the audit. Other damage
  is outside the contract, and its detection is best effort: the start
  refuses the copy before it writes anything, or a read fails the
  database (P7). The cheap refusals of 015-72, 75 and 019-01 stay in the
  goal's list: a violation is refused rather than used.
* 014-01's holes in an unforced tail are such other damage, not a fault
  (Frans, 2026-11-05, 14:36).
* So is 015-73's (Frans, 2026-11-05, 15:35, option (a)): a last record's
  startupPos changed to the exact start of an earlier record that the
  take never reached passes 015-72's and 015-75's checks, and the start
  succeeds without the transactions before it. The harness counts such a
  copy as known to pass undetected, not as a failure. A checksum of the
  record header would catch it, at the next change of the record format
  (019-07).
* Built on 2026-11-06: see 018-07. It fails on each of the five, and
  found 019-30 to 019-34. It runs in the unit tests of
  `before-commit.sh` (a sample) and in the night tests (the full set);
  its skip list holds the four open ones until they are fixed or decided
  (019-34 was fixed the same night).


### 6.2. Failures and interrupts in storage

* Known faults: 015-06's rest, 32, 34, 35, 38, 53, 66, 78, 81, 82.
* What it does: a test stream wraps `FileStream` or `MemoryStream` and,
  at its Nth call, throws an `IOException`, throws an unchecked exception
  or an `Error`, or interrupts the calling thread. A short workload
  (start, puts, gets, reclaim and eviction on, stop or close) runs for
  N = 1, 2, ... until it ends with no injection. BergDB's own threads (the
  storage consumer, the evictor, JMX's monitor) are interrupted too.
* What it checks, after each run: the database went on, or it failed and
  every later call says so (P7); `close()` returns and reports the
  failure; the directory's lock is released, and a new start on the
  directory works; no BergDB thread is left; a restart holds every
  transaction that a `sync()` confirmed, and none that was refused.
* Built on 2026-11-06: see 018-03. It wraps `FileStream` from above
  (6.3's `StrictStream`) and from below (`FileStreamIo`), on a new and a
  reopened database, and makes a `stop()` too. It fails on 015-32, 35,
  53, 78 and on 019-09, each before its fix, and found 019-10; 015-06's
  rest, 34, 38, 66, 81 and 82 it does not reach (018-03, section 6). It
  runs in the unit tests of `before-commit.sh` (a sample, about 4 s,
  beside the f-tests) and in the night tests (3.5 minutes); its skip list
  holds 015-80 (019-10 until its fix, the same night).


### 6.3. The stream contract

* Known faults: 015-26, 31, 33, 79, 80, 83.
* What it does: a strict `AppendOnlyStream` for tests checks each call
  against the interface's Javadoc: one writer at a time (as R5-F5's test
  stream does), no negative length, a cut within the length, `EOFException`
  for a read past the end. It throws at once on a breach. `BufferedStream`
  and `StorageManager` run on it. `FileStream` and `MemoryStream` pass one
  shared contract tester, with the edges: an empty stream, a cut at the
  length, the file-size limit.
* What it checks: no breach in any run, and every implementation passes
  the contract tester.
* Built on 2026-11-05: see 018-02. It fails on each of the six, and found
  019-02. It runs in the unit tests of `before-commit.sh`, at no cost to
  its time, and in the night tests; its skip list holds the seven until
  their fixes remove their lines.


### 6.4. Sizes and times at their limits

* Known faults: 015-50, 55, 76.
* What it does: makes transactions at the edge of every limit: values
  near `valueLimit()`, value transformations that grow a value, times near
  the last database time, settings at their bounds; with reclaim and
  eviction on, and restarts.
* What it checks: each transaction is either refused before its go point,
  with the database going on, or committed. The database never fails, and
  after a restart it takes commits.
* The exception: a value transformation's result above the value limit
  is the caller's fault, as 015-51 decided (Frans, 2026-11-05, 21:03). One
  whose record does not fit fails the database (P7), and the transaction
  is not in the stream. As in 015-27 (intended), readers may see that
  transaction before the failure: `Db.executeInner` calls
  `dbClock.transactionEnd()` before `store()`, where the record check
  throws. The harness counts such a run as the caller's fault, not as a
  failure. A refusal is 017-07, section 3, to consider.
* Built on 2026-11-06: see 018-06. It fails on each of the three, and
  found no new fault. It runs in the unit tests of `before-commit.sh`
  (2 s) and in the night tests (97 s).


### 6.5. Eviction's accounting

* Known faults: 015-67, 68, 69, 70, 71.
* What it does: random eviction schedules and budget changes, during
  reads and writes, with `Audit` after each batch, and the resident bytes
  compared with a recount.
* What it checks: the audit reports nothing that is right; the resident
  bytes equal the recount; no batch passes its handle limit; a budget
  decrease settles within the budget when the pins fit.
* Built on 2026-11-06: see 018-05. It fails on each of the five, and
  found 019-20, 019-21 and 019-22, fixed the same night. It runs in the
  unit tests of `before-commit.sh` (about 1 s) and in the night tests
  (under 2 minutes).


### 6.6. Concurrency

* Known faults: 015-35, 80, 82 (and 015-12 and 015-14, fixed).
* What it does: the jcstress tests planned in 016-07, for the shared
  fields that reviews R1, R2, R4 and R5 list in their section 6.
* What it checks: no forbidden outcome.


### 6.7. The Pub API's promises

* Known faults: 015-41, 42, 47, 48, 59, 62.
* What it does: random sequences of the Pub API's calls on `String` and
  `byte[]` values (put, get, delete, exists, `w()`, `rw()`, lookup times,
  `freezeLookupTime()`, `transactionInfo()`, restarts), run against
  BergDB and against a simple reference in the test: a map of each key's
  versions by time.
* What it checks: every answer equals the reference's, as the Javadoc
  promises it; a change of an array after its put does not change the
  stored value.
* Built on 2026-11-05: see 018-04. It fails on each of the six, and found
  019-15 (key replace and a delete), done 2026-11-06; five questions for
  Frans where the Javadoc is not clear. It runs in the unit tests of
  `before-commit.sh` (1 s) and in the night tests (80 s).


### 6.8. Faults outside the harnesses

Fixed one at a time:

* in the Core Layer: 015-04, 08, 11, 52, 54, 74, 77, 87;
* in the Pub API: 015-05, 44, 45, 57, 58, 60, 63, 64, 65, and S2-F24.

015-27 and 014-01 left this list on 2026-11-05: decided as not faults
(015-27 intended; 014-01's holes outside the crash contract, 014-01,
section 7). The entries' own Status lines say which are done.


## 7. The work

* **W1. DbObject and user indexes marked experimental** (D2, D6): the
  Javadoc of each method and class in D6's list, README.md and
  docs/levels.md where they describe the Pub API, and a line in
  `releases/next.md`. Their tests stay in `before-commit.sh`. Done
  2026-11-05.
* **W2. The harnesses** (section 6), one at a time, the first chosen with
  Frans. Frans chose 6.3 first (2026-11-05, 10:27); built that day
  (018-02). 6.2, on 6.3's strict stream, built in the night 006-12
  (018-03).
* **W3. The Core's faults** (section 3.1), in any order (point 5). Each
  is fixed by its entry: its failing test, the fix, `BEFORE COMMIT OK`,
  and the level script of a mechanism it changes (AGENTS.md), within
  section 2's rules. A new fault becomes a 019 entry (D3); one of the Core
  joins the goal's list. 015-87 is done (14:25), and 014-01's contract
  for 2026.3 is decided (14:36; section 3.1): neither waits.
* **W4. The documentation** (section 1, "Ready", 4): kept up to date as
  the fixes go in, and read through before the release.
* **W5. The release**, made as 2026.2 was (016-09, by 008-01's steps),
  when section 1's "Ready" holds, at Frans's command. Its StreamDigest
  run is compared with 2026.2's digests, every difference explained by
  `releases/next.md` ("Ready", 3), and its digests are the next
  release's reference.


## 8. Log

2026-11-05, 09:35. Written from Frans's goal and answers of 09:28, with
the lists of section 3 from 015's tables and the reviews' reports
(016-06, 016-07). Nothing started.

2026-11-05, 09:50. Frans's answers of 09:43 to Q1 to Q4 (D4 to D7) and his
rules (section 2) added: the rest of the Pub API joins the goal's list
(54 faults), "Ready" is D7, and harness 6.7 is new. New entries go to 019
since 2026-11-05 (D3).

2026-11-05, 10:19. W1 done: the Javadoc of D6's methods and classes says
that they are experimental in 2026.3, with known faults, and may change in
a later release; for a put and a get, when the value is neither a `String`
nor a `byte[]`. So do the Pub API's overview and `bergdb.pub`'s package
description, and a paragraph in README.md and docs/levels.md, section 1,
which did not describe them; `releases/next.md` has the entry. JAVADOC PUB
OK, BEFORE COMMIT OK.

2026-11-05, 10:32. W1's five questions answered by Frans at 10:31: "Sure,
go ahead with those five." Marked too: `Database.PRIMARY`,
`StartupInfo.getStartupJobs()` (the index jobs a start resumes), and
`DbObject` and `DbArray` in `bergdb.pubimp`; the exceptions
`IndexAlreadyExistsException`, `NoSuchIndexException`,
`MissingKeyFieldException` and `ObjectCreationException` say that they
belong to the experimental parts, as `BadReplicaException` said of
replication (016-04). README.md's and docs/levels.md's paragraphs stay.
The entry of `releases/next.md` lists them.

2026-11-05, 10:50. Frans's answers of 10:47, to session bergdb-e8: 015-54
"as recommended", R7-F5's code fix (an agent on it); 015-27 "as
recommended, this is intended, durability is handled separately": done,
not a fault, and out of the goal's list; 015-74's optional check "as
recommended": registered as 019-01, a fault of the Core that joins the
list, for harness 6.1's class. 015-05 is to be discussed further.

2026-11-05, 10:52. W2's first harness, 6.3, built (018-02): sections 6.3
and 7 updated. It found 019-02, which joins the goal's list (section
3.1).

2026-11-05, 11:40. 015-05 decided by Frans (11:34 and 11:39):
`DatabaseBuilder.create(p)`, as today's `dir(p)`, and `open(p)`, which
refuses a directory without a database; `dir(p)` removed. No new setting
(P10). The change started by session bergdb-e8's agent.

2026-11-05, 12:46. Where StreamDigest's reference lives between
releases, which section 2 did not say. (a) Each change of the bytes keeps
its before and after digests in its own entry, as 005-79 and 015-54 did,
and its `releases/next.md` line names the changed configurations and the
entry; the release compares its digests with 2026.2's and explains every
difference. (b) One living file, such as `releases/next-digests.txt`,
that each such change regenerates. Frans: "As recommended", (a).
Sections 1 ("Ready", 3, new; W4 now cites 4), 2 and 7 (W5) updated, and
`releases/next.md`'s intro.

2026-11-05, 14:12. 015-88 decided by Frans, in a discussion with
session bergdb-e8: the retry sleep capped at 640 ms (10, 20, 40, 80,
160, 320, 640, then 640 ms), the contract unchanged; the rest of the
retries moved to 017-06, with his question whether `rw()` should ever
give up under overload. The overload limit is documented: the Javadoc
says that under overload a transaction may never commit, a limit in the
release notes (D5), not a known fault. 015-88 stays in section 3.2's
limits until the cap lands.

2026-11-05, 14:25. 015-87 done (session bergdb-e8's agents): the retain
duration and the internal fraction are kept in the stream, in the reserved
internal KV `/#i/dreclaim/-settings.txt` (the format change Frans approved
at 13:12; F5's option 1 at 13:52), with no builder value; StreamDigest's 4
`l3-*` configurations change, their digests in 015-87's folder.

2026-11-05, 14:40. 014-01 for 2026.3, decided by Frans with session
bergdb-e8 (14:30, his assumption; 14:36: "Yes, do it."): the crash
contract is prefix interruption: written bytes are correct, only a
truncated tail is recovered, and the provider ensures it (014-01, section
7). Its fault, the recovery of holes in an unforced tail, leaves section
3.1's list, as 015-27 did; 014-01 stays open in 014 for the broader model.
Harness 6.1's core is a truncation at every byte; other damage is outside
the contract, its detection best effort. Sections 2, 3.1, 6.1 and 7 (W3)
updated; the contract is stated in AppendOnlyStream's Javadoc,
docs/levels.md, section 8, and `releases/next.md`.

2026-11-05, 15:41. 015-73 decided by Frans, to session bergdb-a2 (15:35:
"Yes. Go ahead."): option (a), a startupPos changed to an earlier
record's start is outside the fault model for 2026.3; 015-75's checks
stay. It leaves section 3.1's list, as 015-27 and 014-01 did, and harness
6.1 counts such a copy as known to pass undetected. Option (c), a checksum
of the record header, is 019-07, for the next change of the record
format, with Frans's approval (section 2). Sections 3.1 and 6.1 updated;
`releases/next.md` names the limit.

2026-11-05, 21:06. 015-51 decided by Frans, to the coordinator of the
night 006-12 (21:03: "'a' for 015-51. And also add the possibility of a
refusal to the to-consider list of the long-term item."): R7's first
option, the contract written down and the code unchanged (8427ff0). A
value transformation's result above the value limit is the caller's
fault, as an exception from it is, and one whose record does not fit
fails the database (P7). It leaves section 3.1's list, as 015-27 and
015-73 did, and harness 6.4 counts it as the caller's fault. A refusal,
which needs a design of when transformations run, is 017-07, section 3.
Sections 3.1 and 6.4 updated.

2026-11-05, night 006-12. Harness 6.7, the Pub API's promises, built
(018-04): random calls on `String` and `byte[]` values against a reference
of each key's versions by time. It fails on 015-41, 42, 47, 48, 59 and 62,
each with its fix reverted, and found 019-15, which waits for Frans; five
questions on the Javadoc (018-04, section 6). Section 6.7 updated.

2026-11-06, night 006-12. Harness 6.2, failures and interrupts in
storage, built (018-03): a fault at every call of the stream and of the
file calls under `FileStream`, on a short workload, with P7, the close,
the lock, the threads and a restart checked after each run. It fails on
015-32, 35, 53, 78 and 019-09, each before its fix, and found 019-10 (an
unchecked exception or `Error` from a read leaves the database going on),
in its skip list until fixed. Section 6.2 updated.

2026-11-06. W2: harness 6.5, eviction's accounting, built in night
006-12 (018-05); section 6.5 updated. It fails on 015-67 to 015-71 with
their fixes taken out, and found three faults of the Core, 019-20 and
019-21 (index nodes counted below their bytes) and 019-22 (a warmup kept
a large value), fixed the same night (section 3.1).

2026-11-06, night 006-12. Harness 6.1, corrupt streams at a start, built
(018-07): copies of streams written by `Db`, truncated at every byte (the
crash contract) and damaged otherwise (bytes flipped, ranges cut out,
header and node fields set). It fails on 005-74, 005-75, 015-07, 015-72
and 015-75, each with its fix's main hunk reverted, and found 019-30 (a
record's time or `topPos` changed within the checks, 015-73's class),
019-31 (whole records cut out of the middle), 019-32 (a node's klongs
and pointers unchecked, 015-07's class) and 019-34 (a meta block's
position unchecked, 019-01's class), faults of the Core that join section
3.1's list, and 019-33 (Fletcher-16's 0x00 and 0xff); all in its skip
list. 019-34 was fixed the same night. Every truncation passes. Section 6.1 updated.

2026-11-06, night 006-12. Harness 6.4, sizes and times at their limits,
built (018-06): random transactions of the Core Layer at the value limit,
the index nodes' bound, the last times and top node ordinals, and setters
at their bounds, with reclaim, eviction and restarts, and a lowered
record limit. It fails on 015-50 and 015-55, each with its fix reverted,
and on 015-76 with the old Javadoc's promise as its oracle; no new fault.
Section 6.4 updated.
