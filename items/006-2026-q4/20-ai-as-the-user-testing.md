# 006-20 AI as the user: black-box application testing

Created 2026-11-09 by Frans Lundberg. Status: done.

A note on a way of testing that the coordinator proposed on 2026-11-09 and that
found more serious bugs that day than any other method: an AI agent plays a new
user of BergDB, writes a real application from the documentation alone, and
checks every result against its own model. Section 4 gives the 12 applications
of that day (020-24) as the worked example.

Frans, 2026-11-09, 16:47: "Please make a subitem of 006. A note with a
description of this way of testing. By AI being the BergDB user, black box. As
we talked about. Also briefly describe the 12 applications created for this
purpose as an example of this method." In his own words, it is scenario
testing, done as a BergDB user, black-box against the specification, with just
the jar and the Javadoc; it would have been far too expensive by hand; "a new
tool for testing".


## 1. The idea

An agent plays a new user of BergDB. It gets only what a user has: the release
jar (`java/build/bergdb-release.jar`), the README, the Javadoc and the release
notes. It does not read the implementation while it writes.

It writes one real application for one realistic scenario: an event log, an
inventory with indexes, a password vault, a multi-threaded service. A typical
application is 1,500 to 2,500 lines of Java, built with plain `javac`, with a
`main` that runs the scenario end to end. The application keeps an oracle of
its own, usually an in-memory model of what the data must be at every time,
and checks every result BergDB gives against it. It exits non-zero on a wrong
result.

The agent reports every bug, every place where the Javadoc was unclear, wrong
or missing, and every awkward API. It fixes nothing.

The method combines known practices:

* **Scenario testing**: tests built from realistic stories of use, not from
  single functions (Cem Kaner, "An Introduction to Scenario Testing", 2003).
* **Black-box testing against the specification**: the tester knows the
  contract, here the Javadoc, not the code.
* **Testing against an oracle** (model-based testing): a simple model gives the
  expected answer to every query.
* **Dogfooding**: using one's own product as a user would, here with users
  written to order, one per kind of user.

Why it was not done before: twelve applications of 2,000 lines, each with an
oracle, are weeks of a programmer's work for one release. With agents the cost
is tokens, not people, and the twelve took an afternoon. The method also uses
little CPU, which mattered on 9 November: F53 was busy with gates and timings,
while the usage left before the week's reset was large.


## 2. Why it finds what reviews and harnesses miss

1. **It tests the contract, not the code.** Reviews and unit tests start from
   what the code's authors thought. An application starts from what the
   Javadoc promises, and finds where the two differ.
2. **It combines features as users combine them**: a long key and then a
   restart; reclaim and then `transactionInfo()`; a parallel stream inside
   `rw()`; a database directory deleted and created again. Each feature was
   tested alone; the combinations were not.
3. **It uses sizes no test uses**: keys of 90 KB, arrays of 2 GB, 200 open
   databases, 4,000 start cycles, a full disk.
4. **It misuses the API as real people do**: a hurried developer sharing a
   `Connection`, calling the database from inside an action, reusing a
   builder. This gave the principle that misuse must end in an exception to
   the caller, never in silent damage.
5. **Every application has an oracle**, so a wrong value cannot pass quietly.

The rule that makes it work is **independence**: the agent does not read the
implementation while it writes the application, only afterwards, to explain a
surprise. An agent that reads the code first writes applications that follow
the code's assumptions and finds much less. The same rule kept the day's
reviewers apart from each other's findings.


## 3. How to run it

**The brief.** One common brief for all applications
(`/Users/f/fl/bench/2026-11-09/apps-brief.md`), with a short prompt per agent
that names its scenario. Its rules, in short:

* "You are a new user." Build the release jar once from a clone of `main`;
  use only `bergdb-release.jar` on the class path.
* Read only what a user reads: README, the Javadoc, the overview page, the
  release notes. "Do NOT read java/src/bergdb/pubimp, core or other
  implementation code while writing the app; afterwards you may read it to
  explain a surprise."
* Write the application outside the repository, plain `javac` and `java`,
  with a `main` that runs it end to end and checks its own results.
* Record as you go: Javadoc unclear, wrong or missing; results that
  surprised; bugs (a wrong result, a throw from legal use, a hang); awkward
  API. A minimal reproduction for each bug.
* The report: a findings table (ID, kind bug, doc or API, severity, what,
  reproduction), then what went well. Fix nothing; commit nothing.

**The agents.** One agent per scenario, at high effort or above, in rounds of
three, each round with a deadline well before the release candidate: the
fixes need time to land (on 9 November, reports were due two hours before the
last landing).

**After each report.**

* A bug goes to a fixer agent: a failing test first, then the fix, the gate,
  `level1.sh` for the Core, and an independent review for a Core fix. Each
  becomes an entry in the release's todo list (021-13 to 021-23 on that day).
* A documentation finding: the Javadoc is made true; no behaviour change.
* An API wish or a question of meaning goes to Frans's list; in a release
  meant as a stable baseline, nothing changes meaning without his word.

**Choosing scenarios.** The kinds of application users build (logs, catalogs,
services, embedded and mobile use); the parts least tested (the storage
layer's error paths, encryption, the Core API used directly); and misuse.
Each round can aim at what the previous rounds did not touch.


## 4. The 12 applications of 9 November (020-24)

Four rounds of three, started at 12:41, 13:50, 15:10 and 15:50; each agent
reported within about 25 to 60 minutes. The reports are
`items/020-release-2026-4/24-new-user-apps/01` to `12`; the applications are in
`/Users/f/fl/bench/2026-11-09/app-u1` to `app-u12`. Sizes are the hand-written
Java lines.

| App | Scenario | Lines | Main findings |
|---|---|---|---|
| 01 | event log with time travel | 2,017 | `transactionInfo()` during writes failed the database (high; 021-13) |
| 02 | inventory, user indexes | 2,393 | no bug in 1.2 M checks; a double read into an int is cut, not rounded (doc) |
| 03 | service, 8 writers, 8 readers | 2,494 | no bug in about 150,000 transactions; `stop()`'s Javadoc wrong (doc) |
| 04 | 2 M objects, 4 MB cache | 1,853 | no bug in 15 M values; the heap follows the startup distance (doc) |
| 05 | document store | 2,373 | a key of 90 KB or more: the database could not start (critical; 021-16) |
| 06 | metrics with reclaim | 1,618 | `transactionInfo()` refused live data after reclaim (medium; 021-17) |
| 07 | encrypted password vault | 1,689 | keystream reuse, no integrity (high); writes 8 times slower than needed |
| 08 | disk full, I/O errors | 1,593 | a lost last stream file drops synced records silently (medium; doc) |
| 09 | the Core API as a byte store | 2,945 | prefix scan wrong (high; 021-18); a KV's time inexact (021-19) |
| 10 | 200 databases, 4,000 starts | 1,612 | a deleted and recreated directory lost synced data (high; 021-20) |
| 11 | re-entrancy and misuse | 2,870 | threads in `rw()` gave wrong data, a wrong index (high; 021-21, 021-22) |
| 12 | rich Java types | 6,430 | a 2 GB array put failed the database (high; 021-23) |

App 12's line count leaves out generated classes of up to 32,768 fields.

**Totals.** About ten high or critical bugs (two of them in every release since
2026.1), several medium ones, and about 60 Javadoc corrections, each fixed with
a test or written down for Frans. The applications also confirmed much that
held: crash recovery was exact in every app that crashed its database (36
crashes in app 06, 14 in app 09), every value was right across 4,000 start
cycles, and no deadlock was found in 57 scenarios of misuse.

**Decisions they led to.**

* Encryption removed from 2026.4's public API (Frans, 16:12; 020-28): the
  keystream reuse after a crash cannot be avoided by a careful user, and a fix
  needs a format change; the design for a later release is 017-10.
* The principle that misuse of the API ends in an exception to the caller,
  never in wrong data or a failed database (021-21, 021-22).
* Every null or bad argument of the Core API refused with
  `IllegalArgumentException`, as in the Pub API (020-27).

**The yield did not fall over four rounds.** Round 1 found one high bug,
round 2 one critical and one medium, round 3 two high in the Core API and the
encryption flaw, round 4 four high. New scenarios kept finding new faults.


## 5. What to keep, and next steps

* **Make it a standard step before every release**, with new scenarios each
  time: the scenarios of one release become cheap regression tests, and new
  ones find new faults.
* **Keep the applications.** Each exits non-zero on failure and runs in a few
  minutes (`run.sh` in each directory). The best could become regression
  tests in `java/stress/`, run by `night.sh`; a decision for after 2026.4.
* **Ideas for next scenarios**: an application across two releases (export
  and import); Android, on the emulator (006-18-03); a long-running service
  under a week of simulated clock; an application written from the C port's
  header alone (022), to test the port's documentation the same way.


## 6. Later the same day: round 5, and the C port's users

Round 5 (020-24-13 to 15, 17:28) found one high fault (U14-1, puts slowing down under index churn with a
retain duration) and about 20 contradictions between the documents. Round 6 (16 to 18) ran on the frozen
candidate.

At 17:20, Frans sent the method to the C port's session (022) as a suggestion. Three black-box users of the
C library wrote applications from `bergdb.h` and its readme alone (022-06). The C library writes Java's bytes,
so a fault they found in C was often Java's too, and a Java reproduction followed within the hour:

* **021-25:** reclaim stops cutting under keys in time order with deletes. It was in 2026.3 too; a part of it
  was fixed for 2026.4, and the rest is for 2026.5.
* **021-26:** a regression from that day's own clock fix, fixed before the candidate.
* **021-27**, and the slow loop with long keys; both for Frans's list.

The C session also fixed six faults of its own.

Frans, 19:20: "The C port has been valuable for finding issues with the Java implementation. That is one
conclusion from today's bug hunt. The other is the value of AI-user testing. Those were the most productive
bug hunting tool."


Log
===

2026-11-09. Written at Frans's request (16:47) by coord-1109.

2026-11-09. Section 6: round 5, the C port's black-box users, and Frans's conclusion (19:20).
