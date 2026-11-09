# 020-15 A kill-and-restart harness for the Pub layer

Created 2026-11-09 by Frans Lundberg. Status: done.

A harness that kills the JVM for real, with SIGKILL, during Pub-layer work
(objects and user indexes), restarts the database in a new JVM, and checks
what the promises allow: one of the bug hunts before release 2026.4's
candidate (020). Written by agent k15 of coord-1109 in a clone of `main` at
`a9e5488`.


## 1. The request

Frans, 2026-11-09, 09:21: "Start 1 to 4" (the coordinator's bug hunts,
this one among them); 09:22: "Use effort xhigh".

The coordinator's brief: nothing in the code killed a JVM during Pub-layer
work; IndexHarness, IndexJobsHarness and PrimaryHarness restart databases
inside one JVM. Build a harness where a child JVM runs a seeded random
schedule (objects of format 2, DbObjects and Data Objects, plain values at
object keys, index definitions and builds, deletions, lookups; several
threads) and logs what it believes is committed; the parent kills it at
random moments, many times, reopens the directory in a fresh JVM and checks
that the start works, that the state is one the promises allow, that every
active index gives exactly what IndexReference computes, that builds and
cleanups resume or end as 020-10 says, and then continues the schedule, so
that kills land in every phase. Stop when it runs clean for at least 1,000
kills spread over all phases, or at 15:00.


## 2. The method

The harness is `bergdb.pubimp.KillRestartHarness` (in `java/src`, beside
IndexHarness, whose generators and IndexReference it reuses) and the script
`java/stress/kill-restart.sh`. Its class Javadoc has the details; in short:

* **The parent** starts a child JVM (`-ea`) on a database directory, waits
  for the phase the kill aims at, waits a random delay and kills it with
  `Process.destroyForcibly()` (SIGKILL), then starts the next child on the
  same directory; a new database every 40 kills. The phases: during the
  start (`open`), during the checks after the start, while the start's
  resumed builds and cleanups run (`started`), during the waits for builds
  and cleanups (`verified`), during the schedule (`running`), in it right
  after a creation (`build`) or a deletion (`cleanup`), and during or after
  a `close()` that the schedule makes while its writers write (`close`).
  And one end with no kill (`exit`): the schedule calls `stop()` and
  returns from `main`, and the JVM must end by itself with status 0.
  For a probe, the parent's system properties `killrestart.phase` and
  `killrestart.delay` aim every second kill at one phase within a delay.
* **A child** opens the directory with `DatabaseBuilder.create()`, checks it
  against the journal of the earlier children, then runs its schedule until
  it is killed: 1 to 4 writer threads (transactions of 1 to 4 puts and
  deletes in `w()` and `rw()`: DbObjects with fields of every kind and
  their edges, Data Objects, Strings and byte[]s at object keys and at keys
  with a suffix, over three directories, the second inside the first; a
  sync after one in twenty), and an index thread (creations with or without
  `join()`, creations of a used name, deletions, deletions of a free name,
  joins, `Database.sync()`, and checks at a lookup time when every
  transaction up to it is known).
* **The journal**, a file beside the directory, one `write()` per line, so
  that a kill of the process keeps it: a transaction's start and its commit
  with its time, each sync that returned, each index operation with the
  time interval around it, each join that returned ACTIVE, and the start's
  time, written by `DatabaseImp.testHookAfterStart` before the index
  manager starts anything. A transaction's values are made again from the
  seed, so the journal holds no values. Each transaction also writes a
  stamp, its ID at `/x/sTHREAD.txt`, so that the database tells the last
  transaction of each thread that is there, and `transactionInfo()` gives
  that transaction's time and KVs.
* **The checks after a kill**, at T, the start's time of the first start
  after the kill (docs/levels.md, sections 3 and 8; Database's Javadoc;
  020-10, sections 3.2 and 4 to 6):
  1. the start works (a `DatabaseNotCreatedException` only before any
     start succeeded, as `DatabaseBuilder.start()` allows);
  2. a prefix: every transaction committed at or before T is there, none
     after it; the one in flight in each thread whole or not at all; each
     index creation or deletion that ended by T is there, none that began
     after it, and each name's definition is the result of a prefix of the
     run's operations on it;
  3. durability: no transaction lost that a sync returned for, or that was
     committed before a `Database.sync()` that returned; the same for index
     operations, and for an activation that a join saw before a sync; after
     a `close()` that returned, every transaction and index operation that
     returned is there, and so after a `stop()` and a return from `main`
     (`Database.stop()`: "also when the program returns from main right
     after this method");
  4. the data is the model's, key by key and byte for byte, and each
     directory's primary listing has no key more or less;
  5. the indexes: the definitions are the model's (name, generation,
     directory, levels; known active stays active); an active index's raw
     entries are exactly f over the data (IndexReference), a building one's
     a part of them; each marker is a deleted generation's; no entry of a
     generation that is neither live nor marked; each job ACTIVE with count
     0, or BUILDING, never FAILED; a free name has no job;
  6. the history: at three random past times of transactions that are
     there, each directory's listing, and each index stored then (its
     definition read at that time) with f over the data then as its
     entries, and `useIndex` working exactly when it was active;
  7. in a third of the runs and in each database's last run: every build
     ends ACTIVE, every cleanup ends, and every index gives exactly the
     reference's entries and scans (IndexHarness.queries);
  8. during the schedule, at a lookup time with every transaction up to it
     known: each index active or building as known, with the reference's
     entries and scans; a free name has no index; a directory's listing is
     the model's; no orphan entry.
* **So that a build or a cleanup is there to be killed**: half of the
  creations and deletions are synced at once; runs take now and then build
  steps of 2 to 9 values and a sleep of 1 to 8 ms in each build step, 5 to
  30 ms in each cleanup step (IndexManager's test hooks): a cleanup that
  ends within the 50 ms buffer of its deletion is never seen by a start.
  A third of the runs sleep 1 to 3 ms between a commit and its journal
  line, so that more kills find a transaction committed and not yet in the
  journal (its stamp then tells).
* **Per database**, the same in all its runs: reclaim on (a retain duration
  of 20 s) or not, a startup distance of 5 MB or the default, a cache of
  4 MB or the default.
* **Its own check** (`selfcheck`, first in the script, about 5 s): four
  planted faults, each must be found: a transaction written without its
  first write, syncs not made, an entry of a generation that does not
  exist, an entry of a live generation for a key without a value. Each was
  found (2026-11-09) by the check meant for it: a directory's listing, the
  durability check at the next start, the orphan check, the entries of an
  active index.

The Core's crash tests (CrashTest, PowerLossTest in the level scripts) cut a
copy of the stream at chosen byte positions inside one JVM; this harness
does not cut at chosen positions, but kills real processes with their
storage threads, build and cleanup threads, lock files and file streams,
and starts in a fresh JVM.


## 3. The findings

**No fault of BergDB found.** In 2,993 kills and 78 stops with a return from
`main`, every restart came to a state that the promises allow, with every
index exact; the runs are in section 4.

One observation, low, documentation, not fixed (for Frans, or 020-19):

* **KR-O1** (low): an index creation or deletion that returned can be undone
  by a kill, as any transaction that is not synced; the Javadoc of
  `IndexBuilder.start()` (`java/src/bergdb/pub/IndexBuilder.java`, lines 111
  to 131: "From its return, every write of the directory keeps the index")
  and of `Database.deleteIndex()` (`java/src/bergdb/pub/Database.java`,
  lines 329 to 339: "when this returns, the index is gone at every later
  lookup time and its name is free") does not say so. It is the general
  rule, which docs/levels.md, section 8, and the package page's "Good to
  know" state ("A transaction is written to storage soon after it returns;
  sync() waits until it is durable"), and the harness accepts it: each such
  loss was a prefix, the index back or absent as before the operation, its
  entries and markers consistent. Seen 15 times in the probe of seed 24
  (kills 0 to 5 ms after a deletion returned); in ordinary runs rarely, as
  the writers fill the write buffer and it flushes within milliseconds.
  Proposed: a sentence in both Javadocs, such as "Durable when a sync()
  after it returns, as a transaction." No test needed beyond the harness.

Faults of the harness itself, found while it was written and fixed before
the runs counted (false alarms, kept here for whoever extends it):

* **KH-1**: a `Database.sync()` was taken to cover the transactions up to
  `currentTime()` read before it, and that time to be a transaction's. It
  need not be one: `currentTime()` gives a time above the last completed
  transaction (here ...180003 with the deletion at ...180001), so "synced
  up to it" was compared with the start's time and failed. Now: no logged
  transaction with a time in (start's time, sync point] may be lost.
* **KH-2**: a killed run was resolved with the time of the start that
  resolved it; runs killed in between, before their schedule, had committed
  resumed build and cleanup steps after it, so the run's lost transactions
  looked like ones before the start's time. Now: the first start after the
  kill, its time written by `DatabaseImp.testHookAfterStart` before the index
  manager starts anything.
* **KH-3**: a creation lost by a kill leaves its generation in the journal,
  and a later creation of the name can get the same generation (G is the
  latest transaction's time, and the lost one's time never was there);
  the match of a creation in flight no longer excludes it.


## 4. State

**Done.** The harness, in the clone `/Users/f/fl/bench/2026-11-09/clone-k15`,
one commit `75be808` on `a9e5488` (BEFORE COMMIT OK, under the gate lock,
11:20): `java/src/bergdb/pubimp/KillRestartHarness.java` and
`java/stress/kill-restart.sh`, both new; nothing else changed. For the
coordinator to take to `main`.

The runs, all on F53 (2026-11-09), all clean:

| Seeds    | Harness                                    | Kills | Notes                            |
|---|---|---|---|
| 20261109 | `75be808`, by `kill-restart.sh 1000`       | 1,000 | 26 min; self-check; 45 exits     |
| 1109     | earlier: no close, exit, settings, history | 1,000 | 22 min; the phases it had        |
| 20 to 34 | this version, short runs and probes        |   993 | about 90 s each; and 33 exits    |
| 25       | a probe that killed every run at its start |   494 | empty databases: not counted     |

The final run, seed 20261109, `java/stress/kill-restart.sh 1000` at
`75be808` (11:21 to 11:47): the self-check, then by phase open 122,
started 130, verified 86, running 248, build 177, cleanup 150, close 87,
and 45 exits. At the starts that reached their checks: 301 builds in
progress, 55 cleanups, 84 runs resolved after a `close()` that returned
and 42 after a `stop()` and a return from `main` (all their transactions
there), 410,561 committed transactions there, 5,761 committed and not
synced lost, 22 in flight there and 1,060 not, 1,699 index operations
there and 42 lost (not synced, KR-O1); 180,749 entries compared at the
start's time, 74,222 in the schedule, 363,686 at 2,376 past times; 4,984
scans equal to the reference's.

The 1,000 kills of seed 1109, by phase: open 130, started 137, verified 92,
running 301, build 170, cleanup 170. At the starts that reached their
checks: 332 builds in progress, 71 cleanups (markers), 195,452 entries
compared at the start's time and 79,248 in the schedule, 5,098 scans;
715,936 committed transactions there, 9,018 committed and not synced lost,
2 transactions in flight there and 593 not. The probes of this version:
264 kills within 80 ms of a new database's open (no start refused, no
`DatabaseNotCreatedException`), 40 within 5 ms of a deletion (15 index
operations lost, as allowed, KR-O1), 42 right after a start with builds and
cleanups resumed, 25 at a `close()` (20 after it returned: every
transaction there), 44 right after a creation; and 33 runs that called
`stop()` and returned from `main` with writers, builds and cleanups in
flight, each JVM ending by itself, every transaction there.

**Left.**

* A line for `night.sh`, proposed, not made: after `night-tests`,
  `step kill-restart sh stress/kill-restart.sh 1000` (26 minutes on a
  loaded F53; the self-check first), and a line in its header's list of
  steps; the seed is the date, printed.
* KR-O1, for Frans: a sentence in two Javadocs, or nothing.
* Not covered, possible later: Linux (s1's ext4; only macOS's APFS ran);
  values that a build cannot take (format 1), whose FAILED build a start
  takes again; a power loss (the Core's PowerLossTest has its model).

**To continue**: `java/stress/kill-restart.sh [KILLS [SEED]]`; or by hand,
`java -cp java/build/bergdb.jar bergdb.pubimp.KillRestartHarness parent
BASE SEED KILLS [PER_DB [SECONDS]]`, with `-Dkillrestart.phase=NAME
-Dkillrestart.delay=MS` for a probe. A failure prints the child's output and
keeps the database's directory and its journal (`BASE/dbN`,
`BASE/dbN.journal`); the journal's lines are in the class Javadoc and
`readJournal`. A new check goes in `Child.checkAtStart` (at the start's
time) or `checkIndexAt` (any time); a new operation needs its journal line
before it acts, so that a kill between them is read as "not done".


## 5. Log

2026-11-09, 09:25. Created by agent k15 of coord-1109: the harness written
and run in the clone `/Users/f/fl/bench/2026-11-09/clone-k15`; its first
smoke runs found its own false alarms KH-1 and KH-2, fixed before any count.

2026-11-09, 09:56 to 10:19. 1,000 kills on F53 at the coordinator's word
("Run the 1,000 kills on F53 now, one parent"): clean.

2026-11-09, 10:20 to 11:10. The self-check (four planted faults, each
found); the close and exit phases, per-database settings, the history
checks, the commit lag and the probes added (KH-3 found by reading, fixed);
short runs and probes, clean; KR-O1 seen in the deletion probe. Committed
in the clone (`d91c0ff`, BEFORE COMMIT OK under the gate lock).

2026-11-09, 10:55 to 11:20. The exit phase (a `stop()` and a return from
`main`) added; short runs clean; the commit amended to `75be808` (BEFORE
COMMIT OK under the gate lock).

2026-11-09, 11:21 to 11:47. `java/stress/kill-restart.sh 1000` at
`75be808`, at the coordinator's word: the self-check and 1,000 kills and 45
exits, clean. Status done: the commit is the coordinator's to take to
`main`; KR-O1 and the `night.sh` line are Frans's.
