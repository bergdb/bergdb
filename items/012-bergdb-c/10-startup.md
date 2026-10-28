012-10. Task: startup and recovery
==================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase C (012-01, section 8). Effort: max. After: 012-09.


# 1. The goal

C opens existing databases as Java does, with bounded startup (Level 2),
and recovers after a crash: it rebuilds exactly what Java has in memory
after its startup, so that the next records are the same bytes. With this
task, Levels 0 to 2 are done and milestone M3 is reached.

Done when:

1. **Recovery**, as `RecoverableStream`: the last valid meta block, the
   last whole record after it, the torn record's fill, an incomplete
   creation refused (`DatabaseNotCreatedException`, 005-33), and what a
   start writes and does not write.
2. **The start's checks**, as `Db.startInner`: the formats, the node size
   (005-50), the database id, the startup distance taken from the stream.
3. **The startup**, as `DbStarter` and `NodeCollection`: the startup
   section read from the last record's startup position, its nodes and
   positions (`posMap`, `newById`, `posToId`), the key nodes cut back to
   the startup time, Rule R, the memory pointers, the super root at the
   startup time from `topPos`, the section's transactions rerun so that D,
   the take's state (`TransSeq`: since `f89846d` also each transaction's
   own bytes, the sums D and O and their checksum, and the span) and the
   startup position are as Java's, and rule 4 by position (005-57) in
   `linkToCanonical`.
4. **Loads**: a node not in memory is read from the stream when a read or
   a write follows a stream pointer, as `NodeCollection` does it, Rule R
   included.
5. **The bytes after restarts.** `StreamDigest`'s third mode (restarts)
   for its Level 2 configurations, and random workloads with restarts:
   C's files equal Java's.
6. **In turns.** The same workloads run with Java and C taking turns at
   every restart: the files equal those of Java alone and of C alone.
7. **Crashes.** 012-05's crash variants: C and Java recover each cut copy
   to the same bytes, give the same dumps, and write the same bytes after
   it.
8. **Java to C.** C opens every database of the sets without reclaim with
   its bounded startup, and its dump equals Java's; full replay (012-08)
   is no longer used to open a database.


# 2. Read first

* Java: `DbStarter` (501 code lines), `NodeCollection` (456),
  `RecoverableStream` (its recovery), `Db.start` and `startInner`,
  `StartupPos`, `StartInfo`.
* `docs/sis-model.md` (startup, Rule R, D, T1 and T2), 011-11 (the Level 2
  alignment, M18 on `topPos`), 005-57 (rule 4 by position) and 005-58
  (its proof), 005-32 (a start that throws), 005-33 (an incomplete
  creation), 005-40 (formats checked before anything is written), 007-01
  and 007-05 (what startup costs).
* `java/stress/RestartInvariance.java` and `CrashTest.java`.


# 3. The work

1. Recovery first, with the crash variants: C recovers each copy as Java
   does (bytes and dumps), before any startup logic (open, recover,
   close).
2. Port `DbStarter` and `NodeCollection`'s startup and loads, keeping
   Java's order of steps.
3. The restart comparisons: one restart, then a restart after every
   transaction (`StreamDigest`'s `l2-every1`), then the random sets.
4. The runs in turns: the strongest check of the rebuilt state, as a
   difference in D or the take shows in the next record.
5. Java's databases opened with bounded startup, and `bergdb-dump` on
   them.


# 4. Tests

The comparisons of done items 5 to 8 on the quick and full sets;
functional tests of a restart after every transaction, of a crash cut at
every position of a small stream (C alone, against C's own dumps), and of
the refusals (another format, another node size, an incomplete creation).


# 5. Notes

* The hardest task of 012 (012-01, section 10). A difference after a
  restart is a difference in the rebuilt state: compare C's D, the take's
  queue and the startup position with Java's at the same point. A small
  Java probe that prints them (in the harness, package `bergdb.core`, on
  the internals through `Db.internal()`) and a C counterpart help; they
  are tools of this task, not part of the API.
* What startup reads is bounded by the startup distance (Level 2). C must
  not read more than Java, as that would hide a difference in the section.


# 6. Progress

Not started.
