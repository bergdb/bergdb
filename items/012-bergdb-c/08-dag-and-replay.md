012-08. Task: the Dag, reads, and Java's databases by full replay
=================================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: not started**; approved with 012-01 by Frans's
go (012-01, 9.1).
Phase B (012-01, section 8). Effort: max. After: 012-07.


# 1. The goal

The multiversion map in C (Level 0) and C's first reads of Java's
databases (Level 1, a replay of the whole stream): `Dag`'s puts, deletes
and reads at a time, `getMany`, and `getTrans`. Milestone M2: C reads
Java's databases.

Done when:

1. `Dag`: put and delete of a transaction's keys at its time, with the
   splits and new top nodes as Java makes them; `getOne` at a time,
   giving the value, its time and its transaction's position (as
   `GetData.kvTime` and `tpos`); `dirtyNodeBound` (005-31).
2. `getMany`: forward and backward, from a start key, inclusive or not,
   with the stop conditions of `GetMany` (none, end key, count, prefix, a
   callback), as `GetMany.Chain` walks.
3. `getTrans`: the record at a position, its time, positions and
   key-value pairs, with Java's refusals of positions (005-34, 005-43).
4. **Full replay**: a database is opened by reading every record from the
   start and applying its value nodes, puts and deletes, at the record's
   time. On databases without reclaim only: a cut stream cannot be
   replayed (Level 3 needs Level 2), and what reclaim rewrites is 012-11's
   to understand.
5. `tools/bergdb-dump` prints 012-05's dump format; for every database of
   the sets without reclaim, C's dump by full replay equals Java's
   `Dump.java`. `cross.sh` runs it with C as side B.
6. Java's tests ported where C has the behaviour: `DagTester`, the
   `@Nano` tests of `Dag` and `GetMany`; a random test of the Dag against
   a simple model map (key to its versions) with reads at random times.


# 2. Read first

* Java: `Dag` (802 code lines), `GetMany` (336), `KeyAccessPath`,
  `PutData`, `GetData`, `Kvt`, `DagTester`; `Db.getOne`, `getMany`,
  `getTrans` and `getOneInternal` for what the database adds around the
  Dag (the first available lookup time, the actual lookup time).
* `DbClock.lookupTime`: a read never sees a running or a future
  transaction.
* `docs/levels.md`, Levels 0 and 1; 011-04, "The level 1 bugs", for what
  went wrong in Java's Level 1 in 2026.


# 3. The work

1. Port `Dag`'s put path and read path, then `GetMany`.
2. An in-memory database (Level 0): a Dag fed by transactions in memory,
   for the unit tests and the model test.
3. Full replay over 012-06's trans iterator.
4. `getTrans` over 012-06's parser.
5. `bergdb-dump`, and its place in `cross.sh`.
6. The ported tests and the model test.


# 4. Tests

The ported tests; the model test under the sanitizers; the dump
comparison on the quick and full sets (databases without reclaim).


# 5. Notes

* A full replay gives the same key-value versions as Java's database, so
  the dumps compare, but not the same nodes in memory as Java's startup:
  that is 012-10. The replay is a step and a test vehicle, not the way C
  will open databases.
* The replay applies every record's value nodes, Java's internal ones too
  (the dummy of `setStartupDistance`), as Java's Level 1 replay did; the
  dump shows internal keys as Java's dump shows them.
* Memory (012-01, 4.5): the Dag's replacements and splits share values and
  handles between objects, and make temporaries (`first`, `last`), as in
  Java; the counts and the pending list take care of both, so the port
  keeps Java's order. `getMany`'s cursor counts the objects it holds, so
  that a long range frees what it has passed at safe points between
  leaves; a version read for one operation only is made without a holder
  and freed at the next safe point.


# 6. Progress

Not started.
