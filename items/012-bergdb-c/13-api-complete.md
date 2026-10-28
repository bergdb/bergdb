012-13. Task: the rest of the API, and durability
=================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase E (012-01, section 8). Effort: high. After: 012-11, 012-12.


# 1. The goal

Every function of `bergdb.h` (012-03) implemented, tested and described,
and the durability of a C database written down and tested: what a user
of the C clone can rely on.

Done when:

1. Every function of `bergdb.h` exists and has a functional test, and the
   table of 012-03 says for each of `Db`'s public methods what C has.
2. **Settings and status**: the startup distance (with Java's clamp and
   dummy transaction), the retain duration, the internal fraction, and
   every status value of 012-03's table, equal to Java's on the same
   database where Java's is not a matter of timing (the stream length,
   the counts, the first available time and position, the startup
   distance).
3. **Durability**, written in the C directory's `readme.md` and tested:
   what is durable after `execute`, after `sync` at each level, and after
   close; the buffer's size; `F_FULLFSYNC`; the durable length; a write or
   a force that fails fails the database (P7), and what `sync` and close
   do then.
4. **Close**: writes, forces, frees everything; a second close is
   harmless; calls after close get STATE.
5. **Examples**: C's `CoreDemo`, which prints the same as Java's on each
   other's databases; and the `getMany` example of 012-03.
6. **The API's text**: the header's comments checked against the code,
   and a short guide in `readme.md` (open, write, read, close, errors,
   one caller at a time).


# 2. Read first

* 012-03 (the design and the table); 012-01, 4.3; `Db`'s Javadoc of each
  method; `docs/levels.md`, section 3; 011-07 (Java's durability) and
  005-44 (what a sync waits for).


# 3. The work

1. A list of `bergdb.h`'s functions with their state (done, tested,
   missing); finish the missing ones.
2. The durability tests: kill the process (`kill -9`) after `execute`,
   after `sync`, and during a write, and check what a restart finds
   (C alone; the power-loss side is 012-14's).
3. The examples and the guide.


# 4. Tests

The functional tests (done item 1); the durability tests; the examples in
the gate.


# 5. Notes

* Small API, as Java's (P12): no function beyond 012-03's design without a
  note in this file of why.


# 6. Progress

Not started.
