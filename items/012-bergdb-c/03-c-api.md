012-03. Task: the C API
=======================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase A (012-01, section 8). Effort: high. After: nothing.


# 1. The goal

`bergdb.h`, the C clone's whole API, designed before the code: the C
counterpart of `Db`'s public methods (012-01, section 5), with Java's
semantics where C can have them, and the reason for each departure.

Done when:

1. `include/bergdb.h` declares every type and function, each with a
   comment that says what it does, its errors, and who owns what. It
   compiles alone with the flags of 012-01, 6.1 (012-04's build checks
   it).
2. This file holds the table of `Db`'s public methods (43 on 2026-10-27;
   count them again, as 005-52 adds a setter and a getter of the cache
   size), `DbBuilder`'s settings and the inner types (`Trans.Builder`,
   `GetData`, `GetMany` with its stop conditions, `StoredTrans`,
   `StartInfo`, `SyncLevel`), each with its C counterpart or the reason it
   is left out.
3. The error codes cover every exception that `Db`'s methods declare,
   each mapped.
4. The rules are written: one caller at a time; ownership of keys, values
   and results, and lifetimes, as 012-01, 4.5 says (the caller's objects
   and their free functions, freed before close; data given to a callback
   valid during it only; no call of the database from a callback); what a
   failed database (P7) still allows; the units of time; the clock (012-01,
   4.4); what `bergdb_open` creates.
5. Two small examples are written against the header (and compile): C's
   `CoreDemo` (006-08) and a `getMany` with a prefix.


# 2. Read first

* `Db`'s Javadoc and each public method's comment and code, `DbBuilder`,
  `Trans` and `Trans.Builder`, `GetData`, `GetMany` and its stop
  conditions, `StoredTrans`'s public fields, `StartInfo`, `SyncLevel`,
  `KeyTransformation`, `ValueTransformation`, and the exceptions of
  `pub.util`, `storage` and `core`.
* `docs/levels.md`, section 3 (a transaction or a read that fails).
* 010-01: P7, P9, P10, P12. 012-01, sections 4 and 5. 006-08's
  `CoreDemo.java`.


# 3. The work

1. Go through `Db`'s methods one by one and write the table (done item 2).
2. Decide, and write why:
   * **Handles and contexts.** An opaque `bergdb_db`; a transaction
     builder `bergdb_trans`; a read context in place of `GetData` that owns
     the buffer a value is returned in; a result type for `getTrans`.
   * **Options.** A struct with Java's defaults (`bergdb_options_init`):
     the node size (8, 14, 30 or 62; 30 by default), the startup distance
     (50 MB), the cache budget (200 MB), the retain duration (forever),
     the internal fraction (0.25), the clock (a function and its context;
     by default the system clock, milliseconds times 10,000 as Java's
     `SystemClock`; the test clock, `CoreTestClock`'s, in the library, so
     that times and bytes can be deterministic: 012-01, 4.4), the
     database id (random, or given, or the test id). Java's checks of each
     (a startup distance of at least 10, a retain duration of at least one
     second, and so on).
   * **Keys.** Byte keys (bkeys), converted to segments inside as
     `Keys.toSegments(byte[])`; a helper for ikeys, as Java's
     `Keys.toBytes(String)`, since the Core's string keys are ikeys.
   * **Values.** How `getOne`'s null (no value: never put, or deleted) is
     told apart from an empty value; how long a returned value stays
     valid (in the read context's buffer, until its next call; 012-01,
     4.5).
   * **`getMany`.** A range struct (lookup time, start key, inclusive,
     direction) and the stop conditions (none, end key, count, prefix), or
     a callback that returns `ADD`, `STOP`, `CONTINUE` or `ADD_AND_STOP`
     as Java's; both, if simple.
   * **Transactions.** Put, delete, the read set (`keyRead`, the lookup
     time; refusal as `RerunException`), the key and value transformations
     as callbacks that must not fail; after `execute`, the time and the
     positions (`tt`, `tpos`, `lastPos`, `nextPos`).
   * **Errors.** One enum: OK, RERUN, NOT_AVAILABLE (a lookup time or a
     position before the first available one), FAILED (the database has
     failed; the first failure's text is kept), IO, FORMAT (corrupt, or
     another version), STATE (not started, or closing), ARG, LIMIT (the
     record limit, the top node ordinals), NOT_CREATED (an incomplete
     creation), NOMEM. A text for the last error of a handle.
   * **Status.** One struct filled by one call, or one function per
     getter: choose the simpler to keep in step with Java.
   * **Replicas and encryption** left out (012-01, section 1); an
     encrypted database gives FORMAT.
3. Write the header, then the examples against it.


# 4. Tests

The header compiles alone; the examples compile (they link once the
functions exist, in 012-13). Later tasks implement the functions and test
them; this task checks only the design.


# 5. Notes

* Small and like Java (P12): no function that Java's `Db` does not have,
  but for the C necessities (free functions, the error text, the ikey
  helper).
* The header may change as the implementation teaches; each change after
  this task is noted in this file's progress section, with its reason.


# 6. Progress

Not started.
