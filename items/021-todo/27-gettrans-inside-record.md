021-27. Decide: Db.getTrans at a position inside a record fails the database
============================================================================

Status: waiting. Kind: Decide. Frans: decision.
Created 2026-11-09 by Frans Lundberg.

What: the Core's `Db.getTrans(tpos)` given a multiple of 8 inside a
committed transaction's record, not its start, and not in a meta block,
passes the checks made before the read, reads the bytes there as a
record, and fails the database: `DbFailedException` ("A read failed on
the storage (the cause)"), its cause a `StreamFormatException` ("Bad
transaction size, 2", "Bad lastByte: 120", "Bad item byte size,
2021161080 ... beyond the stream's record bytes"); every later call
throws `DbFailedException` until a restart, and a database in memory is
lost. Found by a black-box user of the C port (022), U2-4 (medium), with
`bergdb_get_trans` at `tpos + 8`; the C reproduction
`repro_get_trans_fails.c` in `/Users/f/fl/bench/022/apps/u2/`. Java does
the same.

Why: today's rule is that misuse of an API ends in an exception to the
caller, never in a failed database (020-24's 021-21 and 021-22; 020-27's
Q2, a bad argument of the Core API refused with
`IllegalArgumentException`). A position that is not a transaction's is a
caller's mistake, and the database takes it for damage.

Frans: decision. Which option below, and when. Not fixed: telling a bad
position from damage at a transaction's position is a design choice, and
the behaviour is what `Db.getTrans`'s Javadoc says today ("the bytes at
'tpos' are not a committed transaction": `DbFailedException`).

Done when: Frans has chosen; then, for A or B, a test that fails before
(the one below, its expectation turned), the fix, the Javadoc's
`@throws`, `BEFORE COMMIT OK` under the gate lock, and a line in
`releases/next.md`; C follows (022).

First step: Frans's choice.


1. What is known
----------------

* Reproduced in Java: `DbTester.testGetTransInsideARecord`, a put of a
  value of 1,000 bytes, then `getTrans(tpos + d)` for d = 8, 16, 24 and
  512: each `DbFailedException`, and a get after it throws
  `DbFailedException`. The test keeps today's behaviour, as the Javadoc
  says it; a fix turns it.
* Only the Core API can give such a position. The Pub API's
  `Connection.transactionInfo()` takes the position of the last get's
  value, never a caller's number. In C, `bergdb_get_trans` is in the
  public header, and `bergdb.h` contradicts itself: section B's list for
  `BERGDB_ARG` has "a position that is not a transaction's", while the
  function's comment says the database fails (022's own U2-4 note).
* `getTrans` refuses before it reads: a negative position, one not a
  multiple of 8, one in a meta block (005-34), one at or past the end
  (005-43). A position inside a record passes them all.
* The stream has no mark of a record's start. Each meta block, every
  200,000 bytes, holds the position of the last committed record before
  it (`MetaBlock.getLastTransSpos()`), and each record starts with its
  size, so the starts after a meta block can be found by walking the
  sizes, as `NodeStream.TransIterator` does.


2. Options
----------

* **A. Tell them apart on the failure path only.** `getTrans` reads at
  `tpos` as now. Only when the read or the parse throws
  `StreamFormatException`, or finds the record not committed, it checks
  whether `tpos` is a record's start: from the meta block at or before
  `tpos`, its last committed record, it walks the records' sizes forward
  (`RecoverableStream.getSpos()`, which skips meta blocks) until it
  reaches or passes `tpos`. Passed over: `IllegalArgumentException`
  ("Not a position of a transaction, P: inside the record at Q."), the
  database goes on. Reached: the record at `tpos` is damaged,
  `DbFailedException` as now. The walk meets a bad size or an invalid
  meta block: damage, `DbFailedException` as now. Cost: nothing on
  a good position; on a bad one, at most the records of one block
  distance and the record that reaches into it, a 4-byte read each. Left
  as now: a position inside a record whose bytes there form a well-formed
  committed record (a value can hold such bytes) gives a `StoredTrans`
  of them, not a failure. Needs care: a cut stream (reclaim; 005-39's
  search for a meta block after the cut), records over several meta
  blocks, and a position at or after `appendedEnd` (021-13's wait comes
  first). About 40 lines and tests; C follows.
* **B. Check before every read.** The same walk before each `getTrans`:
  every position that is not a record's start is refused, also one that
  would parse. Cost on every call, and `transactionInfo()` is one per
  get: up to a few thousand header reads for small records in 200 KB.
  Not recommended for that cost.
* **C. Keep it, and say it plainly.** The behaviour is the Javadoc's
  today; the Core API is "less stable, less safe" (020-27, Q1, Frans,
  16:27), and the Pub API cannot reach it. `Db.getTrans`'s Javadoc would
  say in so many words that a position other than a get's or
  `Trans.tpos` is taken as damage and fails the database; C's
  `bergdb.h` would drop "a position that is not a transaction's" from
  `BERGDB_ARG`'s list and say what its checks are. Javadoc only.
* **D. Read a failed header check as a bad argument.** A position whose
  size, version byte or last byte is wrong refused with
  `IllegalArgumentException`, without a walk. Damage at a real record's
  start would then be reported as the caller's mistake and the database
  would go on with it. Against 005-30, 005-34 and 005-82; not
  recommended.

Recommendation: C for 2026.4, as the Javadoc already says it and only
the Core API reaches it; A after the release, if the Core API (and C's
public header) should meet today's rule. A is local to `getTrans` and
costs nothing on a good position, but its cases (cuts, records over meta
blocks) need tests that do not fit before 2026.4's landings close.


Log
---

2026-11-09. Registered by coord-1109 from 022's U2-4 and taken by its
agent h31 (clone `clone-h31`, on main's b3a6b05): reproduced in Java,
not fixed (a design choice), options above. The test in commit "021-27"
in `clone-h31`, to land. Under the gate lock (18:22 to 18:30), on the
tree of 021-26's commit and this one: `BEFORE COMMIT OK (273 s)` (unit
1620, f 86, demos), `JAVADOC PUB OK`, `LEVEL 1 OK`.
