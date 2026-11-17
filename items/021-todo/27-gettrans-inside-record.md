021-27. Decide: Db.getTrans at a position inside a record fails the database
============================================================================

Status: done; landed (9dd125f3); Q27-1 fixed on branch
`021-27-size-bound`, gated, to land (section 5).
Kind: Decide, then Fix. Frans: decided 2026-11-12 (section 3).
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


3. Decision (Frans, 2026-11-12)
-------------------------------

13:21: "Yes, fix this in a agent at high. This is important. I consider
it a bug. It does destroy the Core database, the KV store. The Core API
may damage the integrity of the functionality built on top of it such as
Pub layer's secondary indexes, but it should not destroy the integrity
of the KV store itself." The fix was first option A.

13:26, a change of design: "021-27, option A. About this. Why is this
tricky. It is a read-only operation. It should fail or succeed, but never
block the database. This position comes from the user and cannot be
fully trusted. It is not from the internal database." With it the rule
010-04, R5: the Core API never destroys the KV store; a caller's mistake
is refused and the database goes on.

So the fix is option D, now right by R5: the paths are split by who gave
the position. Option A's walk (the records' sizes walked from the meta
block before `tpos`) had been written in the clone, not committed; it
was dropped and is not in the branch.


4. The fix
----------

Branch `021-27-gettrans` in the clone (section State), two commits on
main's `5c194e69`.

* **`Db.getTrans(tpos)`, a caller's position.** The checks before the
  read as before (negative, not a multiple of 8, in a meta block, at or
  past the end: `IllegalArgumentException`, nothing read; the wait for
  the writer at or after `appendedEnd`, 021-13). When the read or the
  parse at `tpos` throws `StreamFormatException` (a bad size, version
  byte or last byte, a record not committed, a node's checksum, a
  malformed node; `StreamChecksumException` and
  `VersioningStreamException` are subclasses), the call throws
  `IllegalArgumentException` ("Not a position of a transaction, P: the
  bytes there are not a committed transaction's record (the cause).", the
  read's exception its cause), and the database goes on.
  `IllegalArgumentException` because it is the type the same method
  already throws for the other positions that are not a transaction's
  (005-34, 005-43) and the Core API's type for a bad argument (020-27,
  Q2). An I/O error of the read (`StreamIoException`) is the
  environment's (010-01, P7) and fails the database as before; a read
  below a cut expires (`LookupTimeNotAvailableException`) as before. An
  `Error` fails the database as before (019-10).
* **`Db.Internal.getTrans(tpos)`, the database's own position.** The same
  read, with today's behaviour: a `StreamFormatException` is damage and
  fails the database (005-30, 005-34, 005-82).
* **Not detected, said in the Javadoc:** a position inside a record whose
  bytes there happen to form a well-formed committed record (a value can
  hold such bytes) gives a `StoredTrans` of them, of no real transaction.
  No check against it: the position is the caller's responsibility
  (010-04, R3's spirit).
* **The record's header before its array** (`NodeStream.readRecordHeader`).
  At a caller's position the 4 bytes read as the size can be anything up
  to the stream's length, and the iterator made an array of that size
  before it checked the last byte: up to 2 GB, an `OutOfMemoryError`
  that fails the database. Now the header check refuses a last byte
  other than 0 and 10, and for an exact start position also 0 (not
  committed), before the array is made. The same exceptions and messages
  as the checks after the read; a good record reads as before (one
  1-byte read was already made there). Left: bytes whose size is at most
  the stream's length and whose last byte and format byte are both right
  (about 1 in 65,000 for random bytes, or a value made so) still make the
  array; on a large stream with a small heap that can be an
  `OutOfMemoryError`, which fails the database (question Q27-1 below;
  fixed, section 5).

Callers of `getTrans` and their path:

| Caller | Position from | Path |
|---|---|---|
| `ConnectionImp.transactionInfoInner`       | the last get's `GetData.tpos` | Internal |
| the same, its loop over reclaim's steps    | a get before the step's time  | Internal |
| `stress/core-build/CoreDemo`               | `Trans.tpos`, as a user       | public   |
| `DbTester`, `DbTesterFailure`, `PubTester` | as each test says             | both     |

Reclaim and the start do not call `getTrans`: they read with
`NodeStream.TransIterator`, unchanged but for the header check above.

The Needs care of option A, with D: the walk is gone, so a cut stream
and records over several meta blocks need nothing of their own; tests
check them anyway. A position at or after `appendedEnd` waits for the
writer first (021-13), then is refused if it is inside the record.

Tests (all unit tests):

* `DbTester.testGetTransInsideARecord`, **turned** (its own commit,
  `91e5f352`, a changed expected value approved by Frans's 13:21 and
  13:26): `getTrans(tpos + d)` for d = 8, 16, 24, 512 now
  `IllegalArgumentException`, then a get, `getTrans(tpos)`, a put and a
  get work.
* `DbTester.testGetTransInsideARecordOverMetaBlocks`, new: a record of 20
  random values and one of 401,000 bytes, over two meta blocks; every
  multiple of 8 inside it is refused or gives a `StoredTrans` at that
  position (none fails the database), every one inside the next, last
  record refused; then the database goes on.
* `DbTesterFailure.testGetTransBelowTheCut`, more: a position inside a
  record below a cut expires, one inside a record after it is refused.
* `DbTesterFailure.testGetTransOfARecordBeingAppended`, more: a reader at
  `tpos + 8` of the record being appended waits for the writer, then is
  refused.
* `DbTesterFailure.testGetTrans` (corrupt reads) and
  `getTransOfDamagedRecord` (testGetTransChecksum, -Malformed,
  -BadValueSize): the damage now reached first through `Db.getTrans`,
  refused, the database goes on; then through `Internal.getTrans`, as
  `transactionInfo()` reads, which fails the database with today's
  expectations (their assertions moved to the internal path, not
  changed). A read error (`failReads`) through `Db.getTrans` fails the
  database as before.
* `testGetTransRefusesBadPositions` (positions past the end, in a meta
  block) unchanged and passing.

Javadoc: `Db.getTrans`'s `@throws IllegalArgumentException` and
`@throws DbFailedException`, and `Internal.getTrans`. `releases/next.md`:
a line in the Core API section.

C clone (022): C follows later, not now. `bergdb_get_trans` should then
do the same (refuse a format failure at a caller's position with
`BERGDB_ARG`; an internal read for its own positions), and its header's
contradiction (section 1) goes.

Question for Frans:

* Q27-1. The garbage size that passes the header check makes an array up
  to the stream's length (at most 2 GB). Bound it for a caller's
  position (for example, refuse a size over the heap's free memory, or
  read the record in parts)? Default: leave it, as the chance is small
  and a value made for it is the caller's own doing.
  **Decided, Frans, 2026-11-12, 14:09: "fix it."** (010-04, R5: a
  caller's misuse must never fail the database; an `OutOfMemoryError`
  from a garbage size would.) Section 5.


5. Q27-1: a large size believed only at a record's start
--------------------------------------------------------

Branch `021-27-size-bound` in the clone, from main's `06e91ff9` (with
021-27 landed, 9dd125f3), commit `2858ed36`.

What: the public `Db.getTrans(tpos)` reads with
`NodeStream.createTransIteratorAtCallersPos(tpos)`. When the header's
size at `tpos` (after the checks of section 4: range, last byte, format
byte) is over `NodeStream.CALLERS_SIZE_LIMIT`, 1 MiB, the iterator first
calls `NodeStream.recordHolding(tpos)`, before the record's array is
made. It walks the records forward by their sizes, reading each one's
header (`readRecordHeader`), from `RecoverableStream.getRecordStartBefore
(tpos)`: the record that the last valid meta block at or before `tpos`
names, if it is at or after the first position; else the first record
after the first position (meta block 0's end in a stream not cut; the
cut, a record's start, in a cut one). `getSpos()` skips meta blocks, also
those inside records. Reached `tpos`: the record is read as before.
Passed over it: `StreamFormatException` ("A size of S bytes at stream
pos P, which is inside the record at Q, not a record's start."), which
the public path turns into `IllegalArgumentException`, its cause; the
database goes on. A bad header or meta block on the way, or a start
after `tpos`: `StreamFormatException`, refused so too. A read of the
walk below a cut expires, as the read at `tpos` does.

When and by whom: on every public `getTrans` whose header size is over
1 MiB, by the reader's thread, after 021-13's wait for the writer (the
records before `tpos` are then in the stream in whole).
`Internal.getTrans` (transactionInfo) is unchanged: its positions are
the database's.

Why (a), the walk, and not (b), a read in bounded parts: the walk is
option A's code, local to one branch of `next()`, and costs nothing for
a record of at most 1 MiB, nearly all of them; a real record over 1 MiB
at its start (reclaim's, the take's, maintain()'s) costs the walk once:
the headers of the records from the meta block before it, at most one
block distance (200 kB) of records, three small reads each. (b) would
still need the whole record in one array for the parse
(`StoredTrans.parse` takes one array), so it bounds nothing unless the
parse is changed too. No record at its true start is refused, and no
`OutOfMemoryError` is caught. The bound, 1 MiB, is a cost choice only:
any size up to it is allocated, as for any read of a record.

Tests:

* `DbTester.testGetTransCraftedSizeInsideARecord`, new: a value of 3 MB
  (over 15 meta blocks) with eight crafted candidates (size of about the
  record's rest, the format byte, `LAST_BYTE` at its end), one at a
  multiple of 8 whatever the value's position. That position is refused
  with the walk's cause, so before the array; without the walk (checked
  by turning it off) the read made the 3 MB array and failed later, in
  the parse. The real 3 MB record at its start is still read; the
  database goes on.
* `DbTesterFailure.testGetTransBelowTheCut`, more: a record of 1.1 MB
  after the cut, at its start, is read: its walk starts at the cut, as
  no meta block after the cut is at or before it.

`releases/next.md`: a sentence added to 021-27's Core API line.


Log
---

2026-11-09. Registered by coord-1109 from 022's U2-4 and taken by its
agent h31 (clone `clone-h31`, on main's ef5b52f): reproduced in Java,
not fixed (a design choice), options above. The test in commit "021-27"
in `clone-h31`, to land. Under the gate lock (18:22 to 18:30), on the
tree of 021-26's commit and this one: `BEFORE COMMIT OK (273 s)` (unit
1620, f 86, demos), `JAVADOC PUB OK`, `LEVEL 1 OK`.

2026-11-12. Taken by coord-1112's agent gtr (13:22). Option A built in
the clone, then dropped at Frans's 13:26 (section 3); option D made on
branch `021-27-gettrans` (section 4). Gates on its head `ce3eb857`, each
in a slot: `BEFORE COMMIT OK (66 s)` (unit 1689, f 89, demos 14),
`LEVEL 1 OK` (13:38), `LEVEL 3 OK` (13:38 to 13:50).

2026-11-12. Landed by the coordinator (9dd125f3). Q27-1 decided by
Frans (14:09, "fix it."), fixed by gtr on branch `021-27-size-bound`
(section 5). Gates on its head `2858ed36`, each in a slot:
`BEFORE COMMIT OK (63 s)` (unit 1697, f 89, demos 14; 14:12 to 14:13),
`LEVEL 1 OK` (14:13 to 14:16).


State
-----

* Done: the fix and the tests, two commits on branch `021-27-gettrans`
  in clone `/Users/f/fl/bench/2026-11-12/gtr/clone` (from main's
  `5c194e69`): `91e5f352` the turned test, `ce3eb857` the fix. The
  targeted tests pass (DbTester, DbTesterFailure, the Pub testers, 535
  tests).
* Gates on `ce3eb857`, each in a slot: `BEFORE COMMIT OK (66 s)` (unit
  1689, f 89, demos 14; 13:33 to 13:34), `LEVEL 1 OK` (13:38),
  `LEVEL 3 OK` (13:50). Logs in `/Users/f/fl/bench/2026-11-12/gtr/`.
* Landed on main: 9dd125f3.
* Q27-1: branch `021-27-size-bound` in the same clone, from main's
  `06e91ff9`, head `2858ed36`. `BEFORE COMMIT OK (63 s)`, `LEVEL 1 OK`,
  each in a slot. Logs `before-commit-2.txt`, `level1-2.txt` in
  `/Users/f/fl/bench/2026-11-12/gtr/`.
* Not done: C (022), later.
* To continue: the coordinator lands `021-27-size-bound`.
