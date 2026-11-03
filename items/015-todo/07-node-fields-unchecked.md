015-07. Fix: a node's inner fields are not checked, and a read that meets one does not fail the database
========================================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For release 2026.2 (016-01, section 6, the rule for findings: verified,
no format or API change).

What: the node parsers do not check their inner fields against the node's
size: `StoredKeyNode`'s key count, `StoredValueNode`'s value and key
sizes, and `StoredTopNode`'s pointer count (only by an assert). A node
whose Fletcher-16 checksum is right but whose field is wrong (a corrupt
stream, or a fault in a writer) gives an `ArrayIndexOutOfBoundsException`
or a `NegativeArraySizeException` in a load (`NodeStream.readNode`).
`Db.getOneInternal`, `getMany` and the reads before a transaction's go
point catch only `StreamException`, so the exception escapes to the
caller and the database stays active.

Why: docs/levels.md, section 3: a read that fails fails the database. A
database that goes on after such a read may write on a wrong view.

Verified: a probe in 005-82's work (its Log, 2026-11-03), on the clone's
jar: `getOne`, `getMany` and a put each threw
`ArrayIndexOutOfBoundsException`, and a later put was taken.

Done when: each parser checks its fields against the node's size and
throws `StreamFormatException` (as 005-74 did for the record and node
sizes), and the reads fail the database with that cause; a test per
parser that fails before the fix; `BEFORE COMMIT OK`.

First step: 005-82's probe as tests in `DbTesterFailure`.

Found 2026-11-03 by the work on 005-82 (016-05).

**State** (2026-11-03, 16:50, F1): the change, its tests and the gate are
done in `/Users/f/fl/bench/016/015-07/repo` (base `3e32f02`, in
`/Users/f/fl/bench/016/015-07/BASE`; made on `c70a87d`, then moved onto
`f2cb23b` and `3e32f02` as `main` took 005-69, 005-79, 005-80 and 005-82,
with 005-82's tests adapted, see the Log); handed off for the review
(`/Users/f/fl/bench/016/015-07/handoff/`). Next: the review's findings,
answered in the Log, then the final hand-off with Outcome and Status. To
resume: the Log's last entry; the clone's `git diff` holds the change.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 16:20 to 16:25, by F1 (016-05), in
`/Users/f/fl/bench/016/015-07/repo`:

* **The parsers** check their inner fields against the node's size, read
  from its first four bytes, and throw a `StreamFormatException` (not a
  checksum's), as 005-74 did for the record's and the nodes' sizes:
  * `StoredValueNode.parse`: the node's size at least `MIN_SIZE`, 24 (the
    header, the id, the offset from the transaction, a size field), and
    within the buffer; the value's size from 0 to what leaves room for the
    key's size field; the key's size, as before a positive multiple of 8,
    now also within the node.
  * `StoredKeyNode.parse`: the node's size at least 32 and within the
    buffer; the key count at most `(size - 32) / 16` (`getByteSize`).
  * `StoredTopNode.parse`: the node's size exactly `40 + 16 *` the pointer
    count (`getByteSize`), and within the buffer, checked before the
    arrays; before, only an `assert` after them checked it (the `assert`
    stays, now always true).
  The callers keep their signatures: `NodeStream.bytesToNode`, as a load
  (`readNode`) and a record's parse call it, and the tests.
* **The reads fail the database**: with the parsers' exception a
  `StreamFormatException`, `Db.getOneInternal`, `Db.getMany` and the reads
  before a transaction's go point (they catch `StreamException`) fail the
  database with it as the cause; no change there.
* **The tests**:
  * Per parser (unit): `StoredValueNode.testRefusesSizesBeyondTheNode`
    (a value size of -1 and of 1,000, a key size of 8,000 and one 16
    bytes past the node, a node size of 20), `StoredKeyNode.
    testRefusesKeyCountBeyondTheNode` (counts 32,767 and 3, one more than
    the node holds), `StoredTopNode.testRefusesPointerCountBeyondTheNode`
    (one pointer more, and 127). Each makes the node's checksum right and
    parses it with `NodeStream.bytesToNode`, in a buffer 64 bytes longer
    than the node, as a load's is (helper
    `StoredValueNode.parseWithRightChecksum`).
  * 005-82's probe as tests, `DbTesterFailure` (unit):
    `testBadKeyCountInGetOne`, `testBadKeyCountInGetMany`,
    `testBadKeyCountInPut`, with a new test stream, `KeyCountStream`, whose
    reads of a whole key node give it a key count of 32,767 with its
    checksum made right. Each: 2,000 keys with eviction after every
    transaction; the get, the scan or the put fails the database with the
    parse's `StreamFormatException` ("Bad key count") as the cause;
    `assertRefused`; nothing appended; a restart on a copy, with the
    audit, reads every key.
* **The mutation**: the parsers' new checks disabled (`if (false)`), the
  tests kept: all six new tests fail. The three `DbTesterFailure` tests
  with "the load did not fail the database:
  java.lang.ArrayIndexOutOfBoundsException: Index 1024 out of bounds for
  length 1024" (and `databasesStopped` names them); the parser tests at
  their first case. Case by case (a probe outside the repository, on the
  mutated build): value size -1, `NegativeArraySizeException`; 1,000 and
  key size 8,000, `ArrayIndexOutOfBoundsException`; the key size 16 past
  the node and the node size 20, parsed without an error (the bytes after
  the node read); key count 32,767, `ArrayIndexOutOfBoundsException`; 3,
  parsed; top node, one pointer more, the `AssertionError` with `-ea` (a
  later check without it, for this node only), 127,
  `ArrayIndexOutOfBoundsException`. With the checks, each a
  `StreamFormatException`.
* **With 005-82's patch**: the two patches apply together (`git apply`
  of 005-82's hand-off, then this change, on a clone of `main`); their
  hunks in `DbTesterFailure` are apart, and this change adds no import.
* **The gate**: `java/before-commit.sh` on `f2cb23b`, 16:24 to 16:26:
  `BEFORE COMMIT OK (107 s)`, 1,104 unit tests and 78 f-tests. Then `main`
  took 005-82 (`3e32f02`); the change applies on it unchanged, and is
  gated again there (below). No level script (none was asked; F53 busy).
* **On `3e32f02`** (005-82 in `main`): the gate failed, 16:27 to 16:29,
  on one test, 005-82's `DbTesterFailure.testGetTransUncheckedParseError`
  ("the cause's cause: null"): its value size of -1 is now refused by the
  parser (`StreamFormatException`, "Bad value size"), so no
  `NegativeArraySizeException` reaches `Db.parseTrans`'s wrap. After this
  change no malformed node is known to give a `RuntimeException` other
  than a `StreamFormatException` in a record's parse (the record's fields
  are 005-74's; the top node's ordinal is read in 48 bits, never above
  `TopNode.MAX_TOP_NODE_ID_VALUE`). So:
  * the test is renamed `testGetTransBadValueSize`, with the same damage,
    and asserts the parser's `StreamFormatException` ("Bad value size",
    no cause) as the failure's cause;
  * a new unit test, `testParseTransWraps`, tests the wrap itself: a
    `TransIterator` that has read a record, its buffer then set to null
    (a bug's stand-in: `StoredTrans.parse` throws an
    `IllegalArgumentException`), and `Db.parseTrans` throws a
    `StreamFormatException` ("A malformed record at stream pos ...") with
    it as the cause. `parseTrans` is package-private for it, and its
    Javadoc says that since 015-07 it is a net for a bug. Mutation: the
    wrap catching only `IllegalStateException`: the test fails, the
    `IllegalArgumentException` escaping;
  * 005-82's entry (closed) is not changed; its Log names the old test.
* **The gate on `3e32f02`**, with the adapted tests: `java/before-commit.sh`,
  16:47 to 16:49: `BEFORE COMMIT OK (102 s)`, 1,108 unit tests and 78
  f-tests.

2026-11-03, 16:52. Reviewed by the coordinator (016-05, H5): no faults; the
checks refuse no valid node (a key node is exactly 32 + 16 count bytes; the
top node's size equality is what the -ea assert held). Combined gate on
main: BEFORE COMMIT OK.
