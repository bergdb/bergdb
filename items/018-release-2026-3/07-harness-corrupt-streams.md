018-07. Harness 6.1: corrupt streams at a start
==============================================

Created 2026-11-06 by Frans Lundberg, as harness 6.1 of 018-01 (W2), in
the night 006-12 (Frans, 2026-11-05, 21:33: "Will you fix all bugs?
[...]"). Built by Claude (Opus 5.5, Claude Code), a harness agent of that
night.

**Status: built; runs in `before-commit.sh`'s unit tests (a sample, about
2 s) and in `night.sh`'s night tests (the full set, 64 s).** Every
truncation starts with exactly its committed transactions and passes the
audit. It fails on each of the five known faults of its class (018-01,
section 6.1), with each fix's main hunk reverted, and found five more:
019-30, 019-31 and 019-33 for Frans's decision (damage that the
format's checks cannot see), 019-32 a fault of the Core to fix, and
019-34, fixed the same night. The four open ones are in its skip
list, and it passes on `main`.


## 1. What it checks, and why

A start reads a stream that a crash, a disk or a bug may have damaged.
The five known faults of the class (018-01, section 6.1) each let a start
take, or crash on, a stream that was damaged in one particular way, and
each was found by a review or a probe that made that one damage:

* 005-74: a negative node size moved the parser back, and it looped
  until the heap ran out; a huge size was allocated before it was read.
* 005-75: a record time out of order was not refused (the check never
  advanced), and a key node's times were not checked.
* 015-07: a node's inner fields (a key count, a value size, a pointer
  count) were not checked against its size; a read threw an
  `ArrayIndexOutOfBoundsException`, and the database went on.
* 015-72: a record whose size field was larger than its content was
  taken, and the records it covered were lost.
* 015-75: checks of a got-dirty id, a `topPos` and a `startupPos` were
  asserts: without `-ea` the damage was taken, with it an
  `AssertionError`.

The harness makes every such damage, and more, on streams written by
real runs of `Db`, and starts each damaged copy. Two kinds of checks:

* **Truncation, the crash contract** (014-01, section 7;
  `AppendOnlyStream`'s Javadoc), a hard requirement. A copy cut at a
  length starts with exactly the transactions whose records end before
  the cut: the counter key that each transaction puts names the last
  one, every key has the value it had after that transaction, now and
  at the times of the earlier ones, and the audit (`Audit.check`) finds
  nothing. Then one more transaction, a close, and a start again: it
  holds the same and the new key, and passes the audit. A cut before
  the first transaction's record ends may instead be refused with
  `DatabaseNotCreatedException`, with nothing written (005-33).
* **Other damage, best effort** (018-01, section 6.1). A start of the
  copy has one of these outcomes, each counted:
  * refused: the start throws a `DbException` (a
    `StreamFormatException` above all) and writes nothing;
  * a read fails the database (P7 of 010-01): the read throws a
    `DbException`, and the next call says the database has failed
    (`IllegalDbStateException`);
  * the copy holds what the original held after some transaction: all
    of them (a damage that does not matter, such as a flipped padding
    byte), or fewer (one that looks like a cut tail, such as a flipped
    last byte of the last record).

  Anything else is a fault: a start or a read that throws another
  exception (`ArrayIndexOutOfBoundsException`, `AssertionError`,
  `OutOfMemoryError`, `IllegalArgumentException`), one that does not
  end in 60 s, a read that fails and the database goes on, and a copy
  that answers other values than the original's without failing
  ("undetected"). Two kinds of damage pass undetected by Frans's
  decision and are counted as known, not failed:
  * 015-73 (2026-11-05, 15:35, option (a)): a record's `startupPos`
    set to the start of a later record than its own startup pos, which
    the take never reached;
  * 014-01 (005-83's case, moved to 014-01 on 2026-11-03): a start that
    refuses a damaged size after recovery's zero fill has written.


## 2. How it works

One test class, `bergdb.core.CorruptStreamTester`, registered in the
package's `Pack`; test code only, nothing in the production code.

* **The originals.** Three workloads, each on a `MemoryStream`, from a
  seed: transaction i puts the counter `/n` = i and 0 to 3 puts and
  deletes of 14 keys (one to three levels), values of 1 to 200 random
  bytes:
  * `all`: 30 transactions, startup distance 1 MB, so the startup
    section is the whole stream (about 10 KB);
  * `take`: 50 transactions, startup distance 300 bytes: the take moves
    the startup pos and writes the index nodes in later records, and a
    start reads a short section and loads the rest from the stream when
    it is read (about 20 KB);
  * `meta`: 30 transactions, startup distance 50 KB, a value of 30 to
    60 KB in one transaction in three: records that span a meta block
    (every 200,000 bytes), and a recovery from a meta block that is not
    the first (about 500 KB).

  The test keeps each original's bytes, the state after each
  transaction, and its records (position, size, nodes, got-dirty list),
  found by walking the stream as `RecoverableStream` lays it out.
* **The copies.** A copy's bytes are made when it is checked, from the
  original's and the damage, so only the copies being checked take
  memory. Each is started on a `CopyStream`, a test stream over the
  bytes that copies nothing and keeps what the start appends (recovery's
  zero fill, a transaction), so that a refusal after a write is seen.
  The damage:
  * truncation at a length (every length, or a sample: around each
    record's start, its header's end and its last byte, around each
    meta block, and random ones);
  * a byte flipped (xor 0x01, 0x80 or 0xff), at every position or a
    sample (each record's header, and random ones);
  * a record header's field set: the size (to end on each later
    record's last byte, as R6-F1's probe did, and to small, odd, huge
    and negative ones), the time (one unit or one step before or after,
    0, -1, `Klong.MAX_TIME` and above, a high bit), the `startupPos`
    (each record's start and the 8 bytes after it, 0, 8, 120, 128,
    negative, a high bit, the stream's length), the `topPos` (each node
    of the stream, its own record's start, near and far values), each
    got-dirty entry's id and position, and the got-dirty count;
  * a node's bytes changed with its checksum made right (Fletcher-16,
    `NodeChecksum`, as 015-07's tests did): each of its first 64 bytes
    flipped (by each mask in the night, by 0x80 in a sample), and each
    4-byte field set to -8, 0x7ffffff8 and 0x10000. A node so changed
    is a valid node with another meaning: a start that takes it, and
    reads that answer other values, are outside the fault model (019-07,
    "a change made with the checksum made right again"); only a start or
    a read that throws another exception than a `DbException`, or a
    database that goes on after a failed read, is a fault here;
  * a range cut out: whole records (pairs of record starts), and
    random ranges of up to 2,000 bytes.
* **The check of a copy** (`check`): the start, then the reads (the
  counter, every key now, the counter at each transaction's time, every
  key at a few of them), as section 1 says. Copies run on 2 (unit) or 4
  (night) threads; each must end within 60 s.
* `SKIP`, as 6.3's and 6.7's (018-02, section 4): an open known fault
  of the class is listed, its failures are printed and skipped, so that
  the harness passes on `main`; a fix removes its line.
  `-Dbergdb.corrupt.skip=none` skips nothing. `KNOWN` lists the two
  decided kinds of section 1. `entryOf` says which failures are a
  listed entry's (section 4).
* A start may append at most 1 MB to a copy (`MAX_APPENDED`): a
  damaged size field makes recovery zero-fill up to 2 GB before the
  start refuses the stream (014-01, 005-83's case), which took minutes
  and gigabytes per copy in the first runs; the append past it fails,
  and the copy counts as 014-01's known case.
* `main(seed, [full, [threads]])` runs one seed by hand and prints the
  outcomes by kind and the first 30 failures.

Adapted from 018-01's proposal, and why:

* The audit runs on the truncated copies only: on a damaged copy its
  own reads of the stream would meet the damage before the code under
  test, and it checks invariants of a valid stream.
* `MemoryStream`'s bytes, not `FileStream`'s files: a start reads the
  same bytes through either; `FileStream`'s prefix across its files is
  014-01's point (b), checked separately on 2026-11-05.
* Reclaim is off (the retain duration is forever, as in the test
  setup): a cut stream, reclaim's table and its settings KV are not
  damaged here (section 7).

## 3. Where it runs, and its cost

* **The unit tests** (`testSample`, the Nano group "unit"): the sample
  of seed 1 on 2 threads, about 5,600 copies of the three originals:
  3.3 s alone (`bergdb.dev.Unit -c CorruptStreamTester`).
  `before-commit.sh` runs the unit tests beside the f-tests, which set
  its time: BEFORE COMMIT OK in 115 s with the harness, as the gates of
  the night before it took (113 to 115 s).
* **The night tests** (`testFull`, the group "night", run by
  `night.sh`'s step night-tests): every truncation of `all` and `take`
  (each length from 0 to the end), 20,000 random truncations of `meta`
  and the sample's points, every byte of `all` and `take` flipped by
  each of 0x01, 0x80 and 0xff, 5,000 random bytes of `meta`, every
  record's header fields and every node's first 64 bytes; on 4 threads,
  a new seed each day (the day's number, printed). 278,484 copies in
  64 s (seed 20398), 52,690 of them truncations; the night tests' step
  gets about a minute longer.
* By hand, from `java/`:

```sh
java -ea -cp build/bergdb.jar bergdb.core.CorruptStreamTester 1        # the sample, seed 1
java -ea -cp build/bergdb.jar bergdb.core.CorruptStreamTester 20398 full 4   # the full set
java -ea -Dbergdb.corrupt.skip=none -cp build/bergdb.jar bergdb.core.CorruptStreamTester 1
                                                     # nothing skipped: 019-30 to 019-33
```


## 4. The skip list

As 6.3's (018-02, section 4) and 6.7's: `CorruptStreamTester.SKIP` holds
the open entries whose failures the harness prints as "Known fault,
skipped" and counts, and `entryOf` says which failures are whose:

```java
static final String[] SKIP = {
    "019-30",   // a record's time or topPos changed within the checks: undetected
    "019-31",   // whole records cut out of the stream's middle: undetected
    "019-32",   // a node's klongs and pointers unchecked: an assert at a start or read
    "019-33",   // a node byte changed between 0x00 and 0xff: the checksum misses it
};
```

* 019-30: an undetected outcome of a header field's change or a byte
  flip in the header's time or `topPos`;
* 019-31: an undetected outcome of a range cut out;
* 019-32: a start or a read of a damaged node (changed with its
  checksum made right, or flipped in a way the checksum misses) that
  throws an `AssertionError`, an `IllegalStateException` (without `-ea`)
  or a `ClassCastException`;
* 019-33: an undetected outcome of a node byte flipped by 0xff.

019-34 had its line until its fix the same night: a flip in a meta block
that made the start throw `IllegalArgumentException: spos >= streamSize`.

A fix (019-32) or a decision ((a) of 019-30, 019-33) removes its line:
a decided kind moves to `KNOWN`, with 015-73's and 014-01's, and is
counted as known. Unlike 6.3's list, a line whose failures no longer
come does not fail the test: the copies of a sample depend on the seed.
`-Dbergdb.corrupt.skip=none` skips nothing: seed 1 then fails with 50
copies (2 cut out, 7 flips and 40 header fields, 1 node), all of the
listed entries.


## 5. The evidence

### 5.1. On main: the outcomes

Seed 1's sample on `main` with the harness (5,636 copies, 1.9 s on 4
threads), the outcomes by kind:

| Damage | Outcome | Copies |
|---|---|---|
| truncation | holds the committed prefix, then one more and a start      | 1,310 |
| truncation | holds all (cut at or after the end of the last record)       | 3 |
| truncation | refused, `DatabaseNotCreatedException`, nothing written      | 89 |
| flip       | holds all (padding, unused bytes, a meta block's spare)      | 962 |
| flip       | refused: format 528, checksum 97, version 44, I/O 4           | 673 |
| flip       | a read failed the database                                   | 42 |
| flip       | holds a prefix (the last record looks torn)                  | 26 |
| flip       | 014-01: recovery wrote before the start refused, or past 1 MB | 59 |
| flip       | 019-30, skipped                                               | 7 |
| header     | holds all, or a prefix                                       | 1,107 |
| header     | refused: format 897, I/O 3, version 3                        | 903 |
| header     | 014-01: recovery wrote before the start refused, or past 1 MB | 36 |
| header     | 015-73, known                                                 | 2 |
| header     | 019-30, skipped                                               | 39 |
| node       | refused 81, a read failed 6, holds all or a prefix 82         | 169 |
| node       | undetected, its checksum made right (outside the model)      | 28 |
| node       | 019-32, skipped                                               | 1 |
| cut out    | refused: format 88, `BadCryptoKey` 50 (meta block 0 cut)      | 138 |
| cut out    | holds a prefix 12; 014-01 28                                  | 40 |
| cut out    | 019-31, skipped                                               | 2 |

Seeds 2 to 5 of the sample: no failure but those of the skip list
(seed 5 first showed one more: a zero fill that the storage's thread
appended after the start, which the harness now counts as 014-01's).

The full set, seed 20398 (the day's number of 2026-11-06), 278,484
copies in 64 s on 4 threads: no failure but the skip list's. Every one
of the 52,690 truncations held its committed prefix (52,117), all (3),
or was refused as an incomplete creation with nothing written (570).
Skipped: 019-30 132, 019-31 3, 019-32 200, 019-33 1,016; and 019-34's
4 until its fix, after which they are refused. The
first full run, before 019-32's pointer cases and 019-34 were in the
list, failed with 111 copies, all of these two (section 6).

### 5.2. On the code before each known fault's fix

Each fix's main hunk reverted in a second clone
(`/Users/f/fl/bench/006-12/h61-old`, the harness copied in; the reverts
are a script, `/Users/f/fl/bench/006-12/h61-patches/revert.py`), seed 1's
sample, with `-ea` as the unit tests run:

* **015-72** (`StoredTrans.Parser.parse`'s check that the content ends
  where the size says): 2 failures, the size of the record at 1016 set to
  end on a later record's last byte: "undetected: holds 30 transactions
  by the counter, and /a is 70 bytes, not ...", the records it covers
  lost (R6-F1's effect).
* **015-75** (the checks in `Db.checkStartupPos` and `DbStarter`): 50
  failures, among them every flip of a record's `startupPos` high byte:
  "the start threw java.lang.AssertionError: Bad storedTrans.startupPos:
  -9223372036854775808 (at core.Db.getStartupPosFromLastTransaction)".
  Without `-ea` the same copies were refused with a format or an I/O
  error, as 015-75's entry says; its got-dirty and `topPos` cases are
  among the header fields.
* **015-07** (the parsers' checks of a node's inner fields, in
  `StoredKeyNode`, `StoredTopNode` and `StoredValueNode`): 16 failures,
  each a node changed with its checksum made right (a value or key size,
  a count): "the start threw java.lang.NegativeArraySizeException:
  -2147483646 (at core.StoredValueNode.parse:102)", an
  `ArrayIndexOutOfBoundsException` ("arraycopy: last source index 33204
  out of bounds for byte[464]"), and an `OutOfMemoryError` for a size of
  0x7ffffff8.
* **005-74** (`Parser.next`'s check of a node's size): 13 failures,
  "the start threw java.lang.ArrayIndexOutOfBoundsException: Index 320
  out of bounds for length 320 (at core.NodeChecksum.sumWithZeroReplace)"
  for a node size flipped or set; the heap loop of 005-74's probe needs
  a size of exactly -32 at the right place, and the harness's -8 gave the
  out-of-bounds read first.
* **005-75** (`DbStarter.validateTransactions`' checks of the times):
  89 failures, for every flip of a record time that broke the order: "the
  start threw java.lang.AssertionError: lastTimeIndex=1, lastTime: 32778,
  time=20, keyNode: K/a3 ...".

On `main` each of these copies is refused with a `StreamFormatException`.


## 6. What it found

* **019-30** (Decide): a record's time changed within its neighbours',
  and the last record's `topPos` set to a version of its top node before
  the startup section, pass undetected; 015-73's class (no header
  checksum, 019-07). Recommendation: (a), as 015-73.
* **019-31** (Decide): whole records cut out of the stream's middle
  pass a start undetected (the `all` configuration, startup pos 0): the
  stream left is a valid stream of fewer transactions, as nothing links a
  record to the one before it. Recommendation: (a), as 015-73; a link
  between records with 019-07.
* **019-32** (Fix): a node's klongs and pointers are not checked: a
  key node changed with its checksum made right (a klong's type, a key
  klong's pointer) meets an assert at the start, or an
  `IllegalStateException` without `-ea`; a damaged value pointer an
  assert at a read; a pointer to a node of another type a
  `ClassCastException`. 015-07's class, a fault of the Core. Found at
  03:38 and 03:44, too late to fix that night.
* **019-33** (Decide): Fletcher-16 modulo 255 does not see a byte
  changed between 0x00 and 0xff, so a value byte flipped by 0xff is read
  back changed. Recommendation: (a) for 2026.3, a stronger checksum with
  019-07.
* **019-34** (Fix): a meta block's last-transaction position flipped
  past the stream's end passed the meta block's checks, and recovery
  threw an `IllegalArgumentException`; 019-01's class, a fault of the
  Core. Found by the first full run (03:44) and fixed the same night:
  recovery refuses such a block with a `StreamFormatException` before it
  writes (`RecoverableStream.checkLastTransSpos`; test
  `DbTesterRestart.testMetaBlockLastTransPosRefused`, which failed
  before the fix).

The crash contract held: no truncation failed, in the samples of seeds 1
to 5 and in the full set.


## 7. What it does not cover

* Reclaim and a cut stream (`getFirstPos() > 0`), reclaim's table and
  its settings KV; eviction during the reads (the test setup has none).
* `FileStream`'s files: a cut across two files, a missing file
  (014-01, point (b)); the streams here are bytes.
* Damage of more than one place at once, except the ranges cut out.
* A damage whose outcome is a prefix is accepted: such as a flip that
  makes the last record look torn. A flip of a middle record's size that
  makes recovery zero-fill it as a torn one and then take the stream
  with fewer transactions would be counted so too (014-01's question;
  none seen with fewer than all but the last).
* Writes after a damaged start, except for truncations (one transaction
  and a start again).
* The C clone (012), which has its own corrupt-input runs (012-14).


## 8. State (night 006-12)

Clone `/Users/f/fl/bench/006-12/h61`, branch `h61`; the old-code clone
`/Users/f/fl/bench/006-12/h61-old`; outputs and scripts in
`/Users/f/fl/bench/006-12/h61-patches`. Done: the harness, this item,
019-30 to 019-34, and 019-34's fix. Next: 019-32's fix (test first: the
harness's copies); Frans's decisions on 019-30, 019-31 and 019-33;
then the lines leave `SKIP`.


## 9. Log

2026-11-06, night 006-12. Built (W2 of 018-01, harness 6.1):
`CorruptStreamTester`. Every truncation holds its committed prefix and
passes the audit. It fails on 005-74, 005-75, 015-07, 015-72 and 015-75,
each with its fix's main hunk reverted, and found 019-30 to 019-34, all
in its skip list. In the unit tests (a sample, about 2 s) and the night
tests (the full set). BEFORE COMMIT OK.

2026-11-06, night 006-12. 019-34 fixed: recovery refuses a meta block
that names a transaction outside the stream, before it writes; its line
left `SKIP`, and the full set of seed 20398 passes. BEFORE COMMIT OK.

2026-11-06, 04:14, night 006-12. 019-31's cause found by a probe: the
copy left is a valid stream of fewer transactions; it became a Decide.
