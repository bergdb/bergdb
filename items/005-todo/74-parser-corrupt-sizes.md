005-74. Fix: Java's record parser and corrupt sizes (a negative node size loops)
================================================================================

Status: done (2026-11-02, option A). Kind: fix. Created 2026-10-28.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
012-06's corrupt-input tests of the C stream reader (012-06, section 7,
findings F2 and F3), as 012-01's decision D5 says. Only corrupt or crafted
streams reach these; Java never writes such sizes.


The issue
---------

* **F2. `StoredTrans.Parser` takes a negative node size** and moves its
  offset back. A crafted record loops for ever, its node list growing
  until `OutOfMemoryError` (an `Error`, not a `StreamFormatException`).
  Probe (012-06): a record of 112 bytes, format 5, a delete node at 32
  (size 32, its checksum right, stored offset 32, one key segment), and at
  64 a "node" of size −32, type 40, format 4, checksum 0, stored offset
  64, key size 8; `StoredTrans.parse(128, r)` gives `OutOfMemoryError:
  Java heap space` within 3 s (`-Xmx256m`). `readNode` already refuses a
  node size of 6 or less; `Parser.next` does not.
* **F3. A record's or a node's size is allocated before its bytes are
  read** (`NodeStream.TransIterator.next`, `readNode`, `readTransBytes`):
  a corrupt size near 2^31 gives `OutOfMemoryError` in a small heap,
  instead of a format error or the read's own error.

Found by 012-14's corrupt-input runs (2026-10-29, 012-14 section 6; its
probes in `/Users/f/fl/bench/012/14-out/probes/`):

* **`Db.getTrans` parses the record outside its `try`** (now 005-82), so a checksum
  failure (or an `ArrayIndexOutOfBoundsException`) escapes, and the
  database stays active; C fails the database, as 005-34 and 012-03 say
  (probe `gettrans-checksum/`).
* **A start that refuses can first write** (now 005-83): a flipped size field makes
  recovery write about 1 MB of zero fill before the start refuses the
  stream, in Java and (as Java) in C; outside 005-40's scope (probe
  `refused-start-writes/`).

A database whose stream is corrupt should be refused with a clear error
(`StreamFormatException`, levels.md section 3), not take the JVM's heap.


Options
-------

* **A.** `Parser.next` refuses a node size below the smallest node (as
  `readNode` refuses 6 and less), and the readers check a size against
  what the stream holds (its length, or the record's size) before they
  allocate. Small; a unit test with the probe's record.
* **B.** Nothing: a crafted stream is not BergDB's threat model.

Recommended: A, as it is a few lines and turns a heap exhaustion into the
format error the rest of the parser gives. The C clone already refuses
both (012-06, decision 8); a Java fix brings the two scanners' texts in
line on such streams.


Done when
---------

Decided; for A, the change with its tests and `before-commit.sh`.


Decision and scope
------------------

2026-11-02. Frans: "Fix 005-74 as recommended. That is: Option A. Commit
if successful." Option A is the parser and reader size checks (F2 and
F3). The two findings added from 012-14 concern error handling and
recovery policy, respectively; they remain open as 005-82 and 005-83.


Outcome
-------

2026-11-02, by Codex, on `main` from `b0b4732`:

* `StoredTrans.Parser` checks the record's minimum size, confines nodes
  and the got-dirty list to its declared size, and checks space for the
  end marker and padding. Its array may be larger than the record, as
  with the serializer's reused buffer. Node sizes smaller than the common
  8-byte header, negative sizes included, are refused before parsing or
  advancing the offset. Subtraction bounds avoid overflow in these checks.
* `NodeStream.readNode`, `readTransBytes` and `TransIterator.next` check
  the declared extent before allocating its buffer. The check locates
  the last byte in stream coordinates, excluding meta blocks; it accepts
  a record ending just before a meta block, including one a crash has
  not yet written. The format and the writer do not change.
* Nine regressions cover the looping 112-byte record, small and oversized
  nodes, record and list bounds in a reused buffer, the three allocating
  readers, and meta-block boundaries. The positive boundary control
  passes on both builds. On the old code eight tests fail, four with an
  `OutOfMemoryError`; on the fix the focused parser/reader suite passes
  at `-Xmx64m` (37 checks including the stopped-database check).
* The final `before-commit.sh`: `BEFORE COMMIT OK (96 s)`, 1,082 unit
  tests and 78 f-tests. `level2.sh quick`: `LEVEL 2 OK`, including crash
  and restart checks and 14 conformance traces. StreamDigest, one compiled
  copy run against the before and after jars: `DIGESTS IDENTICAL (36 of
  36)`. These checks concern the implementation and tested workloads, not
  a proof of the parser.
* The C reader already rejects the original negative and oversized input
  cases; C is unchanged and its gate was not rerun. The two later findings
  are open as 005-82 (`getTrans` failure handling) and 005-83 (recovery's
  writes before refusal). Option A does not settle either.

Evidence is in [74-parser-corrupt-sizes/](74-parser-corrupt-sizes/): the
before and after tests, final gate output, Level 2 quick output, and both
digest sets with their comparison. `releases/next.md` records the fix.
