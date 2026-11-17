# 024-25, review rev25: CRC32C as the node checksum

Written 2026-11-11, 18:32 to 18:50, by the reviewer "rev25" of coord-1111.
Reviewed: branch `024-25-crc32c` of `/Users/f/fl/bench/2026-11-11/crc/clone`,
head `a9c8d029`, the diff `08659847..a9c8d029`: the change `26c21000`, the
five test commits `bd3063ac`, `ef7762b4`, `a0ea6312`, `44fe5673` and
`57246318`, and the documents in `a9c8d029`. While I worked, crc added
`e3cf5937` (level1's SS limits, R4), which I also read.
Design read: 024-25 (main tree, 18:31), 024-17 (F6, QL9) and 024-02
sections 8 to 12 on the branch.
Probes ran in my own clone `/Users/f/fl/bench/2026-11-11/rev25/clone`, in a
worktree of `0cb7eff7` (`rev25/base`), and in class directories under
`/Users/f/fl/bench/2026-11-11/rev25/probe/`. crc's clone was not changed. I
took no slot: each probe was a build, a unit test or a run of a few seconds.


## 1. Verdict: land with fixes

**The code is right.** Every node checksum is written and checked as
CRC-32C over bytes 0 to 7 and 12 to the node's end, as 024-02, section 9
says. No node checksum still uses Fletcher-16. Each node type's reader
agrees with its writer at every offset, and every size formula agrees too.
The creation record is 144 bytes. A database of 2026.4 is refused with the
format-6 message. A format-7 database written by `main` before this change
is refused with a checksum error, and the failed start leaves its file
unchanged. The five test commits keep their tests' purposes: I removed
each fix the pinned copies guard, and each test then failed. The finding
on `testFoundLinkByIdPrevPos` is confirmed. On `0cb7eff7` the test passes
with its fix removed. On the branch it fails with the fix removed.

**Before it lands:**

* **R4.** level1 failed on `a9c8d029` (SS 1.53 > 1.52, SS3 1.69 > 1.66).
  crc raised the limits in `e3cf5937`. level1 must pass on that head, and
  Frans must approve the raised limits with the other changed expectations
  (QC2).
* **R1.** The new 12-byte lower bound on a node's size is untested. Two
  guards keep `NodeChecksum.sum`'s `IllegalArgumentException` from escaping
  a read. I removed both guards, and none of the tests that cover them
  failed.
* **R2.** 024-02 still states the old layout in about ten places outside
  the tables that were updated.

R3, R5 to R9 are notes.

At 18:43, `crc/gates/summary.txt` showed level1 exit 1 (R4), unlinkfuzz
exit 0, and level2 running, all on `a9c8d029`. The verdict assumes that the
rest of the chain ends OK, and that level1 is rerun on `e3cf5937`.


## 2. Findings

### R1. The 12-byte lower bound on a node's size is untested (should fix)

* **Where:** `java/src/bergdb/core/NodeStream.java:308` (`checkChecksum`:
  a size below `HEADER_SIZE` gives an SFE) and
  `java/src/bergdb/core/StoredTrans.java:447` (`Parser.next`: was
  `nodeSize < 8`, now `< NodeChecksum.HEADER_SIZE`).
* **Why they matter:** `NodeChecksum.sum` throws `IllegalArgumentException`
  for a length below 12. Without the guards, a damaged size field of 8 to
  11 reaches `sum`: from a record through `Parser.next`, or from a pointer
  through `readNode`, whose own check refuses only sizes up to 6 and
  `checkReadSize` sizes below 8. The `IllegalArgumentException` then
  escapes the reads' failure handling. That is the class of fault fixed in
  015-07 and 019-32.
* **Probe:** in my clone I disabled the `checkChecksum` guard and set
  `Parser.next` back to `< 8`. Every `@Nano` test of `StoredTrans`,
  `NodeStreamTester`, `NodeStream`, `StoredValueNode`, `StoredKeyNode`,
  `StoredTopNode` and `NodeChecksum` passed (62 of 62).
  `testNodeSizeOutsideRecord` (`StoredTrans.java:960`) tries sizes 1, 6, 7
  and `Integer.MAX_VALUE`, all below the old bound. CST sets size fields
  to -8, 0x7ffffff8 and 0x10000, or flips them by 0x01, 0x80 and 0xff. Its
  streams never give a size of 8 to 11.
* **Fix:** add 8 and 11 to `testNodeSizeOutsideRecord`'s sizes. Add a
  `NodeStreamTester` case: a node of size 8 to 11 read by `readNode` (or
  `bytesToNode` with that size) must be an SFE, not an
  `IllegalArgumentException`. This adds tests and changes no existing
  expectation.

### R2. 024-02 still gives the 8-byte header outside sections 9 to 12's tables (should fix)

The brief asks that the draft match the code. The tables of sections 9 to
12 are right: I checked each offset against `toLongs`, `toBytes` and
`parse`. But the text around them, and later sections, still describe the
old layout (line numbers from the branch's file):

* :449 (8.1) "a node size from 8 to what is left": now 12.
* :633 (10) "the size exactly 40 + 16·h": now 48 + 16·h
  (`StoredTopNode.java:105`).
* :649 and :654 (10, unused; G7 top) "Byte 9": now bytes 6 and 7, 12 to
  15, and 17.
* :696 (11.1) "format 2": now 3.
* :767, :790 and :796 (11, unused; G5; G7 key) "Bytes 19 to 23" and
  "Byte 19, the third byte of what Java writes as n": now byte 15 (and 6,
  7). 11.1's own text, :692, is already right.
* :827 (12) "format 4": now 5. :838 "Unused and reserved. The padding
  only.": bytes 6 and 7 too.
* :1320 (20) "node byte 9, key node 19 to 23" and :1364 (21.1) "node
  formats 2, 2, 4": not updated.
* :548 "Format 7 since 024-25" reads as if record format 7 began with
  024-25. It began with 024-21 (`d502af3d`). Suggest "The 12-byte header
  since 024-25 (record format 7, ...)".
* 8.1's table (:425) and 8.2 still say record format 6. That was already
  stale before this branch, and the subitem's log says so. Fix it with the
  rest if convenient.

None of the new unused bytes (6 and 7 in every node, 12 to 15 and 17 in a
top node, 15 in a key node) is checked to be zero. The checksum covers
them, so damage is still found. A specification should list them under
G7, as it lists the reserved bytes of before.

### R3. testFoundLinkByIdPrevPos: the finding confirmed (note)

* On `0cb7eff7`, with `NodeCollection.checkLinkById`'s refusal
  (`21e8db97`) removed, `testFoundLinkByIdPrevPos` **passes**. Its copy
  is the record whose tpos is 21584 (the test asks for 22448, inside it).
  The first node there is a top node (type 10, offset 32, size 72), so the
  xor at byte 8 hit h. The copy was refused for its size, and the test
  guarded nothing.
* On the branch, with the same refusal removed, the test **fails**: the
  start throws `AssertionError: rule 4 by position is not rule 4 by node
  id ... pointer 1 of node 5753 names 15952`. With the refusal it passes
  and checks the refusal's text. The text check means the copy cannot
  drift to another refusal unnoticed again. The Javadoc's "the record at
  21584" is right: it is that record's tpos.

### R4. level1 fails on a9c8d029 and is fixed in e3cf5937 (blocks until rerun)

* `crc/gates/level1.log`: `LEVEL 1 FAILED: Props SS:1.53 (1.11, 1.21,
  1.69, 2.40), more than 1.52 1.11 1.21 1.66 2.41`. SS does not depend on
  the machine. My runs of `bergdb.dev.props.SS`: base `0cb7eff7` 1.51
  (1.10, 1.20, 1.64, 2.41), branch 1.53 (1.11, 1.21, 1.69, 2.40). This is
  the expected cost: 4 bytes more in every value node, 8 in every top
  node.
* `e3cf5937` raises `SS_MAX` (`java/stress/level1.sh:139`) to 1.54 1.12
  1.22 1.70 2.41 and gives the reason in `docs/log.md`, as step 6's rule
  asks. My numbers pass these limits. The commit is right, but:
  * level1 has to be rerun on `e3cf5937`; crc's chain runs on
    `a9c8d029`.
  * This is a changed expected value. Add it to QC2 for Frans's approval.
  * The comment at `level1.sh:119` to `:121` still says "The SS limits are
    the values of 2026-10-28 after 007-07 ... plus ... 0.01". Add "raised
    on 2026-11-11 for 024-25 (docs/log.md)".
* 024-25's section 3, "Cost in bytes", could give these SS figures as the
  measured cost.

### R5. Db.checkDirtyNodes' top node bytes use the old size (note)

* **Where:** `java/src/bergdb/core/Db.java:2748`: `topBytes = 2 * (40 +
  16L * 64 + 16)`. A top node is now 48 + 16·h bytes.
* **Still sound:** h is at most 48, since the ordinal has 48 bits and is
  below 2^30 in practice. 48 + 16·48 + 16 = 832 is at most 40 + 16·64 +
  16 = 1,080. The bound is still an over-estimate.
* The same expression is in 024-24's branch: Java `Db.java:2860`, and the
  Lean `ReleaseFits` (`lean/SIS/Tree/Bound.lean:346, :357` in
  `lim3/clone`). Whichever branch lands second should write it as
  `StoredTopNode`'s size, or keep 40 + 16·64 with a comment that says
  why it bounds 48 + 16·48. No theorem breaks either way.

### R6. A format-7 database from before this change: a checksum error (note; acceptable)

* **Probe** (`rev25/probe`, `Rev25Open`): I made databases with
  `0cb7eff7`'s build (200 puts and a delete, `FileStream`) and with
  `releases/2026.4/bergdb-2026.4.jar`, then started each with the
  branch's build:
  * 2026.4: `VersioningStreamException: Cannot parse stored transaction of
    format version 6; ... format 6 was written by release 2026.4, which
    opens it ...`. Clear.
  * `0cb7eff7`: `StreamChecksumException: spos: 160, storedSum: 0,
    computedSum: 1269713866, nodeType: 10`, the first node of the
    creation record. The record format byte is 7, so the record header
    passes. The node's checksum is checked before its format byte, so the
    node format 2 is never reported.
  * Both files are byte for byte the same after the refused start (shasum
    before and after). Each old build still opens its own database.
* **Acceptable:** no release wrote format 7, and `main` wrote it only
  from 16:53 today (`d502af3d`). The only risk is a bench or test
  database made in that window, whose error looks like damage. QC1's
  recommendation stands. If a clear message is wanted without a format
  number, `bytesToNode` could check the format byte before the checksum
  for the previous node formats (2 for top and key, 4 for value and
  delete) and throw a `VersioningStreamException` that names 024-25. That
  is optional.

### R7. releases/next.md cites a section that is not yet written (note)

* `releases/next.md:76`: "StreamDigest's digests change in every
  configuration (024-25, section 7)." Section 7 of 024-25 does not yet say
  so: StreamDigest is still among the running gates. Fill it in when the
  chain ends, or drop the sentence.
* The entry could also give the stream's cost: SS 1.51 to 1.53 (R4).

### R8. NodeChecksum.sum makes a CRC32C object a call (note)

`NodeChecksum.java`: `new CRC32C()` for each node written or read. The JIT
probably removes the allocation, and crc's measured figures (0.05 us for a
key node of 544 bytes) include it. No change needed. Revisit only if a
profile shows it.

### R9. Other documents that name Fletcher-16 (note)

* `java/src/bergdb/core/doc-files/stream-format.txt:141` ("now
  Fletcher-16") is the 2015 document, history like `docs/log.md`, so no
  change is needed. One line under 2026.5 would stop a reader from taking
  it as current.
* 022's C port (`checksum.c`) stays Fletcher-16 at 2026.4's format 6, as
  024-25, section 2, says. When 022 follows 2026.5, it needs CRC-32C and
  the new header.
* `lean/test-traces/*.trace` hold stream positions only in comments
  (`# ... tpos=264`). The checker reads records by index
  (`docs/trace-format.md`), so these files need no change.


## 3. What I checked and found sound

* **Writers and checks, by grep** (`NodeChecksum`, `Fletcher`,
  `sumWithZeroReplace`, `toLongs`, `bytesToNode`, `.parse(`):
  * Written in `StoredValueNode.toBytes` (after the padding is zeroed),
    and in `StoredTrans.Serializer.serializeNodes` for top then key
    nodes, on the record's bytes from offset 32. The order and sizes
    match `prepareToSerialize`, and an assert checks the end.
  * Checked in `NodeStream.checkChecksum` from `bytesToNode`, which serves
    `readNode` and `Parser.next`. No other path parses a stored node: the
    direct `parse` calls are unit tests. `readNodeHeader` reads only the
    type and id, unchecked, as before; its `ID_OFFSET`s are 24, 24 and
    12, inside its 32 bytes.
  * The tests' helpers (`CorruptStreamTester.nodeCopy`, `DbTesterFailure`
    at 2 places, `StoredValueNode.parseWithRightChecksum`, `StoredTrans`'s
    hand-made record of 2 delete nodes of 36 bytes) use `NodeChecksum.set`.
  * No Fletcher-16 is left in `java/`, and `lean/` has no checksum. The
    record header, the got-dirty list and the meta block have no checksum,
    as 024-25, section 2, says.
* **Layouts, writer against reader:**
  * Top node: long 1 is zero (bytes 8 to 15), and h and the ordinal
    (`pointersLength | ordinal << 16`) are at 16 to 23. `parse` reads h
    at 16 and the ordinal as `bytesToLongLE(16) >>> 16`. The id is at 24,
    then the root time and root pointer, then the pointers from 48. The
    size is 48 + 16·h in `getByteSize`, in `parse`'s check and in the
    class comment.
  * Key node: `leaf << 32 | n << 40` puts the leaf at 12 and n at 13 and
    14, and `parse` reads them there. prevPos is at 16 and the id at 24.
    The size is 32 + 16·n, unchanged.
  * Value and delete nodes: the id at 12, the offset at 20, L at 24, the
    value at 28. `getByteSize` and `getByteSizeLong` agree (12 + ...).
    `MIN_SIZE` is 28.
  * Formats 3, 3 and 5, in each writer and each parser.
  * `CREATION_LENGTH` 128 + 144: 32 + (48 + 16) + 32 + 9 = 137, rounded
    up to 144. The assert in `writePrimordialTransaction` holds,
    `DbTester` checks it, and the branch's builds start.
* **Sizes elsewhere:**
  * Heap accounting (`TopNode`, `KeyNode` and `ValueNode.getMemSize`)
    counts objects, not stream bytes: unchanged and right.
  * `TransSeq` (:347, :595), `Reclaim` (:635, :942 to :948, :1953),
    `TransNodes` (:116), `Db.checkSize` and `LimitsTester` call
    `getByteSize` or `getByteSizeLong`, so they follow the change.
  * `checkDirtyNodes`' key node bytes (32 + 16·(M + 1) + 16) are
    unchanged, and so are `dirtyNodeBound`'s counts. Its top node bytes
    are R5.
  * 024-24's limits (L1 to L5) count keys and values, not node bytes. The
    4 bytes a KV (2,000 a transaction at L1 = 500) are far inside 1/8 of
    the record limit.
* **The test commits:**
  * `bd3063ac` changes the same fields at their new offsets: the top
    node's h at 16 and its ordinal at 18; a key node's count at 13; a
    value node's value byte at 28 and its size at 24; the hand-made record
    of 120 bytes.
  * `ef7762b4` refuses the old format byte.
  * `57246318`: the field range 72 and 48 covers the same fields as 64
    and 40 did. The sample's 48 still reaches a top node's root pointer
    (40 to 47).
  * `44fe5673`: CRC-32C sees every one-byte change, and `NodeChecksum`'s
    `testField` checks this, so an undetected 0xff flip is rightly a
    failure.
* **The pinned copies of `a0ea6312`.** I removed the fix each copy
  guards. All five pass on the branch as written.
  * `testFoundDescentCycle`: with the cycle checks of `58eba7cb`
    (`OpData.descentTo`, `GetMany`) off, it fails: "did not end in 60
    s".
  * `testFound021_11`: with `checkPointeeType` (`36e003ff`) off, it
    fails: "undetected". In this run and the 019_32 run below,
    `DbStarter:515`'s `validateKeyNode` was off too: one switch turned off
    both.
  * `testFound021_12`: with both calls of `validateKeyNode` for nodes
    before the section (`4ff84fb3`; `DbStarter:515` and
    `NodeCollection:602`) off, it fails: a `Bug` from
    `Dag.appendDeleteKlong`. With only one of the two calls off it still
    passes, because the other call refuses with the same text.
  * `testFound019_32`: with `checkPointeeType` off, the row of seed
    729003 fails with the `ClassCastException` of 019-32.
  * `testFoundLinkByIdPrevPos`: R3.
* **The documents:**
  * `docs/levels.md`, `docs/sis-model.md` and `docs/trace-format.md` name
    no checksum algorithm and no node layout, so they need no change.
    levels.md's "record format 7 since release 2026.5" stays true.
  * `releases/next.md`'s entry matches the code and my probe of R6: 12
    bytes, formats 3, 3 and 5, +8 and +4 bytes, the refusal of an earlier
    format-7 database. CRC-32C detects every burst of up to 32 bits.
    Its figures of 1 ms and 47 ms are 8 × 0.12 and 8 × 5.6 ms. R7 is the
    exception.
  * 024-02's tables in sections 9 to 12: right (R2 for the rest).
  * 024-25 sections 2 to 5 match the code. The table in section 3 matches
    each class comment.


## 4. What I did not check

* CST's full set, StreamDigest, the level scripts 2 to 4 and conformance:
  crc's chain runs them. I read only level1's and unlinkfuzz's results.
* The measurements of 024-25, section 6. I made no timing runs. My SS
  figures (R4) are byte counts and do not depend on the machine.
* The C port (022) and its vectors.
* Merging with 024-24's branch: conflicts in `Db.java`,
  `CorruptStreamTester` and `StoredTrans` are likely, and R5 applies.
* Whether another session made databases with `main` in the window of R6.


## 5. Probes

All under `/Users/f/fl/bench/2026-11-11/rev25/`. Each source change of a
probe was reverted, and `clone` is at `e3cf5937` with no local changes.

* `probe/src/bergdb/core/Rev25Open.java`: makes or opens a `FileStream`
  database. Compiled against each of the three builds. Used for R6.
* `probe/run/bergdb/core/Rev25Run.java` and `Rev25All.java`: run one named
  test, or every `@Nano` test of the named classes, with `-ea`. Used for
  R1, R3 and section 3.
* `probe/rec/bergdb/core/Rev25Rec.java`: prints a LONG original's record
  and its nodes (offset, size, type). Used for R3 on `base`.
* `base`: a worktree of `0cb7eff7`. Its `build/bergdb.jar` was built with
  `checkLinkById`'s refusal off, for R3. Rebuild it before any other use.
