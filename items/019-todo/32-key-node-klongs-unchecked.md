019-32. Fix: a node's klongs and pointers are not checked at a parse, and a start or a read meets an assert
=========================================================================================================

Status: done 2026-11-06. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: `StoredKeyNode.parse` checks the key count against the node's size
(015-07), but not the klongs themselves: their types (time, key, delete
bitmap), and that a key klong's pointer is there. A key node whose
checksum is right and whose klong is damaged is taken, and the start
meets an `assert` of the Core's own invariants: with `-ea` an
`AssertionError`; without it, in the first case below, an
`IllegalStateException: unexpected klong type, 2` (at
`KeyNode.replaceKlong:928`). 015-07's rule is that a parser checks what it reads and throws a
`StreamFormatException`, so that the start refuses the stream or a read
fails the database (P7).

Found by harness 6.1 (018-07), in the night 006-12, a node's byte changed
with its checksum made right (as 015-07's tests do):

```text
meta, seed 3348004 (sample seed 1), node, xor 128 at its byte 39, checksum right, of the
  node at offset 104 (size 496, type 20) of the record at 365024: the start threw
  java.lang.AssertionError: Bad klong type, 2 (at dag.KeyNode.getLastDeleteBitmap:1822)
take, seed 3552484 (sample seed 3), node, xor 128 at its byte 37, checksum right, of the
  node at offset 156 (size 40, type 30) of the record at 31880: the start threw
  java.lang.AssertionError: pd.kwi.klong is Klong.NULL, non-null expected, node: K/7e
  12259:30984   (at Dag.java:672)
```

The full set of the night (seed 20398) found the same class at reads
and at a start: a key node's value pointer or pointer position damaged
(by a byte flipped by 0xff, which the checksum does not see, 019-33),
"a read threw java.lang.AssertionError: bad value pointer
-72057594037927640, index 2 of 0 (at core.NodeCollection.
followValuePointer:585)", "bad pointerPos (...), to read from stream";
and a pointer to a node of another type, "the start threw
java.lang.ClassCastException: class bergdb.dag.ValueNode cannot be cast
to class bergdb.dag.KeyNode" (a node's byte 16 xor 1, checksum right).

Why: 015-07's class (a node's inner fields), a fault of the Core (018-01,
W3). Only a damaged node whose checksum is right reaches it: a crafted
change, or a writer's fault; random damage is caught by the checksum but
for 019-33's case.

Frans: none.

Done when: the parser (or `DbStarter.validateNode`, which already
refuses a key node's times since 005-75) checks each klong's type and a
key klong's pointer, a read checks that a pointer names a node of the
type it expects, and each throws a `StreamFormatException`, so that a
read fails the database (P7); a test per case that fails before the fix
(the harness's copies above); the
line "019-32" removed from `CorruptStreamTester.SKIP`; `BEFORE COMMIT
OK`; the stream's bytes unchanged.

First step: `java -ea -Dbergdb.corrupt.skip=none -cp build/bergdb.jar
bergdb.core.CorruptStreamTester 3` shows the second case, and seed 1 the
first (with and without `-ea`).


Log
---

2026-11-06. Registered in night 006-12 by the agent of harness 6.1
(018-07), with the line "019-32" in `CorruptStreamTester.SKIP`. Not fixed
that night: found at 03:38, too late for a fix and its gate before the
night's stop.

2026-11-06. Taken and done by coord-1106's agent f32 (clone f32, branch
f32). The night's cases first, by a probe: the second one ("pd.kwi.klong
is Klong.NULL", `take`) was not a key klong's pointer but a value node's
key, its bit 63 set (byte 37 of a node of type 30), which the start's
rerun put into the graph. The full set of seed 20398 with nothing
skipped failed with 200 copies; with the checks below, none. The checks,
each a `StreamFormatException` (a `DbException` in the `dag` package,
which knows no streams), so that a start refuses the stream and a read
fails the database (P7):

* `StoredKeyNode.parse`, from the node's own bytes: each klong's type is
  time, key or delete bitmap (type 2 is no klong's); a key klong's
  pointer is a position or `Spos.NULL`, as `DbStarter.validateNode`
  allows it; the node's size is its count's exactly (`getByteSize`; 015-07
  checked only that the count fits), as a count one lower read the
  pointers from the wrong bytes and gave a key klong a time klong's
  `Spos.NULL`.
* `StoredValueNode.parse`: the key is one that `Keys.toSegments` makes
  (`isKey`): each segment with bits 0 to 2, 62 and 63 zero, all but the
  last of length 7, the last shorter. Not the bytes after a segment's
  length: such a key works in the graph, and a Core caller could have
  written one.
* A read checks that a pointer names a node of the type it expects
  (`NodeCollection.checkPointeeType`: a top node's root pointer a key
  node, its skip pointers top nodes, a key node's pointers key nodes or
  values as `pointsToIndexNode` says), on a node read
  (`readVersion`, before it is installed; `followValuePointer`), on the
  object a handle gave (`followStreamPointer`), and where the start
  links the startup section's pointers in memory
  (`DbStarter.createMemoryPointers`). The asserts on a pointer's
  position became checks (`followStreamPointer`, `followValuePointer`:
  negative or, for a value, odd; `NodeStream.readNode`: below the first
  meta block's end).
* `Cache3.register` and `install`: one id, one type. A key node's id 0
  (the first key node's) changed to 1 (the first top node's), or the
  reverse, put a node into the other's handle, and a read got a
  `ClassCastException` (`TopDs.rightMostGte`). An id rule at the parse
  (odd, but the first key node's 0) was tried and dropped: tests build
  nodes without an id (-1), and the rule is no format rule.
* `Dag.setValue` and `setNode`: a key node that is not a segment leaf
  has a klong at or below the key (an assert before; without `-ea` the
  put followed the last search's pointer). Reached by the first key
  node, without keys, made a non-leaf by its byte 16 (the `all` copy).

Not checked: a key klong's pointer that is exactly `Spos.NULL` at a read
(an 8-byte change; the asserts of `Dag.getEqNodeInSegment` and
`NodeCollection.followPointer` stay), the key bytes after a segment's
length, and two nodes of one type with one id (a valid node with another
meaning, outside the model). No format change; valid streams are read as
before; the stream's bytes are unchanged (nothing that writes changed).

Tests that fail before the fix and pass after (before: the fix's
production code taken out in a second clone, f32-before):

* `StoredKeyNode.testRefusesBadKlongs`: a klong of type 2, a pointer of
  -8, a count of 1 in a node of 2. Before: "parsed".
* `StoredValueNode.testRefusesBadKey`: bit 63, bit 0, a last segment of
  length 7, a first of length 6. Before: "parsed".
* `CorruptStreamTester.testFound019_32`: the harness's copies, the two
  of this entry and eight of the full set (a key count, the ids 0 and 1,
  a leaf's flag at a start and in a node without keys, a skip pointer to
  a key node, a value pointer negative and odd). Before: each of the ten
  threw as the night's copies did: an `AssertionError` (a klong's type,
  the key, a key klong with no pointer, a value pointer negative and
  odd, a non-leaf without keys) or a `ClassCastException`.

The line "019-32" left `CorruptStreamTester.SKIP`, which is empty, and
`entryOf` returns null. Runs: `unit.sh` of the touched classes
SUCCESS; harness 6.1's samples of seeds 1 to 5 with no failure (seed 1
also without `-ea`); `night.sh tests -c CorruptStreamTester` (seed
20398) SUCCESS, 104 s; by hand, the full set of seed 20400 (296,805
copies) with no failure, and of seeds 20398 (also without `-ea`) and
20399. 018-07 (sections 4, 5.4, 6, 8, log), 018-01 (section 6.1, log)
and 018's readme follow; `releases/next.md`, Reliability, a line.
BEFORE COMMIT OK.

