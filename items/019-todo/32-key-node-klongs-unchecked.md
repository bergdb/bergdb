019-32. Fix: a node's klongs and pointers are not checked at a parse, and a start or a read meets an assert
=========================================================================================================

Status: open. Kind: Fix. Frans: none.
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
