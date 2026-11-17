021-11. Fix: a pointer linked by node id is not checked for its node's type
===========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: 019-32's check that a pointer names a node of the type it expects
(`NodeCollection.checkPointeeType`) is made where a pointer is followed,
but not where the Core gives a pointer the handle of the node that its
position names, by node id: `NodeCollection.linkToCanonical` (the start's
rule 4, `DbStarter.linkD`) and `resolvePointers` (the writer, before a
node is written). A damaged pointer, its node's checksum right, that names
a version of a node of another type gets that node's handle, and a later
read throws a `ClassCastException` (an `AssertionError` under `-ea`)
instead of the start's `StreamFormatException`. Found by reading, not
reproduced in Java, by the session porting the Core to C (022-01, step
2).

Why: 019-32's class (015-07: a parser or a link checks what it takes from
the stream, so that a start refuses the stream or a read fails the
database, P7), a fault of the Core (018-01, W3).

Frans: none.

Done when: a failing test on a stream damaged as 019-32's tests damage
one (a node's pointer set, its checksum made right), or the finding
refuted; the fix, so that the start refuses with `StreamFormatException`
at the link; the other sites that take a node id from a pointer without
the type check looked for; `BEFORE COMMIT OK` and `java/stress/level1.sh`
under the gate lock; a line in `releases/next.md`.

First step: a stream with key nodes that point to index nodes, and a
key node's pointer set to a top node's version.


Log
---

2026-11-09. Registered by coord-1109 from the finding of the C port's
session (022-01, step 2), and taken by its agent p11 (clone
`clone-p11`).

2026-11-09. Done by p11: confirmed, and wider than reported; commit
1035b64 in `clone-p11` (on main's dfb0c50), to land.

* Harness 6.1's workloads (`CorruptStreamTester`, 018-07) never meet it:
  their keys (`KEYS`) are of one segment and at most 15, so no key node
  points to a key node, and a top node's damaged pointer in them was
  refused by `DbStarter.createMemoryPointers` or a follow. A probe on
  workloads of long keys did: every index pointer of every key node set
  to each top node version, each top node's root pointer to each top node
  version and its skip pointers to each key node version, the checksum
  made right, then a start and reads of every key. On one of them
  (startup distance 5,000, seed 1), 14,300 copies: 783 failed with `-ea`,
  189 without; with writes before the reads, 88 more without `-ea`.
* Three sites, each a node id taken from a pointer's position and its
  handle put into the pointer without the type check:
  1. `NodeCollection.linkToCanonical` (the start's rule 4, `linkD`), by
     the section's ids (the reported case: a key node's pointer set to
     the newest top node version; a read threw `AssertionError: Expected
     a KeyNode` at `Dag.getEqNodeInSegment`, without `-ea` a
     `ClassCastException`), and, for a top node's pointer, by the header
     (a skip pointer set to a key node version, or the root pointer to a
     top node version: a read threw a `ClassCastException` at
     `TopDs.rightMostGte` or `TopDs.findRoot`).
  2. Its check of 005-57 (`checkLinkById`, with `-ea` only): a key node's
     pointer set to an older top node version, outside the section; the
     start threw `AssertionError: rule 4 by position is not rule 4 by
     node id`. Without `-ea` the pointer is not linked, and a read fails
     the database by the follow's check, as it should.
  3. `NodeCollection.resolvePointers` (the writer, before a node is
     written), by the header: a pointer of case 2, not linked at a start
     without `-ea`, got a dirty top node's handle when its node was
     written, and a read threw a `ClassCastException`.
* Fix: `checkPointeeType` at each, before the handle goes into the
  pointer, so the start refuses the stream (or the write fails the
  database) with 019-32's `StreamFormatException`, "Pointer i of node X
  names a node of type T at P, not E." Ten lines.
* Other sites looked at, no fault: `followStreamPointer` (the id from the
  header; the object checked after step 4, 019-32), `createMemoryPointers`
  (checked, 019-32), `DbStarter.updateStreamPointers` (Rule R by the
  section's ids, positions only), `topNodeOfLastTransaction` (checks its
  type, 015-75), `canonicalNode` (got-dirty ids: the id checked, and any
  type may be dirty), `Audit` (tests only). The Rule R reference that a
  follow raises and `resolvePointers` sets, by the header's id, is set
  before the type is checked, so a damaged pointer may name the other
  node's newest version, in memory or in the node written; a follow of it
  refuses it.
* Tests, each failing before the fix (the fix's lines taken out):
  `CorruptStreamTester.testFound021_11`, on the new workload `LONG` (80
  keys of three segments, startup distance 5,000; not in `CONFIGS`;
  `Config` takes its keys): the reported case and the skip pointer
  (before: a read threw, with and without `-ea`) and case 2 (before: the
  check's `AssertionError`); each now refused at the start.
  `NodeCollection.testResolvePointersChecksTheType`, case 3 (before: the
  key node's pointer got the top node's handle; under `-ea` a stream
  reaches case 2 first). The probe after the fix: no failure, with and
  without `-ea`, writes first or not; on `LONG`, seed 1, with the
  harness's own check, 4,263 copies, 67 failures before, none after.
* `releases/next.md`, Core API, a line. Valid streams are read as
  before; the stream's bytes are unchanged.
* For the harness (018-07): adding `LONG` to `CONFIGS` would give harness
  6.1 key nodes that point to key nodes, which it has never damaged; not
  done here (the sample's and the night's time).

`BEFORE COMMIT OK (134 s)` and `java/stress/level1.sh`: `LEVEL 1 OK`,
under the gate lock (2026-11-09, 11:47 to 11:52).

2026-11-09. At coord-1109's request, `LONG` joins harness 6.1's full set
(`testFull`, the night tests: `FULL_CONFIGS`), not the unit tests' sample
(`CONFIGS`), so `before-commit.sh` keeps its time; commit 7c872e5 in
`clone-p11`, on 1035b64. Its first full run (seed 20766, 4 threads, F53):
332,291 copies in 82 s, the night's added time, and 51 failures of one
new fault, registered as 021-12 (a key node read at a start from outside
the startup section is not validated), with its line in
`CorruptStreamTester.SKIP` until its fix: all 51 skipped, none left.
`BEFORE COMMIT OK (135 s)`.

2026-11-09. 021-12 fixed (bdebaef in `clone-p11`, on 7c872e5): the line
"021-12" left `CorruptStreamTester.SKIP`, and the night's full set with
`LONG` (seed 20766) passed with nothing skipped, in 160 s.
