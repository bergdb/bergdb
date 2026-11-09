021-12. Fix: a key node read at a start from outside the startup section is not validated
=========================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a start validates the key nodes of the startup section
(`DbStarter.validateNode`, `KeyNode.validateStreamNode`: sizes, the last
time's index, times increasing, its pointers), but not a key node version
that it reads from before the section (by the rerun's follows, or as the
canonical object of a got-dirty node). If such a node is damaged so that
it breaks `KeyNode`'s invariants (times not increasing, a key klong whose
pointer is `Spos.NULL`), the start's own check of the nodes in memory
(`DbStarter.postStartupCheck`, `Db.checkNodes`, `KeyNode.check`) throws
an `AssertionError` out of the start, also without `-ea` (an explicit
throw), or, when the rerun puts into the node, an `assert` of
`KeyNode.addKlong` does (`lastTimeIndex=...`; without `-ea` the start
goes on), where 019-32's rule wants a `StreamFormatException`.

Found by harness 6.1's full set on the workload `LONG` (021-11), at its
first run (seed 20766, 2026-11-09): 51 of 332,291 copies, all of this
class, in one key node (node 22807, version at 36536, in the record at
36336) outside the section: 25 bytes flipped by 0xff (019-33's flips,
which the checksum misses) and 26 node fields changed with the checksum
made right.

Why: 019-32's class (015-07: what a start reads from the stream is
checked, so that it refuses a damaged stream with a `StreamFormatException`,
P7), for the nodes a start reads outside the section. 019-32 left a key
klong's pointer `Spos.NULL` unchecked at a read on purpose (`parse`
allows it, as `validateNode` does).

Frans: none.

Done when: the start refuses such a node with `StreamFormatException`,
at the site where it reads it (as `validateNode` does for the section's
nodes) unless the parse is clearly right; a test that fails before the
fix (LONG's seed and copy as a fixed case); the line "021-12" removed from
`CorruptStreamTester.SKIP`; `BEFORE COMMIT OK` and `level1.sh` under the
gate lock.

First step: the copy "flip, xor 255 at 36570" of LONG's original of seed
3971358 (the full set's seed 20766): the start throws `AssertionError:
Time not increasing` from `Db.checkNodes`, with and without `-ea`.


Log
---

2026-11-09. Registered by coord-1109 from the finding of its agent p11
(021-11), with the line "021-12" in `CorruptStreamTester.SKIP` so that
the night's full set, which runs `LONG` from 021-11's second commit,
stays green until the fix.

2026-11-09. Fixed by p11, at coord-1109's request after the
registration: commit bdebaef in `clone-p11`, on 7c872e5, to land.

* The first step's copy, and two more: "flip, xor 255 at 36738" (a time
  klong made later than the rerun's put: `KeyNode.addKlong`'s assert,
  `lastTimeIndex=21 ...`, with `-ea` only) and "int 2147483640 at its
  byte 36" of the node (its first klong, a time klong, made a key klong
  whose pointer is `Spos.NULL`: `Bad spos of pointer 0`, from
  `KeyNode.check`, also without `-ea`). The node is read from before the
  section by the rerun's follows (`NodeCollection.readVersion`).
* The site: where the start reads such a node, as `validateNode` does for
  the section's, not the parse (019-32 left a key klong's pointer
  `Spos.NULL` unchecked at a read, and a read after the start keeps its
  behaviour). The new `DbStarter.validateKeyNode`, which `validateNode`
  now calls: `KeyNode.validateStreamNode` (its size, the last time's
  index, times increasing, a key klong's pointer valid for the times up
  to the startup time) and, for a version from before the section, that
  none of its times is after the startup time (it was written before
  it). Called by `NodeCollection.readVersion` during the reconstruction,
  for every key node version read, before it is cut back, and by
  `DbStarter.canonicalNode`, for the version it reads of a node of D.
  Each refusal a `StreamFormatException`. This adds no check that
  `Db.checkNodes` (`KeyNode.check`, at the start's end) did not already
  make of every key node in memory, so a valid stream's start is not
  refused by it; the time check holds for every version written before
  the startup time.
* Test `CorruptStreamTester.testFound021_12`, the three copies; before
  the fix each threw an `AssertionError` at the start, with `-ea` (the
  first and the third also without), now each is refused. The line
  "021-12" left `CorruptStreamTester.SKIP`, which is empty again.
* `releases/next.md`, Core API, a line.

Runs, under the gate lock (2026-11-09, 12:23 to 12:32): the night's full
set (`night.sh tests -c CorruptStreamTester -m testFull`, all four
workloads, seed 20766) SUCCESS in 160 s, with nothing skipped;
`BEFORE COMMIT OK (165 s)`; `java/stress/level1.sh`: `LEVEL 1 OK`.
