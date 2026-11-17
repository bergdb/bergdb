015-14. Fix: the fast path's plain reads rest on the address dependency, not on the JMM
==========================================================================================

Status: done. Kind: Fix (decided). Created 2026-11-03 by Frans Lundberg.

For Frans; a known issue of 2026.2 until decided. Found by review R1
(016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F3, with the interleaving written out (to be checked by a
second agent, 016-06, section 2.6).

What: 009-02, 3.4 argues that the fast path's plain read of a pointer is
safe by the Java Memory Model. R1 shows an interleaving in which the
JMM allows the plain read to pair the handle's older object with the
pointer's older reference, which `usable` accepts, giving a version
without a change committed before the reader's lookup time. HotSpot does
not do it, as the read of the object depends on the pointer's address; so
it is a gap in the argument, not a fault seen. 015-12's fix leans on the
same dependency on the reader's side.

Options: A, acquire reads of the pointer (T6a) and of the key node's
arrays, which costs a little on AArch64 per follow and search (to be
measured in a quiet block); B, rewrite 009-02, 3.4 to state the reliance
on the dependency, as HotSpot keeps it.

Recommendation: B for 2026.2 (no change to the read path), then A
measured; if its cost is small, A.


State
-----

2026-11-03, 20:34: the investigation, the fix (T6a, option A, for every
read of the Log's list that rested on the dependency or on a 64-bit JVM),
the tests and the gate done in the clone
(`/Users/f/fl/bench/016/015-14/repo`, from `main` at `b1651a5`, rebased
on `2d7daae`); reviewed (016-05, H5: no fault; three doubts and five
nits, answered in the Log, the nits on the text fixed); handed off again
(`/Users/f/fl/bench/016/015-14/handoff/`).

The read path's cost in 2026.2 is unmeasured: estimated in the Log (seven
more load-acquires a hop on AArch64, none on x86), to be measured after
the release; the 2026.2 notes should say so. Open: that measurement, with
the review's nits 4 and 5 (the note at the end).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:18. Frans: ""thread safety rests on today's JVM
behaviour". This is not acceptable. Ensure this is either fixed before the
release or clearly documented as an open todo item. This needs an
investigation and a fix." So: an investigation (R1-F3's interleaving
checked; every plain read of a shared field on the read path that relies
on an address dependency, 015-12's reader side included) and a fix that
makes the read path correct by the Java Memory Model, before the release.
If it is not done by the freeze, this entry stays an open Fix and the
notes say so in their known issues.

2026-11-03, 19:34 to 20:10, by an agent of the coordinator (016-05), in
`/Users/f/fl/bench/016/015-14/repo` from `main` at `b1651a5`:

* **R1-F3's interleaving, checked against the code at `b1651a5`.** It
  holds as R1 wrote it. The fast path (`NodeCollection.followPointer`)
  read pointer i of a key node plainly for a handle (`getPointee`), then
  its reference plainly (`getPointerPos`), then `h.obj` (volatile). The
  writes of R1's steps 2 to 5 are: the raise (`followStreamPointer`, step
  2, `raiseRef` under x's monitor, a plain store), the install
  (`Cache3.install` under h_b's monitor, a volatile store of `h.obj`) and
  the swizzle (step 5, `KeyNode.swizzle` under x's monitor, a release
  store). A plain read of a release store makes no edge, so R3's reads of
  the reference and of `h_b.obj` may see the writes before the raise and
  the install (17.4.5), and `usable(v at P1, P1)` is true: a version
  without T's change. One more thing than R1 wrote: the read of the
  reference did not depend on the read of the pointer at all, so even the
  hardware could read it first. It did, on F53: jcstress `SwizzleOrder`
  (below) on the base's jar gave the new handle with the reference before
  the raise 21 times in 86 million (quick mode, 24 s). Harmless there (the
  object, read through the dependency, was the new one), but the pair was
  of two moments. A top node's pointers were worse: changed in place by
  plain stores under the monitor, no release at all (`TopSwizzleOrder`:
  56 in 82 million).
* **Every plain read of a shared field on the read path** (a get: the
  top node search, `findRoot`, the key node searches, the fast path; the
  slow path where it reads without a lock), at `b1651a5`, and what its
  safety rested on: (D) the address dependency, (L) a 64-bit JVM, where a
  plain long does not tear (17.7 allows it), (E) a happens-before edge,
  (H) a race whose every value is harmless.
  1. `KeyNode.pointers[i]`, a pointer to a handle, on the fast path
     (`followPointer`) and in `getPointerNode` (each search's `kwi.node`,
     the walks, the audit): plain. The reads after it, `pos[i]` and
     `h.obj`: (D) for `h.obj`, no order at all for `pos[i]`. R1-F3.
     Fixed: an acquire.
  2. `KeyNode.pos[i]` (the fast path's reference, `getPointerNode`'s, the
     searches' `kwi.pos`): plain, in a race with `raiseRef`, `setRef` and
     `setPointer`: (L), and unordered with point 1. Fixed: an opaque read
     after the acquire; opaque stores in place.
  3. The fields `KeyNode.klongs`, `pointers`, `pos`, which a growth
     replaces (the searches read `klongs`, the fast path `pointers` and
     `pos`, `pointsToIndexNode` `klongs`): plain reads of plain stores
     after 015-12's release fence; a reader that read `size` before the
     growth read the copies through the address of the array it read: (D),
     015-12's reader side. Fixed: the fields volatile, the fence gone.
  4. `TopNode.rootPointer`, `pointers[i]` (`findRoot` on every get, and
     `findSuperRootAtTime`'s `getPointerNode` and follows): plain reads of
     plain stores under the monitor: (D) for `h.obj`, nothing for the
     reference. Fixed: an acquire read, release stores.
  5. `TopNode.rootPointerPos`, `pointersPos[i]` (the follows; `TopDs`'s
     `rightMostGte` and `leftMost` read `pointersPos[i]` directly): (L),
     and unordered. Fixed: opaque reads after the acquire, opaque stores.
  6. `Handle.writtenPos`, read by the slow path without the handle's
     monitor (`followStreamPointer`, step 2; the maintenance follower):
     (E) through the eviction's null, but (L) when the read races with the
     eviction. Fixed: volatile (no cost on the fast path).
  7. `KeyNode.isCanonical`, `TopNode.isCanonical` in `Handle.usable`:
     plain, in a race with `makeCanonical` and the eviction: (H), with the
     clock's edge for a stale true (009-02, 3.4, point 6). Not changed.
     TopNode's synch note said "Db.writeLock only"; corrected.
  8. `KeyNode.spos` in `usable` (`getSpos`: `size`, then `spos`): set
     before a version's install (E); changed after publication only on a
     canonical object, by a record (`StoredTrans`, `setSpos`), which serves
     every reference: (H), even torn. Not changed.
  9. `Handle.ref`, the CLOCK bit: a byte, (H). `Handle.id`: final, 17.5.
     `Handle.obj`, `Handle.state`, `KeyNode.size`, `TopNode.spos`,
     `TopDs.superRoot`: volatile (E). A top node's `pointersTime`,
     `rootTime`, a key node's `id`: set before publication (E). Not
     changed.
  10. A value's fields (C5): `value` final, `spos` volatile, through the
      acquire of point 1 (E), as before. Not changed but for the read,
      which is now the same acquire as for a handle.
  11. The slow path's pair, under the node's monitor (E); the handle's
      object under the handle's monitor (E). Not changed.
  The writer's own reads of the pointers it copies are under the node's
  monitor (`lastVersionGivenDel`, `TopDs.newSuperRoot`, `resolvePointers`)
  or of a node no reader sees yet (`firstAndSecond` of `lastVersion`'s
  copy).
* **The fix** (option A, T6a; 009-02, 3.4 rewritten):
  * `dag/KeyNode.java`: `klongs`, `pointers`, `pos` volatile; the release
    fences of 015-12 removed (the volatile stores order the copies before
    them); `getPointee` an acquire read for every pointer
    (`getPointeeAcquire` merged into it); `getPointerPos` an opaque read;
    `setRef`, `raiseRef`, `setPointer` opaque stores of the reference (the
    reference first in `setPointer`); the searches' result by one helper,
    `pointerInto`: the pointer with its acquire, then the reference, each
    field once; `getPointerNode` through the same order. Class comment and
    synch notes.
  * `dag/TopNode.java`: the root pointer and the skip pointers by
    VarHandles: acquire reads, release stores; the references opaque.
  * `dag/TopDs.java`: the skip pointers' references by `getPointerPos`.
  * `core/NodeCollection.java`: the fast path reads every pointer by
    `getPointee` (no `pointsToIndexNode` test on the fast path).
  * `dag/Handle.java`: `writtenPos` volatile. `dag/Node.java`: the
    contracts of `getPointee` and `getPointerPos`.
  * 009-02: section 3.4 rewritten to the code, edge by edge (the model,
    the ten points, R1-F3's interleaving with the new code, C1 to C7,
    the cost); 3.3's rows, the status line, 1, 4.4, 5 (3c), 6 (T6) and 9
    (`pos[i]`) say T6a since 015-14. docs/levels.md, section 7, the
    readers' bullet. Not changed: the stream format, the Pub API.
* **The cost, expected** (not measured: F53 is shared tonight), per hop
  of a get, a search and a follow: on AArch64 (F53) seven more
  load-acquires (`ldar`) than before: the search's `klongs`, `pointers`,
  `pointers[i]` and `pos`, the follow's `pointers`, `pointers[i]` and
  `pos`; and two plain loads fewer (the klong the follow read to choose
  its read). An `ldar` that hits the cache costs about a plain load, but
  no later load may complete before it; the searches' loads depend on
  them anyway. 004-01's `handleacq` (5 edges a lookup, one acquire each)
  measured +1.4 ns a lookup in cache (72.1 against 70.7 ns, F53, one
  thread), about 0.3 ns an acquire: seven a hop, some 2 ns a hop, 10 ns a
  get of five hops in cache. Out of cache it measured +19 ns a lookup
  (583 against 564, 3 %); an acquire keeps later loads from overlapping
  its miss, so this is the larger risk, if it scales with the count: up
  to some tens of ns a hop. On x86 (s1) none of these is more than a
  plain load (TSO: acquire, opaque and volatile loads are a `mov`), so
  about nothing; the volatile stores of the array fields (a growth, a new
  key node: three each) add a locked instruction each on x86, on the
  writer only. To halve the acquires later: the follow could take the pointer
  that the search read (an API change of `PointerFollower`), and the
  readers' searches need not compute `kwi.node`, which only the audit and
  tests use.
* **Tests.** jcstress (`java/stress/jcstress/`; `/Users/f/fl/bench/016/
  jcstress-lib`, quick mode, `-c 4`, 24 s each run, F53 at a load of 8
  to 10): new `SwizzleOrder` (R1-F3's steps 4 and 5 on a key node: a
  raise, an install, a swizzle, against a fast-path read) and
  `TopSwizzleOrder` (the same on a top node's root pointer). The mutation,
  the base's jar (`b1651a5`, built in
  `/Users/f/fl/bench/016/015-14/mutbase`): both `[FAILED]`, the forbidden
  "1, 2" (the new handle with the reference before the raise) 21 times in
  86 million and 56 in 82 million; "1, 0", R1-F3's wrong answer, 0 (the
  JMM allows it there, HotSpot does not give it). "1, 2" is harmless
  (`usable` accepts the version at 300 for 200, and it is the right one):
  the tests show the order that the fix adds, not a wrong answer of the
  code before. The fix's jar: both `[OK]`, every forbidden outcome 0 in 77
  and 79 million. All eight tests
  (with `GrowthPublication`, `HandlePublication`, `InstallPublication`,
  `ValuePublication`, `EvictionRace`, `PlainPublication`) on the fix,
  quick mode, 19:57 to 19:58: `[OK]` each; `GrowthPublication` "14, 1, 1"
  (the old size, a new array with its copies) 145,593 times, never a
  forbidden one. Unit tests: `KeyNodeTester.testPointerInPlace` and
  `TopNode.testPointerInPlace` (in-place raise, swizzle, setPointer read
  back as a follow reads them, across a growth); the existing tests
  unchanged. run.sh's header names the new tests.
* **The gate**: `java/before-commit.sh`, 20:02 to 20:04: `BEFORE COMMIT OK
  (106 s)`, 1,125 unit tests and 78 f-tests. Then the clone rebased on
  `main` at `f219dc7` (015-09, 015-16, 015-10: other files) and gated
  again, 20:06 to 20:07: `BEFORE COMMIT OK (105 s)`, 1,127 unit tests and
  78 f-tests.


2026-11-03, 20:27 to 20:34, the review's findings (016-05, H5, 20:09 to
20:30: no fault; `/Users/f/fl/bench/016/015-14/handoff/review-findings.md`)
and the answers, in the clone rebased on `main` at `2d7daae`:

1. Doubt, the tests: "1, 2" is harmless, "1, 0" was not seen on the base;
   the tests show the order the fix adds. Agreed: 009-02, 3.4, point 10,
   this Log (the tests bullet above) and the commit message
   (`handoff/commit-message.txt`) now say exactly that.
2. Doubt, the model: JLS 17.4 has no acquire, release or opaque mode; the
   edges rest on the VarHandle specification (the Java SE API), which
   009-02, 3.1 counts as the JMM. Agreed, not changed tonight: it is not
   today's JVM behaviour but the platform's specification. If Frans means
   17.4 to the letter, `getVolatile` and `setVolatile` give the same proof
   by 17.4.4, at the same reads (`ldar` on AArch64, a plain load on x86)
   and a fence per in-place store on x86; 3.4's model paragraph says so.
3. Doubt, the cost is unmeasured. Agreed: the State says so, and that the
   2026.2 notes should; the measurement is the note at the end.
4. Nit, cost: `pointerInto` fills `kwi.node` and `kwi.pos`, which readers
   use only in asserts, before the follow reads the pointer again: 3 of
   the 7 added load-acquires a hop. Agreed; no code change tonight: into
   the note at the end.
5. Nit, cost: the volatile array fields cost on writer-only paths too
   (loops the JIT cannot hoist, `StoredKeyNode.parse`'s `addToEnd`, the
   constructor's three volatile stores). Agreed; no code change tonight:
   into the note at the end.
6. Nit, 3.4's C7 did not name `KeyNode.spos`. Fixed: C7 names it, with
   point 6's reason.
7. Nit, point 6 said every eviction runs under the write lock;
   `Cache3.dropIfEmpty`, a reader's, does not. Fixed: point 6 names it
   (R1's D2, outside the argument, as before); `Handle.writtenPos`'s
   Javadoc says so and why it is volatile.
8. Nit, point 3(c) omitted a reader's `setPointee` of a value; KeyNode's
   synch notes omitted `replaceKlong`; 3.3's table had stale cells and
   rows of up to 302 characters. Fixed: point 3(c) and the synch notes
   name them; 3.3 is a list now, its stale cells (`writtenPos`, `pos[i]`)
   corrected, and the line after it wrapped.

Comments and documents only; `java/before-commit.sh` again, 20:30 to
20:32: `BEFORE COMMIT OK (105 s)`, 1,128 unit tests and 79 f-tests.


After the release: the cost
---------------------------

A 015 note, for after 2026.2 (to become an entry of its own if the
coordinator registers one): measure what 015-14's acquires cost, with
`java/stress/performance.sh` on a quiet F53 (AArch64, where they are
load-acquires), against the code before (`b1651a5`), in turns: the
in-cache and the out-of-cache gets, and a put-heavy suite (the volatile
array fields: a few more `ldar` in the writer's own reads). On s1 (x86)
a short check only: no new instructions are expected there. If the
in-cache or out-of-cache gets lose more than a few percent: the follow
takes the pointer that its search read, so that each hop reads pointer i
once (an internal API change, `PointerFollower`), and the readers'
searches stop computing `kwi.node`, which only the audit and tests use;
both keep the edges of 009-02, 3.4.

The review's nits 4 and 5 (016-05, H5), measured with it:

* `KeyNode.pointerInto` fills `kwi.node` and `kwi.pos` in every search,
  which the readers use only in asserts (`Dag.java`'s `getEqNodeInSegment`;
  `GetMany` reads the klong and the pointer index), before the follow reads
  the same pointer again: 3 of the 7 added load-acquires a hop (the fields
  `pointers` and `pos`, the element), with `h.obj` and `usable`, already
  wasted before 015-14. Only `Audit` reads them; a separate method could
  fill them for it.
* The volatile array fields cost on writer-only paths too, where one
  thread stores them: each `klongs[i]`, `pointers[i]`, `pos[i]` in a loop
  is a volatile load the JIT cannot hoist (`lastVersionGivenDel`'s nested
  loops, `addToEnd` for each klong of a node that `StoredKeyNode.parse`
  loads, `Dag`'s writer loops, `Residents.bytesOf`), and a new key node's
  constructor makes three volatile stores (a fence each on x86). A local
  copy of the field, or VarHandle plain access on those paths, avoids it.

2026-11-03, 20:36, by the coordinator: the review's answers read; the
change committed after the combined gate on `main` (the gate line in the
commit). Open after the release: the read path's cost (the note above).
