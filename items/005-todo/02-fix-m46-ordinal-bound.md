005-02. Fix M46: the top node ordinal bound
==========================================

Status: done (2026-10-19; see Outcome). Kind: fix. Created 2026-10-19.


The issue
---------

Top node ordinals are bounded by `TopNode.MAX_TOP_NODE_ID_VALUE`, 2^30 − 1,
over a database's whole life. Reclaim bounds the stream but not the
ordinals. Register row M46 of
[docs/level4-alignment.md](../001-lean-model-levels-3-4/08-level4-alignment.md). The analysis,
with a patch: [item 002, 002-02](../002-top-node-ordinal-bound/02-report.md).

Why it matters now: with Level 4 the heap is a cache, so memory no longer
stops a database before the bound. A small database with a few hot keys at
1,000 transactions a second reaches it in about six months at node size 30,
five to seven weeks at node size 8; a full-speed soak on one key in 15 to 29
hours. At the bound Java fails in the worst way: in the middle of a root
split, with wrong reads, and once one more transaction commits, the database
cannot be started again (002-02, section 2).


The task
--------

Widen the ordinal as 002-02 recommends (sections 5 and 6):

1. `topNodeId` to a `long`, reading the 48 bits the stream already has
   (bytes 10 to 15 of a top node). No format change: the same bytes for
   every ordinal below 2^30.
2. A guard just below 2^48 that refuses a user transaction before it changes
   anything, so even the end is clean. (2^48 lasts centuries at the fastest
   rate measured, past the end of the database clock.)
3. Rebase 002-02's patch (7 files, 55 lines added, 32 removed, written at
   `0a732c3`) onto today's code, which item 001 changed.
4. Check the Lean model and the checker: do they bound the ordinal, or read
   it as 32 bits anywhere? The exporter and `tracecheck` must handle
   ordinals above 2^30.

Not part of this: the 2012 height decrease (002-02, section 7); it saves
bytes, does not lift the bound, and changes the format.


Done when
---------

* A database crosses 2^30, 2^31, 2^32 and close to 2^48 with restarts and
  reclaim, every historical lookup right (002-02's probes, as tests).
* The guard refuses a transaction cleanly at the end, and the database
  still restarts.
* No stream changes below 2^30: StreamDigest identical to R8's.
* The four gates print `LEVEL n OK`.
* M46 is closed in the register, item 002 is closed.


First step
----------

Apply 002-02's patch to a branch of today's code and list what no longer
fits.


Size and order
--------------

S to M. Together with 005-01 (both touch `Db.executeInner`; the bound is
one of M49's triggers).


Outcome
-------

2026-10-19, by Claude (Opus 5.5, Claude Code), at Frans's request ("Fix
005-02"), without 005-01. Worked in a scratch copy of the repository at
`0739170`, then applied to the work tree, not committed.

**First step.** 002-02's patch applied to today's code without a conflict,
only with offsets: item 001 had not changed its lines. What differs from it
is said below.

**The change.** Java, 8 files:

* `TopNode`: the ordinal, `topNodeId`, is a `long`. `MAX_HEIGHT` is 48, so
  `MAX_TOP_NODE_ID_VALUE` is 2^48 − 1; `height`, `power2`, `createDummy` and
  `getTopNodeId` take or give longs.
* `StoredTopNode`: `parse` reads the ordinal from bytes 10 to 15 as an
  unsigned 48-bit number (before: bytes 10 to 13 as an int); `toLongs` writes
  the long shifted by 16, as before. The check for a negative ordinal is gone
  (an unsigned 48-bit number never is one); the check against the bound
  stays. The class comment now gives the layout of a stored top node.
* `Db.executeInner`, the guard: when the super root's ordinal has reached
  `Db.LAST_TOP_ORDINAL`, 1,024 below the bound, a user transaction is refused
  with a `DbException` ("The database has used its top node ordinals (up to
  281474976709631); it takes no more transactions."), under the write lock
  and before `x.begin`, so it changes nothing. Reads go on; a restart works,
  and refuses again. This is Frans's principle of 005-01: the condition is
  checked before the transaction gets the go. Internal transactions are not
  refused: reclaim runs them after a user transaction that has committed. At
  most five follow one user transaction (a new iteration's table, a step, the
  table at its end, the safe marks, a cut), each with at most one top node,
  so with the margin of 1,024 no transaction reaches the bound, where
  `TopNode` still throws.
* `TopDs.newSuperRoot`: the ordinal as a long. For tests, the top node after
  the first can get a large ordinal instead of 1: `DbBuilder.secondTopOrdinal`,
  which `Db.Internal.setDag` passes to `TopDs.setSecondOrdinal`. Its skip
  pointers name the first top node, as `newSuperRoot` does for any skip
  pointer that the super root lacks, so every top node has the layout that
  `parse` checks. This replaces 002-02's scratch hook, which gave the first
  top node a large ordinal from a system property and skipped the parser's
  check for it: no check is relaxed. A test gives the option at every start,
  as it gives the node size, since the startup's rerun makes top nodes again.
* `TransNodes`, `DbTesterRestart` and `stress/TraceExport`: a local each
  made a long.

**Tests** (unit tests, in `DbTesterRestart` unless named):

* `testOrdinalsAcrossBoundaries`: the second ordinal 20 below 2^30, 2^31, 2^32
  and 2^47, one hot key at node size 8, to 20 above. Three setups: a startup
  distance of 1,000 bytes (the restart reads top nodes above the boundary
  from the stream, asserted); 100,000 bytes (the restart's rerun makes them
  again); and 1,000 bytes with every evictable object evicted after every
  transaction and the audit on (lookups load top nodes). Every historical
  value before and after the restart, the super root kept, and the next top
  node one more.
* `testEndOfOrdinals`: up to `LAST_TOP_ORDINAL`; two transactions refused,
  the super root, the values and the history unchanged, no node in the
  writer's list; the same after a restart; an internal transaction is not
  refused.
* `testOrdinalsWithReclaim`: reclaim with a retention of one second on a
  `CutStream` (a read below the cut throws), node size 8, one hot key and one
  written once, a restart every 150 transactions, both keys checked at every
  transaction's time from the first available time after each restart:
  across 2^32 (from 400 below to 300 above) and to the end (from 400 below
  `LAST_TOP_ORDINAL`). The front of the stream, with the first two top nodes,
  is cut (asserted); at the end the user transactions are refused and the
  super root stays within five of `LAST_TOP_ORDINAL`.
* `StoredTopNode.testOrdinalField` (new: the field's bytes, and below 2^30
  those of the old int); from 002-02's patch, `testOrdinalsRoundTrip` and
  `testParserRefusesSlotsThatDoNotFit` up to 2^48 − 1, and
  `TopNode.testHeight2`.

Each part of the fix has a test that fails without it, checked in a copy: the
old 32-bit parser fails 4 tests, the old bound 6, no guard 2, the guard on
internal transactions too 1. The three new tests take about 0.5 s together.

**The Lean model and the checker.** No change needed, by reading. In the
model, ordinals are levels, natural numbers (`Spec.topLevel`;
level2-alignment.md, 8.4). The checker reads every number of a trace with
`String.toNat?`, takes a top node's ordinal as its level minus `topLevel`
(C-S's layout in `Check/Steps.lean`, R4's chain in `Check/R4.lean`), and uses
`Nat.testBit`, division and `log2` on it: no 32-bit value and no bound. The
exporter computed levels as longs already; one local was an int. The root's
level, `keyMax + 2 + MAX_TOP_NODE_ID_VALUE`, is now about 2^48 in every
trace (level2-alignment.md, 8.4); the checker only compares levels, and the
gates' conformance steps check traces with it. A trace with ordinals above
2^30 needs that many root changes in one run:
the checker counts ordinals from the trace's first top node, so the test
option does not make one (the checker would see the jump as a layout
fault).

**Evidence.**

* StreamDigest `all` against R8's digests (`java/build/digest/r8-c4.txt`):
  `DIGESTS IDENTICAL (36 of 36)`. No record changes.
* The four gates, full, one after the other, in the scratch copy (its
  `level1.sh` with the uncommitted step 6 of 006-02, Props): `LEVEL 1 OK`
  (165 s), `LEVEL 2 OK` (793 s; conformance 60 of 60 traces `TRACECHECK
  OK`), `LEVEL 4 OK` (932 s; 30 of 30 with eviction); `level3.sh` failed in
  its unit tests on a test that fails on today's code too (below), and passed
  when run again: `LEVEL 3 OK` (507 s; 25 of 25 traces with cuts). Unit
  tests: 947 of 947 in each of the other runs, four of them new.
* MEM 227 bytes per KV (`level1.sh`'s limit 228; 226 to 227 before, 006-02),
  SS 1.50 (at most 1.51): the wider field of a top node does not show, as a
  database makes few top nodes per KV.

**Done when**, point by point:

* Crossing 2^30, 2^31, 2^32 and close to 2^48 with restarts and reclaim,
  every historical lookup right: the three tests (the crossing at 2^47; the
  end, 2^48 − 1,025, with restarts and with reclaim).
* The guard refuses cleanly at the end and the database restarts:
  `testEndOfOrdinals` and `testOrdinalsWithReclaim`.
* No stream changes below 2^30: StreamDigest, above, and `testOrdinalField`.
* The four gates: above.
* M46 closed in docs/level4-alignment.md (its row and section 6.4), item 002
  closed. Also docs/levels.md ("Bugs found by the alignment of Levels 3 and
  4", 2), docs/level2-alignment.md (8.4) and docs/log.md.

Not part of this: the height decrease (002-02, section 7) and 005-01. The
guard removes the bound from M49's triggers: no transaction reaches it now.

**Found on the way: a test that fails now and then.** The first `level3.sh`
run failed 1 of its 947 unit tests,
`EvictionReaderTester.testReaderPausedInsideAFollow`: "INV-CAN: the node
table names a snapshot of node 55735". It is not this change's. Repeated under load (four JVMs
per build beside four busy loops), the test failed once in 600 runs on
today's code (`0739170`), with the same message, and in none of 600 with the
change. A likely cause, from reading the code, not tested further:
`Cache3.pointerCreated` checks that the object is canonical outside the
table's lock and enters it under the lock, and a sweep's release (the flag
cleared, then `Cache3.released`) can come in between; the table then names a
released object, which INV-CAN forbids. The test opens that window: it
pauses a reader just before its step 4 (`NodeCollection.followStreamPointer`)
and lets it go after 500 ms, and a sweep slowed by load is still running
then. Readers and sweeps overlap like this outside tests too. Not M46's: it is
item 001's eviction (Q8). Registered as 005-09
([09-fix-node-table-snapshot-race.md](09-fix-node-table-snapshot-race.md)).
