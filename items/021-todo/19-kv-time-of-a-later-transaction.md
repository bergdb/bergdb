021-19. Fix: a KV's time is a later transaction's, not its write's
================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a KV's time in the Core API, `Kvt.time` (a `GetMany` result's) and
`GetData.kvTime` (a `getOne()`'s), is the time of a later transaction
that did not write the key, once that transaction has rewritten the key
node that holds it: T1 puts 27 keys of one byte, T2 a 28th, and all 27
read T2's time, also after a restart. `GetMany.result`'s Javadoc said
"the resulting KVs including the time it was last written to the DB";
the two fields had line comments only, which `javadoc` does not show.
The values and `GetData.tpos` are right, and `getTrans(tpos).tt` gives
the write's time. Found by a new-user application, 020-24-09, U9-3 (high
for Core users; 2.5 million wrong times in its last run); the
reproduction `ReproTime2` in `/Users/f/fl/bench/2026-11-09/app-u9/app/src/`.

Why: an application that keeps a change feed by `Kvt.time > T` gets keys
that did not change.

Frans: none for this entry. A format change is his; an exact time would
be one, so it is a question below, for his list, not blocking.

Done when: where the time comes from, and whether it was meant to be the
write's; a fix if it is small and keeps the stream format, else the
Javadoc of `Kvt.time` and `GetData.kvTime` saying exactly what they give
and how to get the write's time, and the design question for Frans here;
whether the Pub API or the indexes use the fields; `BEFORE COMMIT OK` and
`java/stress/level1.sh` under the gate lock; a line in `releases/next.md`.

First step: `KeyNode`'s searches and `Dag`'s splits.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-09's U9-3, and taken by
its agent c18b (clone `clone-c18b`, on main's 62345d3).

2026-11-09. Done by c18b: the commit "021-19: ..." in `clone-c18b`, on
021-18's, to land. Severity: high for Core users, as 020-24-09 gave it,
for the Javadoc; the behaviour is the 2017 baseline's, in 2026.1 to
2026.3.

* Where the time comes from. A key node's klongs are time klongs, each
  followed by the entries made at that time (`KeyNode`). A search takes
  as an entry's time the last time klong before it (`kwi.klongTime` in
  `searchEq`, `searchLte` and the others), which
  `Dag.getEqNodeInSegment` puts in `GetData.kvTime` and `GetMany.Chain`
  in `Kvt.time`. A transaction that finds a key node full
  (`Dag.handleFullNode`) replaces it by its last version
  (`KeyNode.lastVersion`, a time split) or by two halves
  (`firstAndSecond`, a space split), each with one time klong, the
  transaction's, before every live entry. So every entry that the node
  keeps gets that transaction's time, whichever keys it wrote. In
  ReproTime2, T2's put finds T1's node of 27 entries full (30 klongs by
  default) and splits it in space, as its last version is more than half
  full, and both halves are T2's. A read at a time before T2 goes through
  T1's node and gives T1's time. Reclaim's copy of a value is a new value
  node, its entry at the step's time.
* Was it meant to be the write's time? The 2017 code said so
  (`GetMany.result`'s Javadoc; the Pub API's `Kv.time()`), but the nodes
  never kept it. Since 2026-10-13 it is not: 011-01, Q9, answered by
  Frans, "there is no exact value time in the product"; the Pub API's
  `Kv.time()` and `Connection.time()` were removed, and `GetData.kvTime`
  and `Kvt.time` stayed, "marked inexact" (011-04, W3), by line comments
  only, while `GetMany.result`'s Javadoc kept "the time it was last
  written". Reclaim chose values by `kvTime` until that day and lost old
  values; it decides by `tpos` since (`Reclaim`'s comment). The Lean
  model has no time of a key, and `docs/levels.md` says nothing of it.
* A fix within today's stream format: none is small. A value node holds
  no time, and a key node's entries only the time klongs of their node.
  To give the write's time, a read would read the record's header at
  the value's `tpos`, a stream read per KV of a scan, also for a value in
  memory; or a split would keep each entry's time klong, which makes
  other bytes in the stream, other split points (more time klongs in a
  node) and other bytes for the C port, a change of the stream's bytes
  that is Frans's (018-01, section 2). So the Javadoc, as asked.
* Javadoc (no change of behaviour): `GetData.kvTime` (what the time is,
  why, its bounds: at or after the write's time, at or before the lookup
  time; two reads at lookup times before and after a split may differ;
  the write's time `Db.getTrans(tpos).tt`; Q9), `GetData.tpos` (the
  transaction that stored the value: for a reclaim copy, reclaim's step,
  whose time is the step's; a get at the step's time less one follows it
  back, as 021-17 does), `Kvt.time` (as `kvTime`; for a scan's KV, the
  `tpos` from a `getOne()` of its key at `GetMany.actualLookupTime`),
  `GetMany.result`, and `DbUtil.checksum`'s `includeKvTime`.
* Test: `DbTesterJavadoc.testKvTimeIsTheEntrysTime`, ReproTime2's case:
  the bounds, `getOne()`'s time equal to the scan's, `getTrans(tpos).tt`
  the write's, a read before T2 giving T1's time, and all 27 of T1's keys
  with T2's time. It passes on the code as it is, as the Javadoc tests of
  020-27; its last assertion fails if the time becomes the write's, so
  that the Javadoc changes with it.
* Users: no code of the Pub API or of the indexes reads either field
  (`java/src/bergdb/pubimp`: none; the Pub API's `transactionInfo()` reads
  `getTrans(tpos)`); reclaim uses `tpos`. `DbScan` and `DbUtil`'s
  checksums include `Kvt.time` when asked, in tests that compare two
  databases, where the times are the same in both. The C port's
  `bergdb.h` says already that its `time` is "the key node entry's time,
  not the write time".

For Frans, not blocking (his list, after the release). Options:

1. Keep it so (done now). The Javadoc says what the time is; the write's
   time is `getTrans(tpos).tt`, a read of the transaction's record, and
   for a scan's KV a `getOne()` before it. Nothing else changes.
2. Add `Kvt.tpos`, the value node's transaction, as `GetData.tpos` gives
   it: a new public field of the Core API, set at no cost (the value node
   has it); no format change. A scan's KV then leads to its transaction
   without a second get. The C port's `bergdb_kvt` to match.
3. An exact write time, Q9's "may come later": the write's time in the
   value node (a format change, 8 bytes or a varint per value, which
   reclaim copies), so that `Kvt.time` and `kvTime` give it and reclaim
   stays invisible. Costs stream bytes per value, and a new format in
   Java and C.
4. Rename or remove the two fields (`kvTime` to `entryTime`, say), as the
   Pub API removed `Kv.time()`, so that no user takes them for the
   write's time: an API change for Core users and the C port.

Recommendation: 1 for 2026.4; 2 when a Core user needs a change feed; 3
only together with another format change.

Runs, under the gate lock (2026-11-09), on the tree of 021-18 and 021-19:
`BEFORE COMMIT OK (142 s)` (16:16 to 16:18; unit 1579, f 86, demos);
`java/stress/level1.sh`: `LEVEL 1 OK` (ended 16:37; RestartInvariance
identical, MEM 129, SS 1.51).
