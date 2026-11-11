021-25. Investigate: reclaim stops cutting a FIFO of keys in time order
======================================================================

Status: done 2026-11-11: fixed by 023 in release 2026.4 (020-31,
section 4). Kind: Investigate. Frans: decision.
Created 2026-11-09 by Frans Lundberg.

What: a new user of the C library (022-06-3, U3-1 and U3-2; report and
reproductions `repro_fifo.c`, `repro_growth.c` in
`/Users/f/fl/bench/022/apps/u3/`) found that reclaim stops cutting under
an audit log keyed by time: one key per transaction, "/t/" and the time
in 16 hex digits, the key put 1,024 transactions back deleted in the same
transaction (a FIFO, 1,024 live keys of 80 to 479 bytes), startup
distance 2 MB, retain duration 20 s, a test clock of 1.5 ms per
transaction, 300,000 transactions. Reclaim cuts for a while, then no
more, and the directory grows; now and then a transaction of one put and
one delete writes a record of MBs. No data is lost and every read is
right. The C library writes Java's bytes, so the question was whether
Java does the same, and whether today's changes (2026-11-09) caused it.

Why: release 2026.4's candidate is cut tonight. A log with retention is
an ordinary use, and the directory then grows without a bound.

Frans: decision. Not a regression, and not fixed here: what to do about
it for 2026.4 (a fix in reclaim, or the known issue that
`releases/next.md` now has), see "Cause" and "For Frans".

Done when: Java's behaviour is known on main and on 2026.3, the cause is
named with its places in the code, and Frans has decided.

First step: the workload in Java against the Core API.


Method
------

`ReclaimFifo.java` (in `/Users/f/fl/bench/2026-11-09/g30/`, not in the
repo): repro_fifo.c's workload against `bergdb.core.Db`, with
`Db.builder().mainStream(new FileStream(dir)).clock(clk)
.startupDistance(2000000)`, a `TestClock` advanced 15,000 units (1.5 ms)
before each transaction from T0 = 17626464000000000, the keys by
`Trans.Builder.put(String, byte[])` and `delete(String)` (Keys.toBytes,
as the C library's `bergdb_ikey_to_bkey`), the same values, and
`setRetainDuration(20 s)` at transaction 1,000. It measures, per
transaction, the record's size (`nextPos - tpos`) and the changes of
`getFirstAvailablePos()` (the cuts), and every 5,000 transactions the
first available time against the clock, `getReclaimIterationCount()`,
the stream's length and the directory's bytes. With `ROWS=1` it prints
reclaim's table, and with `STATS=1` `Reclaim.Stats` (by reflection). A
fresh database for each run, created by the jar under test, so no 2026.3
database is involved. One JVM at a time on F53; a run of 300,000
transactions takes 12 to 19 s.

Main at a2fa9df (clone `clone-g30`) and release 2026.3 (tag
`release-2026.3`, 929fa33, worktree `clone-g30-263`), each built with
`java/build.sh`.


Findings
--------

**Not a regression.** Main and 2026.3 give the same run, byte for byte:
the same stream length at the end, 226,557,072 bytes on both.

| Run                  | Iterations | Cuts | Last cut   | First avail. | Dir    | > 1 MB | Largest |
|---|---|---|---|---|---|---|---|
| main, 300,000        | 16         | 15   | 190-195 k  | 182.2 s back | 135 MB | 20     | 4.17 MB |
| 2026.3, 300,000      | 16         | 15   | 190-195 k  | 182.2 s back | 136 MB | 20     | 4.17 MB |
| main, hashed keys    | 16         | 14   | 255-260 k  | 80.2 s back  | 349 MB | 0      | 435 KB  |

(Iterations: completed; first available: at the end, against the clock;
a 20 s retain duration. The C library: 16 cuts up to transaction 240,000;
022's cross run of the same workload, `bergdb.cross.Run` on main, gives
the C library's stream files exactly, the last cut between transactions
190,000 and 195,000 and the 4.17 MB record at 180,041.)

The first available time stays within 20 to 58 s of the clock up to the
last cut, between transactions 190,000 and 195,000, then falls behind by
7.5 s per 5,000 transactions: 92 s at 240,000, 182 s at 300,000. The
directory grows from 55 MB at 200,000 to 135 MB at 300,000, for 300 KB of
live data. Records over 1 MB come in two runs: from transaction 45,559,
about one per iteration, growing from 1.07 MB to 4.17 MB at 180,041 (part
1 below); then from 222,868, every 4,000 to 14,000 transactions, growing
from 1.0 MB to 3.13 MB at 295,719 (part 2). They are user transactions'
records: up to transaction 240,000 reclaim's steps wrote 3.1 MB of
records in all.

With the time hashed in the key (`KEYS=hashed`), reclaim still cuts, but
the stream grows by 1.6 KB per transaction at 20,000 to 60,000 and 2.7 KB
at 240,000 to 280,000 (the time-ordered run: 0.75 KB throughout), and the
directory reaches 349 MB.


Cause
-----

Two parts. Places in main (a2fa9df); the same code is in 2026.3, from
2026-10-13 (bergdb 011-04, level 3).

1. **The index keeps nodes of deleted keys.** A FIFO of keys in time order
   leaves every deleted key below the live ones, and the index keeps index
   nodes there that hold deleted keys only (a time split drops deleted
   klongs, as far as `KeyNode` was read here, but not every node or
   segment subtree whose keys are all deleted, which is not checked
   further; Reclaim's class comment, "Nodes that hold deleted keys only,
   and the segment subtrees of deleted long keys", Q7 of 011-01). Their
   number grows with the deletes, about one node per 10 deleted keys: the
   first step of the 17th iteration (begun at transaction 178,500) scanned
   20,642 index nodes to find its 4 KVs (`Reclaim.Stats`, `maxStepNodes`;
   the scan in `Reclaim.step()`, Reclaim.java:557, from `it.lastKey` =
   null at time tStart, stopped by the step reserve at line 568), and its
   touch made 17,493 nodes dirty, 4.17 MB. The first steps of earlier
   iterations made dirty 1,243 nodes (the iteration begun at transaction
   15,000), 5,752 (57,400), 9,781 (97,300) and 14,043 (131,700). Those
   dirty nodes are written by the next user transactions that take dirty
   nodes: the records of MBs (U3-2).

2. **The touch of each step runs on to the next live key, past every key
   deleted since the iteration began.** `Db.touchRange()` (Db.java:2944)
   is a scan at the transaction's time from `touchFrom` (Reclaim.java:675,
   the last key of the step before) whose stop condition (Db.java:2979) is
   called for live KVs only: it stops at the first live key after
   `touchTo`. Under the FIFO the keys of the step, live at tStart, are
   deleted by the time of the step, and the next live key is the newest
   window; so every step touches all the nodes of the keys deleted since
   tStart. The step's dirtied bytes count in the iteration's `rewritten`
   (Reclaim.java:656), and the next step waits until the stream has grown
   by 4 times `rewritten` (the internal fraction 0.25, line 472). In the
   17th iteration the steps between transactions 200,000 and 220,000
   dirtied about 3,150 nodes (750 KB) each for 26 KVs, and those between
   220,000 and 240,000 about 5,500, written by the user records of 1 to 3
   MB. That is about one node per 10 keys deleted since tStart, as in part
   1: some 3,100 at 210,000 and 5,000 at 230,000. The later a step, the
   larger its touch, and the rarer the steps. The 17th iteration, begun at
   transaction 178,500, had covered 273 of its 1,027 KVs at 240,000 and
   323 at 260,000. No new iteration starts while it runs
   (Reclaim.java:460), and only a finished iteration can be cut, so the
   cuts stop (U3-1). While the history is short, an iteration finishes in
   time and the cuts keep up, which is why 60,000 transactions cut as
   expected.

3. **Every transaction afterwards pays for the largest touch.**
   `Db.touchRange()` follows the nodes with the transaction's
   `x.putData.pointerListener` (Db.java:2947), which appends every key
   node followed to `PutData.keyAccessPath` (Dag.newPutData(),
   Dag.java:303 and 307), and its arrays grow and never shrink
   (KeyAccessPath.add, enlargeArrays). `PutData.clear()`, at the end of
   every transaction (Db.putKvs), calls `KeyAccessPath.clear()`
   (KeyAccessPath.java:29), which nulls the whole array, not the `size`
   used. In the FIFO the array grew to 4,356 entries at transaction
   30,000, 17,840 at 120,000 and 28,544 from 180,000 on, so from then
   every transaction of one put and one delete cleared 28,544 references.
   A writer's cost per transaction, not a change of the stream. The same
   code in 2026.3.

With hashed keys the deleted keys lie among the live ones, so part 2 has
little to pass, but part 1 makes every write dearer as the deletes add up.

022-06-3's report has the same in the C library's own index counts
(probe_dag.c: 22,134 key nodes for 1,024 live keys after 80,000
transactions).

App u14's finding (2026-11-09: user indexes created and deleted again and
again, a retain duration of 2 s; puts in another directory slow down with
the cycles, from 155k/s to 6.3k/s, and reclaim stops cutting) is the same
mechanism, its put cost mostly part 3: `PutCost.java` (in
`/Users/f/fl/bench/2026-11-09/app-u14/app/`) changed to put 400,000 times
after 150 cycles ran 31,845 puts/s, and 6 of 10 stack samples of the
writer were in `KeyAccessPath.clear()` under `PutData.clear()`, none in a
touch; its stopped cuts are likely parts 1 and 2 (not checked).


For Frans
---------

* For tonight's candidate: no revert (nothing of today's is involved), a
  known issue in `releases/next.md` ("Known issues and limits", commit
  ef46ffb in `clone-g30`).
* A fix is three pieces of work in the Core: (a) end the touch at
  `touchTo`, not at the next live key, which needs a stop on the keys
  passed, not only on live KVs; (b) drop index nodes and segment subtrees
  that hold deleted keys only, so that the index of a key range shrinks
  after its deletes; (a) and (b) change what reclaim writes (the stream's
  bytes, so StreamDigest's digests and the C library's equality, 022). (a)
  alone would likely restore the cuts of this FIFO; (b) is what keeps the
  cost of deletes bounded, also with hashed keys and for u14. (c)
  `KeyAccessPath.clear()` nulls only what was used since the last clear (a
  high-water mark), or the touch does not record its path; no change of
  the stream, small, and likely much of u14's slowdown of puts (not
  tried).


Fix (c)
-------

Fix (c) only, by fixer k32 for coord-1109: the slowdown of puts of part
3. Parts 1 and 2, and so the cuts, are unchanged.

The change: `KeyAccessPath.clear()` nulls only the entries that `add()`
set since the last `clear()`, below a high-water mark, `used`, that
`add()` raises to `size` and `clear()` sets to 0. Entries left by
`clearFast()` before later, shorter adds lie below it, and an enlargement
copies only entries below it, so no key node reference outlives the
transaction, as before. The callers: `clear()` from `PutData.clear()`, at
the end of `Db.putKvs()`, and from `DagTester`; `clearFast()` from
`PutData.clearFast()`, after the touch and after each put
(`Db.putKvs()`), after each rerun put (`DbStarter`, on a `PutData` of its
own that it never clears) and in `DagTester`. Nothing else in the code
writes the arrays. The touch still records its path; the stream and
reclaim are as before.

The test: three Nano tests in `KeyAccessPath` (in the unit tests by its
`Pack`), `testClearNullsTheNodes`, `testClearAfterClearFast` and
`testClearAfterEnlargement`: after `clear()`, `size` is 0 and no entry of
the array holds a node, also after `clearFast()` and later, shorter or
longer adds, and after enlargements of the arrays (16 entries at first,
then 25, 40 and 64). They pass on the old `clear()` too, which nulled every
entry; they are there to keep the high-water mark right.

Measured on F53, loaded by other sessions (load 8 to 13), one JVM at a
time and one run each, with the jars of this clone before and after the
change (main's a2fa9df and the change), no `-ea`:

App u14's `PutCost` (`java PutCost DIR retain`: startup distance 5 MB,
retain duration 2 s; the rate of puts in `/w/` after K creations and
deletions of an index on `/c/`), puts per second:

| Cycles        | Before  | After   |
|---|---|---|
| 0             | 224,052 | 165,550 |
| 10            | 140,232 | 190,918 |
| 100           | 32,998  | 170,046 |
| 300           | 9,931   | 172,677 |
| 1,000         | 6,131   | 202,406 |
| after restart | 243,130 | 237,983 |

The rate no longer falls with the cycles; the spread among the after
figures, and at 0 cycles, where the change does nothing, is the noise of
the loaded machine.

The FIFO (`ReclaimFifo.java`, 300,000 transactions, in a copy that keeps
the directory when `KEEP` is set): 6.2 s before, 4.9 s after (its own wall
time at transaction 299,999). The run is the same: every line of the
output but the wall time and, before the end, the directory's bytes
(files written and deleted in the background; g30's runs differ there
too) is the same: the stream's length at every 5,000 transactions and
226,557,072 bytes at the end, the first available position, 15 cuts, 16
iterations, the 20 records over 1 MB and the largest, 4,170,176 bytes, and
the directory, 134,375,552 bytes, at the end. The 22 files left in the
directory (136,557,297 bytes) are the same names and sizes and equal byte
for byte but for 683 runs of 16 bytes, each at offset 24 of a 200,000-byte
block, one value in each run: the meta blocks' database id
(`Db.java:1364`), random for each new database. So the stream is
unchanged.

The FIFO's cuts still stop (parts 1 and 2), and so do u14's (not
measured here).



The note for the tag (draft, 19:58)
-----------------------------------

Round 6 of the new-user apps ran on the candidate (020-24-16 to 18). An ordinary
metrics store met this fault within an hour of simulated time (020-24-18, U18-1):
50 sensors, one sample a second, the samples deleted after 15 minutes, a retain
duration of 20 minutes. Reclaim made one cut, at about 3,300 transactions of 100
keys, then no more. At 12 hours the directory was 1,188 MB for 1.8 MB of live data,
and records grew to 149 MB. The number of deleted keys sets when it starts, not
the number of transactions. A ring of keys overwritten in place, with no deletes,
stayed bounded.

U18-2 found that the note in `releases/next.md` (69600f9) does not let a user
recognise the fault. A draft to replace it before the tag, if 2026.4 ships without
fix (a):

> **Reclaim can stop cutting when many keys are deleted.** With a retain duration
> set, an application that deletes many keys can make reclaim stop cutting after a
> few thousand transactions. Examples are a log or time series that deletes its old
> entries, a queue, and frequent index creation and deletion. The directory then
> grows far beyond what the retention needs: in one test, 1.2 GB for 1.8 MB of live
> data after 12 hours. Some transactions then write records of tens of MB and take
> seconds. The number of deleted keys matters, not the number of transactions. No
> data is lost and every read is right. The sign: the current time minus
> `getFirstAvailableLookupTime()` grows far beyond the retain duration. A
> workaround: overwrite a fixed set of keys, such as a ring of time slots, instead of
> deleting old keys. The same in 2026.3; bergdb 021-25.

Reads have a related cost from deleted keys (020-24-16, U16-1; 020-24-17, U17-1). A
scan over a range from which many keys have been deleted, or past the end of a range
followed by deleted keys, gets slower, also after a restart. An index built again is
fast. Investigator q34 looks at a fix on the read path (branch `scan-deleted-keys`).


Log
---

2026-11-09. Registered by coord-1109 from 022-06-3's U3-1 and U3-2; taken
by investigator g30 (clone `clone-g30` on main's a2fa9df, and a worktree
of `release-2026.3`). The Java workload reproduces the C library's run on
main and on 2026.3 alike: not a regression. Cause found (parts 1 and 2
above) from reclaim's table and statistics; no fix made. A known issue in
`releases/next.md` (ef46ffb).

2026-11-09. Part 3 (the key access path that every transaction clears)
from u14's put cost (coord-1109: is u14 the same?): stack samples of
`PutCost.java` changed to a long put phase, and the array's length in the
FIFO. Investigation ended; the item stays for Frans's decision.

2026-11-09. Fix (c) by fixer k32 (clone `clone-k32` on g30's 4daeff8):
`KeyAccessPath.clear()` with a high-water mark, three Nano tests, u14's
`PutCost` and the FIFO before and after (section "Fix (c)"); the stream
unchanged. A line in `releases/next.md`. The item stays for Frans's
decision on (a) and (b).

2026-11-09. Status "waiting" (for Frans's decision), one of 021's
status values, where it said "for Frans"; the main commits of the
item: `69600f9` (the known issue), `c6e60ba` (part 3) and `e3b9787` (fix
(c)); its row in 021-todo. By coord-1109.

2026-11-09. Frans, 19:17: "021-25, good catch. Yes it should be for 2026.5." The fixes (a) and (b) wait for 2026.5; fix (c) is in 2026.4 (coord-1109).

2026-11-09. Section "The note for the tag": round 6's evidence (U18-1, U18-2, U16-1, U17-1)
and a draft of the known issue to replace before the tag; p33 prototypes fix (a) on a branch (coord-1109).

2026-11-09. Fix (a), a prototype by p33 (branch `021-25-fix-a`, 50ef43ff, in clone-p33; its section "Fix (a), a prototype" there): the cuts go on in the FIFO (20 cuts, the first available time 20 to 62 s back, 80 MB against 134 MB) but the database is not bounded: part 1 stays (an iteration's first step touches every deleted key's node, records up to 7.27 MB), and u18's metrics store gets 4 cuts in 5 h and 446 MB against 517 MB. Every database with a retain duration writes other bytes (StreamDigest, the C port). Gate, level1, level3 and level4 quick OK. Coordinator's recommendation: not into 2026.4; (a) with (b) in 2026.5, and the note of section "The note for the tag" before the tag (coord-1109).
