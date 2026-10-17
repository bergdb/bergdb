002-02. Report: the top node ordinal bound
==========================================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-17, at Frans's request:
"Investigate this, use subitem 02 for the report", with six questions (the summary below
answers them in order). Code at bergdb `059dbf1` and, for the final checks, `5b1abdd`
(item 001's commits during the work). All runs used copies of `java/` outside the
repository, at low priority, on a machine busy with item 001's runs; nothing in bergdb
was changed but this item. The probes, the patch and their outputs are in
[02-report/](02-report/) (section 10). The sources are in [01-sources.md](01-sources.md).


## Summary

1. **Is the current solution good enough? No, not for Levels 3 and 4.** Today no
   database reaches the bound: the heap keeps all history (about 250 bytes per
   transaction for a hot key), so a 32 GB heap is full after about 2^23 top nodes, 128
   times fewer than the bound. Level 4 makes the heap a cache (eviction on by default,
   item 001, Q10), and then the bound is the lifetime of a hot database. And what Java
   does at the bound is the worst kind of failure: the transaction fails in the middle
   of a root split, every later root change fails, a reader can see a value that was
   never stored, the next transaction stores the failed one's values, and once one more
   transaction has committed, the database cannot be started again (section 2).
2. **When is it reached?** Each change of the space root makes a top node, at most one
   per transaction. One hot key changes the root every 15 transactions at node size 30
   (14 with reclaim on), every 4 at node size 8 (3 with reclaim on). Databases with
   1,000 keys or more and spread updates change it every few hundred to thousands of
   transactions (section 3).
3. **A realistic scenario? Yes.** A small database with a few hot keys (counters,
   leases, last-seen times, the head of a queue) at 1,000 transactions per second
   reaches the bound in about six months at node size 30, five to seven weeks at node
   size 8. A benchmark or a soak at full speed on one key reaches it in 15 to 29 hours.
   Databases of 100,000 keys or more with spread updates take centuries at that rate
   (section 4).
4. **Widening `topNodeId` to a long is easy.** The field in the stream already has 48
   bits (bytes 10 to 15 of a top node); the reader reads 32 of them. The change is 7
   files, 55 lines added and 32 removed, tests included, and no format change: the same
   stream bytes for every ordinal below 2^30 (33 of 33 stream digests identical), and
   today's code refuses, with an error, every stream with a larger ordinal. The unit
   tests, level1.sh and level3.sh pass, and so does level2.sh's quick run (the full one
   was not run). Databases crossed 2^30, 2^31, 2^32 and 2^47 with restarts, every
   historical lookup right (section 5).
5. **48 bits.** That is the field that exists. At the fastest rate of top nodes
   measured (19,400 per second) it lasts 460 years, past the end of the database clock
   (100 ns units in 56 bits: May 2198). A guard just below 2^48 refuses user
   transactions before they change anything, so even the end is clean (section 6).
6. **The 2012 height decrease** is safe: dropping the skip slots older than the cut
   changes no search from the first available time on (argued, and checked on 383,263
   searches). It saves bytes: top nodes are 11 to 33 percent of a hot key's stream
   today, and near ordinal 2^30 dropping those slots would save 6 to 19 percent of the
   bytes written. It does not lift the bound. It costs a format change, a weaker parser
   check, a coupling of top node construction to reclaim (also in the startup's rerun),
   and changes to the model, the proofs and the checker. Not now. If top node bytes
   matter later, storing only the slots at set bits saves about as much, with none of
   the coupling (section 7).

Found on the way (section 8): **a transaction that throws in the middle of its puts is
half committed.** A failing value transformation shows it without the bound. It is a
separate defect, worth its own register row.

Recommendations (section 9): widen to 48 bits with the guard, using the patch in
02-report/, before eviction is on by default, or now; register the exception defect;
leave the height decrease.


## 1. The bound

* Each new super root gets the previous ordinal plus one (`TopDs.newSuperRoot`); the
  first top node has ordinal 0. A second root change in the same transaction updates
  that transaction's top node in place, so a transaction makes at most one top node.
* The ordinal is an `int`, and `TopNode.height` throws `IllegalStateException("Bad id
  value")` above `MAX_TOP_NODE_ID_VALUE`, 2^30 − 1 (`MAX_HEIGHT` 30). So a database makes
  at most 2^30 = 1,073,741,824 top nodes in its life. A restart continues the ordinals;
  BergDB has no tool that copies a database into a new one; a replica has the same
  ordinals.
* The stored top node (format version 2): bytes 8 to 15 are one little-endian long,
  with the slot count in byte 8, a zero in byte 9, and the ordinal in bytes 10 to 15,
  48 bits. The writer has written all 48 bits since item 001's A3; the reader reads
  bytes 10 to 13 as an `int` and skips 14 and 15 ("2 zero bytes").
* History ([01-sources.md](01-sources.md), section 4): the 2012 design expected few top
  nodes ("We will never see a height about 12, I believe"). The code of 2013 already had
  `MAX_HEIGHT = 30`, without a check; the check came in 2014 (`2c6ceb5`). Until
  2026-10-16, the codec defect (M30, fixed in A3) made the real limit 32,768 top nodes.


## 2. Is the current solution good enough?

### 2.1 Today the heap runs out first

Levels 1 to 3 keep every version in the heap (docs/levels.md, "Memory"; M26: nothing
is released). Measured with `M46Heap` (one hot key, the stream's own bytes subtracted):
251 bytes of heap per transaction at node size 30 (1,000,000 transactions), 439 at node
size 8. A 32 GB heap is full after about 1.3 · 10^8 transactions, 8.5 million top
nodes (2^23); 2^30 top nodes would need about 4 TB. Reclaim bounds the stream, not the
heap. So today a database runs out of memory 128 times before it could reach the bound.

### 2.2 With Level 4, the bound is the lifetime

Level 4 makes the heap a cache, and item 001 turns eviction on by default (Q10). Then a
database with reclaim can run indefinitely, and the ordinal is the counter that runs out
first, by far. The others: stream positions and node ids are longs (2^63 bytes: 290
years at a gigabyte per second), and times have 56 bits of 100 ns (until May 2198).

### 2.3 What Java does at the bound

`M46Bound`, on today's code, with a scratch hook that starts the ordinals near the bound
(`-Dm46.firstTop`, [probe-hook-int.patch](02-report/probe-hook-int.patch)); in-memory
database, node size 30; with and without assertions unless noted.

| Probe | What happened |
|---|---|
| One hot key | Transaction 149 throws `IllegalStateException: Bad id value: 1073741824`, from `TopNode.height` in `TopDs.newSuperRoot` in `Dag.timeSplit`. Every later write fails, with the same exception; with assertions, with `AssertionError: two canonical objects for node 14179`, since the failed transaction's new node stays registered and the next transaction reuses its id. A restart works; the first root change fails again. |
| /a and /b in one transaction, where /a fits in the root and /b splits it | The transaction throws, but /a's new value stays in the old root at the transaction's time. A reader sees `/a = A130`, which was never stored; after a restart, `/a = A117`, the last committed value. |
| 1,000 keys, one put per transaction | The first failure at transaction 1,443. The next committed transaction stores the failed one's value with its own (its record holds `v1443 v1444`). From then on the stream cannot be started: the startup's rerun replays the failed put, which reaches the bound again (`restart FAILED: Bad id value: 1073741824`). Restarted right after the failure, before another commit, the database starts. Without assertions, the share of failing writes grows as more paths fill up to the root: of the 557 transactions from the first failure to transaction 2,000, 90 failed; of the next 2,000, 1,571; of the 2,000 after those, 1,992. The heap grew with the failures (5 MB at transaction 2,000, 82 MB at 4,000), and a run with a 1 GB heap ran out of memory before transaction 6,000. |

So reaching the bound does not stop the database cleanly. It degrades it, and one more
commit after a failure makes it impossible to start with this code. The mechanism is the
defect of section 8, triggered over and over.

### 2.4 Verdict

Not urgent today, but not good enough. Under Level 4 the bound is reachable by plausible
workloads (section 4), and reaching it breaks the database. The fix is small and needs no
format change (section 5), so it belongs before eviction is on by default; since it costs
little, it can also be done now.

A clean refusal at 2^30 alone (one of M46's two options) would avoid the damage but make
the database read-only after 2^30 root changes, the lifetimes of section 4. Leaving that
state would need a copy into a new database, for which BergDB has no tool.


## 3. When the bound is reached

A new top node comes with every time split or space split of the space root
(`Dag.spaceSplitInPlace`, `timeSplit` and `spaceSplit` call `TopDs.newSuperRoot`). With
one or a few keys the root is also the leaf: each transaction appends a time klong and a
key klong to it, so a root of node size s is full after about s/2 transactions, and a
time split replaces it. With many keys, the root fills only from the splits of its
children.

Transactions per new top node, measured with `M46Rate` (200,000 to 500,000 transactions
after a warm-up), and from review-13-claude's `TopNodeRate` where marked:

| Workload | Node size | Transactions per top node | With reclaim on |
|---|---|---|---|
| One hot key | 8 | 4.00 | 3.00 |
| One hot key | 14 | 7.00 | |
| One hot key | 30 | 15.00 | 14.00 |
| One hot key | 62 | 31.00 | |
| 10 keys, one put per transaction | 30 | 10.00 | 9.98 |
| 1,000 keys, one put per transaction | 30 | 965 | 654 |
| 1,000 keys, ten puts per transaction | 30 | 149 (review) | |
| 100,000 keys, one put per transaction | 30 | 7,143 (review) | |
| New keys appended | 30 | no new top node in 50,000 (review) | |

"Reclaim on": a retention of 1 s, a startup distance of 100 KB and 10 ms between
transactions, so that reclaim cut the stream many times in the run. Its own transactions
change the root too: up to 48 percent more top nodes (7 percent for one key at node size
30).

Throughput, same probe, one writer, in memory, at low priority on the loaded machine:
153,000 transactions per second for one key at node size 30, 122,000 at 14, 78,000 at 8,
126,000 for 10 keys. (LoadTest measured 100,000 to 155,000 single-put transactions per
second on disk; docs/levels.md.) So the fastest rate of new top nodes measured is about
19,400 per second (one key, node size 8).

Time to 2^30 top nodes ([numbers.py](02-report/numbers.py); its output is in
[outputs.txt](02-report/outputs.txt)):

| Workload | 10 tx/s | 100 tx/s | 1,000 tx/s | 10,000 tx/s | 100,000 tx/s |
|---|---|---|---|---|---|
| One hot key, node size 30 | 51 years | 5 years | 186 days | 19 days | 45 hours |
| The same, reclaim on | 48 years | 5 years | 174 days | 17 days | 42 hours |
| 10 keys, node size 30 | 34 years | 3 years | 124 days | 12 days | 30 hours |
| One hot key, node size 8 | 14 years | 497 days | 50 days | 5 days | 12 hours |
| The same, reclaim on | 10 years | 373 days | 37 days | 4 days | 9 hours |
| 1,000 keys, node size 30, reclaim on | 2,225 years | 223 years | 22 years | 2 years | 81 days |
| 100,000 keys, node size 30 | 24,000 years | 2,430 years | 243 years | 24 years | 2 years |

At full speed: 29 hours for one key at node size 30, 15 hours at node size 8, 24 hours
for 10 keys.


## 4. Realistic scenarios

* **Hot state.** A service that keeps a few hot keys in BergDB, updated per request:
  rate-limiter counters, a sequence number, a lease renewed by a leader, last-seen
  times, the head of a queue, the state of a few sessions. At 1,000 transactions per
  second: 124 to 186 days at node size 30, 37 to 50 days at node size 8. At 100 per
  second: 3 to 5 years, or one to one and a half years at node size 8. With reclaim and
  eviction, such a database is meant to run for years.
* **Benchmarks, load tests and soaks** at full speed on one or a few keys: 15 to 30
  hours.
* **Large databases** with updates spread over many keys: decades to centuries. Only a
  sustained rate near the maximum (100,000 transactions per second on 100,000 keys)
  gets there in about two years.
* **Not affected**: workloads that mostly append new keys (few root changes), and
  databases recreated from scratch now and then.

So a database built to run for years, which is what reclaim and eviction are for, with
a hot set and a high rate will meet the bound.


## 5. Widening `topNodeId` to a long

### 5.1 The change

[widen-48.patch](02-report/widen-48.patch), against `5b1abdd` (`git apply --check`
passes on the repository at that commit):

* `TopNode`: `long topNodeId`; the constructor, `createDummy` and `getTopNodeId` take or
  return a long; `MAX_HEIGHT` 48; `power2` returns `1L << x`; `MAX_TOP_NODE_ID_VALUE`,
  2^48 − 1, a long; `height(long)`. The test of the height covers 2^30, 2^32, 2^47, the
  bound, and the refusal above it.
* `TopDs.newSuperRoot`: the ordinal is a long.
* `StoredTopNode`: `parse` reads bytes 10 to 15 as an unsigned 48-bit number; the slot
  check uses `1L << i`; `toLongs` writes the long shifted by 16, the same bytes as before
  for every ordinal below 2^30. The round trip test covers 2^30 − 1 to 2^48 − 2 (2^30,
  2^31, 2^32, 2^32 + 5, 2^40, 2^47), and the parser test writes a six-byte ordinal.
* `TransNodes`: an assertion compares longs.
* `Db.executeInner`: the guard of 5.5.
* `DbTesterRestart` and `stress/TraceExport`: one local variable each.

Nothing else needed a change: `src`, `src-dev` and `stress` compile. `DagChecksum` already
hashes the ordinal as a long, and `Db`'s choice of the newest written top node compares
ordinals. The patch keeps the parser's checks for a negative ordinal and for one above
the bound, which can no longer fail; the real change may drop them.

The Lean model and the checker need no change: ordinals are natural numbers there
(`n.testBit j` in C-S, levels in `Check/R4.lean`), and traces print them as decimal
numbers. One textual difference: TraceExport gives an object it cannot see the level
`keyMax + 2 + MAX_TOP_NODE_ID_VALUE`, which now grows with the bound; the checker uses
levels only to order nodes.

### 5.2 The serialization: no format change

* **Writer.** The same bytes as today for every ordinal that today's code can make.
  StreamDigest's quick set gave 33 of 33 identical digests, at `059dbf1` and again at
  `5b1abdd`.
* **Reader.** It reads every stream that today's reader reads, the same way: no writer,
  old or new, has put anything but zeros in bytes 14 and 15 of a top node that today's
  reader accepts. It refuses, as today, the streams the codec defect of M30 wrote (they
  fail the slot checks).
* **Older code on new streams.** Today's reader refuses every top node with an ordinal
  of 2^30 or more, with one of its existing checks, never with a wrong reading. Shown on
  streams written by the prototype ([outputs.txt](02-report/outputs.txt), "readers"):

  | First ordinal of the stream | Today's code | Prototype |
  |---|---|---|
  | 1,000 | starts, `/hot = v599` | starts, `/hot = v599` |
  | 2^30 + 3 | refused: "TopNode ID too large in stream, 1073741827" | starts |
  | 2^31 + 3 | refused: "Bad TopNode ID of TopNode in stream, -2147483645" | starts |
  | 2^32 + 3 | refused: "TopNode at 160 with ordinal 3 has 33 skip pointers, not 2." | starts |
  | 2^40 + 3 | refused: "TopNode at 160 with ordinal 3 has 41 skip pointers, not 2." | starts |

  The last two rest on A3's check that the slot count equals the ordinal's height.

So the top node format stays version 2. A new version would make older code refuse every
new stream, also those that never pass 2^30, and gain nothing. The comment in
`StoredTopNode` documents the field; `stream-format.txt` leaves top nodes to that class.

### 5.3 What grows past 2^30

* **Top node size** grows with the bit length of the ordinal: 520 bytes at height 30,
  536 at 31, 680 at 40, 808 at 48 (40 + 16 per slot), and three arrays of that length in
  memory. Only after 2^30 root changes.
* **Hops.** A search follows at most the bit length of the head's ordinal
  (review-13-claude, 4.3): up to 48 instead of 30. Recent queries stay short: sampled
  from heads of 21 to 48 bits, a query within the last 2^w top nodes followed at most w
  of them ([hops_window.py](02-report/hops_window.py)).
* **Run time**: a long instead of an int in a few places; not measured.

### 5.4 The evidence

* Unit tests: 918 of 918 on the patched `5b1abdd`. On the patched `059dbf1` (with the
  probe hook, inactive), 917 of 917 in 6 of 7 runs; the other run, on the loaded
  machine, failed one test, which the output I kept does not name, and it did not recur.
  The unpatched `059dbf1` passed 5 of 5 runs. Item 001 also notes a test that fails now
  and then under load.
* The gates, on the patched `5b1abdd`, in a scratch copy: `LEVEL 1 OK` and `LEVEL 3 OK`
  (full runs). level2.sh quick passed its steps 1 to 6 and the Java half of step 7
  (A2A3Check2), then stopped at `lake build`, since the copy has no `lean/`; its
  conformance check, run with a copy of the checker built in the repository (14:49),
  gave `CONFORMANCE OK`, 12 of 12 traces. The full level2.sh was not run.
* StreamDigest, quick set: identical (5.2).
* `M46Wide cross` (prototype with the hook of
  [probe-hook-long.patch](02-report/probe-hook-long.patch)): one hot key from first
  ordinals 2^30 − 20, 2^31 − 20, 2^32 − 20 and 2^47 − 20, 600 transactions each, across
  the boundary, with startup distances of 1,000 bytes (top nodes written, and read back
  from the stream at the restart) and 100,000 (all rerun): before and after a restart,
  0 of 600 historical lookups wrong, and the next top node continues the ordinals (for
  example 4,294,967,317 after 4,294,967,316).
* Readers (5.2) and the guard (5.5).

### 5.5 The guard at the end

With 48 bits the bound is not reached, but Java should still end cleanly. The patch
refuses a user transaction before it changes anything when the super root's ordinal is
within 1,024 of the bound: `DbException: The database has used its top node ordinals (up
to 281474976709631); it takes no more transactions.` Reads go on, and restarts work and
keep refusing. Internal transactions are not refused: reclaim runs its steps from inside
a user's `execute`, after that transaction is stored, so a refusal there would reach a
caller whose transaction committed; the margin of 1,024 is their room, and
`TopNode.height` still throws above the bound itself. `M46Wide end` (first ordinal
2^48 − 1,030): refused at transaction 75, no nodes left behind, the last committed value
read, 75 of 75 historical lookups right before and after a restart, and the transaction
after the restart refused.


## 6. How many bits: 48

1. **The field exists.** Bytes 10 to 15: no format change, and old code refuses new
   streams cleanly (5.2).
2. **It outlasts the rest of the database.** At the fastest rate of top nodes measured
   (19,400 per second: one key, node size 8, full speed), 2^48 lasts 460 years; at node
   size 30, 870 years. With reclaim's own root changes on top (a third more at node size
   8) at the same throughput, 26,000 per second, it lasts 340 years. Transactions with
   many puts make fewer top nodes per transaction, not more (4 keys in every transaction
   at node size 8: one top node per 12 transactions). The database clock ends in May
   2198 (2^56 − 1 units of 100 ns since 1970), 172 years from now. To use 2^48 before
   then, a database would have to make 52,000 top nodes per second on average for all of
   that time, 2.7 times the fastest rate measured, and the guard would then end it
   cleanly.
3. **It costs nothing until used.** Heights above 30 come only after 2^30 root changes.
4. **More bits need a new format.** 56 bits, the clock's width, so that the ordinal
   could never run out before the time: byte 9 lies below the field, and moving the field
   would change every stream. 63 or 64 bits need another word. Neither buys anything over
   48 in practice.
5. **Fewer are not enough.** 32 bits (an unsigned int in bytes 10 to 13) give four times
   today's lifetime: about two years for one hot key at 1,000 transactions per second.


## 7. The 2012 idea: decreasing the height after a stream refresh

### 7.1 The idea

From `2012-05-TopDS.txt` (01-sources, section 4): "We could DECREASE the top node
height. When the pointer with the highest pointer id, has a right-most pointer that
points to a top node that is too old (spos is 'forgotten' because of stream refresh), we
can reduce the height. Simply by omitting the right-most pointer. Note, height reduction
is not essential." In today's terms: a top node made after a cut leaves out its skip
slots whose target is older than the oldest top node that reclaim keeps (the top node
live at the first available time f). Top nodes never change after their transaction, so
this applies only to new ones.

### 7.2 It is safe, and searches do not need it

A search for a time t from f on follows the highest slot whose cached time is at or
after t. A dropped slot names a top node created before the oldest kept one, whose time
is at most f, so the slot's cached time is before t, and the slot is never followed. The
final step follows the lowest slot, the predecessor n − 1, which a top node made after
the cut never drops. So every answer, and every path, is the same.
[height_decrease.py](02-report/height_decrease.py) checks it with Java's search on both
layouts: heads 1 to 400, cuts at windows from 1 to the head, every query time from the
oldest kept top node on: 383,263 searches, the same answers and the same hops.

This is also why searches do not need the idea: they never touch the slots below the cut
(the footprint lemma, review-13-claude 4.3). In 2012 the worry was pointers to forgotten
positions; today's search does not follow them, and they stay stream pointers that
nothing reads (M33, `NodeCollection.resolvePointers`).

### 7.3 What it would save

Bytes written. A stored top node has 40 bytes plus 16 per slot up to its height, set or
not. Measured with `M46Bytes` (startup distance 1 MB, 400,000 transactions, every top
node written once), at heights of 15 to 17:

| Workload | Top nodes, share of the stream | Bytes per transaction |
|---|---|---|
| One hot key, node size 30 | 11.5 % | 17.0 of 148.8 |
| 10 keys, node size 30 | 15.2 % | 26.6 of 174.8 |
| One hot key, node size 8 | 33.3 % | 71.8 of 215.4 |
| 1,000 keys, node size 30 | 0.3 % | 0.5 of 160.4 |

48 percent of the stored slots are unset (their bit of the ordinal is 0). The share grows
with the height, so with the age of the database. Average stored bytes per top node, by
the size of the ordinals (2^a means ordinals from 2^a to 2^(a+1)) and the number of top
nodes kept (the window), computed by height_decrease.py:

| Ordinals | Window | Today | Slots below the cut dropped | Only set slots stored | Both |
|---|---|---|---|---|---|
| 2^20 | 2^10 | 376 | 232 | 216 | 136 |
| 2^30 | 2^10 | 536 | 232 | 297 | 136 |
| 2^30 | 2^16 | 536 | 328 | 297 | 184 |
| 2^30 | 2^20 | 536 | 392 | 296 | 216 |
| 2^30 | 2^24 | 536 | 456 | 296 | 248 |
| 2^40 | 2^20 | 696 | 392 | 376 | 216 |
| 2^47 | 2^20 | 808 | 392 | 432 | 216 |

For one hot key at node size 30 with 1,000 transactions per second, a window of 2^16 top
nodes is 16 minutes of transactions and 2^20 is 4.4 hours. Near ordinal 2^30, in bytes
written per transaction:

| | Node size 30 (167.5 bytes per transaction) | Node size 8 (277.6) |
|---|---|---|
| Slots below the cut dropped, window 2^16 | −13.9 (8.3 %) | −52.0 (18.7 %) |
| The same, window 2^20 | −9.6 (5.7 %) | −36.0 (13.0 %) |
| Only set slots stored | −15.9 (9.5 %) | −59.8 (21.5 %) |
| Both, window 2^16 | −23.5 (14.0 %) | −88.0 (31.7 %) |

Besides bytes: no slot of a top node made after a cut would name a record below the cut.
That is tidier, but nothing needs it. Memory: with eviction, few top nodes are resident.

It does not lift the bound: the ordinal still counts every root change. Keeping 30 bits
by wrapping the ordinal around would need the height decrease and also a special case
where the ordinal wraps to 0: a top node with ordinal 0 has no slots, so no predecessor.

### 7.4 What it would cost

1. **A format change in effect.** A3's parser check (as many slots as the ordinal's
   height, set exactly at its set bits) must accept fewer slots, and today's code would
   refuse the new top nodes.
2. **Top node construction would depend on reclaim.** `TopDs.newSuperRoot` would need
   the ordinal of the oldest kept top node, from `Reclaim`. The startup's rerun makes top
   nodes again, and to make the same ones (restart invariance, T2) it would need
   reclaim's cut as of each rerun transaction, during the reconstruction, where Java
   today needs the first available time only after it (M32; level3-alignment.md, 4.1).
3. **The construction gets a third case.** The 2012 rule ("inherit slot k of the
   previous top node, or point to the previous top node") would make a slot that the
   previous top node dropped point to the previous top node; it must stay dropped.
4. **The layout would no longer follow from the ordinal.** The layout in the model, the
   proofs of review-13-claude (construction keeps the layout, R4, the search, the hop
   bound, the footprint), the checker's C-S and C-A, and TraceExport would all change.

### 7.5 Verdict

Not now. The saving is real but moderate, only for hot workloads, and it comes with a
coupling to reclaim that the restart arguments (T8, M32) would have to absorb. If top
node bytes ever matter, first store only the slots at set bits; the ordinal says which.
That saves about as much (45 percent of a top node near ordinal 2^30, against 15 to 39
percent for windows of 2^16 to 2^24 top nodes, 57 for 2^10), touches only
`StoredTopNode` (a new top node format version) and needs no state from reclaim. The
height decrease could come on top of it later.


## 8. Found on the way: a transaction that throws in the middle is half committed

`M46Throw`, today's code, no bound: transaction 1 puts `/a = a1`, then `/b` with a value
transformation that throws. `execute` throws. But:

```
after transaction 1: /a = a1, /b = b0; nodes left in the transaction's node list: 1
transaction 2 (put /c = c2) committed; its record holds the values: a1 c2
after the restart: /a = a1, /b = b0, /c = c2
```

A transaction that failed is partly committed: readers see /a at once, and the next
transaction makes it durable.

The causes, in `Db.executeInner`: an exception from `putKvs` skips `store()` and
`x.end()`, but `dbClock.transactionEnd()` still runs, so the transaction's time becomes
readable. The klongs of its earlier puts stay in nodes that existed before; the nodes it
made stay registered in `Cache3` and in the writer's node list (`x.transNodes`); and the
next transaction writes that list as its own and reuses the node ids (with assertions on,
the "two canonical objects" error of 2.3). From reading the code, not tested: nodes it
made dirty are in no transaction's list in `TransSeq`.

What can throw there: a value or key transformation (`Trans.Builder.put` with
transformations, meant for counters), a read error when a put loads a node (lazy startup
today, and more with Level 4's eviction), and the ordinal bound. It is not M46, and the
guard of 5.5 removes only the bound's case. A fix: finish whatever can fail before the
first change, or make an exception inside `putKvs` stop the writer (refuse further
transactions; the stream holds only committed records, so a restart gives a consistent
state).


## 9. Recommendations

1. **Widen to 48 bits with the guard**, with [widen-48.patch](02-report/widen-48.patch):
   before item 001 turns eviction on by default (its J work packages and K4), or now. It
   is independent of item 001's open work, but touches files that item 001 changes
   (`TopNode`, `StoredTopNode`, `Db`), so it is best applied between two of its commits.
   Before a commit, the three gates as AGENTS.md requires (here: level1.sh and
   level3.sh in full, level2.sh quick).
2. **Close M46** in docs/level4-alignment.md with this resolution, and note the change
   in docs/levels.md and docs/log.md.
3. **A database-level test across 2^31**, which the patch lacks: it needs a way to start
   a database at a large ordinal. The probes use a scratch hook and skip A3's slot check
   for the first top node; a test-only way to do that (or a stream built for the test)
   is the work.
4. **Register the defect of section 8** as a row of its own.
5. **Leave the height decrease.** If top node bytes ever matter, store only the set slots
   first (7.5).


## 10. Evidence and how to rerun

[02-report/](02-report/):

* `widen-48.patch`: the change of section 5, against `5b1abdd`.
* `probe-hook-int.patch`, `probe-hook-long.patch`: the scratch hooks (against `059dbf1`,
  and against it with the widening): the property `m46.firstTop` gives the first top
  node's ordinal, and the parser skips A3's slot check for that top node alone. Never for
  production.
* Probes, Java, package `bergdb.core`: `M46Bound` (2.3), `M46Throw` (8), `M46Rate` (3),
  `M46Bytes` (7.3), `M46Heap` (2.1) against today's code with the int hook; `M46Wide`
  (5.4, 5.5) against the widened code with the long hook; `M46Load` (5.2) against either.
* Python: `height_decrease.py` (7.2, 7.3), `hops_window.py` (5.3), `numbers.py` (the
  tables of sections 3, 6 and 7).
* `outputs.txt`: the outputs, by section.

To rerun, in a copy of bergdb (`git archive 5b1abdd java | tar -x -C DIR`), with
`JAVA_HOME=/opt/homebrew/opt/openjdk`. The hook patches apply to `059dbf1` and
`5b1abdd` alike; `widen-48.patch` has paths from the repository's root, the hook patches
from `java/`:

```
cd DIR/java && patch -p1 < probe-hook-int.patch        # today's code with the hook
# or, for the widened copy: cd DIR && patch -p1 < widen-48.patch
#                           cd java && patch -p1 < probe-hook-long.patch
sh build.sh
javac --release 8 -cp build/bergdb.jar -d probes M46Bound.java    # and the others
java -ea -Dm46.firstTop=$(( (1<<30) - 10 )) -cp build/bergdb.jar:probes bergdb.core.M46Bound hot
java -ea -Dm46.firstTop=$(( (1<<30) - 10 )) -cp build/bergdb.jar:probes bergdb.core.M46Bound two
java -da -Dm46.n=1446 -Dm46.firstTop=$(( (1<<30) - 5 )) -cp build/bergdb.jar:probes bergdb.core.M46Bound many
java -cp build/bergdb.jar:probes bergdb.core.M46Rate 30 1 500000 0 10       # node, keys, n, retain s, tick
java -cp build/bergdb.jar:probes bergdb.core.M46Rate 30 1 300000 1 100000 100000
java -Xmx3g -cp build/bergdb.jar:probes bergdb.core.M46Bytes 30 1 400000 1000000
java -Xmx4g -cp build/bergdb.jar:probes bergdb.core.M46Heap 30 1000000
java -ea -cp build/bergdb.jar:probes bergdb.core.M46Throw
# widened copy (widen-48.patch, then probe-hook-long.patch):
java -ea -Dm46.firstTop=$(( (1<<32) - 20 )) -cp build/bergdb.jar:probes bergdb.core.M46Wide cross 1000 40
java -ea -Dm46.firstTop=$(( (1<<48) - 1030 )) -cp build/bergdb.jar:probes bergdb.core.M46Wide end 1000
java -ea -Dm46.firstTop=$(( (1<<31) + 3 )) -cp build/bergdb.jar:probes bergdb.core.M46Wide save 1000 40 s.bin
java -ea -Dm46.firstTop=$(( (1<<31) + 3 )) -cp OTHER/bergdb.jar:loadprobes bergdb.core.M46Load s.bin
python3 height_decrease.py 400; python3 hops_window.py; python3 numbers.py
```

StreamDigest: `java -cp BUILD/bergdb.jar:STRESS bergdb.core.StreamDigest quick > a.txt` for
each build, with one compiled copy of the stress classes, then `... StreamDigest compare
a.txt b.txt` (java/stress/StreamDigest.java).
