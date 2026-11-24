028-19. Measure and change: PE's speed and reclaim's pace with PE
==================================================================

Status: done. Kind: Change. Frans: decided (2026-11-19, 09:32).
Created 2026-11-19 by Frans Lundberg.

Frans, 2026-11-19, 09:32, on merging Java's PE (026-25): "Yes, do it. As
recommended including the follow-up." The follow-up, as recommended: an
optimization round of PE's Java writer and a look at reclaim's pace with
it. 09:25, before the decision: "Is there room for optimizations still?
[...] Could performance end up as good as or even better than main after
optimizations?"

What, from 026-25 (sections 6 and 7):

* **The short way** (small transactions): `PeWriter`'s short path builds
  the leaf's whole live list (`PeWriter.live`) and an `IdentityHashMap` a
  transaction; when the leaf is full the try is wasted and the plan and
  emit follow. CORE's set is 11 to 18 % slower than with the old writer
  (1.94 against 1.75 µs a transaction, quiet F53). Decide the leaf by
  counts, without the list; detect a full leaf before the try.
* **The plan's allocations:** a VN object a node and a leaf's changes are
  garbage at a transaction's end: GC time and RSS about 10 % above the
  old writer's. Work arrays for a leaf's changes; VNs reused between
  transactions; emit reusing what plan found on the path.
* **The load:** 0.90 to 0.97 of the old writer's puts a second at 10M
  keys.
* **Reclaim's pace:** at 10M keys with reclaim, PE made 3 physical cuts in
  6M transactions against 1, wrote 6.8 % more bytes a put although its
  user records are 16 % smaller, and its worst commit was 1.2 to 1.8
  times longer. Find why (reclaim's pacing on PE's tree shapes, or the
  reclaim row's bytes, 026-25 section 2) before changing anything.
  **Part of it explained and fixed by 028-26** (2026-11-19): a step's
  row charged only the nodes that its touch made dirty, not PE's new
  nodes (replacements, cuts, joins), so the allowance let reclaim
  rewrite more than f of the growth (Codex's review of PE, finding 1:
  90,832 of 301,856 index bytes uncharged in a probe's first iteration
  at node size 8). Now charged, the row stored again after the step; in
  the probe's workload over 20,000 updates the stream grew 1.5 to 7.8 %
  less, with fewer steps (028-26, Measurements). To remeasure here, as
  026-25 section 7, on F53 and s1: Perf write at 10M keys with reclaim
  (bytes a put, physical cuts in 6M transactions, the stream kept at
  most, reclaim's steps and records, the worst commit), against main
  before 028-26 and the old writer; whether the rest of the 6.8 % and
  the extra cuts remain.

The rule: an optimization that keeps the trees (node for node the proved
writer, `Contract.PE.peTx`) needs no proof work; the level scripts check
it against the oracle. One that changes the trees (such as an uneven
split for sorted appends) changes the model's writer and its proof
(030-21) too, and needs Frans's word first.

Done when: each point above measured before and after on a quiet machine
(F53 or s1, as 026-25 section 7), changes gated (`java/before-commit.sh`,
`level1.sh` to `level4.sh` with the PE oracle, kill-restart, CORE and the
10M timing again), reclaim's pace explained, and the result written here:
how close to the old writer, or better, each point came.

Sources: 026-25 (sections 2, 6, 7), 026-24, 030-21.


Result
------

2026-11-24, by an agent of lead-1124 (section Measurements of
2026-11-24). Against the old writer (ef02ec41, main just before PE's
merge), at 10M keys unless said:

* **Reclaim's pace: explained; neither the 6.8 % nor the extra cuts
  remain.** They came from the fault that 028-26 fixed: without it PE's
  steps charged 257 of the 483 MB of index nodes they made dirty, so its
  iterations ended after 24 % less stream than their work called for,
  and came faster. With 028-26, `main` writes 1,181 bytes a put against
  the old writer's 1,262 (0.935) and 2026.5's 1,267, and cuts once in the
  6M transactions, as both do. The worst commit is still longer, 306 to
  384 ms against 252 and 299: in every run a G1 young pause, as G1 gives
  PE's runs a young generation twice as large (with ZGC the pause probe's
  longest get or commit was 14.5 against 14.4 ms, 2026-11-21).
* **The short way: 1.04 times the old writer's** in the set test, from
  1.17 (1.81 against 1.74 µs a transaction); CORE's set 0.36 against
  0.34, from 0.40 to 0.41. A leaf is decided by counts from one pass into
  work arrays, a full leaf found before that pass (100d0c9b).
* **The plan's allocations: in part.** The routing and the inner nodes
  appended to by counts no longer make live lists (c01ac655), and the
  short way allocates 34 % less: 562 against 854 MB sampled (JFR) for
  300,000 updates, the old writer 374. A load still allocates 3.3 times
  the old writer's (3,594 against 1,085 MB for 2M keys in transactions
  of 100): a frame, a VN and entries a planned node. Work arrays for a
  leaf's changes and VNs reused between transactions were not made:
  G1's pauses in a load of 10M keys are 0.27 s longer than the old
  writer's in 51 s, so they could buy at most about 0.5 % of its time.
* **The load and CCBench: 0.98 and 1.00.** The load (transactions of 500
  puts) 189,532 against 193,566 puts a second (0.979; main 0.968); over
  CCBench's 16 cases the median transaction 1.003 times the old writer's
  (main 1.037), from 0.86 (insert, 1) to 1.11 (update, 1).

Against release 2026.6 (PE as released), `java/timing.sh`: TIMING OK, no
alerts; CORE 1.000 (its set 0.35 to 0.36 against 0.40 and 0.41), the
writes 6 to 11 % more commits a second, `w10m-fin` +7.8 % (with 028-01's
and 028-48's changes of the conflict check, also since 2026.6).

No tree changed: each change keeps PE's decisions and the order of its
reports, and the Perf run with reclaim of each build after them wrote
`main`'s stream to the byte (7,083.6 MB; the same steps, records and
index nodes).


Measurements of 2026-11-21
--------------------------

`java/timing.sh` on F53, quiet, `main` at `40cb9ae9` (PE, with 028-26)
against release 2026.5 (the old writer), run `2026-11-21-0800`
(`java/build/timing/`, not in the repository):

* CORE: 0.265 against 0.250, ratio 1.060 (alert above 1.10). The run of
  01:52 the same night had 1.102.
* Pauses (PauseProbe, ZGC): the longest get or commit 14.5 ms against
  14.4 ms (guide 50 ms).
* Writes with reclaim at work, faster: `w10m-fin` +27.4 % commits/s
  (68,936 against 54,104), `r-100-fin` +27.2 % in its mixed phase,
  `w-uni-100-fin` +10.2 %.
* Writes with no reclaim (retain=inf), slower: `w10m-inf` -6.3 %,
  `w-uni-100-inf` -9.7 %; restart after `w-uni-100-inf` 1.98 s against
  1.75 s.
* Reads: -1 % to -5 %; `get_longkey` -5.4 %, the run's one alert
  (unconfirmed, threshold 5 %); `r-100-fin`'s mixed gets -12.3 % (no
  threshold for it).

The rest of the done criterion (each point measured before and after a
change, reclaim's pace explained) was open until 2026-11-24 (below).


Measurements of 2026-11-24
--------------------------

By an agent of lead-1124, on F53, in the lead's work directory
(c19, the branch; c19-runs.noindex, a clone a build; not in the
repository). The scripts are in tools/ and the summaries in results/ of
this directory. The builds:

* `old`: ef02ec41, the old writer, main just before 026-25's merge
  (026-25's "main"; the same reclaim as PE's);
* `2026.5`: the release (3611130c), the old writer and reclaim before
  026-05;
* `pre26`: b2fe8dad, PE before 028-26 (the first parent of its merge);
* `main`: 70807233, PE with 028-26 (the base of this branch);
* `sw`: 100d0c9b, the short way; `r1`: c01ac655, the routing too.

Each clone's Perf.java was given a dump of reclaim's iterations, cuts and
records (`Reclaim.Stats`, by reflection; tools/patch-perf.py), not
committed. **Times** are from sessions with nothing else heavy on F53,
each JVM after a check of no other JVM and the CPU idle: at least 78 %,
not 026-25's 85, as macOS's photo analysis (mediaanalysisd) held 0.7 to
0.8 of a core all evening (80 to 84 % idle before each JVM, in the logs);
builds in ABBA order. **Counts** do not depend on the machine (Perf's
clock is simulated): old's run gives 026-25's to the byte (7,573.4 MB
appended, 259,432 steps), and every rerun of a build its own.

**Reclaim's pace.** 026-25, section 7's run: Perf write at 10M keys,
8-byte values, uniform updates, retention 0.1 updates a key (R = 1M
transactions), 6M transactions after a warm-up of 200,000, heap 8 GB, G1
(results/counts.txt):

* bytes a put: main 1,180.6, pre26 1,347.7, old 1,262.2, 2026.5 1,267.2;
  of them user records 463.2, 421.5, 501.0, 507.1; steps' records 666.9,
  926.2, 761.2, 760.1; main's rows stored again (028-26's 4b, counted as
  table records) 50.5;
* reclaim's steps 246,570, 432,724, 259,432, 300,445; iterations done 2,
  4, 3, 3; physical cuts 1, 3, 1, 1;
* the stream kept at most (sampled each second): 9,764 to 9,834, 9,074 to
  9,118, 10,002 to 10,059, 10,021 MB.

The first iteration does the same work in each build (every live value
stored before the end of the warm-up), and its stream is its charge over
f (1/4): the steps put again while the allowance, f of the stream's
growth since pStart less the charge, passes MIN_STEP (027-13, 1.2); the
charge over the iteration's stream is 0.250 in each.

* main: 3,608 MB of stream in 3,008,461 transactions, 8,632,313 values
  put again; charged 902 MB: the values 414 MB (8 s + v + VN each) and
  the index nodes made dirty 488 MB, of them 225 MB PE's new nodes, made
  dirty after the row (028-26);
* pre26: 2,771 MB in 1,991,163 transactions, 9,072,202 values; charged
  693 MB: of the 483 MB of index nodes its steps made dirty only 257 MB,
  the new nodes charged nowhere;
* old: 3,663 MB in 2,877,500 transactions, 8,674,679 values; charged
  916 MB (values 416 MB, index nodes 500 MB, all but 0.9 MB of them);
  2026.5: 3,668 MB in 2,873,994 transactions, charged 917 MB.

So pre26's iterations ended after 24 % less stream than their whole
charge called for (2,771 against 3,672 MB): in 6M transactions it ended
4 iterations, cut 3 times, and its steps wrote 22 % more bytes a put than
the old writer's: the 6.8 % and the 3 cuts of 026-25. With the charge
whole, main's first iteration charges 1.5 % less than old's (488 against
500 MB of index nodes) and lasts 4.6 % more transactions (3.01M against
2.88M): PE's records are smaller (user records 463 against 501 bytes a
put), so the same stream takes more transactions: 1,199 bytes a put over
the iteration against 1,273 (0.942).

The 6M window counts iterations by thresholds. In each build the second
iteration begins when the first ends (R div 4 has passed), its pCut the
first's pStart: it puts nothing again but scans the 10M keys, a step a
commit, in 66,891 to 66,893 steps and 92 to 103 MB (2026.5: 72,468
steps). The third begins R div 4 after the second. The cut comes R after
the first ends, at the first's pCut (the end of the warm-up); the next
needs the third ended. Old's third ended 10,618 transactions before the
window's end, main's had put 7.6M of its about 8.5M values again: 3
iterations against 2, one cut each. Main's ratio over the window, 0.935,
is near the first iteration's, 0.942.

The rows stored again (028-26): 189,233 records (with the table's own
stores 189,242), 50.5 bytes a put (4.3 % of main's stream), 1,601 bytes
each: the row 308, the record's header 62, and 1,232 bytes (3.7 nodes)
of index nodes that the take wrote with the record.

The times (results/times.txt; main 3 runs, old 2, pre26 2, sw 2):

* commits a second: main 79,224 to 80,031, old 59,150 and 60,309, pre26
  60,057 and 60,332: main 1.33 times old's, pre26 1.00. Not the writer's
  gain: pre26 writes with PE too; between it and main came 028-26 (fewer
  steps) and 028-01 and 028-48 (the conflict check's KeyModSet), not timed
  apart here. sw 82,153 and 82,253 (1.03 of main);
* the append latency: p99 main 248 to 252 µs, old 358 and 365 (0.69);
  p99.9 360 to 365 against 510 and 522 (0.70);
* the worst commit: main 384, 306 and 313 ms; old 252 and 299; pre26 368
  and 359; sw 355 and 364. Each of the 5 slowest commits of every run
  fell in a G1 young pause (by the JVM's uptime in the GC log;
  tools/gcsumm.py): the worst commit is the collector's pause, not
  BergDB's code. Main's young pauses last 190 to 248 ms on average, at
  most 312 to 389; old's 211 and 212, at most 251 and 298. Each of main's
  frees 2.0 to 2.1 GB, each of old's 1.0 GB: G1 gives PE's runs a young
  generation about twice as large (PE allocates more), so a pause copies
  the nodes made over a longer interval. GC time 2,660 to 3,053 ms
  against 2,529 and 2,545; sw's runs 12 and 14 collections against main's
  16 to 18, with pauses as long. With ZGC, timing.sh's PauseProbe found
  the longest get or commit 14.5 ms against 2026.5's 14.4 (2026-11-21);
* the load (10M puts in transactions of 100): main 192,825 to 194,949
  puts a second, old 205,227 and 206,045 (0.94).

**The short way** (100d0c9b; `PeWriter.shortLeaf`, `liveInto`):

* the size test first: a leaf without room for its puts' klongs and one
  more is full whatever its counts (decideNode's extra is at least 1 +
  added), found before its klongs are read;
* else the counts (live compare values, key klongs) and the membership of
  each operation's compare value come from one pass into live()'s work
  arrays (`liveInto`, the pass live() now uses too): no Live and no
  IdentityHashMap a transaction; a plan after a refused short way makes
  the leaf's list again;
* one operation's marks are its path reversed (the sort's order for one
  operation), with no list to sort; a node's change list is made for a
  leaf only.

Before and after (results/setloop-core.txt): the set test alone (026-25's
SetLoop, 30 runs a JVM, the median), µs a transaction: old 1.745 and
1.743, main 2.016 and 2.050, sw 1.813 and 1.803 (1.17 to 1.04 times the
old writer's). CORE's set (level 1's Props, a JVM a run): old 0.34 and
0.34, main 0.40 and 0.41, sw 0.36 and 0.36; CORE 0.24, 0.24 / 0.25, 0.26
/ 0.24, 0.25.

**The plan's allocations** (100d0c9b, c01ac655):

* an inner node appended to by counts (`appendedByCounts`) takes the
  counts of its live list from liveInto's pass when the list was not
  made; its VN makes the list if a join or a settle needs it (`VN.lb()`);
* more than 4 operations (16 before) go to an inner node's children by
  route over the live compare values in the work arrays (`routeByLive`,
  for `routeByList`), with no Live and no array of starts; fewer, by the
  searches, which now stop at the first operation below a klong's compare
  value (the operations are in increasing order).

JFR's allocation samples (Perf write, 2M keys loaded in transactions of
100, then 300,000 updates of one put; tools/jfralloc.py): the load old
1,085 MB, main 3,632, r1 3,594; the updates old 374, main 854, r1 562.
In r1's load: live()'s arrays 19 %, the leaves' whole lists when cut
(`merged`) 9 %, the planned children's entries 7 %, the frames 10 %, the
VNs 7 %. These are PE's design, a frame, a VN and entries a planned node,
read again by emit after the whole plan; work arrays for a leaf's changes
and VNs reused between transactions would keep them across frames and
transactions, with their state reset at each: a larger change than this
entry's, not made. What they would buy is small: in CCBench's load of
10M keys (transactions of 500 puts, about 51 s) G1 paused 751 and 757 ms
with r1 against 484 and 486 ms with old (the GC logs), so the plan's
garbage costs about 0.5 % of the load's time; the rest of r1's 2 % is the
plan's own work.

**The load and CCBench** (results/ccbench.txt): CCBench at 10M keys
(026-25's cc10m: 8-byte values, transactions of 1 to 500 operations,
history kept), ABBA, old 4 runs, main 2, sw 4, r1 2. Its mean time an
operation moves with a G1 pause that falls in a phase (the same phase in
both runs of a build: main's mixed 100 1.41 times old's, sw's update 10
1.29); the median transaction does not. The median transaction over the
16 cases, geometric mean: main 1.037 times old's, sw 1.022, r1 1.003; r1
from 0.86 (insert, 1) to 1.11 (update, 1). Update 1 is the first phase
after the load; alone, with 2M operations, old and sw take 6.25 and
6.21 µs (a JFR profile, not quiet). The load (transactions of 500 puts):
old 193,566 puts a second, main 187,398 (0.968), sw 187,911 (0.971), r1
189,532 (0.979).

**Gates** on c01ac655, the last change of java/ (results/gates.txt;
tools/gates.sh: each in its own clone, at nice 10, at the same time):

* `java/before-commit.sh`: BEFORE COMMIT OK (59 s), on 100d0c9b too;
* `level1.sh`: LEVEL 1 OK; MEM 129 (at most 131), SEG 227.8, MEM10M
  128.2, SS 1.53 (at most 1.54), as 026-25's;
* `level2.sh`: LEVEL 2 OK; the tree checker (PE, node for node) on the
  small, drain and reclaim sets, 7,240, 14,120 and 8,731 transactions;
  the contract and the bridge on them, 0 failures; pecmp, 0 differ;
  A2A3Check2's marking and joins; RestartInvariance, stream identical;
* `level3.sh`: LEVEL 3 OK (C-CUT 0 of 816, C-STEP 0 of 25,822);
* `level4.sh`: LEVEL 4 OK (C-P and C-H 0 of 14,709);
* `kill-restart.sh 1000`: KILL RESTART OK: 1000 kills and 67 exits in
  1427 s, seed 20261124;
* StreamDigest quick, main's build against c01ac655's: DIGESTS IDENTICAL
  (44 of 44);
* before the gates, on each change: the unit tests and `treeconf.sh`
  (small, then all with 2 seeds), TREECONF OK.

**CORE and the 10M timing again**: `java/timing.sh` on c01ac655 against
release 2026.6 (PE as released), 20:05 to 21:05, with MINIDLE=78 (the CPU
82 to 88 % idle before each run; results/timing.txt): **TIMING OK**, no
alerts. Since 2026.6 the conflict check changed too (028-01, 028-48), so
the writes' gains are not the writer's alone; the writer's own, sw
against main in Perf's run with reclaim above, was 3 % in commits a
second.

* CORE: 0.250 against 0.250 (ratio 1.000); its set 0.35 to 0.36 against
  0.40 and 0.41.
* The pause probe (ZGC): the longest get or commit 13.1 against 15.6 ms
  (guide 50 ms).
* `performance.sh ab`, commits a second: `w10m-fin` +7.8 % (76,673
  against 71,115), `w10m-inf` +10.4 %, `w-uni-100-fin` +11.2 %,
  `w-uni-100-inf` +6.3 % (193,924 against 182,510: on 2026-11-21 2026.6's
  writer was 9.7 % below 2026.5's here), `r-100-fin`'s mixed phase
  +11.5 %; the reads +0.2 to +9.1 %; the restarts -7.3 to +7.2 %
  (`w10m-fin`'s 2.07 against 1.93 s, no threshold).


State
-----

2026-11-24, 21:10. **Done** on the branch `028-19` in
the clone c19, from main 70807233: the code in
100d0c9b and c01ac655 (only `java/src/bergdb/dag/PeWriter.java`), gated
on c01ac655 (above: BEFORE COMMIT OK, LEVEL 1 to 4 OK, KILL RESTART OK,
DIGESTS IDENTICAL, TIMING OK); 027-08 and 027-13 brought to it. Not
merged, not pushed: the lead lands it. Left, for a later item if wanted:
the plan's allocations in loads (work arrays, VNs reused), at most about
0.5 % of a load's time; the worst commit under G1, which is G1's pause.


Log
===

2026-11-19. Registered by coord-1118 at Frans's word (09:32).

2026-11-19. Reclaim's pace: the uncharged PE nodes fixed in 028-26; what
to remeasure noted above. By an agent of coord-1118.

2026-11-21. timing.sh's figures against 2026.5 added, by coord-1120.

2026-11-24. In progress, by an agent of lead-1124 (from 18:17): reclaim's pace
remeasured first, then the short way and the plan's allocations.

2026-11-24. Done by an agent of lead-1124 (18:17 to 21:10), on the
branch `028-19`: reclaim's pace remeasured and explained (the nodes left
out of the charge before 028-26: no 6.8 % and no extra cuts left; the
worst commit a G1 pause); the short way decided by counts without live
lists (100d0c9b); the routing and the inner nodes appended to by counts
without live lists (c01ac655); measured before and after on F53, gated,
timing.sh against 2026.6 TIMING OK. The entry a directory with its tools
and results; 027-08, 027-13 and releases/next.md (Speed) updated.
