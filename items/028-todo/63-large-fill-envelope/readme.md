028-63. Investigate: week.sh's large reclaim run: the fresh fill is 3.4 times 028-43's
=====================================================================================

Status: done: the seed's key order, not a change of the database; the
harness's data cap now scales with the fill. Kind: Investigate. Frans:
none.
Created 2026-11-25 by Frans Lundberg.

What: `week.sh` on `main` at `09bf9efb` (2026-11-25, step
large-reclaim, `java/stress/large.sh` full, seed 20782, 10,000,000
keys): the fresh fill reached a stream of 7,244,195,488 bytes, and the
run failed its first check, "fresh database is too large for the fixed
space envelope" (`LargeReclaimRun.fill`: 8 L0 + 2 GB must be below the
40 GB cap). 028-43's full run of 2026-11-21 (seed 20778, the database
at `40cb9ae9`) filled 2,106,983,240 bytes. The fill writes the same
10,000,000 puts of 8-byte keys and 64-byte values in transactions of
100, in an order that the seed gives, with no reclaim.

Why: the same fill writing 3.4 times the bytes is either the seed (the
order of the keys) or a change of the database since `40cb9ae9` that
writes more index nodes for the same puts: a large rise of the write
amplification at 10 million keys, where BergDB is meant to be best
(Frans: optimize for large databases). The stream's bytes are
deterministic (010-01, P2), so the lengths compare exactly.

Frans: none.

Done when: the fill's length at 10,000,000 keys for seeds 20778 and
20782 on `40cb9ae9` and on `main`; if `main` writes more for the same
seed, the commit that raised it found by bisection (the fill only), the
cause named, and a 028 entry for the fix (or the reason it stays); if
the seed alone explains it, the harness's envelope or its choice of
orders fixed so that every seed passes, with `java/stress/large.sh
quick` passing.

First step: 028-43, sections on the space envelope and the full run;
`LargeReclaimRun.fill` and `keyAt`; a probe or a mode of the runner that
stops after the fill and prints the length.


Result
------

The seed alone explains it (2026-11-26). The same seed writes the same
bytes at `40cb9ae9` and at `main` (`243585c1`), so no commit was bisected.
The two seeds' orders write different numbers of index nodes.

Probe: `probes/FillProbe.java`, the loop of `LargeReclaimRun.fill` (the
harness source of 2026-11-21: `keyAt`, the values, the clock,
`cacheSizeIndicator(300 n)`, `Eviction.Schedule.BUDGET` with the seed,
`FileStream` with `setMax2G`, the marker, the retention and the sync),
compiled against each worktree's `build/bergdb.jar` and run with
`-Xmx10g`; it deletes its data at the end. Arguments: `OUT SEED KEYS
[STEP [MAXKEYS [HISTORY [ORDER]]]]`. It reproduces both runs' LOAD lines
byte for byte.

Fresh lengths (the stream after the marker, the retention and the sync):

* 10,000,000 keys, seed 20778: 2,106,983,240 bytes at `40cb9ae9` and at
  `main` (028-43's full run: the same).
* 10,000,000 keys, seed 20782: 7,244,195,848 bytes at `40cb9ae9` and at
  `main` (week.sh's run of 2026-11-25: its LOAD line at 10,000,000 keys,
  7,244,195,488, is the same on both).
* 1,000,000 keys (quick's size, its own order and a 300 MB cache), seed
  20778: 184,240,328 bytes at both commits; seed 20782: 197,969,896 at
  both.
* After the first 1,000,000 puts of the 10,000,000-key fill: 179,836,800
  (20778) and 213,445,728 (20782) at both commits. The two orders part
  from about 2,000,000 keys on: 20778 adds about 0.21 GB a million keys
  to the end, 20782 0.43 GB in the second million and 0.97 GB in the last.

Other orders at 10,000,000 keys, on `main`:

* A random permutation of the keys (`java.util.Random(20782)`):
  6,059,523,432 bytes.
* Seed 20772: 7,079,378,696 bytes; seed 20785: 3,539,538,792.
* After 3,000,000 puts, the 36 seeds 20765 to 20800: from 603,776,224
  (20777, the same multiplier as 20778) to 1,334,178,544 (20772); 20782
  1,310,112,000, the random permutation 1,083,475,088. 30 of the 36 are
  above 900 MB.

Why the order matters. A transaction makes dirty the key nodes on the
paths of its puts; a later record's take writes them, paced so that the
startup section stays about one startup distance (50 MB by default) of
stream (`TransSeq.take`). A node that more puts reach while it is dirty
is written once for all of them. With `keyAt(s) = a s + offset mod n`,
slots s and s + d put keys a d mod n apart. For seed 20778 (a =
1,020,781), a key's neighbour (a distance of 1) is put 4,379 slots, 44
transactions, later: puts that follow each other in the fill fill in
runs of neighbouring keys, so many of a node's puts fall in one stretch
of dirtiness. For seed 20782 (a = 1,020,787) the nearest such pair, a
distance of at most 8 keys, is 168,615 slots apart, more than one
startup distance of this fill: its puts spread over the key space as
evenly as a random order's or more, and once the tree has a few million
keys nearly every put makes its own leaf and path dirty again. The
random permutation writes 6.06 GB, 20782's lattice 7.24 GB, 20778's
2.11 GB: 20778's order is the exception. `probes/order-locality.py`
prints that distance for each seed: 534 of the 100,000 multipliers
give at most 5,000 slots, 2,050 at most 20,000; among the day numbers
20600 to 21329, which week.sh passes as seeds, 6 of 730 give at most
5,000. It is a rough measure (20791, with no pair within 8 keys closer
than 1,022,936 slots, wrote 1.09 GB after 3,000,000 puts, 20782 1.31
GB), but it separates the local orders.

The history follows the same order with four keys a transaction. Over
its first 2,500,000 transactions (one epoch, `HISTORY` of the probe,
without the harness's reads and syncs) seed 20778 appended 4,202,448,544
bytes (1,681 a transaction; 028-43's whole run 1,859) and seed 20782
15,801,707,144 (6,321 a transaction), 3.8 times as many. The logical
kept stream of 20782 reached 13,050,962,552 bytes before the first cut,
between 1,000,000 and 1,250,000 transactions, against its absolute envelope 8 L0 =
57,953,566,784. So with most seeds, if the first epoch's rate holds, the
full run appends about 630 GB in place of 186 GB, and takes longer than 028-43's 79 minutes; it was not
run in full.

So the fixed 40 GB cap of 028-43 holds only for fills below about
4.75 GB (8 L0 + 2 GB < 40 GB), a minority of the orders; 028-43's seed
was one of the few local ones. The database did what it does for a
random insertion order; the rise is not a change of the writer. At
10,000,000 keys a random order writes about 8.4 bytes for each byte of
key and value (72 a put), 20782's order 10.1, 20778's 2.9, the same at
both commits: not a fault; whether it should be lower is a performance
question outside this entry.

The harness change (java/stress, 2026-11-26):

* `LargeReclaimRun`: the fixed `DISK_CAP` of 40 GB is gone. The data
  cap is 8 L0 + 3 GB (`diskCap()`), one GB above the absolute envelope
  8 L0 + 2 GB, so that the envelope's checks fail first; the near-cap
  check in `observe()` and `diskCheck()` use it. After the fill, the
  free disk must hold the rest of the cap and the 2 GB reserve, or the
  run fails with the bytes it needs. A fill of more than 1,000 bytes a
  key fails (`FILL_BYTES_PER_KEY`): the orders measured wrote 211 to 724.
  The FILL line prints `dataCap`. The `verify` mode reads `fresh.txt`, as
  the child does, so that its cap is the run's.
* `large.sh`: full requires 85 GB free before building (8 x 10 GB + 3 GB
  and a 2 GB reserve), quick 13 GB; the header gives the range of L0 and
  the bytes of most orders.
* Every check relative to L0 (G3's 6 L0 + H_R, H_R <= 2 L0, the history
  of at least 12 L0) is unchanged, and every seed's order is kept: the
  test now covers random-like orders, which 028-43's run did not.
* `java/stress/large.sh quick 20782` passed (2026-11-26): fresh
  197,969,896 bytes, data cap 4,583,759,168, 4,081,920 transactions, 37
  physical cuts, peak physical kept 871,313,432 bytes, two clean
  restarts and the SIGKILL recovery. No full run.

Not settled:

* The duration of a full run with a random-like order, and with it the
  "60 to 90 minutes" of `java/week.sh`'s step 10 and `java/readme.txt`
  (outside this entry's files): a full run of a week.sh, or fewer epochs
  in full mode (12 L0 asks for about 15,000,000 transactions with L0 =
  7.24 GB), is the lead's choice.
* The other choice, an order that is always local (a multiplier picked
  by `order-locality.py`'s distance), keeps 028-43's 40 GB and duration
  but tests one kind of order only; not taken.


Log
---

2026-11-25. Registered by lead-1125, from `week.sh`'s report
(2026-11-25-1409); taken by an agent of lead-1125.

2026-11-26. Done: the seed's key order explains the fill, the same bytes
at `40cb9ae9` and `main` for each seed (2,106,983,240 for 20778,
7,244,195,848 for 20782); a random order writes 6.06 GB. The harness's
data cap is now 8 L0 + 3 GB, with a fill ceiling of 1,000 bytes a key;
`large.sh quick` passed. By an agent of lead-1125.
