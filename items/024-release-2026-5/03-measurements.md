# 024-03. Release 2026.4 measured at 1M and 10M keys (PF1)

Created 2026-11-11. Status: done (2026-11-11). Not measured: 100M keys
and s1; 2026.5 claims 10M keys and the scale law (024-05, QF7, decided
2026-11-12).

PF1 of 024-01 (section 9.1): release 2026.4 at large sizes, with 2026.3
beside it where the API allows, to decide CL1, CL2, CL7 and PF3 by
numbers (024-01, sections 4.1, 4.2, 4.7, 9.3). Frans, 2026-11-10, 19:49:
"Measurements on 2026.4 can be done in parallell when possible, or at
night." Run on F53 from 05:03 to 06:29. The probe, the scripts and every
output are in `03-measurements/`.

**Corrections, 2026-11-11, 07:26** (the text below is left as written):

* **MEM 327 at 10M keys is explained** (024-08): it is the shape of
  MEM's keys, not the count. A key of exactly 7 bytes is two segments
  and gets a key node of its own, and 9M of the 10M keys `"" + i` are 7
  bytes. Keys with a shared prefix cost 127 bytes a KV at 10M. Do not
  quote 327 as MEM at 10M.
* **"A get reads about 25 versions" (sections 3 and 8) is wrong**
  (024-05): the counter printed is the loads since the start, the fill
  included. The second million gets added 1,924,301 loads: 1.9 a get.
* **"20 records of 17 MB" (section 7)** is loose: 20 records over 1 MB,
  the largest 17 MB (024-05).


## 1. In short

* **Puts, gets, scans: 2026.4 is 2026.3.** At 10M keys the fill, the
  gets, the scans, the start and the stream are the same within 2 %; the
  stream after the fill has the same length to the byte. Nothing to win
  back.
* **The mass-delete fault is gone at 10M.** After 9M of 10M keys are
  deleted, a scan of the first 1,000 keys left visits 101 key nodes and
  takes 3.0 ms; 2026.3 visits 882,271 and takes 3.5 s. 2026.3's reclaim
  then stops (no iteration in 50,000 transactions, the stream grows);
  2026.4's goes on.
* **CL1 (P8): not needed on these numbers.** After the mass delete at
  10M, 2026.4's stream is back in its twin's range after about 60,000
  drive transactions (about 4 reclaim iterations, 2.5 GB written). P8
  would save one iteration of that lag, about 13,000 transactions.
* **CL2 (merges): a measured cost at 10M.** With all but every 30th key
  deleted, 2026.4 keeps 11 to 16 times the key nodes of a fresh database
  of the same keys, and reclaim does not shrink them (55 iterations).
  Under the same overwrites it writes 3.3 times the bytes a transaction,
  keeps 2.6 times the stream and scans 4.6 times slower. At 1M the
  stream cost does not show.
* **CL7 (the last touch): needed.** With keys in time order (a FIFO of
  10M live keys) the end of each reclaim iteration writes one record of
  191 to 206 MB, and that commit takes 20.6 to 22.2 s. At 1M live keys:
  17 MB and 1.7 s. It grows with the live keys. 2026.3 does the same or
  worse; it is old, not new in 2026.4.
* **PF3: no number here.** Reclaim's value reads were not counted
  separately; section 9 says what would measure them.


## 2. Setup

* **Code.** The release jars: `releases/2026.4/bergdb-2026.4.jar`
  (SHA-256 `fed88f75…`, as its `SHA256SUMS`; tag `release-2026.4`,
  `76f66f89`) and `releases/2026.3/bergdb-2026.3.jar`. A clone at the tag
  in `/Users/f/fl/bench/2026-11-11/pf1/clone`; the main tree unchanged
  but for this file and `03-measurements/`.
* **Probe.** `03-measurements/probe/PF1.java`, package `bergdb.core`,
  compiled apart against each jar as 023-10's probe was. It uses the Core
  API (`Db`, `Trans`, `getOne`, `getMany`) and, for the node counts,
  CleanupRule's counting follower (023-03's probe), which wraps
  `nodeCollection().maintenance()` and so loads without installing. The
  same source compiles against both jars. Runners: `pf1.sh` (one JVM),
  `runs.sh 1m|10m`, `runs2.sh` and `runs3.sh` (the FIFOs).
* **Database.** A `FileStream`, the builder's defaults: startup distance
  50 MB, cache indicator 200 MB, eviction on. A test clock (`CoreTestClock`),
  10,000 time units (1 ms) a transaction, kept between JVMs; a retain
  duration of 1 s on that clock, so 1,000 transactions.
* **Workload.** Keys `/k/%010d` (13 bytes), values of 100 bytes, 100 KVs
  a transaction, `execute()` with no sync (an append commit). The fill
  puts the keys in random order unless said; deletes go in ascending key
  order, 100 a transaction.
* **The drive** after a delete: 100 overwrites of random live keys a
  transaction, 100 bytes each. **The twin**: a fresh database of only the
  keys left, then the same drive (023-03's method for T1 and T2).
* **The FIFO** (keys in time order, 021-25's shape): each transaction
  puts 100 new keys after every key so far and deletes the 100 oldest.
* **JVM and machine.** OpenJDK 27.0.1 (Homebrew), G1, `-Xms8g -Xmx8g`, no
  `-ea`. F53: Apple M1 Pro, 10 cores, 32 GB, internal SSD. One JVM at a
  time.
* **Quiet.** No other benchmark, gate or JVM ran (`ps` before; no
  QUIET-BLOCK marker for the day). The 1-minute load at the 40 step
  starts was 1.3 to 4.9, median 3.4: macOS's `mediaanalysisd` used 60 to
  200 % of a core all night and Spotlight's `mds_stores` 40 %; neither was
  touched. The probe's main work is one thread, so the times are good to
  a few percent between the releases, which ran under the same load, not
  as references (011-09).
* **OS file cache.** Warm: no `purge` (it needs root). "Cold" below means
  a new JVM with an empty node cache over files the OS still holds. One
  exception, by accident, in section 6.
* **Units.** MB and GB are 10^6 and 10^9 bytes. "kept" is the stream from
  the first available position to the end (`getStreamLength()` minus
  `getFirstAvailablePos()`); "key nodes" are the distinct key nodes a full
  scan of the user's keys follows.


## 3. Puts, gets, scans, stream and MEM (measurement 1)

Fill of N keys in random order, then in the same JVM 1M gets of random
keys twice and two full scans ("warm"); then a new JVM: 100,000 gets, 1M
gets, two scans ("cold", OS cache warm). Gets and scans are the second
pass where two were made.

| Measure, 10M keys                  | 2026.3   | 2026.4   |
|---|---|---|
| fill, puts/s                       | 51,290   | 51,971   |
| fill, µs a put                     | 19.5     | 19.2     |
| fill, commit p99.9 / max           | 5.5 / 208 ms | 5.4 / 114 ms |
| stream written, bytes a put        | 722      | 722      |
| kept after the fill                | 6.79 GB  | 6.79 GB  |
| reclaim iterations in the fill     | 3        | 3        |
| key nodes                          | 892,251  | 892,251  |
| heap after the fill (default cache) | 194 MB  | 195 MB   |
| warm get, µs                       | 7.79     | 7.82     |
| warm scan, ns a key                | 2,645    | 2,631    |
| start, ms                          | 2,084    | 2,097    |
| cold get, first 100,000, µs        | 8.61     | 8.64     |
| cold scan, ns a key                | 2,645    | 2,679    |
| MEM, bytes a KV (10M KVs)          | 327.0    | 327.1    |

| Measure, 1M keys                   | 2026.3   | 2026.4   |
|---|---|---|
| fill, puts/s                       | 128,253  | 127,746  |
| stream written, bytes a put        | 328      | 328      |
| key nodes                          | 88,997   | 88,974   |
| warm get, µs                       | 2.22     | 2.22     |
| warm scan, ns a key                | 1,307    | 1,321    |
| start, ms                          | 1,470    | 1,544    |
| cold get, first 100,000, µs        | 4.09     | 4.16     |
| MEM, bytes a KV (1M KVs)           | 129.6    | 129.6    |

* **The same.** No measure differs by more than 5 % (the 1M start) and
  most by under 2 %. At 10M the stream length after the fill is
  7,228,907,448 bytes in both. 023's changes touch the deletes and
  reclaim's cut, not a fill of new keys.
* **MEM** is `bergdb.dev.props.Mem`'s method (a `DummyStream`, empty
  values, keys `"" + i`, no eviction); `Mem` itself from 2026.3's jar
  prints 129 (2026.4's jar has no `bergdb.dev` classes). At 10M KVs it is
  327 bytes, 2.5 times the 1M figure, in both releases. Not explained
  here; its cause should be found before 10M is quoted as MEM.
* **At 10M the default cache is small.** The stream is 6.8 GB and the
  cache 200 MB, so a get reads about 25 versions from the stream (25.6M
  loads in 1M gets) and costs 7.8 µs against 2.2 at 1M; warm and cold
  hardly differ. With a cold OS cache each of them would be a disk read.
* **Kept after a fill is 6 times the data.** 6.79 GB for 10M keys of
  about 113 bytes: reclaim made 3 iterations in the fill's 100,000
  transactions, so most old node versions are still in the stream. A
  fill in key order writes 244 bytes a put (section 7).


## 4. A mass delete and the scans after it (measurement 2)

On the 10M database of section 3: delete keys 0 to 8,999,999 (90,000
transactions), so 1M keys are left at the end of the key range; scans;
then 300,000 drive transactions (50,000 for 2026.3). The twin holds the
same 1M keys, put fresh.

| After the delete, 10M keys        | 2026.3       | 2026.4    | twin      |
|---|---|---|---|
| deletes/s                         | 84,246       | 107,240   | -         |
| largest record in the delete      | 153 MB       | 126 kB    | -         |
| slowest commit in the delete      | 4,315 ms     | 94 ms     | -         |
| scan of the first 1,000 keys      | 3,479 ms     | 3.0 ms    | 0.5 ms    |
| its key nodes                     | 882,271      | 101       | 87        |
| scan of the 1M keys left          | 6,292 ms     | 2,769 ms  | 1,881 ms  |
| its key nodes                     | 980,212      | 98,042    | 88,974    |
| dead KEY klongs in them           | 10,553,457   | 208,143   | 214,754   |

2026.3's run started with its files out of the OS cache (section 6); its
full scan before the delete read them back, so its delete rate is only
roughly comparable. Its counts and record sizes are exact.

**Reclaim's lag after the delete, 10M.** kept at every 10,000 drive
transactions, in GB. The delete started in reclaim iteration 1; an
iteration of this drive is about 13,000 transactions (23 in 300,000).

| Drive tx    | 0    | 10k  | 20k  | 30k  | 40k  | 50k  | 60k  | 70k  | 80k  | 300k |
|---|---|---|---|---|---|---|---|---|---|---|
| 2026.4      | 6.90 | 7.26 | 7.70 | 5.22 | 5.67 | 2.41 | 1.59 | 1.46 | 1.93 | 1.61 |
| twin        | 0.33 | 0.66 | 1.12 | 1.59 | 1.73 | 1.64 | 1.48 | 1.95 | 1.79 | 1.48 |
| 2026.3      | 7.28 | 7.75 | 8.27 | 8.80 | 9.34 | 9.89 | -    | -    | -    | -    |

* From 30,000 transactions on the twin moves between 1.45 and 1.95 GB
  (the cut follows the iterations). 2026.4 is above that range until
  between 50,000 and 60,000 transactions, and inside it from 60,000 on:
  **the lag is about 60,000 transactions, 2.5 GB written by the drive,
  about 4 iterations.** In that time kept peaks at 7.7 GB, 1.1 times what
  it held before the delete.
* **At the end** (300,000 transactions) 2026.4 and its twin agree: kept
  1.61 against 1.48 GB (a phase of the cut), 111,565 against 111,399 key
  nodes, 526,308 against 526,980 dead klongs, heap after a GC 225 against
  218 MB. The scan of the first 1,000 keys: 2.2 ms in both.
* **2026.3** made no reclaim iteration in its 50,000 drive transactions:
  kept grew from 7.28 to 9.89 GB, 10 records were over 1 MB (the largest
  122 MB) and the slowest commit took 3.1 s. Its heap after a GC: 422 MB.

**The same at 1M** (900,000 deletes, 100,000 left; iteration about 5,000
transactions): 2026.4's first 1,000 keys visit 118 key nodes, 2026.3's
87,512 (2.0 against 28.4 ms). 2026.4's kept fell from 532 MB to 312 MB
between 10,000 and 15,000 drive transactions, inside the twin's 233 to
328 MB, so the lag was about 3 iterations. 2026.3 kept iterating at 1M,
but its nodes stayed (98,504 against the twin's 11,058 after 100,000
transactions) and its records reached 29 MB.


## 5. Scattered deletes: the underfill (measurement 3)

023-03's "sparse" shape (section 3, T2) at scale: a fill of N keys in
random order, then every key deleted but each 30th, in ascending order;
then the drive of section 2 for 300,000 transactions (100,000 at 1M). The
twin holds the N/30 keys left, put fresh, with the same drive.

| 10M keys, 333,334 left            | 2026.4 sparse | twin     | ratio |
|---|---|---|---|
| key nodes after the deletes       | 419,680       | 26,746   | 15.7  |
| KEY klongs after the deletes      | 5,505,664     | 366,901  | 15.0  |
| scan of the keys left             | 2,418 ms      | 316 ms   | 7.6   |
| get, µs                           | 7.33          | 1.42     | 5.2   |
| key nodes after the drive         | 420,636       | 37,084   | 11.3  |
| KEY klongs after the drive        | 3,664,200     | 544,651  | 6.7   |
| bytes written a drive transaction | 86,651        | 26,351   | 3.3   |
| commit p50 in the drive           | 2.66 ms       | 0.85 ms  | 3.1   |
| drive time, 300,000 transactions  | 858 s         | 284 s    | 3.0   |
| kept after the drive              | 1.04 GB       | 0.39 GB  | 2.6   |
| scan after the drive              | 1,777 ms      | 390 ms   | 4.6   |

| 1M keys, 33,334 left              | 2026.4 sparse | twin     | ratio |
|---|---|---|---|
| key nodes after the deletes       | 42,075        | 2,662    | 15.8  |
| key nodes after the drive         | 42,180        | 3,710    | 11.4  |
| bytes written a drive transaction | 24,215        | 20,711   | 1.17  |
| kept after the drive              | 230 MB        | 283 MB   | 0.8   |

* **The node count does not come down.** 55 reclaim iterations at 10M
  rewrote the sparse nodes but did not merge them: 420,636 key nodes for
  333,334 keys, under one live key a key node (the twin: about 9).
  This is 023-04's X3 "about B/2 times the twin's nodes", now at 10M.
* **At 10M it costs bytes and time**, not only memory: each live node is
  rewritten once an iteration, and there are 11 times as many, so a
  transaction of the same overwrites writes 3.3 times the bytes and the
  stream holds 2.6 times as much. At 1M the drive's own bytes dominate
  and the difference does not show.
* **Not measured:** milder shapes (every 2nd or 3rd key deleted), or
  deletes spread over time with puts between them. Every 30th left is a
  hard case, but a realistic one for an expiry by key range or a cleanup
  of most of a table.


## 6. A start after the mass delete (measurement 4)

A new JVM on the database at the end of section 4, at the default
startup distance of 50 MB.

| Start                                       | ms    | kept    | stream length |
|---|---|---|---|
| 2026.4, 10M, after the delete and drive     | 1,733 | 1.61 GB | 22.1 GB       |
| 2026.4, 10M, after the fill                 | 2,097 | 6.79 GB | 7.2 GB        |
| 2026.4, 1M, after the delete and drive      | 1,208 | 0.30 GB | 2.5 GB        |
| 2026.3, 10M, after its delete and drive     | 3,912 | 9.89 GB | 11.1 GB       |
| 2026.3, 10M, files out of the OS cache      | 6,041 | 6.79 GB | 7.2 GB        |

* After the start, 2026.4 scans the first 1,000 keys in 5.9 ms and the 1M
  keys in 2.2 s; 2026.3 takes 2.6 s for the first 1,000.
* **The last row** was not planned: 2026.3's 10M database waited about
  50 minutes, while about 80 GB were written by other runs, before its
  mass delete, so its files had left the OS cache. Its start took 6.0 s
  against 2.1 s warm, and the full scan before its delete 63 s against
  31 s. It is the one start here that read from the SSD. The start code
  is not one of 023's changes, so 2026.4 should be close; not measured.
* The start does not grow with the stream: 22.1 GB written and 1.6 GB
  kept start faster than 7.2 GB written and 6.8 GB kept, as the bounded
  start promises (007-05; 005-57).


## 7. Keys in time order: the last touch

Added for CL7 (024-01, section 4.7: "the record sizes at 10M keys in time
order"). A fill of N keys in key order, then the FIFO of section 2: each
transaction puts 100 keys after every key so far and deletes the 100
oldest, so N keys stay live; 200,000 transactions at 10M, 100,000 at 1M.

| FIFO                        | 2026.4, 10M | 2026.3, 10M | 2026.4, 1M |
|---|---|---|---|
| reclaim iterations          | 2           | 1           | 7          |
| records over 1 MB           | 2           | 29          | 7          |
| largest record              | 206 MB      | 307 MB      | 16.9 MB    |
| slowest commit              | 22,243 ms   | 20,524 ms   | 1,682 ms   |
| commit p99.9                | 4.9 ms      | 5.0 ms      | 4.7 ms     |
| kept, start to end          | 2.34 to 6.43 GB | 2.34 to 8.70 GB | 0.20 to 0.95 GB |
| key nodes at the end        | 789,924     | 2,369,790   | 78,996     |
| dead KEY klongs at the end  | 228         | 20,363,969  | 51         |
| scan of the first 1,000 keys | 3.1 ms     | 6,564 ms    | 2.7 ms     |

* **One huge record at the end of each iteration.** 2026.4 at 10M wrote
  every record under 1 MB but two (under 31 kB before the first): 191 MB
  at about 45,000 transactions
  and 206 MB at about 175,000, each when the iteration count rose. The
  commit that carried each took 20.6 and 22.2 s; commits are serial, so
  every writer waits that long. This is the last touch (023-08, section
  4: one step dirtied 81,018 nodes), not instrumented here but where it
  must be.
* **It grows with the live keys**: 17 MB and 1.7 s at 1M, 191 to 206 MB
  and 21 s at 10M, about 20 bytes a live key. At 100M it would be about
  2 GB and minutes, if linear (not measured). The same happens with 1M
  keys left after section 4's mass delete: 20 records of 17 MB in
  300,000 transactions, the slowest 1.6 s.
* **A fill in key order** has it too: one record of 30 MB and a commit of
  5.7 s at 10M (2026.3: 5.9 s).
* **2026.3** has the same records and more (29 over 1 MB, up to 307 MB),
  and the FIFO's old nodes pile up (2.4M key nodes, 20M dead klongs; the
  first 1,000 keys scan in 6.6 s). 2026.4's FIFO stays clean: 228 dead
  klongs in 10M live keys. So the huge record is old, while the rest of
  021-25's shape is fixed in 2026.4 at 10M too.
* **The iteration is long in time order**: about 130,000 transactions at
  10M, so kept rose from 2.34 to 6.43 GB in 200,000 transactions with 10M
  live keys throughout; it had not levelled off.


## 8. What the numbers say

* **CL1, P8** (024-01, 4.1). After a mass delete of 90 % at 10M, 2026.4
  is back to its twin after about 4 iterations (60,000 drive
  transactions, 2.5 GB written); in between kept peaks at 1.1 times its
  size before the delete, and scans, gets and commits are fine at once
  (3.0 ms for the first 1,000 keys). P8 would remove one of those
  iterations (023-05 P8, section 1), about 13,000 transactions here.
  **The numbers do not ask for P8**: option (a) of 024-01, 4.1 stands.
* **CL2, merges** (024-01, 4.2). The underfill is real at 10M and does
  not heal: 11 to 16 times the twin's nodes after scattered deletes, and
  under further writes 3.3 times the bytes a transaction, 2.6 times the
  stream, 3 to 5 times slower scans, gets and drives. At 1M only the
  memory and scan cost show. So 024-01's "not in 2026.5" now rests on how
  often such deletes happen, not on their cost. With a stable stream
  format (2026.5's theme when this was written; since 2026-11-11 that of
  2026.6, 026; 024-04), merges change the rerun (024-02, section 20, Q1):
  either the format reserves the switch now, or merges come only with a
  versioned record format later. Recommended: decide Q1 in 2026.5, even
  if merges themselves wait.
* **CL7, the last touch** (024-01, 4.7). The largest latency fault
  measured: a 22 s commit and a 206 MB record at 10M keys in time order,
  growing with the live keys, about once an iteration. It is old (2026.3
  too) and no stream format is involved (the touch is not rerun). **The
  numbers ask for CL7 (b), first among the Core's changes.**
* **PF3, reclaim's value reads** (024-01, 9.3). Not measured directly.
  What the runs show: at 10M the stream (1.6 to 6.8 GB) is far above the
  default cache (200 MB), and a get already reads about 25 versions; the
  drive ran at 700 commits a second (350 sparse) with the OS cache warm.
  A probe that counts the loads of reclaim's steps alone (the cache's
  loads before and after each step) and, better, a cold OS cache would
  show what PF3 saves.
* **Beside the CL items.** 2026.4 costs nothing against 2026.3 in puts,
  gets, scans or stream size (section 3). Under steady overwrites the
  stream holds 4.5 to 6 times a fresh database of the same keys (twin:
  1.45 to 1.95 GB against 0.33 GB), and after a random fill of 10M keys
  6 times the data: reclaim's pace, not a CL item, but a number for
  2026.5's aim of proportional storage (024-04, aim 3). The default cache of 200 MB makes a get
  at 10M read about 25 versions. MEM at 10M (327) needs an explanation.


## 9. Not measured

* **100M keys.** A random fill at 19 µs a put and rising would take more
  than an hour and write about 72 GB, on a disk with 119 GB free; it did
  not fit before 07:00. The FIFO extrapolation in section 7 is the only
  number for 100M.
* **s1**, and Linux; a cold OS cache (no `purge` without root), but the
  accident of section 6.
* **Startup distances other than 50 MB**; retain forever; values other
  than 100 bytes; durable commits; more than one writer or reader thread.
* **The cache's tables after a mass delete** (CL6) apart: heap after a GC
  at the end of section 4 is 225 MB against the twin's 218 MB.
* **Reclaim's reads** (PF3) and the lag in a drive of one key a
  transaction (T1's drive): the lag in transactions depends on the
  drive's bytes, so section 4's 60,000 holds for 42 kB a transaction.
* **006-16's CORE across releases**, PF2's write probe, PF4 (long keys).
* **Repeats.** Each figure is one run. The 2026.3 and 2026.4 runs ran
  under the same background load, minutes apart, and agree within 2 %
  where they should; counts (nodes, klongs, bytes, records) are exact and
  repeat.


## 10. Log

2026-11-11, 04:57 to 06:31. Clone at `release-2026.4`; probe written and
checked at 100,000 keys; 1M set 05:03 to 05:09, 10M set 05:10 to 06:15,
the FIFOs 06:15 to 06:29 (10M) and 06:27 to 06:29 (1M). Data directories
deleted after each run; outputs in `03-measurements/out/`. Nothing in the
main tree changed but this file and `03-measurements/`; nothing
committed.

2026-11-13. Status set after the release (coord-1113).
