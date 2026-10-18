# BergDB Level 4: larger than memory

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-18. WP J8 of
bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md));
the eviction it relies on is in [level4-alignment.md](level4-alignment.md),
section 7.

## Result

`LARGER THAN MEMORY OK`. A database of 20 million keys, 2 GB of values and
an index of 1.07 GB after the load (1.5 GB at the end, with its history),
ran on disk in a JVM capped at 2 GB with the capacity controller's budget at
500 MB: the load, two rounds of uniform and hot updates (8 million puts),
gets and scans warm and cold, two cold restarts, and every key checked after
each restart and at the end, 60 million checks of the whole key space and
4.8 million more reads, all right. The resident bytes stayed at or below
the budget the whole run, and after the first fill between the low
watermark and the budget (374 to 500 MB in every sample); what was live in
the heap, after a full collection at the end of every phase, was 460 to
646 MB, at most 30 percent of the cap. Eviction unswizzled 68 million slots
and released 68 million objects in 115 sweeps, none of which needed a
complete sweep and none ended above the budget (D, pinned, was at most
22 MB). The index alone is three times the budget, the database about six
times.

## The run

`java/stress/LargerThanMemory.java` (2026-10-18 04:00 to 04:58, 57 minutes):

    java -ea -Xmx2g -Dkeys=20000000 -Dbudget=500 -Dsd=10000000 -Ddir=... \
        -cp java/build/bergdb.jar:java/build/stress bergdb.core.LargerThanMemory

On disk (`FileStream`), G1, assertions on. 20 million keys (4-byte binary
ints) with 100-byte values, node size 30, reclaim on with a retention of 2 s
on the run's clock (100 µs between transactions), a startup distance of
10 MB. Level 4's default schedule, the capacity controller, with a budget of
500 MB (`cacheSizeInMb` 500 gives the same). Every value read is checked
against its key and version, an int per key in the heap (80 MB; no copy of
the data). The machine was not quiet: other runs of this item used most of
its ten cores, so the rates below are what a busy machine gave.

| Phase | Work | Time | Rate | Loads |
|---|---|---|---|---|
| Load, random order, 1,000 keys a transaction | 20,000,000 puts | 912 s | 21,935 puts/s | |
| Index size, a scan that caches nothing | 1,613,294 index nodes, 1,071 MB | 202 s | | |
| Uniform updates, 10 puts a transaction | 2,000,000 puts | 665 s | 3,007 puts/s | |
| Hot updates, 90 percent on 1 percent of the keys | 2,000,000 puts | 217 s | 9,224 puts/s | |
| Gets, warm | 1,000,000 | 25.5 s | 39,144/s | 1,871,891 |
| Scans, warm, 10,000 KVs each | 200,000 KVs | 2.8 s | 71,328 KVs/s | |
| Restart 1 | startup 593 ms; 24.3 GB on disk; 30 MB resident | | | |
| Gets, cold | 1,000,000 | 18.2 s | 54,849/s | 1,974,397 |
| Scans, cold | 200,000 KVs | 2.5 s | 80,967 KVs/s | |
| Every key checked | 20,000,000 | 197 s | 101,309/s | |
| Uniform updates | 2,000,000 puts | 402 s | 4,972 puts/s | |
| Hot updates | 2,000,000 puts | 172 s | 11,654 puts/s | |
| Gets, warm | 1,000,000 | 25.8 s | 38,742/s | 1,944,966 |
| Scans, warm | 200,000 KVs | 2.7 s | 74,491 KVs/s | |
| Restart 2 | startup 627 ms; 26.0 GB on disk; 39 MB resident | | | |
| Gets, cold | 1,000,000 | 21.0 s | 47,610/s | 2,035,278 |
| Scans, cold | 200,000 KVs | 1.2 s | 172,923 KVs/s | |
| Every key checked | 20,000,000 | 186 s | 107,351/s | |
| Every key checked, at the end | 20,000,000 | 188 s | 106,662/s | |
| Index size, at the end | 2,156,543 index nodes, 1,525 MB | 181 s | | |

"Warm" gets come right after updates in the same process, "cold" ones right
after a restart; with an index three times the budget, both load about two
versions a get, so they differ little. The startups read only the tail of
the stream (Level 2) and leave 30 and 39 MB resident.

A first run of the same program (02:14 to 03:36, on J7's tree before its
last fix) passed too, with the same checks, the live heap at most 643 MB
and the resident bytes at most the budget; but its sweeps counted only the
objects they released, not those that left the resident set with them, and
its last sweep went from 500 MB down to D, 22 MB. J7's fix (a sweep counts
what leaves with what it releases, `Eviction.drop`) is in the run above,
whose every sweep ended at the low watermark.

## Memory

Sampled every second (342 lines in the run's log, one every 10 s): the
resident bytes as the controller counts them (`Residents`) were at most
500 MB, the budget; the controller swept 115 times, each time when a load
had passed the budget (`Eviction.afterLoad`; the writer's warm-up reads
count too), down to its low watermark, three quarters of the budget, in 1.5 s
on average and 2.2 s at most (175 s in all, 5 percent of the run). The heap
in use after a full collection at the end of every phase was 460 to 646 MB.
G1's collection usage reached the heap's size, 2,139 MB, since it counts the
old generation's garbage until a mixed collection; a histogram of the live
objects during an earlier attempt's load showed about 400 MB of node objects
and arrays, the node table's entries (about 90 MB, not counted in the
budget), and the run's own 160 MB of arrays.

## Limits

* **Writes when the index does not fit cost several times as much.** The
  same program at a million keys (a 53 MB index), once with a budget of
  20 MB and once with 2 GB (nothing evicted), on the same busy machine
  (`-Xmx3g`; 500,000 puts each; J7's tree before its last fix): loading
  22,090 against 53,845 keys a second, uniform updates 6,209 against 29,698
  puts a second, hot updates 9,379 against 51,734; gets 14,787 against
  432,655 a second (warm) and 18,088 against 89,543 (after a restart).
  Forty samples of the writer's stack during the uniform updates under
  pressure: 24 following stream slots, the loads (10 of them reading the
  node's header at the slot's position for its id, before the node table is
  asked, 12 reading the node itself: two reads a load); 6 in the
  controller's sweeps; 5 in `NodeCollection.resolvePointers` (node table
  lookups by id for the slots of the nodes it writes); 8 of the 40 inside
  reclaim's steps. The loads are the price of a cold index; the header read
  could be saved (the id could be kept in the slot when it is unswizzled, or
  cached by position as `resolvePointers` does), an improvement not made
  here.
* **The sweep walks every resident object**, twice: up to 2.2 s at a budget
  of 500 MB. It runs once per quarter of the budget loaded; it is not
  incremental, so a reader or the writer that passes the budget waits for
  it.
* **The node table's entries are not in the budget**: about 90 MB at this
  scale, beside the 500 MB.
* **Reclaim lags at this size.** The stream reached 26 GB on disk for about
  3 GB of live data: an iteration scans every KV at a fraction of the
  stream's growth, and over 20 million keys it takes long (the retention of
  2 s on the run's clock was not the limit). A Level 3 matter, not the
  cache's.
* **The startup distance bounds D only loosely.** D is pinned: eviction never
  takes it. With 10 MB, D's peak here was 22 MB; Level 2's default, 50 MB,
  would let it grow about five times larger. For a small budget the startup
  distance should be smaller (problem.md, R6; levels.md, "Bounds,
  measured").
