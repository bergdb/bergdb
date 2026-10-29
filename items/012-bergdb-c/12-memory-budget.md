012-12. Task: the memory budget
===============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done 2026-10-29 03:16** (started 02:00);
approved with 012-01 by Frans's go (012-01, 9.1). In the clone
`/Users/f/fl/bench/012/12-memory/` (main at `a90a1ba`, then `ca9e583`
merged), beside 012-11. Section 6.5 says how "Done when" holds.
Phase D (012-01, section 8). Effort: high. After: 012-10.


# 1. The goal

Level 4 in C: a database larger than its memory. The index nodes and
values that are not pinned are evicted to a budget, and loaded again from
the stream when needed. Rewritten for C, not ported (012-01, 4.1): Java's
`Cache3`, `Eviction` and `Residents` are built for threads and the
garbage collector; C has one caller, and frees as 012-01, 4.5 says.

Done when:

1. **The node table**: node id to the node's handle (012-07's design), the
   canonical object of each node, and the bytes each resident node and
   value takes, counted exactly by the allocator (P8; 012-01, 4.5).
2. **What is pinned**, as Java pins it (levels.md, section 7): the super
   root, D (the index nodes dirty since the startup position), the record
   being written, the newest written top node; and a node in use by the
   call that runs.
3. **Eviction** to the budget at transaction ends and after loads, where
   Java evicts, in the call: a simple policy (CLOCK over the unpinned
   nodes and values, or what Java's capacity controller does, if as
   simple). It runs at the end of the call, a safe point (012-01, 4.5),
   so what it takes is freed at once; an evicted object's handle dies as
   in Java and is freed when no pointer holds it.
4. **The bytes do not change** (P2): every cross workload with budgets from
   a few kilobytes to unlimited gives the same files and dumps as without
   eviction, as Java's `EvictionInvariance` checks for Java.
5. **Larger than memory**: a database of a million keys with a budget of
   a few megabytes runs, its resident bytes stay below the budget plus
   what is pinned, and its reads equal Java's on the same workload.
6. The budget is the option `cache budget` (Java's cache size
   indicator), and `bergdb_stats` reports the resident bytes. It can be
   changed while the database runs (`Db.setCacheSizeIndicator`, 005-52):
   for the run only, and after a decrease the setter evicts at its own
   end, where Java wakes its eviction thread, so that an idle database
   gives the memory back too (P3).


# 2. Read first

* Java: `Cache3` (292 code lines), `Eviction` (401), `Residents` (136),
  `Handle` (73), `NodeCollection`'s loads, `Db`'s `eviction` calls.
* 012-01, 4.5 (memory in C).
* `docs/levels.md`, Level 4 and section 7; 001-08 and 009-05 (the
  alignment of Level 4, with handles); 009-02 (the handle and the
  table); 010-01, P1, P3 and P8.
* `java/stress/EvictionInvariance.java`, `LargerThanMemory.java`.


# 3. The work

1. The node table and the byte counts, beside 012-07's handles.
2. Pinning, and the check that a pinned node is never evicted (a debug
   check under the test build).
3. Eviction in the calls; loads through 012-10's path.
4. The invariance runs, and the larger-than-memory run.


# 4. Tests

The cross sets with small budgets; a C invariance test (the same workload
under several budgets, the same bytes); the larger-than-memory run under
the sanitizers on a smaller size; `leaks` after long runs.


# 5. Notes

* Eviction decides only what is in memory, never the bytes. If a byte
  changes with the budget, the cause is a pointer whose serialized
  reference depends on residency: a bug in C, as Java proved the opposite
  for its handles (009-05).
* Java's default policy depends on timing (P8's noted departure); C's need
  not, and should not.


# 6. Progress

## 6.1 Decisions

1. **Resident bytes** are the allocator's: `MEM_INDEX + MEM_VALUE +
   MEM_HANDLE` (key and top nodes, values, handles, live and dead) plus the
   node table's own arrays (`nt_bytes`), exactly as allocated (P8).
   `bergdb_stats.resident_bytes`. The other maps (`idOf`'s cache of 100,000
   positions, Rule R's `newById`), the write buffer, D's lists and the
   caller's objects are not in it, as Java's `Residents` does not count its
   `HashMap`s. `bergdb_stats.pinned_bytes`: the part that must stay, by a walk
   of D (each pinned object, its handle, what its pointers hold, and the
   table); `bergdb_stats.evicted`: objects evicted and values unswizzled.
2. **What is pinned** is Java's `Eviction.detachable`, ported (`ev_detachable`):
   in the record; the super root; the newest written top node; canonical and
   dirty (D); not at a stream position. A node in use by the call is not
   pinned but counted: eviction runs only at safe points, so an object the
   call holds outlives the eviction of its handle (as a Java reader may finish
   with an evicted object).
3. **The policy** (`evict.h`): Java's capacity controller (BUDGET) made
   deterministic. CLOCK over the node table's slots (the bit `OBJ_REF`, set by
   `ncoll`'s follows, as Java's `touch`), from the hand's last place: an
   empty live handle leaves the table; a pinned key node's written values
   become stream pointers (`unswizzleValues`); a set bit is cleared; anything
   else is evicted (`nt_evict`: `hd_kill` and out of the table) and freed at
   once (`obj_collect`). A sweep runs when the resident bytes are over the
   trigger, and stops at the low watermark (0.75 of the budget, Java's
   `LOW`) or after two rounds of the hand. The trigger: the budget; after a
   sweep of two rounds (all that could go has gone), the floor then plus the
   gap between the watermarks if more (Java's `pinnedOfLastRound + (high -
   low)`, the floor measured by the allocator); the budget again when D has
   lost nodes since (the floor is old). Java's time bound (2 ms), handle bound
   (4,096) and thread are left out: C evicts in the call until the resident
   bytes are at the low watermark or nothing more can go, and its choices
   depend on the calls only, never on timing (section 5).
4. **Where it runs** (Java's places, in the calls): the end of `db_execute`
   (`afterTransaction`, before reclaim's `transactionCompleted`, as Java's,
   and so also after each reclaim step's internal transaction); the end of
   `db_open` (after the startup's loads); the end of the API's `getOne` and
   `getMany` (`afterLoad`), and between `getMany`'s pairs (a safe point: the
   chain counts its links, and each pair is copied when added), so that a
   long scan stays within the budget; and `setCacheSizeIndicator`, which
   evicts at its end on an active database (005-52, P3). Not inside a
   transaction, and not in reclaim's own reads (`db_get_many` and
   `db_get_one` called by reclaim do not evict; only the API's do). A floor
   found between pairs lasts for the call only (`call_trigger`), as the
   chain's objects go when the call ends.
5. **Admission** (`Eviction.largeValueCreated`, `recordWritten`): Db's
   pointer-created listener keeps the writer's values over 1 MiB, counted,
   until the record is written; then those pointers and the record's key
   nodes' pointers to written large values become stream pointers. Always,
   as Java's (its schedule is BUDGET also with `noEvict()`).
6. **The budget** is `bergdb_options.cache_size_indicator` (Java's
   `cacheSizeIndicator`); under 1 the open is refused with `AssertionError`
   (`Cache3.setSizeIndicator`'s assert; C's asserts are on). The setter takes
   1 and up (Java's `IllegalArgumentException` under 1), for the run only.
7. **The table shrinks** (`nt_shrink`) after a sweep when it holds under an
   eighth of its slots (from 1,024 slots), so that its bytes follow eviction.
8. **The debug check** (test build): after every eviction run, every pinned
   object is its node's object in the node table and D's are canonical and
   dirty (`ev_check_pins`, an assert); the tests also recount every count
   (`db_recount`) after every call.
9. **Files outside the list**: `getmany.h`/`.c` got a hook (`safe_point`,
   called after `collect` between pairs) for eviction inside the API's
   `getMany`; `include/bergdb.h` got three `bergdb_stats` fields and the
   budget's text. `db.h` has the `struct ev` and four functions
   (`db_evict`, `db_safe_point`, `db_resident_bytes`, `db_pinned_bytes`).

## 6.2 Progress

* 02:00: started; read 012-01 (1, 4.2, 4.5, 6), this plan, 012-07 (6),
  012-10 (6), 012-05 (6), `c/readme.md`, `docs/levels.md` (1, 7), Java's
  `Cache3`, `Eviction`, `Residents`, `Handle`, `EvictionInvariance`,
  `LargerThanMemory`, `Db`'s calls; 012-11's `db.c` changes (read only).
* 02:05 (`0eaad30`): `evict` (the controller, the admission), `ntable`'s
  `nt_evict`, `nt_bytes`, `nt_shrink`; the calls in `db.c` and `api.c`;
  `bergdb_stats.resident_bytes`; `bergdb-run -budget N` (the budget at every
  start, over the workload's) and `-mem` (resident bytes at each segment's
  end, on standard error). C's runs of 12 workloads (Level 2 with restarts
  and reads, CoreSame, Gen seeds, the hand-written ones) with budgets 1,
  4,000, 30,000 and 200,000 bytes: the files and the text of the run without
  a budget, every one (thousands of objects evicted in each).
* 02:10: a larger-than-memory workload (`ltm.py` in the scratchpad: N keys
  in a permuted order, 100 a transaction, node size 30, startup distance 1
  MB, budget in the workload; a restart; 2,000 transactions of 50 random puts
  and deletes; gets at the latest and an old time; full checks at both; a
  restart; gets and a check). 100,000 keys, budget 2 MB: C's text and files
  equal Java's `Run` (C 3.0 s, Java 4.6 s). 1,000,000 keys, budget 4 MB:
  equal to Java's (text: 2,500 gets and three full checks of 981,011 and
  500,100 pairs; files: 1.2 GB), see 6.4.
* 02:12 (`2c01ed7`): tests. `t_evict.c`: the table's evict (written position,
  dead, out, a new live handle), bytes and shrink; `detachable`'s rules;
  twins (no eviction against budgets of 1, 2,000, 20,000 and 200,000 bytes,
  node sizes 8 and 14, and the setter mid-run): the same stream after every
  transaction, the same answers at 60 random past times every 25
  transactions, the recount, the pins, resident at most the trigger and at
  most the budget plus the pinned bytes; a value of 1.5 MiB leaves memory
  with its record and a read loads it without keeping it; the allocation
  failures in turn under a budget of 1 byte (1,598 runs: 488 refused, 1,032
  failed databases, all freed). `f_budget.c` (through `bergdb.h` only):
  budgets of none, 1, 4,000, 50,000 and 400,000 bytes with restarts every
  100 transactions: the same files, `getMany` both ways and at an old time,
  `getOne` at many times; a cold scan of the whole database grows the
  allocator's count by 949 KB without a budget and by 7.5 KB with one of 1
  byte; the setter takes 1.5 MB down to 28 KB in its call.
* 02:13: `cross.sh`'s budget runs: each workload that C runs, run again by
  C with `-budget` (quick: 1 and 20,000; full: 1, 4,000, 64,000 and
  1,000,000), the four budgets at once; the files (`compare_db`: from the
  decided cut for reclaim) and the runner's text must be side A's. **C
  BEFORE COMMIT OK (100 s; 24 budget runs)**.
* 02:15: main merged (012-11 done, `ca9e583`): both sides kept; eviction
  runs before reclaim's `transactionCompleted`, as Java's. Reclaim's code
  holds no object across its internal transactions (the maintenance
  follower keeps ids only; its reads' values are copied before the next
  call), so eviction at their ends is safe. Budget runs of 13 reclaim
  workloads (Level 3 restarts and plain, Gen seeds with retain 1 and 2,
  CoreSame, `reclaim-crash`, `reclaim-sync`; up to 112 cuts and 45,806
  evictions a run): the files and text of no eviction, every one.
* 02:20: pinned bytes (`ev_pinned_bytes`; `-mem` prints the most resident
  bytes over the budget plus the pinned, `maxOver`). It found two lags of
  the trigger, both fixed: a floor stays after D shrinks (now: the budget
  again when D has lost nodes since the floor), and a floor measured between
  `getMany`'s pairs included the chain's objects (a 200 kB value of a
  version the chain held), which go at the call's end (now: such a floor
  lasts for the call only). Since, `maxOver` is 0 in every run (25 workloads
  under 4 budgets, the 100,000 and 1,000,000-key runs). The 100,000-key run
  in the test build (ASan, UBSan): Java's text and files.
* 02:26: **C BEFORE COMMIT OK (136 s; 345 unit tests, 11 functional, the
  quick set with 44 budget runs)**, `a91ec40`.
* 02:28: `cross.sh full C=build/tools-full` (a copy of the test build's
  tools at `a91ec40`) started.

* 02:33: the scale workload (Export's `scale:1000000`: sequential keys,
  startup distance 50 MB, so D holds 23 to 41 MB, far over the budget):
  budget 4 MB 8.6 s, none 4.8 s, the same files and text; the resident bytes
  stay at the pinned bytes (D), as Level 4 says. The cost is not the
  sweeps (without the stale-floor rule 9.3 s) but the loads of what was
  evicted; for 012-15.
* 02:34: `leaks` on the release build's run of the 100,000-key workload:
  nothing of the library's; the tool's parsed workload is freed at its end
  now, but for its `set` lines' copies (96 bytes).

* 03:11: **CROSS full OK: 446 workloads, 1368 crash cuts, 498 corrupt
  variants, 6 in turns, 1784 budget runs, the planted difference at 1164
  was found and explained (2,544 s)**, C's test-build tools of `a91ec40`:
  side B's runs, dumps, crash runs and turns C's (181 workloads with
  reclaim), and each of the 446 workloads run again by C with budgets of 1,
  4,000, 64,000 and 1,000,000 bytes, every one with side A's text and files
  (from the decided cut with reclaim), under the test build's pin check.
  Since `a91ec40` only `tools/run.c` changed (`-mem`'s figure, the
  workload freed).
* 03:14: **C BEFORE COMMIT OK (152 s; 345 unit tests, 11 functional, the
  quick set with 44 budget runs)** on the final code.

## 6.3 Findings

* None in Java. The C-side lags of 6.2, 02:20, were C's own (the floor),
  and changed no byte (the floor decides when to sweep, never what is
  written).

## 6.4 Larger than memory

The 1,000,000-key workload of 6.2 (02:10), C's release build, the final
code, on F53 while `cross.sh full` ran (times indicative):

| | budget 4 MB | no eviction |
|---|---|---|
| resident bytes at most (after any line) | 3,999,972 | 210,539,928 |
| pinned bytes at most | 3,897,488 | 14,196,224 |
| objects evicted and values unswizzled | 3,642,933 | 0 |
| the allocator's peak (the library's memory) | 24.0 MB | 223.8 MB |
| the process's maximum RSS (with the tool's workload text) | 113 MB | 359 MB |
| time | 27.9 s | 21.4 s |

The database is 1.2 GB on disk. Both runs give Java's `Run` text (the gets
and checks) and files byte for byte; Java's run of it took 40 s and 974 MB
of RSS. The resident bytes never exceeded the budget plus the pinned bytes
(`maxOver` 0) and, here, not the budget itself.


## 6.5 Done when, as it holds

1. **The node table and the byte counts**: `ntable` (012-10's, with
   `nt_evict`, `nt_bytes`, `nt_shrink`); the resident bytes are the
   allocator's own counts of the index objects, values and handles and the
   table's arrays (6.1, 1), in `bergdb_stats`.
2. **What is pinned**: Java's `detachable`, ported (6.1, 2); the test
   build's check after every eviction run (`ev_check_pins`); the tests'
   recount after every call; `t_evict.c`'s rules.
3. **Eviction in the call** at transaction ends, after the open's loads,
   after and inside the API's reads, and in the setter (6.1, 3 and 4): a
   CLOCK sweep that depends on the calls only; what it takes is freed at
   once; a dead handle is freed when no pointer holds it (the counts).
4. **The bytes do not change**: `cross.sh full`'s budget runs (1,784: the
   446 workloads under budgets of 1, 4,000, 64,000 and 1,000,000 bytes, 0
   differences);
   `t_evict.c`'s twins (the stream compared after every transaction, budgets
   from 1 byte); `f_budget.c` (budgets with restarts, through the API); the
   C runs of 25 workloads with and without reclaim under 4 budgets each.
5. **Larger than memory**: 1,000,000 keys with a budget of 4 MB (6.4): the
   resident bytes at most 3,999,972, never over the budget plus the pinned
   bytes; Java's reads (2,500 gets, three full checks) and Java's files
   (1.2 GB), byte for byte. Under the sanitizers at 100,000 keys, and
   `leaks`, clean.
6. **The option and the setter**: `cache_size_indicator` (Java's indicator),
   `bergdb_stats.resident_bytes` (and `pinned_bytes`, `evicted`); the setter
   evicts at its end (`f_budget.c`'s `budget_setter`: 1.5 MB to 28 KB in the
   call).

The gate: **C BEFORE COMMIT OK** (152 s, the final code). `cross.sh full
C=` the test build's tools: **CROSS full OK: 446 workloads, 1368 crash
cuts, 498 corrupt variants, 6 in turns, 1784 budget runs, the planted
difference at 1164 was found and explained (2,544 s)**.

**The next step**: 012-13 (the rest of the API). For 012-15: the cost of
eviction when D is far over the budget (the scale workload, 6.2, 02:33:
8.6 s against 4.8 s, from reloads), and C's 24 MB of library memory at 4 MB
of resident bytes (the write buffer of 10 MB, `idOf`'s cache).

## 6.6 For the conductor

* The files of 012-12 (under `items/012-bergdb-c/`): this file; new
  `c/src/evict.{c,h}`, `c/test/unit/t_evict.c`, `c/test/func/f_budget.c`;
  changed `c/src/ntable.{c,h}` (evict, bytes, shrink), `c/src/db.{c,h}`
  (`struct ev`, `ev_init` at the open and the budget's check, the
  pointer-created listener for large values, `ev_record_written` in
  `store`, `db_evict` at the ends of execute and open, the setter, the
  eviction functions, `ev_free` in `free_all`), `c/src/api.c` (`getOne`'s and
  `getMany`'s ends and `getMany`'s safe point, `bergdb_stats`' three
  fields), `c/src/getmany.{c,h}` (the `safe_point` hook), `c/include/bergdb.h`
  (`bergdb_stats`' fields, the budget's text), `c/tools/run.c` (`-budget`,
  `-mem`, the workload freed), `c/test/cross/cross.sh` (the budget runs),
  `c/test/unit/main.c`, `c/test/func/f_api.c` (the tables), `c/readme.md`,
  `c/tools/readme.md`.
* Main is merged at `ca9e583` (012-11); eviction runs before reclaim's
  `transactionCompleted` in `db_execute`, as Java's. 012-13 touches
  `api.c` and `db.c` too: 012-12's lines there are the calls named above.
* Not written, for whoever keeps those texts: 012-05's section 6 (the budget
  runs of `cross.sh`, `bergdb-run -budget` and `-mem`), 012-03's
  `bergdb_stats` (`resident_bytes`, `pinned_bytes`, `evicted`) and the budget
  under 1 refused at the open (`AssertionError`, as Java's `-ea`).
* The larger-than-memory workload's generator is outside the repository
  (`ltm.py` in the scratchpad,
  `/private/tmp/claude-502/-Users-f-fl-repos-f1/84ff067e-dce6-4c28-a354-b5d6389d3c5b/scratchpad/12/ltm.py`);
  012-15 may want it in `test/cross/` with a `cross.sh` set of its own.
