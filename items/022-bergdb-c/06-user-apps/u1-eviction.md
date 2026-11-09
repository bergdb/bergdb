# 022-06 U1-3 and U1-4: eviction after a refusal, and under the pins

Created 2026-11-09 by Frans Lundberg. Status: done; both fixed in C.

The black-box user u1 (022-06-1, U1-3 and U1-4) found two faults in
eviction. Its reproductions are in `/Users/f/fl/bench/022/apps/u1/repro/`.
Both are faults of C's own, not of Java. Worker f4 of the session
`022-bergdb-c` fixed them in `evict.c`, `db.c` and `api.c`. Eviction never
writes, so the stream's bytes do not change. What is pinned or detachable
does not change either, and neither does the meaning of `bergdb_stats`'
resident and pinned bytes.

**U1-3, a refused transaction's loads stay resident (medium).** A
transaction refused before its go point left what its warmup loaded in
memory until a later call evicted it. The refusals are `BERGDB_LIMIT`
from the clock, `BERGDB_RERUN` from the STM, and `BERGDB_NOMEM`. The
warmup loads every put key's path and present value. u1's
`budget_after_refusal.c` (2,000 puts over values of 5,000 bytes, a budget
of 100,000 bytes) shows 10,229,632 resident bytes after the refusal and
still after a `bergdb_sync`.

* Cause: `db_execute` evicted only after a commit. Each refusal exit
  returned at once, after `obj_collect`.
* Fix: every refusal exit goes through `refused()`, which evicts as the
  end of a commit does (`db_evict`). Reads had the same gap, also fixed:
  `bergdb_get_one` and `bergdb_get_many` now evict at the end of the call
  when they are refused too (NOMEM, or a stop function's answer out of
  range).
* After the fix, the reproduction stays at 149,632 resident bytes (the
  open's) through both refusals and the sync.
* Java: the warmup's loads call `Eviction.afterLoad(db, false)` (Db's
  load listener; `Trans.WarmupGetData`, not paced). Over the trigger,
  that wakes the eviction thread, which runs batches down to the
  trigger, whether the transaction then commits or is refused. C has no
  thread, so the end of the refused call is where it evicts.

**U1-4, a scan under what must stay is quadratic (medium).** With the
cache size indicator at 1, a full getMany took time that grew with the
square of its keys: 0.22 to 0.57 s for 8,000 keys, against 0.001 s at
the default budget.

* Cause: with a budget under the floor (D, pinned, as after a start with
  the default startup distance), the trigger was the floor plus the gap
  between the watermarks. At a budget of one byte that gap is one byte.
  So each pair that the getMany loaded made a sweep of two rounds over
  the whole node table, and the table grows with D.
* Fix (`evict.c`'s `sweep`, `ev->trigger` and `call_trigger`): when the
  floor raises the trigger, the margin over the floor is now the gap or
  the node table's own bytes (`nt_bytes`), whichever is more. A sweep
  looks at the table's slots, so the next sweep that cannot reach the
  budget comes only after the calls have loaded at least as many bytes
  as the table has. The sweeps' work is then linear in the bytes loaded.
  Above the floor, the resident bytes may now exceed it by up to the
  table's bytes; before, by the gap.
* Java: the trigger is `max(high, pinnedOfLastRound + (high - low))`,
  so the gap is the same one byte. Each reader's load over the trigger
  wakes the eviction thread. Over the trigger plus the gap, the load
  waits up to 2 ms for one batch. A batch is bounded instead (015-67):
  4,096 handles (65,536 under pressure) and 2 ms, on its own thread.
  This is read from the code, not run, as F53 takes no timing runs today.

The hand's work, from the new counter `ev.examined` (the slots the hand
looked at), in `evict_scan_is_linear`'s scans at one byte:

| keys  | before: slots, sweeps | after: slots, sweeps |
|-------|-----------------------|----------------------|
| 1,000 | 512,000, 1,000        | 26,624, 52           |
| 4,000 | 8,192,000, 4,000      | 110,592, 54          |

One short run of u1's `evict_scan.c` (release build, F53 under load),
with a budget of one byte:

| keys   | before        | after   |
|--------|---------------|---------|
| 8,000  | 0.214–0.219 s | 0.015 s |
| 16,000 | (not run)     | 0.032 s |

At a budget of 100,000 bytes, 8,000 keys took 0.015 s; the default
budget took 0.001 s, with nothing loaded.

**Tests** (`t_evict.c`), each failing before its fix:

* `evict_after_refused_transaction`: u1's case in memory. Before: 876,896
  resident bytes after LIMIT and after RERUN, against a trigger of
  100,000. After: 60,104.
* `evict_after_refused_read`: a getMany refused at a value of 500,000
  bytes, and getOnes refused by each allocation failure in turn. Before:
  500,738 resident bytes after the getMany, and two getOnes over the
  trigger. After: 648.
* `evict_alloc_failures`: a new check that the resident bytes are at
  most the trigger after each NOMEM refusal. Before, 465 of 953 refusals
  failed it.
* `evict_scan_is_linear`: the table above. It needs the 4,000-key scan
  to look at no more than 8 times the slots of the 1,000-key scan, and
  at no more than 64 slots per key.

`evict_twins`' and `evict_accounting`'s bound on the resident bytes over
the pinned ones is now the budget or the table's bytes, whichever is
more. With the old bound, `evict_twins` failed 53 checks at budgets of 1
and 2,000 bytes, and `evict_accounting` failed in two of its seeds.

The gate on `2026.4` at `d51d65d` with this change: `C BEFORE COMMIT OK
(533 s)`, F53 under a load of about 9 to 12; `unit` 519 tests (518 in
the release build); `func` 44; `cross quick` OK (23 workloads, 69 crash
cuts, 85 corrupt variants, 2 in turns, 46 budget runs); `writecheck` 0
errors; `corruptset` 63 copies; `allocfail` 628 runs; `examples` OK.
