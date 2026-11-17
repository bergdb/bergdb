019-22. Fix: a transaction's warmup keeps a value over 1 MiB in memory
======================================================================

Status: done 2026-11-06, night 006-12. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: before the write lock, `Db.execute` reads the transaction's keys once
(`Db.warmup`) to load their nodes. Its `GetData` (`Trans.Builder`'s
`warmupGetData`) had the cache policy `Dag.CACHE_ALL`, so a key's current
value over 1 MiB, read there, went into its leaf's pointer: a transaction
that replaced a large value brought the old one back into memory, in the
dirty leaf, where it stayed until a batch of the capacity controller took
it, or, with no batch (a budget above the resident bytes), for good.

Why: the admission rule (`Eviction`'s class comment, bergdb item 009, step
3b): a value over 1 MiB is not kept; a get does not cache one
(`Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES`), and after its record the writer
takes the ones it made (`Eviction.recordWritten`; 015-68 for a start's).
The warmup was the one read that kept them.

Source: harness 6.5 of 018-01 (018-05, `EvictionAccountingTester`), its
recount, unit seed 24: "pointer 1 of node 1298967 holds a value of
1126456 bytes (over 1 MiB: not kept)". Traced: `KeyNode.setPointee` from
`NodeCollection.followValuePointer`, from `Db.warmup`.

Frans: none.

Done when: a test that fails before the fix passes after it, and the
harness's recount passes; the stream's bytes unchanged; `before-commit.sh`;
`level4.sh` (full).


Log
---

2026-11-06. Found by harness 6.5 (018-05) in night 006-12, registered and
fixed there.

* Fix: the warmup's cache policy is `CACHE_ALL_EXCEPT_LARGE_VALUE_NODES`,
  a get's. It still loads the index nodes, its purpose; a large value is
  read again by the transaction if it needs it, as by a get.
* Test: `Eviction.testWarmupKeepsNoLargeValue` (unit group): a value of
  1,200 KiB, then a transaction that puts a small value for its key.
  Before the fix one resident pointer held a value over 1 MiB after it;
  after it, none, and the old value reads back.
* P1 to P12 (010-01): no setting, thread or API. Which values a read keeps
  in memory does not change the records: StreamDigest's digests (quick)
  are those of the night's base, 93f83a7 (018-05, section 5).
