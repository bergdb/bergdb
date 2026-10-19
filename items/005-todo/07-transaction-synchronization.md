005-07. Synchronization of transactions
=======================================

Status: open. Kind: investigate. Created 2026-10-19.


The task
--------

Think about synchronization for transactions: understand how it works in
the code today, and how it may need to change. The writer, the readers,
reclaim and eviction share one in-memory Dag; the Lean model leaves
concurrency out ("Not in the model: concurrency",
[level4-alignment.md](../../docs/level4-alignment.md), section 1 and 5.8),
so the design lives only in the code, its comments, old notes and tests.


The design so far, from F1-007 and the code
-------------------------------------------

There is no single design document. The pieces, oldest first (paths in
the f1 repo, `a/007-bergdb-261012/`):

* **2008 to 2011, the choice of STM** (`bergdb/doc/log-old/2008-2011-log.txt`,
  about lines 216 to 270 and 560 to 612): optimistic transactions (STM) with
  MVCC, chosen over a single read-write lock, for speed and for replication.
* **2012-01, thoughts on transactions**
  (`bergdb/doc/2012/2012-01-thoughts-on-transactions.txt`): read, compute,
  write; a read-write transaction is a write-only transaction plus a read
  set of key hashes and a read time; a `Transactor` with
  `wasModified(time, keyHash)`: "multiple concurrent read threads without
  any blocking. A single write thread can be assumed."
* **2012-02, two-level STM** (`bergdb/doc/2012/2012-02-two-level-stm.txt`,
  and `2012-02-notes.txt`, about line 230): key STM for the client, node STM
  inside; prepare the transaction outside the locks, then lock briefly,
  check, and apply "only two pointers per node". "Reads are NEVER blocked,
  locks are for set() operations only." Never built as two levels.
* **2012-03 and 2012-04, single writer, multiple readers**
  (`bergdb/doc/2012/2012-03-notes.txt`, `2012-04-notes.txt`, "Todo:
  Synchronization"): a global write lock, changes in place, lock-free reads
  (synchronized node access cost 19 percent on gets and would not scale past
  about five threads); "Document somehow, think through carefully again."
* **2013-01, node pointer and thread synchronization**
  (`bergdb/doc/2013/2013-01-notes.txt`, "Node pointer synch" and "Thread
  synch, DB"; `bergdb/log.md`, 130116 to 130124): striped pointer locks
  (`DB.pointerLocks`, by node hash and pointer index) for loads and
  eviction; "All access to DB should be synched with writeLock except for
  get(), getMany()"; readers do `synchronized (readSync) {}` to see the
  writer's writes; a `volatile short KeyNode.size` as the per-node
  publication point. "Synch bugs are the hardest."
* **2013-02, get operations** (`bergdb/doc/2013/2013-02-notes.txt`, about
  line 100): counting running gets, stopping new ones, waiting for running
  ones (for reclaim and shutdown).
* **2014** (`bergdb/log.md`, 141116): a bug, `Db.warmup(t)` ran outside the
  write lock but used the writer's data; fixed by a separate
  `Trans.warmupGetData`. `bergdb/doc/2014/2014-q3-notes.txt`: a rerun at
  startup needs no STM, "one thread only".
* **2015 code** (`repo/java/src/bergdb/core/Db.java`, `execute` and
  `executeInner`), and today's `java/src/bergdb/core/Db.java`, much the same:
  1. `execute`: `synchronized (readSync) {}`, check the state.
  2. `warmup(t)` outside the lock: read the transaction's keys so the nodes
     are in memory.
  3. `synchronized (writeLock)`: `stmCheckConflicts` (the read set's key
     hashes against `KeyModSet` since the read time; `RerunException` on a
     conflict, and also when the read time is older than the set remembers:
     128,000 hash-time pairs in four bins); `dbClock.transactionBegin()`;
     `putKvs()`; `synchronized (readSync) {}` to publish;
     `dbClock.transactionEnd()` (in a `finally`, which is part of M49);
     `stmRecordKeys`; `store()`; listeners, reclaim's listener.
  4. Readers: `synchronized (readSync) {}`, a lookup time strictly before
     any transaction in progress (`DbClock`, a volatile last transaction
     time), no write lock. The client's `Action` may run more than once
     (`pub/Action.java`: "the core of the STM approach").
* **2026, Levels 3 and 4** (bergdb item 001): reclaim's cuts beside readers
  (admission and expiry of overtaken reads, `levels.md`); eviction under the
  write lock at transaction boundaries, each pointer under its striped lock
  (`PointerLocks`, 128 stripes), the readers' protocol Q8 (J5; register
  M39). `KeyNode.size` is no longer volatile; publication is by `readSync`
  and the clock.


Why it may need to change
-------------------------

* **Frans's principle** (005-01): no rollback of in-memory state; check
  every condition first, and once a transaction gets the go it runs without
  exceptions as long as storage, the JVM and memory work. Today the STM
  check is first, but transformations, loads of evicted nodes and the
  ordinal bound can still fail after the go (M49, M46). Where the go point
  is, and what must be done before it, is a synchronization question as
  much as an exception one.
* **The read path's cost**: item 004 measured that the pointer lock, the
  `readSync` monitor and a shared counter per get cut eight readers'
  throughput to a quarter, and gets scale backwards from four threads to
  eight ([004-01](../004-indirect-swizzling/01-report.md), section 8).
* **The write lock's length**: the sweep runs under it (005-03, 3.2 s
  sweeps), and so do `store()` and the listeners. What must be under it?
* **Warm-up under eviction**: `warmup` loads outside the lock, but a node
  may be evicted again before the writer uses it (the writer then loads
  under the lock). A pin until the transaction is done?
* **The STM window**: a fixed 128,000 key modifications; a long-running
  `Action` under heavy writes always gets a rerun. Is that the right
  bound, and is it documented?
* **The Java memory model**: is every publication point right (the empty
  `synchronized` blocks, the volatile clock, the pointer locks), now that
  slots change under eviction? No proof and no model covers it; only
  tests.
* **More than one writer**, group commit, or durability (sync) outside the
  lock: wanted, or not?


Questions
---------

1. Write down the design as it is: the threads (writer, readers, reclaim,
   eviction, the storage's threads), the locks and monitors, what each
   protects, the publication points, the go point of a transaction. A
   document in `docs/`, the one the 2012 note asked for.
2. Check it: is each shared field accessed under the right lock or
   published correctly? Known races or open doubts?
3. What should change, and in what order: the go point (with 005-01), the
   read path (with item 004 and 005-03), the write lock's scope.
4. Should concurrency enter the model, or a separate small model (TLA+, or
   Lean) of the protocol only?


Done when
---------

A design document of today's synchronization in `docs/`, a list of
problems found, and proposals with their order; the changes themselves are
following work.


First step
----------

Read `Db.execute`, `executeInner`, `getOne`, `DbClock`, `KeyModSet`,
`PointerLocks`, `Eviction` and reclaim's reader admission, and draw the
threads and locks; then read the F1-007 notes listed above.


Size and order
--------------

M for the description and the review; reading, no machine time. Best before
or together with 005-01 (the go point), and before 005-03's fix (the sweep
and the read path).
