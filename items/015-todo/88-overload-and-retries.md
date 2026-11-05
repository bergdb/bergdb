015-88. Investigate: transaction retries
========================================

Status: open; moved from 005-81 on 2026-11-05, with its contents as
they were in 005-81 (Frans's plan, approved 2026-11-05, 07:17); its
files stay in [005-todo/81-overload-and-retries/](../005-todo/81-overload-and-retries/).
Left: Frans's review of sections 2.6 and 3.1, then the rest of
section 8.9. Kind: investigate. Created 2026-10-30 as 005-81. Split on
2026-11-04 at Frans's decision: the broad question, overload,
backpressure and admission control, is now a long-term topic,
[017-06](../017-long-term/06-overload/readme.md); this entry keeps the
retries.

Plan and source review until 2026-11-05; on that day the first step of
section 7 was made: a diagnostic harness in
[81-overload-and-retries/](../005-todo/81-overload-and-retries/) and the hot-key,
disjoint-key and history baselines on s1, in section 8. No change to
`java/`.

Registered at Frans's request after 006-11's STM benchmarks, as "client
overload and transaction retries": keep STM; investigate how clients
experience storage, CPU and memory pressure before choosing a replacement
for the hard-coded retry sleeps. Since the split, that pressure is
017-06's, and this entry is the retries. A change to
`RwTransaction.executeRw()` is the expected first implementation outcome,
but its algorithm, defaults and public settings remain to be decided.

The problem, in short: `executeRw()` reruns a conflicting transaction
after hard-coded exponential sleeps, 10, 20, 40 ms and so on, capped at
10,240 ms. There is no jitter, attempt limit, time budget or setting, so a
client on a hot key can sleep over 20 s across eleven reruns. The same
`RerunException` also fires when a long action outlives `KeyModSet`'s
history, where sleeping longer does not help (section 2.5).

## 1. Purpose and scope

Answer these questions:

* Where does BergDB slow or refuse a client today? What resources and locks
  does the client hold while waiting?
* What retry algorithm should replace the 10 ms exponential sleep? Should
  callers have a retry time budget, an attempt limit, or both? What does
  an exception guarantee about whether the transaction committed?
* How is a rerun after history exhaustion told from a changed-key
  conflict, and does it need a different treatment?

The other questions of the plan before the split moved to 017-06,
section 1: throughput, latency, memory and progress at and above capacity,
and recovery when the load falls; which controls belong in BergDB and
which in the application; and whether bounded admission of client work is
justified beyond a retry change.

The scope is the local Java Pub API over one main storage, with the Core
and storage paths traced underneath. Cover read-write actions and the W
transactions that take the same retry loop (section 2.5), with the waits
an attempt meets: its reads, the commit, durability waits, and eviction
and reclaim as competing maintenance work, as far as they shape a retry's
cost. Replication, which the plan called experimental, was removed on
2026-11-04 (005-11, `16fb228`; Frans: "A with C2 now"), and its waits with
it; a future design is 017-03. The C implementation is not a target of
this entry.

Keep 006-11's conclusion: concurrent STM actions have demonstrated value.
This entry studies retries and the progress of retrying clients, not
removal of STM or a general redesign of the write lock. Resource control
is 017-06's.

## 2. What the code does today

Reviewed 2026-10-30 against the live worktree. At the end of the review,
HEAD is `7d967d7b5483aa65e33a68e46b09e503f37964bb`, including the 005-70
restart fix completed by separate work during this review. The remaining
Java worktree change is an unrelated Javadoc addition in `RwTransaction`.
Freeze and record the actual source, patches and build when experiments
start; this description is a dated review, not a claim about a clean
worktree or a new validation run of 005-70.

The conclusion is qualified: there are deliberately designed controls for
the write buffer and eviction, supported by earlier investigations and
tests. The client paths inspected below contain no common admission limit,
request deadline or overload-result policy. This is evidence about today's
implementation, not proof that no historical design discussion exists.

2026-11-04, at the split. The code was not reviewed again. Where a commit
of 2026-11-04 changed what a section describes, a dated note says so:
005-47 and 005-11 in section 2.1, 005-52 in section 2.4. Sections 2.2,
2.3 (but its first paragraph) and the memory part of 2.4 serve the broad
question and moved to 017-06, section 2; their headings stay here, so that
citations of this section keep working.

### 2.1. Storage write throughput and durability

`Db.executeInner()` prepares and warms up outside `writeLock`, then checks
and applies the transaction under that lock. Its `store()` reaches
`StorageManager.append()` and `BufferedStream.append()` while the database
lock is still held.

The normal main-storage buffer defaults to 10,000,000 bytes, with a 50 ms
buffer time (`StorageManager` constants). More precisely than "wait when
full", `BufferedStream.append()` waits when both:

* the next remaining append does not fit; and
* available space is less than one tenth of the buffer.

Otherwise it copies as much as fits and continues. `wait()` releases the
buffer's monitor, allowing its consumer to drain it, but retains the outer
database write lock. Other commits and background eviction can consequently
wait behind storage. Reads do not generally acquire that lock; they can
still suffer shared-device, cache, CPU or other monitor contention.

The consumer writes outside its monitor and signals after making room.
Its normal flush chunk is at most half the ring buffer; wrapping can split
that into two underlying appends. With `FileStream`, appends include a
force to the device. A slow or stalled append therefore fills the buffer
and eventually stalls committing clients. There is no overall room-wait
deadline. Interrupts are remembered and restored rather than aborting this
wait: it is after the transaction's go point.

2026-11-04 note: since 005-47 (`188facf`), per-append forcing is a
setting of `FileStream`, `FileStream(dir, forceAppends)`, on by default and
in the core API only. With it off, an append is written but not forced,
and the forces stay at a file opened for appends, the last file before a
new one, a cut's deletes and `close()`. The Pub API's file storage forces
each append, as before.

The consumer checks the quarter-full flush rule when it wakes. Appends
currently notify an idle consumer, but do not notify on crossing a quarter
while it is already on its timed wait. This is the known, still-open
005-76 issue. A room wait is therefore not by itself proof that the physical
device is at capacity; delayed flushing can also cause it.

`sync()` asks for an immediate flush and waits for the transaction's
durable byte position. Several callers share flushes (005-48). The
`wait(500)` inside `StorageManager.sync()` is a repeated condition wait,
not a 500 ms overall timeout or an obligatory delay: completion notifies
it. Its interrupt is a wait cancellation; the transaction stays committed.
Measure execution and execution-plus-sync separately.

At the review, `StorageManager.append()` also appended to active replica
buffers in sequence, so a slow active replica could impose another buffer
wait in this same path, and the review said not to generalize
one-main-storage measurements to replication. 2026-11-04 note: replication
was removed (005-11, `16fb228`); that wait is gone. The removed design and
the options for a future one are 017-03.

Sources: [Db.java](../../java/src/bergdb/core/Db.java),
[StorageManager.java](../../java/src/bergdb/storage/StorageManager.java),
[BufferedStream.java](../../java/src/bergdb/storage/BufferedStream.java),
[FileStream.java](../../java/src/bergdb/stream/FileStream.java);
005-46, "Interrupts"; 005-48; 005-76, "The issue".

### 2.2. Storage read throughput

Moved to [017-06](../017-long-term/06-overload/readme.md), section 2.1,
on 2026-11-04: the read path's synchronous I/O, its monitors, and the
absence of a database-wide cap on read I/O. For a retry it matters that a
rerun repeats the action's reads on the calling thread, cache misses
included, and that a load can wait for eviction (section 2.4).

### 2.3. CPU and concurrent client work

`ConnectionImp.rw()` calls the action synchronously. User computation,
reads, index preparation and core transaction construction precede the
serialized commit. Each connection is intended for one thread.

The rest of this section moved to
[017-06](../017-long-term/06-overload/readme.md), section 2.2, on
2026-11-04: no CPU admission controller, `Db.writersWaiting` (which counts
writers but neither caps them nor promises fair order), client concurrency
against the maintenance threads and GC, and 005-65's CPU saturation.

### 2.4. Cache, eviction and total memory

The budget controller uses a high watermark and a low watermark of 75%
of it. Above the trigger, the writer performs an eviction batch at a
transaction boundary; reader loads request background batches, which take
the same database write lock between transactions and yield to waiting
writers. Batches have handle-count limits and a nominal 2 ms time budget.

`Eviction.afterLoad()` first requests a batch. If resident bytes exceed
`trigger + (high - low)`, it then parks in 50 microsecond requests until a
batch finishes, the database stops being active, or a 2 ms deadline passes.
There are three qualifications to the earlier short description:

* Time entering `wake()` and its monitor precedes that deadline.
* A park or a scheduled batch can overrun its requested time when the
  thread is descheduled; 2 ms is not a hard wall-clock bound.
* The limit is per load, not per client call; a scan may load many nodes.

The batch's clock is also checked between steps, not continuously; one
map's work or a monitor wait can overrun it even without descheduling.

This wait is skipped during startup and when the current thread holds the
database write lock. A transaction's boundary handles its eviction work.

2026-11-04 note: 005-52 found that a large transaction's warmup, which
runs before the write lock, waited about as long as the convergence after
a lowered budget, each of its loads parked up to 2 ms for a batch.
Its option (B) makes a warmup's loads wake the eviction thread without
parking; a reader's loads still park. That change was coming, not yet in
`main`, when 005-81 was split (HEAD `2753f80`); see 005-52's log for its
state.

The memory part of this section, `Residents`' accounting against the whole
heap, moved to [017-06](../017-long-term/06-overload/readme.md),
section 2.3, on 2026-11-04.

Sources: [Eviction.java](../../java/src/bergdb/core/Eviction.java);
009-02; 005-52; 010-01, P1.

### 2.5. Transaction retries: exact current policy

The primary change candidate is
[RwTransaction.executeRw()](../../java/src/bergdb/pubimp/RwTransaction.java).
For each call:

1. Start `sleepTime = 10` milliseconds and `runCount = 0`.
2. Run the action if present, prepare indexes, build the core transaction,
   and call `Db.execute()`.
3. On `RerunException` from that call, reset the appropriate environment,
   clear outputs, and sleep.
4. After sleeping, double `sleepTime` if its old value is less than
   10,000 ms. Repeat until an attempt commits.

The requested sleeps after successive conflicts are:

    10, 20, 40, 80, 160, 320, 640, 1,280, 2,560, 5,120,
    10,240, 10,240, ... milliseconds

The comparison occurs before doubling, so the actual cap is 10,240 ms,
not 10,000 ms. The first ten sleeps sum to 10,230 ms; the first eleven
sum to 20,470 ms, before action execution, I/O, lock waits and scheduler
delays. The backoff resets for each new transaction.

There is no jitter, early wake on reduced contention, attempt limit,
elapsed-time limit, capacity signal or connection setting. An interrupt
during the sleep restores the interrupt flag and throws `DbException`.
The failed attempt was refused before mutation; the database remains usable.

The loop also serves `WTransaction.execute()` when it has object operations
that require index preparation. A simple write without those operations
takes another path. Cover both call sites when changing this method.

A rerun is not necessarily a same-key collision: `KeyModSet.modifiedAfter()`
also returns true when a read time is older than its retained history.
It has four rotating bins with a nominal total of 128,000 recorded
key-hash/time additions, not a fixed duration or number of distinct keys.
The same exception reports both cases. A long action under unrelated
writes can exhaust that history; sleeping longer need not help it.

The environment reset sets `firstRead = true` and `readTime = -1`.
It does not select the next snapshot before sleeping: the next read
selects it. Preserve fresh reads and successful-attempt-only outputs.
RW retry repeats the action; W retry retains user operations and rebuilds
index information. Arbitrary external side effects in an action are not
rolled back by a refusal.

006-11, section 10.3 measured a largest whole-call latency of 10,258.8 ms
and a worker with only one completion in a three-second hot-key window,
despite a low average attempts/commit. It did not trace individual sleeps.
That observation must not be described as proof of one 10.24-second sleep;
several accumulating sleeps can also explain it.

2026-11-05 note: section 8 traced the sleeps. The stock hot-key runs on
s1 reproduce a whole-call latency of 10.23 s: one request of eleven
attempts, whose ten sleeps request 10 + 20 + ... + 5,120 = 10,230 ms,
measured in the probe build as asked plus about 0.2 ms each. Several
accumulating sleeps, not one 10.24 s sleep.

Sources: `RwTransaction.executeRw()`,
[WTransaction.java](../../java/src/bergdb/pubimp/WTransaction.java),
[RwEnvironmentImp.java](../../java/src/bergdb/pubimp/RwEnvironmentImp.java)
(`prepareForRWRerun/prepareForWRerun/get/createTrans`),
`Db.stmCheckConflicts()`,
[KeyModSet.java](../../java/src/bergdb/core/KeyModSet.java);
006-11, sections 10.3 and 10.7.

### 2.6. A retrying attempt's wait points

2026-11-05, deliverable 1's map, read from the source at `0c6c4be` (after
005-52's option B) and checked against section 8's runs. One attempt of
`executeRw()`, in order, on the caller's thread:

1. **The action** (RW only): the user's reads and work. The first read
   picks the snapshot. Reads take no database lock; a node load is
   synchronous I/O, and a reader's load may park up to about 2 ms for an
   eviction batch (section 2.4). A rerun repeats all of it.
2. **Index entries and the core transaction**: `env.indexEntries()` (the
   internal reads of indexes) and `env.createTrans()`; no lock.
3. **`Db.execute()`**: an empty `synchronized (readSync) {}`, the state
   check, then `executeInner()`: `checkSize()` and `warmup()`, which reads
   every write key at the newest lookup time with no lock held; since
   005-52 (`0c6c4be`) the warmup's loads do not park for eviction.
4. **`Db.writeLock`**: `writersWaiting` is counted, then the monitor is
   taken. The wait is for whoever holds it: another writer's whole
   commit, including its buffer-room wait (section 2.1), its inline
   eviction batch and reclaim's steps and internal transactions, or the
   eviction thread's batch. No deadline, and not interruptible.
5. **The checks under the lock**: the state again, the top-node ordinal
   bound, `checkDirtyNodes()` (a cheap bound, or a walk that can load
   paths for a large transaction), `x.begin()`, then
   `stmCheckConflicts()`. **A refused attempt is refused here**, after it
   has waited for the lock and paid the preflight: the order is the one
   006-11, section 9.4 proposes to change.
6. **The go point** (`dbClock.transactionBegin()`): after it nothing
   refuses; `putKvs()`, `store()` with its buffer-room wait, the recorded
   write hashes, eviction and reclaim run to the end or fail the database.
7. **After a refusal**: `prepareForRWRerun()` or `prepareForWRerun()`,
   `clearOutput()`, then `Thread.sleep()` with the doubling time. The
   caller holds no database lock and no monitor while it sleeps; it holds
   its connection's thread, the environment (a W transaction's user
   operations) and whatever the action keeps. An interrupt here refuses
   the call with `DbException` and restores the flag.
8. **After the commit**, if the caller asks: `sync()` waits for the durable
   position (section 2.1); its interrupt ends the wait, the transaction
   stays committed.

What the runs add (section 8): on a resident hot key, a refused attempt's
`Db.execute()` (steps 3 to 5) took 54 to 268 us on s1 on average per
run, of which the wait for the busy writer's lock was 10% to 78%
(section 8.8); the requested sleep was over 99.8% of the time between
attempts, and the measured `Thread.sleep()` overshot the request by 0.17
to 0.34 ms. The policy's sleeps, not the refused work, are where a
retrying client's time goes on this workload. Storage waits in steps 4
and 6 did not take part: memory storage, no eviction.

## 3. Establish the client contract first

Propose and review a short contract before selecting public settings.
Before the split the contract had six points. Two of them and part of a
third, the bound on outstanding work, where an admission wait occurs, and
the drain after a burst, are about admission and moved to
[017-06](../017-long-term/06-overload/readme.md), section 3. The points
the retries need stay:

1. **Specify refusal precisely.** An admission refusal or exhausted retry
   budget should mean that this transaction did not commit. It is not a
   storage failure and must not fail the database. Distinguish it from
   actual I/O/corruption failure and from cancellation of a durability wait.
2. **Respect the go point.** `Db.executeInner()` changes memory without
   rollback once its checks have passed. A deadline must not throw out of
   the later append/eviction/reclaim path as an ordinary overload refusal.
   Existing monitor acquisition, synchronous I/O and arbitrary action code
   have no hard overall deadline. Merely adding a timer in `executeRw()`
   cannot promise a hard timeout for the whole call. Distinguish a retry
   time budget, a pre-commit deadline, and a durability-wait timeout.
3. **Preserve progress.** Measure per-client completion gaps and fairness,
   including fresh callers competing with retriers. Shorter sleeps may
   improve latency but waste CPU on doomed attempts. Define acceptable
   throughput/latency tradeoffs from the baseline, not from one mean.
4. **Be observable.** Expose enough evidence to distinguish conflicts,
   history exhaustion, storage waits, CPU saturation and eviction pressure,
   without expensive always-on tracing.

Tentative API placement: caller patience as a per-call option or connection
default; shared resource limits, if any, at the database level (017-06).
If a connection setting is chosen, specify it on the public `Connection`
API and implement it in `ConnectionImp`; an implementation-only knob is
insufficient. Keep the number of settings small. A maximum-attempt setting
may be useful, but "a few attempts" alone gives no predictable time budget.

### 3.1. A draft of the contract

2026-11-05, deliverable 1's second half, for Frans's review; not decided.
First, what a caller of `Connection.rw(action)` (and of a W transaction
with object operations) gets today, from the code at `0c6c4be`:

| Outcome | When | Committed? | Database |
|---|---|---|---|
| Returns | an attempt passed the go point | yes; durable after `sync()` | goes on |
| Waits, without bound | each attempt refused, under load (8.5, 8.6) | not yet | goes on |
| The action's exception | thrown in any attempt | no | goes on |
| `DbException`, interrupted | an interrupt during a retry sleep | no; flag set | goes on |
| `DbStoppingException`, `DbFailedException` | at `Db.execute()`'s state checks | no | stopping or failed |
| `DbException`, top ordinals | the bound of 005-02 | no | takes no more transactions |
| A failure after the go point | storage, memory, a bug | unknown to the caller | failed |
| `sync()` interrupted | during the durability wait | yes; durability unknown | goes on |

`RerunException` never reaches the caller: the loop retries it without
end. Earlier attempts' side effects outside the database stand in every
row.

Proposed, as the frame for the retry variants (section 4):

1. **One new refusal**: when a retry budget is exhausted, the call throws
   an exception meaning "not committed, the database goes on", thrown
   only between attempts, never after the go point. Whether it is a
   `DbException` subclass and what it is called is for the proposal.
2. **What a budget bounds**: it is checked before each new attempt and
   clamps the sleep to what remains. It bounds the waiting between
   attempts and the number of new attempts started, not the action, the
   lock wait or the commit (section 2.6, steps 1 to 6); a hard end-to-end
   deadline is not on offer from `executeRw()` alone.
3. **The two reasons told apart**: a changed-key conflict and history
   exhaustion (`KeyModSet.modifiedAfter()` with no bin old enough) are
   different outcomes inside the loop, so that a policy can treat them
   differently; section 8.6 shows why.
4. **Observable per call**: the attempts and the total time slept. Today
   `getRunCount()` is on `pubimp.RwTransaction` only, and the sleeps are
   not recorded; the harness's figures (section 8.1) are cheap enough to
   keep in a call's result, but whether to is for the proposal.
5. **Progress is a measured property, not promised**: the baseline
   (section 8) is the reference for a variant's per-worker completion
   gaps, not a fairness guarantee.

## 4. Retry policies to compare

Use temporary variants over one frozen baseline. Implement the timing
decision separately enough to test with a fake monotonic clock, sleeper
and reproducible random source; avoid ten-second real sleeps in unit tests.

Compare a small initial set:

* **R0: current policy**, unchanged, with requested/actual sleeps measured.
* **R1: one immediate retry, then short capped jitter.** As an experimental
  starting point, let the first conflict retry once without waiting. For
  subsequent conflicts use a saturating exponential ceiling starting at
  50 microseconds, and choose a random delay from zero to that ceiling.
  Try caps of 0.25, 1 and 4 ms; reduce the set after the pilot.
* **R2: capped jitter from the first retry**, with the same timing range,
  to see whether the immediate retry helps or only duplicates wasted work.

These are experiment parameters, not proposed production defaults.
Measure actual wake-up times; asking for microseconds does not guarantee
microsecond sleeps. If `parkNanos` replaces `Thread.sleep`, explicitly
handle interrupts and spurious/early returns and preserve the existing
refusal/interrupt semantics. Cap before multiplication to avoid overflow.

Separately compare an elapsed retry budget and, if useful, a maximum number
of attempts (define whether the first attempt counts). Check before another
attempt and clamp a requested wait to remaining budget. Report deadline
overshoot honestly; a budget checked only between attempts cannot stop a
running callback or a thread blocked acquiring the commit monitor. A final
check before the go point would require deliberate Core integration.

Test one cause at a time: jitter/cap first, exhaustion behaviour second,
shared admission limits only if the overload results justify them (those
results, and an active-attempt permit released across a backoff, are
017-06's, sections 3 and 4).

If hot-key starvation remains, compare a queued/fair admission experiment.
A mutex used only by retriers cannot guarantee progress against fresh
writers that bypass it. Do not run user callbacks under `Db.writeLock`.
Any broader serialization must account for the STM throughput benefits
measured in 006-11.

No adaptive CPU-percentage controller or large collection of tuning
settings is assumed. Evaluate those only if simpler measured controls fail.

## 5. Experiments and measurements

### 5.1. Workloads

Use one connection per worker and fixed, reproducible data/operation
sequences. Start with the two retry cases:

| Case | Deliberate pressure | Important control |
|---|---|---|
| Conflict | Hot counter, skewed keys and different action costs | Disjoint keys; unrelated writes |
| History  | Long action plus many unrelated modifications       | Trace history exhaustion separately |

Include indexed W transactions and RW actions, large versus small
transactions, and a new caller arriving behind retriers. Reuse 006-11's
counter/integrity checks and useful computation. Fixed workers, as in
006-11, are the arrival model of the retry baselines.

The CPU, write, read and memory cases, their combinations with eviction
and reclaim, short bursts followed by quiet recovery, and the other
harnesses to reuse for them moved to
[017-06](../017-long-term/06-overload/readme.md), section 4.1.

### 5.2. Arrival model and attribution

Moved to [017-06](../017-long-term/06-overload/readme.md), section 4.2,
on 2026-11-04: independently scheduled arrivals through a bounded harness
queue, end-to-end latency from the scheduled arrival, the load levels
around capacity, and controlled slow-stream wrappers.

### 5.3. What to record

* p50, p95, p99, p99.9 and maximum whole-call latency, separately for
  successful and refused requests; per-client completions and longest
  completion gap. (End-to-end latency from a scheduled arrival, the
  counts of offered and admitted requests, and drain/recovery time are
  017-06's, section 4.3.)
* Attempts per committed and per refused request; retry reason, requested
  and actual wait, cumulative backoff, snapshot age and history coverage.
  Existing `RerunException` carries only a hash, and `getRunCount()` is
  filled on success; add diagnostic counters to variants as necessary.
* Time in action/preparation, warmup, commit-lock acquisition and holding,
  buffer-room wait, underlying append/force, sync, read I/O and eviction.
  Keep overlapping times distinct: a buffer wait is part of lock holding.

Use existing `takeRoomWaits()`, eviction figures and writer counts where
their semantics fit. In particular, `takeRoomWaits()` measures from the
first room wait through completion of that append, not just the sum of
individual `wait()` calls. Instrument separately if that distinction matters.
Time `wake()` separately from the subsequent eviction park.

Do not make diagnostic probes the basis for performance conclusions without
an overhead check. Compare uninstrumented builds for final throughput and
latency; use targeted diagnostics to explain them. Keep new metrics cheap
and avoid a contended global counter on every fast read.

### 5.4. Reproducibility and correctness

Freeze source, runtime, heap/GC, cache/startup settings, retention, buffer
settings, workload seeds, arrival schedule, queue and concurrency caps.
Keep baseline and variant data directories separate. Run at least three
fresh-JVM repetitions of the selected comparisons in alternating order on
a quiet machine; record CPU/background activity and separate runs that
miss the stated conditions.

Verify final values against acknowledged commits, validate each transaction's
invariants, and check a sync/reopen subset. Account for every scheduled
request exactly once. Failures and watchdog expiry are results, not samples
to omit. Record durable completion separately from committed completion.

## 6. Implementation checks and decision criteria

A later `executeRw()` change needs regression tests that force conflicts
and cover:

* uncontended success without a retry wait; one conflict; repeated conflicts;
* exact cap/overflow and budget/attempt boundaries with fake time;
* fresh snapshot and output reset across RW retries, and preservation of
  user operations with rebuilt indexes across W retries;
* interrupted waiting with the flag restored, spurious wake-ups if parking,
  and database stop/failure while waiting;
* exhausted retries reporting no commit, leaving the database usable and
  leaking no admission permits or retained request state;
* callback exceptions propagating normally and no accidental swallowing of
  failures outside the current `Db.execute()` retry scope;
* a history-exhaustion case distinct from a true changed-key conflict.

Use existing `PubTester.testRw2` and interrupt tests as starting points.
Do not weaken STM validation or reset its history to reduce retry counts.
The 005-70 fix, now committed separately as `7d967d7`, must be present
consistently in both comparison builds.

If the implementation adds a pre-go deadline or admission permit, also test
contention at that boundary, nested calls, shutdown, exceptions, and the
maintenance paths. A pre-go refusal leaves data/stream unchanged; a commit
whose sync wait ends is still a commit. Test these outcomes, not just which
exception class appeared.

Before selecting a default, report:

* whether the long idle backoff and unfair progress improve;
* throughput and latency across uncontended, useful parallel and hot-key
  cases, not just a single aggregate throughput number;
* overhead and regressions with uncertainty; a repeatable loss above about
  5% on uncontended or independent workloads warrants investigation, while
  a smaller change is not automatically zero cost;
* bounds actually enforced (requests, bytes, attempts, waits), their limits
  under scheduler/I/O delays, and recovery after overload;
* added production lines, public settings, synchronization, timers and
  maintenance burden, together with the smallest supported recommendation.

What acceptable overload means, and that the 20 ms internal-pause target is
not a promise of end-to-end service, is 017-06's, section 4.5.

Any production Java change runs `java/before-commit.sh` and must print
`BEFORE COMMIT OK`, plus targeted performance comparisons. Changes to
buffering/reclaim or eviction additionally run the relevant level scripts
(Levels 2/3 or 4) and StreamDigest for deterministic serial input.
Concurrency scheduling may change commit order; do not demand byte equality
between different concurrent histories. No Lean concurrency proof is implied.

## 7. First step, deliverables and related work

First implement a small diagnostic extension of 006-11's harness in this
item's support directory, over an isolated baseline. Reproduce the hot-key
latency while recording each request's attempts and actual sleep time.
Pair it with a disjoint-key case. This tests the measurement method before
selecting a policy. (The plan's first step went on with bounded,
independently scheduled arrivals and a controlled slow-append case; they
are 017-06's first step now.)

2026-11-05: this first step is done, in section 8, with the history case
added. Deliverable 1 has a first draft (sections 2.6 and 3.1), not yet
reviewed; deliverable 2 has its hot-key, disjoint-key and history runs
(sections 8.3 to 8.6), the file, durable and reopen runs (8.7) and the
lock wait and refusal reasons (8.8).

Deliver in order:

1. A reviewed map of wait points and the proposed client contract, extending
   section 2 with any findings from the diagnostic runs.
2. A baseline report for the hot-key, disjoint-key and history cases with
   raw results and correctness checks, identifying where a retrying
   client's time goes. (The overload/recovery report is 017-06's.)
3. A measured comparison of the small retry variants and a concrete
   `executeRw()` change proposal, including public API/defaults if needed.

The plan's deliverable 4, an explicit decision on whether further database
admission controls are needed, is 017-06's (section 5).

Done when the source findings that the retries rely on are checked by the
relevant probes, the measurements support a retry recommendation, and the
`executeRw()` change proposal has Frans's decision, with every remaining
implementation recorded as a decision or a linked follow-up. A completed
plan alone does not close the investigation. An overload policy is not a
condition: it is 017-06's.

Related work:

* [017-06](../017-long-term/06-overload/readme.md): overload, backpressure
  and admission control, split from this entry on 2026-11-04.
* [006-11](../006-2026-q4/11-stm-concurrency.md), sections 9 and 10:
  STM critical section, benefits/costs and the hot-key evidence.
* [005-07](../005-todo/07-transaction-synchronization.md), "Questions": the broader
  synchronization investigation this entry cited, dropped on 2026-11-04 as
  obsolete since handles (009); today's synchronization is reviewed in
  [016-07](../016-release-2026-2/07-concurrency.md). This entry owned
  overload and retries before the split; it owns the retries now.
* [005-46](../005-todo/46-stream-file-lock.md), "Interrupts":
  storage/read concurrency and cancellation boundaries.
* [005-48](../005-todo/48-group-commit.md): group commit.
* [005-52](../005-todo/52-cache-size-while-running.md): a transaction's warmup and the
  eviction park (section 2.4); its pause probe is in 017-06's related work.
* [005-70](../005-todo/70-keymodset-after-start.md): STM restart fix, done separately
  in `7d967d7`; include it in the new baseline.
* [005-76](../005-todo/76-wake-at-a-quarter.md), "The issue": a known source of
  buffer waits before physical storage is necessarily saturated.
* [010-01](../010-principles/01-principles.md), P1 and P3:
  bounded internal pauses and calm when idle.

## 8. The harness and the first baselines

2026-11-05, section 7's first step, approved by Frans that morning:
"005-81 (retries) gets its harness and the hot-key and disjoint-key
baselines, timed on s1." By Claude (Opus 5.5, Claude Code).

### 8.1. What was built

In [81-overload-and-retries/](../005-todo/81-overload-and-retries/):

* `RetryBench.java`: 006-11's `RwBench` (006-11, section 10), with its
  workload, checks and timing unchanged, and per request: the number of
  attempts (the action's invocations, checked against `getRunCount()`),
  the time between attempts as the action sees it (from the end of one
  invocation to the start of the next: the refused commit, the rerun
  reset and the sleep), each worker's longest gap between completions,
  and a CSV row for every request of more than one attempt. A new option,
  `longActionMs=N`, makes worker 0 sleep N ms in its action after its
  reads: the history case. The 45 s drain limit is a setting,
  `drainSeconds` (default 180 s). With file storage, `reopen=true` closes
  the database after the run, starts it again from its files and repeats
  the checks (section 5.4's reopen subset; added at 07:40 for 8.7).
* `make-probe.py`: makes the probe build from a copy of the source (never
  the repo's `java/`): a static hook `RwTransaction.retryProbe`, called
  after each retry sleep with the run count, the requested sleep, the
  measured `Thread.sleep()` and the refused `Db.execute()` call. The policy
  is unchanged. The harness finds the hook by reflection; on a stock jar
  it runs without it.
* `make-probe-db.py` (added at 07:50 for section 8.8; jar SHA-256
  `bb2f83d5…7653`): on top of
  `make-probe.py`, two static hooks in `Db`: `lockWaitProbe`, each
  attempt's wait for `Db.writeLock` in `executeInner()`, and
  `rerunReasonProbe`, the reason of each refusal, a changed key or
  history exhaustion (the read time older than `KeyModSet`'s oldest bin,
  where `modifiedAfter()` answers yes for any key). The jar with both
  patches is the "probe2" build.
* `run-s1.sh`: compiles the harness against the jars and runs the cases
  with the stock and the probe jar in turns (the order reversed on even
  repetitions; `BUILDS` names the builds, default `stock probe`); stops
  if another JVM runs; logs the load before each run;
  with `storage=file`, gives each run an empty data directory and removes
  it after.
* `summarize.py`: the tables below from a session directory.

The two builds are the isolated baseline: the stock jar, unchanged, for
the timing, and the probe jar to explain it; their rates are compared as
the overhead check.

### 8.2. Method

* Source: `git archive` of `0c6c4be` (HEAD that morning, with 005-52's
  option B), built on s1 by `java/build.sh` with JDK 27 and 005-47's
  `unzip` shim on `PATH` for the build only. Jar SHA-256: stock
  `b4f49819…23af7`, probe `61669197…aacc0`.
* s1: 2 vCPUs, 3.8 GB, JDK 27 (`/opt/bergdb-bench/jdk-27`). JVM:
  `-Xms1500m -Xmx1500m -XX:+UseZGC -da`. Before the first session no other
  JVM ran and the load was 0.06; `run-s1.sh` checked before every run
  that no other JVM ran. The load during the sessions, 0.8 to 2.4, is
  their own runs.
* Workload (006-11's): 4,096 counters, `reads=8`, `work=3000` (8.9 us of
  computation on s1, median of the runs' calibrations, 8.7 to 9.7; 9.4 us
  on F53 in 006-11), memory storage, retention
  forever, no eviction; `seconds=10` after `warmupSeconds=2`; one
  connection per worker; fixed seeds. `hot`: 90% of the actions write
  counter 0; `partitioned`: disjoint keys per worker. Threads 2 (one per
  vCPU) and 4 (oversubscribed; a sleeping worker uses no CPU).
* Every run verified the sum of the counters against every commit and
  recomputed the stored work; the attempts counted by the action matched
  `getRunCount()` for every request; in the probe build the hook's
  retries matched the attempts.
* Raw outputs: s1 `/opt/bergdb-bench/005-81/out/SESSION/`, copied to F53
  `/Users/f/fl/bench/005-81/2026-11-05/`. Each run's directory has
  `result.json`, `retried-requests.csv`, `stderr.txt` and `gc.log`; the
  session's `identity.txt` has the hashes, `runs.txt` the load and the
  summary lines.

The build, from the repo on F53 and then on s1:

    git archive --format=tar.gz -o bergdb-0c6c4be.tar.gz 0c6c4be java
    # copy it, RetryBench.java, run-s1.sh and make-probe.py to
    # s1:/opt/bergdb-bench/005-81/in/; then, in /opt/bergdb-bench/005-81:
    for b in stock probe; do mkdir $b; tar -xzf in/bergdb-0c6c4be.tar.gz -C $b; done
    python3 -I in/make-probe.py probe/java
    for b in stock probe; do (cd $b/java && \
        PATH=/opt/bergdb-bench/jdk-27/bin:/opt/bergdb-bench/005-47/bin:$PATH \
        sh build.sh); done

The sessions, in `/opt/bergdb-bench/005-81` on s1:

    sh in/run-s1.sh main 3 "hot:2 partitioned:2 hot:4 partitioned:4" \
        reads=8 work=3000 seconds=10 warmupSeconds=2
    sh in/run-s1.sh ref 3 hot:1 reads=8 work=3000 seconds=10 warmupSeconds=2
    sh in/run-s1.sh history-1000 2 partitioned:2 reads=8 work=3000 \
        seconds=10 warmupSeconds=2 longActionMs=1000

and `history-3000` and `history-6000` alike; for section 8.7:

    sh in/run-s1.sh file-append 2 "hot:2 partitioned:2" reads=8 work=3000 \
        seconds=10 warmupSeconds=2 storage=file reopen=true
    sh in/run-s1.sh file-durable 2 "hot:2 partitioned:2" reads=8 work=3000 \
        seconds=10 warmupSeconds=2 storage=file durable=true reopen=true

and for section 8.8, after building `probe2/` as `probe/` above, with
`make-probe-db.py` applied after `make-probe.py`:

    BUILDS="stock probe2" sh in/run-s1.sh probe2-hot 2 "hot:2 hot:4" \
        reads=8 work=3000 seconds=10 warmupSeconds=2
    BUILDS="stock probe2" sh in/run-s1.sh probe2-history-3000 2 \
        partitioned:2 reads=8 work=3000 seconds=10 warmupSeconds=2 longActionMs=3000

Then, on F53:
`python3 -I summarize.py /Users/f/fl/bench/005-81/2026-11-05/main`.

The session `main` ran the harness before `longActionMs` was added
(SHA-256 `dcc8ead2…2bf9`, kept in `out/main/RetryBench.java`); `ref` and
the history sessions ran the one of the first commit (`89619c52…d26b`);
the file sessions the one with `reopen` (`1bc32a8a…9b5d`, committed
second); the probe2 sessions the one with the Db hooks (`84ed9d7a…eb9d`,
committed third). Each session's `identity.txt` has its hash. The additions are options, off by default. The smoke sessions (`smoke`,
`smoke-file`, `smoke-probe2`; 2 s windows), each before the first use of
a new option or build, are kept with the outputs and not reported.

### 8.3. Hot key and disjoint keys

Session `main`, 07:24 to 07:31, 24 runs: four cases, two builds, three
repetitions; all passed their checks. Medians of three runs, ranges in
parentheses; s1, 2 vCPUs. "Active/s" counts the commits that ended inside
the 10 s window; latency is the whole call, all attempts and sleeps
included; percentiles are histogram upper bounds.

| Case, build | Active/s | p50 us | p99 us | Max latency ms | Retried requests | CPU cores |
|---|--:|--:|--:|---|---|--:|
| hot t2 stock | 37,535 (37,315–37,687) | 24.6 | 61.4 | 10,233, 10,233, 10,233 | 6, 1, 1 | 1.07 |
| hot t2 probe | 37,165 (36,378–38,590) | 24.6 | 61.4 | 5,115, 5,116, 10,234 | 23, 31, 1 | 1.07 |
| hot t4 stock | 36,383 (36,240–38,780) | 24.6 | 65.5 | 10,236, 10,237, 10,235 | 9, 33, 34 | 1.07 |
| hot t4 probe | 38,631 (36,827–38,769) | 23.6 | 59.4 | 10,233, 10,236, 10,236 | 72, 29, 45 | 1.05 |
| partitioned t2 stock | 54,978 (44,531–56,294) | 26.6 | 94.2 | 5.1, 22.8, 9.3 | 0, 0, 0 | 1.91 |
| partitioned t2 probe | 52,652 (51,296–61,527) | 26.6 | 102.4 | 6.1, 8.1, 6.2 | 0, 0, 0 | 1.91 |
| partitioned t4 stock | 39,339 (39,277–42,315) | 27.6 | 2,031.6 | 11.1, 11.1, 15.1 | 0, 0, 0 | 1.47 |
| partitioned t4 probe | 42,831 (40,135–43,624) | 26.6 | 2,031.6 | 12.1, 13.0, 12.1 | 0, 0, 0 | 1.48 |

"CPU cores" is the process's CPU time over the phase, median. A
reference session `ref` (07:31 to 07:33, hot with one worker, so no
conflicts, both builds, three runs each) gave 39,062/s stock (38,345 to
39,402) and 38,064/s probe (37,516 to 38,986), p50 24 us, p99 51 to
59 us, max 1.2 to 2.6 ms, 1.1 cores.

Per worker, the commits inside the window and the longest gap between
two of its completions (ms), each run:

| Run | Commits in the window | Longest completion gap ms |
|---|---|---|
| hot t2 stock 1 | 50,482; 322,672 | 10,233; 1,276 |
| hot t2 stock 2 | 375,354; 0 | 1; 10,233 |
| hot t2 stock 3 | 376,868; 0 | 2; 10,232 |
| hot t2 probe 1 | 169,130; 194,647 | 5,115; 5,112 |
| hot t2 probe 2 | 181,510; 204,393 | 5,115; 5,113 |
| hot t2 probe 3 | 0; 371,646 | 10,234; 2 |
| hot t4 stock 1 | 717; 429; 1,945; 384,705 | 10,236; 10,235; 10,235; 75 |
| hot t4 stock 2 | 1,683; 349,549; 12,473; 122 | 10,233; 152; 10,233; 10,237 |
| hot t4 stock 3 | 7,287; 354,957; 157; 0 | 10,235; 32; 10,235; 10,234 |
| hot t4 probe 1 | 373,690; 5,104; 3,083; 4,436 | 32; 10,232; 10,232; 10,233 |
| hot t4 probe 2 | 1,056; 379,704; 2,410; 4,520 | 10,235; 77; 10,234; 10,234 |
| hot t4 probe 3 | 3,604; 92,808; 31,984; 239,874 | 10,235; 10,232; 10,234; 2,552 |

In the partitioned runs every worker's longest gap was 5 to 22 ms and the
workers' commits were within 12% of each other.

### 8.4. Attempts and sleeps per request

Requests by number of attempts, each run (the first number is the
requests of one attempt):

| Run | Requests by attempts, 1, 2, 3, ... |
|---|---|
| hot t2 stock 1 | 373,150, 4, 0, 0, 0, 0, 0, 1, 0, 0, 1 |
| hot t2 stock 2 | 375,355, then one of 11 |
| hot t2 stock 3 | 376,869, then one of 11 |
| hot t2 probe 1 | 363,756, 19, 2, 0, 0, 0, 0, 0, 0, 2 |
| hot t2 probe 2 | 385,874, 24, 3, 1, 0, 0, 0, 1, 0, 2 |
| hot t2 probe 3 | 371,647, then one of 11 |
| hot t4 stock 1 | 387,791, 3, 2, 1, 0, 0, 0, 0, 0, 0, 3 |
| hot t4 stock 2 | 363,798, 24, 3, 2, 1, 0, 0, 0, 0, 0, 3 |
| hot t4 stock 3 | 362,371, 25, 5, 1, 0, 0, 0, 0, 0, 0, 3 |
| hot t4 probe 1 | 386,245, 57, 8, 2, 2, 0, 0, 0, 0, 0, 3 |
| hot t4 probe 2 | 387,665, 19, 5, 2, 0, 0, 0, 0, 0, 0, 3 |
| hot t4 probe 3 | 368,229, 23, 3, 4, 5, 4, 1, 1, 1, 0, 3 |

The partitioned runs had no retried request. The probe build's sleeps,
summed over each run's retries:

| Run | Retries | Requested ms | Slept ms | Oversleep ms/retry | Refused execute us/retry | Between ms |
|---|--:|--:|--:|--:|--:|--:|
| hot t2 probe 1 | 41 | 10,470 | 10,478.4 | 0.21 | 153 | 10,485.5 |
| hot t2 probe 2 | 58 | 11,890 | 11,899.9 | 0.17 | 97 | 11,906.6 |
| hot t2 probe 3 | 10 | 10,230 | 10,232.2 | 0.22 | 54 | 10,233.0 |
| hot t4 probe 1 | 117 | 31,940 | 31,974.3 | 0.29 | 124 | 31,991.7 |
| hot t4 probe 2 | 65 | 31,170 | 31,191.9 | 0.34 | 156 | 31,204.4 |
| hot t4 probe 3 | 132 | 37,730 | 37,754.2 | 0.18 | 102 | 37,770.1 |

The long requests, every request of 9 or more attempts (the CSV rows;
"begin" is from the start of the window; the measured sleep from the
probe build). The policy requests 2,550 ms of sleep over 9 attempts,
5,110 ms over 10 and 10,230 ms over 11; the probe build's requested sleep
matched that for every row.

| Run | Worker | Begin ms | Latency ms | Attempts | Between attempts ms | Measured sleep ms |
|---|--:|--:|--:|--:|--:|--:|
| hot t2 stock 1 | 0 | 1,327 | 10,233.3 | 11 | 10,232.1 |  |
| hot t2 stock 2 | 1 | 0 | 10,233.4 | 11 | 10,232.7 |  |
| hot t2 stock 3 | 1 | 0 | 10,232.6 | 11 | 10,231.9 |  |
| hot t2 probe 1 | 0 | 316 | 5,115.0 | 10 | 5,113.3 | 5,112.6 |
| hot t2 probe 1 | 1 | 5,431 | 5,112.3 | 10 | 5,111.7 | 5,111.1 |
| hot t2 probe 2 | 0 | 477 | 5,115.9 | 10 | 5,113.6 | 5,112.8 |
| hot t2 probe 2 | 1 | 6,865 | 5,113.8 | 10 | 5,112.8 | 5,112.0 |
| hot t2 probe 3 | 0 | 1 | 10,233.6 | 11 | 10,233.0 | 10,232.2 |
| hot t4 stock 1 | 0 | 35 | 10,236.3 | 11 | 10,233.4 |  |
| hot t4 stock 1 | 1 | 75 | 10,235.8 | 11 | 10,234.4 |  |
| hot t4 stock 1 | 2 | 71 | 10,235.9 | 11 | 10,235.4 |  |
| hot t4 stock 2 | 0 | 86 | 10,233.8 | 11 | 10,233.3 |  |
| hot t4 stock 2 | 2 | 554 | 10,233.8 | 11 | 10,232.3 |  |
| hot t4 stock 2 | 3 | 81 | 10,237.4 | 11 | 10,234.7 |  |
| hot t4 stock 3 | 0 | 548 | 10,235.1 | 11 | 10,232.6 |  |
| hot t4 stock 3 | 2 | 12 | 10,235.1 | 11 | 10,233.6 |  |
| hot t4 stock 3 | 3 | 2 | 10,233.2 | 11 | 10,232.5 |  |
| hot t4 probe 1 | 1 | 425 | 10,232.8 | 11 | 10,232.4 | 10,231.9 |
| hot t4 probe 1 | 2 | 458 | 10,232.8 | 11 | 10,231.5 | 10,231.0 |
| hot t4 probe 1 | 3 | 550 | 10,233.4 | 11 | 10,231.7 | 10,231.2 |
| hot t4 probe 2 | 0 | 95 | 10,235.9 | 11 | 10,232.2 | 10,231.5 |
| hot t4 probe 2 | 2 | 215 | 10,234.2 | 11 | 10,233.3 | 10,232.6 |
| hot t4 probe 2 | 3 | 275 | 10,234.7 | 11 | 10,232.1 | 10,231.2 |
| hot t4 probe 3 | 0 | 403 | 10,235.6 | 11 | 10,233.1 | 10,231.9 |
| hot t4 probe 3 | 1 | 3,148 | 10,232.2 | 11 | 10,231.6 | 10,231.1 |
| hot t4 probe 3 | 2 | 3,608 | 10,234.9 | 11 | 10,232.1 | 10,231.2 |
| hot t4 probe 3 | 3 | 1,055 | 2,552.9 | 9 | 2,552.6 | 2,552.2 |

### 8.5. Findings

1. **The hot-key tail reproduces on s1 with 2 and 4 workers.** In every
   hot run the largest latency is a request of 10 or 11 attempts: 5.1 or
   10.2 s, made of the policy's sleeps (10 + 20 + ... = 5,110 or 10,230
   ms requested). 006-11's 10,258.8 ms is the same shape: several
   accumulating sleeps, not one 10.24 s sleep (section 2.5).
2. **The time between attempts is the sleep.** The probe build measured
   `Thread.sleep()` at the requested time plus 0.17 to 0.34 ms per retry
   on s1; the refused `Db.execute()` took 54 to 156 us per retry on
   average (the warmup, the wait for `Db.writeLock` behind the busy writer
   and the checks, section 2.6; not separated); requested sleep is over
   99.8% of the time between attempts in every probe run. A retrying client's time goes to the
   policy's sleeps, not to refused work, on this workload.
3. **A sleeper commits only when the others stop or by luck.** A retried
   request keeps its keys, so a hot-key request conflicts on each wake-up
   as long as another worker commits the hot key, about 34,000 times a
   second here. The
   11-attempt requests ended after the window's end (begin + 10,230 ms >
   10,000 ms), when the other workers had stopped: under continued load
   they would have gone on at 10,240 ms a sleep. With 2 workers the
   probe runs show turn-taking: one worker does all the work for about
   5.1 s, its turn ends when the sleeper wins one wake-up, and the roles
   swap.
4. **Averages hide it.** Retried requests were 1 to 132 of about 370,000
   per run, attempts per commit 1.00003 to 1.00036, the p99 latency 55 to
   70 us; yet in 10 of 12 hot runs a worker went 10.2 s without a
   completion, and in each of the six 4-worker runs three of the four
   did.
5. **The hot key turns the workers into one.** Hot runs used 0.8 to 1.1
   CPU cores of 2, against 1.9 for partitioned t2: the sleepers leave a
   vCPU idle. Their commit rate, 36,000 to 38,800/s, is one uncontended
   worker's (`ref`: 39,062/s, 1.1 cores), against 55,000/s for two
   disjoint workers. With today's policy, more workers on a hot key buy
   nothing, and a request may wait 10 s for a turn.
6. **Disjoint keys: no retries, no stalls.** No request of the
   partitioned runs took a second attempt; the longest completion gap was
   22 ms (t2) and 15 ms (t4), from scheduling and GC on 2 vCPUs. With 4
   workers on 2 vCPUs the rate falls to about 40,000/s and the p99 rises
   to 2 ms: oversubscription, not retries.
7. **The probe build costs nothing measurable here.** Probe against stock
   medians: hot t2 −1.0%, hot t4 +6.2%, partitioned t2 −4.2%,
   partitioned t4 +8.9%, inside the run-to-run ranges (partitioned t2
   stock: 44,531 to 56,294/s). Its code runs once per attempt (one
   `nanoTime()`) and on retries. s1's noise is about ±10% between runs.

### 8.6. History exhaustion

Sessions `history-1000`, `history-3000` and `history-6000`, 07:33 to
07:38, s1, 2 vCPUs: `partitioned`, 2 workers, the same workload, and
`longActionMs` 1,000, 3,000 and 6,000: worker 0 sleeps that long in its
action after its reads, while worker 1 commits its own keys, one written
key each, at 37,000 to 40,000/s. Worker 0 reads only its own keys, so
every refusal of its requests is history exhaustion, not a changed key.
Two runs per build and session, all passed their checks.

`KeyModSet` keeps four bins of 32,000 key-hash additions; it covers the
last 96,000 to 128,000 additions, depending on how full the newest bin
is. Worker 1 adds that many in about 2.4 to 3.5 s.

| Long action | Worker 0's requests, each run | Commits in the window | Longest gap ms |
|---|---|---|---|
| 1,000 ms | 10 of one attempt, in every run | 9, 9, 9, 9 | 1,001 to 1,005 |
| 3,000 ms | one of 3 attempts, one of 1; stock 1: two of 2 | 1, 1, 1, 1 | 9,031; stock 1: 6,011 |
| 6,000 ms | one of 3 attempts, 18,032 ms, in every run | 0, 0, 0, 0 | 18,032 to 18,033 |

With 6,000 ms every attempt under load was refused: the first (0 to
6 s) and the second (6 to 12 s, the load ending at 10 s). The third
began at 12.03 s, after the other worker had stopped, and committed.
Under continued load the request would never commit. The policy's sleeps
were 10 + 20 = 30 ms of the 18 s (the probe build measured 30.2 to
30.3 ms); the time went to rerunning the action. With 3,000 ms, at the
edge of the history, attempts passed or not, presumably by the bins'
phase.

8. **History exhaustion is a different failure from a hot key.** A hot
   key's time goes to sleeping (99.8%, section 8.5); a long action's goes
   to rerunning it, and no sleep length helps while the load lasts: an
   attempt during which the other transactions write more than 128,000
   keys cannot commit, and one over 96,000 may not. On s1 with one other
   writer that is an action of 2.4 to 3.5 s. The caller sees the same
   endless loop, and today the two cannot be told apart (section 2.5):
   the case for contract point 3 (section 3.1).

### 8.7. File storage, durable commits and the reopen check

Sessions `file-append` (07:41 to 07:44) and `file-durable` (07:44 to
07:46), s1, 2 vCPUs: `hot` and `partitioned` with 2 workers, the same
workload, `storage=file` (the Pub API's `FileStream`, each append forced
by the storage thread) in an empty directory on s1's disk, `reopen=true`;
`file-durable` also calls `sync()` after each commit, outside the retry
loop. Two runs per build and case; every run passed its checks, and the
reopen check (the database started again from its files, the same checks)
passed in all 16, in 2.0 to 3.8 s (append, 59 to 94 MB of stream) and
0.2 to 0.3 s (durable).

| Case | Stock active/s | Probe active/s | Max latency ms | Longest worker gap ms | Most attempts | Retried |
|---|---|---|---|---|--:|---|
| append, hot | 35,856, 32,492 | 32,478, 32,273 | 10,234 to 10,236 | 10,234 to 10,236 | 11 | 6 to 54 |
| append, partitioned | 48,359, 49,945 | 49,725, 47,168 | 4.9 to 9.1 | 4 to 9 | 1 | 0 |
| durable, hot | 272, 243 | 265, 217 | 34.2 to 47.8 | 32 to 47 | 3 | 16 to 25 |
| durable, partitioned | 259, 254 | 252, 242 | 31.3 to 38.0; 1,690.5 | 29 to 37; 1,690 | 1 | 0 |

The probe build's sleeps: append, hot: 48 and 42 retries, 11,150 and
11,240 ms requested, 11,164 and 11,246 ms slept, the refused
`execute()` 238 and 117 us per retry; durable, hot: 20 and 17 retries,
210 and 180 ms requested, 212 and 182 ms slept, 129 and 134 us.

9. **File appends do not change the hot-key picture.** With the buffered,
   forced appends the hot runs are the memory runs again: one worker
   does the work (1.0 to 1.1 cores), the other's request of 11 attempts
   ends after the window, 10.23 s; partitioned runs have no retry.
10. **Durable commits hide it.** With a `sync()` per commit, each worker
    spends about 7 to 9 ms (the p50 latency) waiting for its force, and
    the hot key is written about 220 times a second: an attempt of tens
    of microseconds rarely meets a commit of the key, a refused request
    is retried once or twice after 10 or 20 ms, and its latency stays
    near the partitioned case's. The tail is a property of fast commits
    on a shared key, not of every hot key.
11. **One stall that is not a retry**: in one durable partitioned run
    (probe 2) both workers waited about 1.69 s at once, with no retry;
    a `sync()` on s1's disk, outside the loop (sections 2.1 and 2.6,
    step 8). A note for 017-06, not for the retries.

### 8.8. The lock wait and the reason of each refusal

Sessions `probe2-hot` (07:50 to 07:53; `hot`, 2 and 4 workers) and
`probe2-history-3000` (07:53 to 07:54; section 8.6's 3,000 ms case), s1,
2 vCPUs, `BUILDS="stock probe2"`, two runs per build and case, the
workload of 8.3. All passed their checks; in the probe2 build the
refusal reasons and the lock waits matched the attempts for every run.
The stock runs repeat 8.3 and 8.6: every hot run had a request of 11
attempts, 10,233 to 10,235 ms.

| Run | Refused, changed key | Refused, history | Lock wait us per refusal | Refused execute us per retry |
|---|--:|--:|--:|--:|
| hot t2 probe2 1 | 11 | 0 | 67.6 | 119.0 |
| hot t2 probe2 2 | 39 | 0 | 5.5 | 56.2 |
| hot t4 probe2 1 | 85 | 0 | 209.6 | 267.6 |
| hot t4 probe2 2 | 48 | 0 | 57.8 | 157.6 |
| history 3,000 probe2 1 | 0 | 2 | 3.2 | 166.7 |
| history 3,000 probe2 2 | 0 | 2 | 1.8 | 183.4 |

The attempts that were not refused waited 44 to 56 ns on average for the
lock; the longest single wait was 0.2 to 6.0 ms. Requested and measured
sleeps as in 8.4: 0.12 to 0.29 ms over the request per retry.

12. **The reasons are what the setup says.** Every refusal on the hot
    key was a changed key, every refusal of the long action history
    exhaustion: the probe confirms section 8.6's reading and is a way to
    tell the two apart (contract point 3).
13. **A refused attempt costs about 0.1 to 0.3 ms, partly the lock.** On
    the hot key the wait for `Db.writeLock` behind the busy writer was
    10% to 78% of the refused `execute()`; the rest (the warmup, the
    checks, being descheduled on 2 vCPUs) was not split further. Either
    way it is three orders of magnitude below the sleeps.

### 8.9. What is left

* Deliverable 1: Frans's review of sections 2.6 and 3.1.
* Deliverable 2: indexed W transactions (the other caller of
  `executeRw()`, through `WTransaction.execute()` with object operations);
  a new caller arriving behind retriers (the hot runs show that the busy
  worker's fresh requests win over the sleeper, but no separate arrival
  was measured); a baseline report that gathers sections 8.3 to 8.8 for
  review. F53's runs, if wanted, in a quiet block.
* Deliverable 3: the variants R0 to R2 (section 4) as further patches of
  `make-probe.py`'s kind over the same archive, measured against this
  baseline; then the `executeRw()` proposal, Frans's decision.


## 9. Log

2026-10-30. Registered and planned at Frans's request. Validated the retry
sequence and shared W/RW call sites, buffer-room and durability waits,
read I/O path, eviction watermarks and timing qualifications, memory
accounting, and existing related work against source. No Java changes or
new benchmark/test runs in this planning step.

2026-11-04. Split at Frans's decision (19:11): "005-81, I like your idea
to split this. So, split it." This entry keeps the retries: the wait-point
map and the client contract they need, the diagnostic harness, the
hot-key and disjoint-key baselines, the retry variants and the
`executeRw()` proposal, its deliverables 1 to 3. The broad question moved
to 017-06: the read, CPU and memory parts of section 2, the admission
points of the contract, the overload workloads, the arrival model, the
recovery measures and deliverable 4. Title, purpose, scope, "Done when"
and first step rewritten for the retries; replication's waits dropped
(removed, 005-11); the mention of 005-07 corrected (dropped; 016-07);
dated notes for 005-47, 005-11 and 005-52 in section 2. The code was not
reviewed again. By Claude (Opus 5.5, Claude Code).

2026-11-05, 07:20 to 08:00. Section 7's first step, at Frans's approval
("005-81 (retries) gets its harness and the hot-key and disjoint-key
baselines, timed on s1."). Built the harness (`RetryBench.java`, from
006-11's), the probe patch (`make-probe.py`), the runner and the
summarizer in [81-overload-and-retries/](../005-todo/81-overload-and-retries/);
built stock and probe jars on s1 from `git archive` of `0c6c4be`; ran 24
hot-key and disjoint-key runs, 6 one-worker references and 12
history-exhaustion runs on s1 (2 vCPUs), then 16 runs with file storage
and durable commits, with a reopen check, and 12 with a probe of the lock
wait and the refusal's reason in `Db`; all checks passed (section 8).
The 10 s hot-key tail reproduces as 11 attempts of accumulating sleeps;
a long action under unrelated writes never commits while the load lasts.
Drafted the wait-point map (section 2.6) and the contract (section 3.1)
for review. No change to `java/`. By Claude (Opus 5.5, Claude Code).
