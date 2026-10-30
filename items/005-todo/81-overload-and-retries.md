005-81. Investigate: client overload and transaction retries
==========================================================

Status: open. Kind: investigate. Created 2026-10-30.

Plan and source review only. No implementation or new performance runs
have been made for this entry.

Registered at Frans's request after 006-11's STM benchmarks. Keep STM;
investigate how clients experience storage, CPU and memory pressure before
choosing a replacement for the hard-coded retry sleeps. A change to
`RwTransaction.executeRw()` is the expected first implementation outcome,
but its algorithm, defaults and public settings remain to be decided.

## 1. Purpose and scope

Answer these questions:

* Where does BergDB slow or refuse a client today? What resources and locks
  does the client hold while waiting?
* At and above sustainable capacity, do throughput, latency, memory and
  individual clients' progress remain acceptable? How quickly does the
  database recover when offered load falls?
* Which controls belong in BergDB, and which belong in the application
  that owns its threads and incoming requests?
* What retry algorithm should replace the 10 ms exponential sleep? Should
  callers have a retry time budget, an attempt limit, or both? What does
  an exception guarantee about whether the transaction committed?
* Is a retry change enough, or is bounded admission of client work also
  justified? What is the runtime and code-complexity cost of each option?

The initial scope is the local Java Pub API over one main storage, with
the Core and storage paths traced underneath. Cover reads, write-only
transactions, read-write actions, and durability waits. Include eviction
and reclaim as competing maintenance work. Replication is experimental:
record its additional waits, but a full replicated overload policy is a
separate extension. The C implementation is not a target of this entry.

Keep 006-11's conclusion: concurrent STM actions have demonstrated value.
This entry studies progress and resource control, not removal of STM or a
general redesign of the write lock.

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

`StorageManager.append()` also appends to active replica buffers in
sequence. A slow active replica can impose another buffer wait in this
same path. Do not generalize one-main-storage measurements to replication.

Sources: [Db.java](../../java/src/bergdb/core/Db.java),
[StorageManager.java](../../java/src/bergdb/storage/StorageManager.java),
[BufferedStream.java](../../java/src/bergdb/storage/BufferedStream.java),
[FileStream.java](../../java/src/bergdb/stream/FileStream.java);
005-46, "Interrupts"; 005-48; 005-76, "The issue".

### 2.2. Storage read throughput

`ConnectionImp` performs reads synchronously on the calling thread.
Cache misses reach the stream on that thread. `FileStream` uses positional
channel reads and allows separate readers alongside the writer; it has no
general semaphore or request-rate limit for read I/O.

This does not make the entire read path lock-free. The cache slow path
uses node/handle monitors, a read of buffered bytes uses the buffer's
monitor, and cache loads can trigger eviction waits. Some repeated loads
of the same index node serialize through its handle. Storage, OS scheduling
and those waits determine the latency observed by callers.

No explicit database-wide cap on concurrent read I/O was found on this
path. Application thread limits provide an external bound. A stream read
from the OS page cache is not a physical disk read: report them separately
and do not assume a fixed ratio between disk and memory latency.

Sources: [ConnectionImp.java](../../java/src/bergdb/pubimp/ConnectionImp.java),
[NodeCollection.java](../../java/src/bergdb/core/NodeCollection.java),
`BufferedStream.read()` and `FileStream.read()/DbFile.read()`;
009-02, section 3.4; 005-46.

### 2.3. CPU and concurrent client work

`ConnectionImp.rw()` calls the action synchronously. User computation,
reads, index preparation and core transaction construction precede the
serialized commit. Each connection is intended for one thread.

There is no general CPU admission controller or bounded executor on this
path. `Db.writersWaiting` counts writers approaching the monitor and lets
eviction yield; it does not cap them, promise fair order, or bound their
prepared transaction memory. Waiting client threads are a queue even though
there is no explicit request-queue object in BergDB.

Increasing client concurrency can compete with the storage and eviction
threads and GC, and can increase retries. This needs measurement rather
than a rule based only on CPU percentage or number of cores.

005-65 already studied a relevant case: its quiet runs found CPU saturation
and contention entering `evictorLock`, not loads waiting for eviction
batches. A change to avoid redundant monitor entries is in `988fe1a`;
the entry remains open for the specified quiet rerun. Frans accepted the
remaining scheduler delays at a full machine as outside the earlier
BergDB pause target. This investigation must respect that decision while
still measuring the total latency clients experience.

Sources: `ConnectionImp.rw()`, `RwTransaction.executeRw()`,
`Db.executeInner()/Internal.writersWaiting()`, `Eviction.EvictorRun`;
005-65, "Results", "Decision and fix" and "State"; 010-01, P1.

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

`Residents` accounts for node/value memory using `getMemSize()`, not all
JVM heap allocations. It excludes, for example, the application's request
queue, prepared transaction maps/buffers and uncached temporary objects;
it is not a whole-process memory limit. Shared values can be counted more
than once, and a growing pinned node's accounting catches up when written.
Dirty/pinned objects cannot simply be evicted. The controller raises its
trigger to at least the last round's pinned bytes plus the watermark gap
when that exceeds the configured budget.

Thus a small cache budget does not guarantee a small heap, and limiting
concurrent actions can matter independently of cache eviction. Measure
resident/pinned accounting, actual heap and allocation pressure separately.
The Pub builder normally chooses about a fifth of maximum heap; the direct
Core builder's default is 200 MB, so record the actual settings.

Sources: [Eviction.java](../../java/src/bergdb/core/Eviction.java),
[Residents.java](../../java/src/bergdb/core/Residents.java),
`DatabaseBuilderImp` and `DbBuilder`;
009-02; 005-52; 005-65; 005-80; 010-01, P1.

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

Sources: `RwTransaction.executeRw()`,
[WTransaction.java](../../java/src/bergdb/pubimp/WTransaction.java),
[RwEnvironmentImp.java](../../java/src/bergdb/pubimp/RwEnvironmentImp.java)
(`prepareForRWRerun/prepareForWRerun/get/createTrans`),
`Db.stmCheckConflicts()`,
[KeyModSet.java](../../java/src/bergdb/core/KeyModSet.java);
006-11, sections 10.3 and 10.7.

## 3. Establish the client contract first

Propose and review a short contract before selecting public settings:

1. **Bound outstanding work.** Identify limits on running attempts,
   queued requests, bytes retained by waiting/prepared transactions and
   durability waiters. Blocking one caller provides backpressure only if
   the application also bounds its incoming work.
2. **State where waiting occurs.** Prefer any new admission wait before
   running the action or allocating large transaction state. Do not hold
   the database write lock while waiting for an admission permit. Define
   nested calls and maintenance exemptions to avoid self-deadlock.
3. **Specify refusal precisely.** An admission refusal or exhausted retry
   budget should mean that this transaction did not commit. It is not a
   storage failure and must not fail the database. Distinguish it from
   actual I/O/corruption failure and from cancellation of a durability wait.
4. **Respect the go point.** `Db.executeInner()` changes memory without
   rollback once its checks have passed. A deadline must not throw out of
   the later append/eviction/reclaim path as an ordinary overload refusal.
   Existing monitor acquisition, synchronous I/O and arbitrary action code
   have no hard overall deadline. Merely adding a timer in `executeRw()`
   cannot promise a hard timeout for the whole call. Distinguish a retry
   time budget, a pre-commit deadline, and a durability-wait timeout.
5. **Preserve progress.** Measure per-client completion gaps and fairness,
   including fresh callers competing with retriers. Shorter sleeps may
   improve latency but waste CPU on doomed attempts. Define acceptable
   throughput/latency tradeoffs from the baseline, not from one mean.
6. **Recover and be observable.** After a burst, queued work and memory
   should drain and waits return towards baseline. Expose enough evidence
   to distinguish conflicts, history exhaustion, storage waits, CPU
   saturation and eviction pressure, without expensive always-on tracing.

Tentative API placement: shared resource limits at the database level;
caller patience as a per-call option or connection default. If a connection
setting is chosen, specify it on the public `Connection` API and implement
it in `ConnectionImp`; an implementation-only knob is insufficient.
Keep the number of settings small. A maximum-attempt setting may be useful,
but "a few attempts" alone gives no predictable time budget.

An application-owned bounded executor is a candidate baseline, not an
assumption that BergDB must own another executor. Protect the first
admission queue as well as later database waits. Adding a global read gate
could penalize cheap cache hits, so justify placement by measured costs.

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
shared admission limits only if the overload results justify them. Releasing
an active-attempt permit before backoff and reacquiring it before the next
read is a candidate; waiting requests still consume memory and need a bound.

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
sequences. Establish a sustainable baseline for each case, then exercise
below, near and above that rate. Start with these separate pressures:

| Case | Deliberate pressure | Important control |
|---|---|---|
| CPU | Resident, independent RW actions with useful computation | Tiny actions; varying concurrency |
| Write | File appends with larger values and batches | Unsynced execution versus ordinary sync |
| Read | Random reads with a working set above cache budget | OS-cache reads versus device reads |
| Memory | Small cache, loading reads and concurrent prepared writes | Fixed versus lowered cache budget |
| Conflict | Hot counter, skewed keys and different action costs | Disjoint keys; unrelated writes |
| History | Long action plus many unrelated modifications | Trace history exhaustion separately |

Then combine read/write traffic, eviction and reclaim in a small number of
cases chosen by the isolated results. Include indexed W transactions and
RW actions, large versus small transactions, a new caller arriving behind
retriers, and short bursts followed by quiet recovery.

Reuse 006-11's counter/integrity checks and useful computation, 005-65's
thread sweep, and the existing `PauseProbe`/`LoadTest` mechanisms where
appropriate. Its existing write benchmark `Perf` serializes part of
transaction preparation, so do not use it unmodified to judge parallel
action admission.

### 5.2. Arrival model and attribution

006-11's fixed workers wait for their previous operation before issuing the
next. That is a useful capacity baseline, but it reduces arrival rate when
latency rises. Add independently scheduled arrivals through a deliberately
bounded harness queue. Count arrivals refused by the harness separately
from refusals by BergDB. Never manufacture an unbounded queue to test one.

Record scheduled arrival, actual enqueue/start, database return and durable
completion. Measure end-to-end latency from scheduled arrival, including
queueing and missed dispatch time; report generator lag so a saturated load
generator cannot masquerade as database stability. Use a separate process
or CPU allocation for the generator if needed. Retain fixed-client runs to
separate application admission effects from database effects.

Pilot at roughly 50%, 90%, 110% and 150% of each baseline's sustainable
rate. Choose concurrency and queue caps explicitly. Use below-capacity,
overload and recovery phases long enough to see buffer/cache convergence
and retry drain; determine final durations from the pilot, then freeze
them. A run that ends with requests in flight must report their completion,
refusal or watchdog expiry, not drop them from throughput or latency.

Use controlled slow-stream wrappers to isolate read and append stalls and
test recovery deterministically, followed by real FileStream measurements.
Call injected delays simulated I/O, and warm OS-cache results cache results.
Confirm device I/O with host counters for any claimed disk-bound run.
Vary read and write pressure independently before a shared-device run.

### 5.3. What to record

* Offered, admitted, completed, refused and still-outstanding requests;
  useful transactions/second and application/stream bytes/second.
* p50, p95, p99, p99.9 and maximum whole-call and end-to-end latency,
  separately for successful and refused requests; per-client completions,
  longest completion gap and drain/recovery time.
* Attempts per committed and per refused request; retry reason, requested
  and actual wait, cumulative backoff, snapshot age and history coverage.
  Existing `RerunException` carries only a hash, and `getRunCount()` is
  filled on success; add diagnostic counters to variants as necessary.
* Time in action/preparation, warmup, commit-lock acquisition and holding,
  buffer-room wait, underlying append/force, sync, read I/O and eviction.
  Keep overlapping times distinct: a buffer wait is part of lock holding.
* Active/waiting threads, process and per-thread CPU (including maintenance),
  allocation, heap/GC pauses or stalls, resident/pinned bytes, buffer
  occupancy, eviction work and storage throughput/latency.

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

The original STM benchmark used shorter synthetic runs with a warmed OS
cache. It is evidence to reuse, not evidence for cold-disk overload,
long-running resource bounds or all client workloads.

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

Acceptable overload need not mean constant latency or successful admission
of every request. The aim is bounded outstanding work, useful throughput,
understandable refusal/wait semantics and observable progress. The old
20 ms internal-pause target is not a promise of 20 ms end-to-end service
under arbitrary CPU, storage or memory pressure.

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
Pair it with a disjoint-key case, then add bounded, independently scheduled
arrivals and a controlled slow-append case. This tests the measurement
method before expanding to the other resources or selecting a policy.

Deliver in order:

1. A reviewed map of wait points and the proposed client contract, extending
   section 2 with any findings from the diagnostic runs.
2. A baseline overload/recovery report with raw results and correctness
   checks, identifying each bottleneck.
3. A measured comparison of the small retry variants and a concrete
   `executeRw()` change proposal, including public API/defaults if needed.
4. An explicit decision on whether further database admission controls are
   needed; if so, their justified scope and cost rather than an automatic
   expansion of this item.

Done when the source findings are checked by the relevant probes, the
measurements support a retry recommendation and overload policy, and every
remaining implementation has a recorded decision or linked follow-up.
A completed plan alone does not close the investigation.

Related work:

* [006-11](../006-2026-q4/11-stm-concurrency.md), sections 9 and 10:
  STM critical section, benefits/costs and the hot-key evidence.
* [005-07](07-transaction-synchronization.md), "Questions": the broader
  synchronization investigation. Its historical descriptions are not all
  current; this entry owns overload and retries.
* [005-46](46-stream-file-lock.md), "Interrupts":
  storage/read concurrency and cancellation boundaries.
* [005-48](48-group-commit.md): group commit.
* [005-52](52-cache-size-while-running.md), "Left to do": budget-change
  pause probe; reuse it without claiming it has passed.
* [005-65](65-gets-with-8-readers.md), "State": the remaining quiet
  thread sweep after its monitor fix.
* [005-70](70-keymodset-after-start.md): STM restart fix, done separately
  in `7d967d7`; include it in the new baseline.
* [005-76](76-wake-at-a-quarter.md), "The issue": a known source of
  buffer waits before physical storage is necessarily saturated.
* [005-77](77-cap-pace-factor.md): catch-up work after startup-distance
  changes, a potential additional source of commit cost.
* [005-80](80-setbudget-race-record.md): eviction-budget race evidence.
* [010-01](../010-principles/01-principles.md), P1 and P3:
  bounded internal pauses and calm when idle.

## 8. Log

2026-10-30. Registered and planned at Frans's request. Validated the retry
sequence and shared W/RW call sites, buffer-room and durability waits,
read I/O path, eviction watermarks and timing qualifications, memory
accounting, and existing related work against source. No Java changes or
new benchmark/test runs in this planning step.

