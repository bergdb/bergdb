005-81. Investigate: transaction retries
========================================

Status: open. Kind: investigate. Created 2026-10-30. Split on 2026-11-04
at Frans's decision: the broad question, overload, backpressure and
admission control, is now a long-term topic,
[017-06](../017-long-term/06-overload/readme.md); this entry keeps the
retries.

Plan and source review only. No implementation or new performance runs
have been made for this entry.

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

Sources: `RwTransaction.executeRw()`,
[WTransaction.java](../../java/src/bergdb/pubimp/WTransaction.java),
[RwEnvironmentImp.java](../../java/src/bergdb/pubimp/RwEnvironmentImp.java)
(`prepareForRWRerun/prepareForWRerun/get/createTrans`),
`Db.stmCheckConflicts()`,
[KeyModSet.java](../../java/src/bergdb/core/KeyModSet.java);
006-11, sections 10.3 and 10.7.

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
* [005-07](07-transaction-synchronization.md), "Questions": the broader
  synchronization investigation this entry cited, dropped on 2026-11-04 as
  obsolete since handles (009); today's synchronization is reviewed in
  [016-07](../016-release-2026-2/07-concurrency.md). This entry owned
  overload and retries before the split; it owns the retries now.
* [005-46](46-stream-file-lock.md), "Interrupts":
  storage/read concurrency and cancellation boundaries.
* [005-48](48-group-commit.md): group commit.
* [005-52](52-cache-size-while-running.md): a transaction's warmup and the
  eviction park (section 2.4); its pause probe is in 017-06's related work.
* [005-70](70-keymodset-after-start.md): STM restart fix, done separately
  in `7d967d7`; include it in the new baseline.
* [005-76](76-wake-at-a-quarter.md), "The issue": a known source of
  buffer waits before physical storage is necessarily saturated.
* [010-01](../010-principles/01-principles.md), P1 and P3:
  bounded internal pauses and calm when idle.

## 8. Log

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
