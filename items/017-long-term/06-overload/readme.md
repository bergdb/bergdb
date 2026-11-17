017-06. Overload, backpressure and admission control
====================================================

Status: open (notes only). Created 2026-10-30 as part of 005-81; split
from it by Frans on 2026-11-04, as a long-term topic. The questions, the
review of reads, CPU and memory, the admission points of the client
contract, the overload workloads, the arrival model, the recovery
measures and the decision on admission controls below are 005-81's as
they were when it was split. The retries stayed in 005-81 (015-88 from
2026-11-05) until 2026-11-05, 14:12, when Frans decided to cap the retry
sleep at 640 ms for release 2026.3 and move the rest here:
[retries.md](retries.md), section 8 below. Where this file cites 005-81,
section n, that section is retries.md's section n.

What this topic holds: whether BergDB needs database-wide admission
control and backpressure for CPU, reads and memory under overload; which
controls belong in BergDB and which in the application that owns its
threads and incoming requests; throughput, latency and memory at and above
capacity, and recovery when the load falls. Since 2026-11-05 also the
transaction retries, with Frans's question whether `rw()` should ever
give up under overload (section 8).

## 1. Questions

005-81 asked, before the split:

* At and above sustainable capacity, do throughput, latency, memory and
  individual clients' progress remain acceptable? How quickly does the
  database recover when offered load falls?
* Which controls belong in BergDB, and which belong in the application
  that owns its threads and incoming requests?
* Is a retry change enough, or is bounded admission of client work also
  justified? What is the runtime and code-complexity cost of each option?

Where BergDB slows or refuses a client today, and what the client holds
while waiting, stays in 005-81 (section 1, and the wait-point map of its
section 2); so does the retry algorithm. This topic builds on both.

The scope, as 005-81 had it: the local Java Pub API over one main storage,
with the Core and storage paths traced underneath; reads, write-only
transactions, read-write actions and durability waits; eviction and
reclaim as competing maintenance work. The C implementation is not a
target. 005-81 called replication experimental and left a full replicated
overload policy as a separate extension; replication was removed on
2026-11-04 (005-11, `bd77904`), so such a policy would come with a future
replication design (017-03).

Keep 006-11's conclusion: concurrent STM actions have demonstrated value.
This topic studies progress and resource control, not removal of STM or a
general redesign of the write lock.

## 2. What the code does today: reads, CPU and memory

From 005-81, section 2, reviewed 2026-10-30 against HEAD `24a031a`; that
section holds the review's terms and its qualified conclusion: there are
deliberately designed controls for the write buffer and eviction, and the
client paths inspected contain no common admission limit, request deadline
or overload-result policy. The write and durability path (005-81,
section 2.1), eviction's wait for a load (section 2.4) and the retries
(section 2.5) stay there. The code was not reviewed again for the split.

### 2.1. Storage read throughput

005-81, section 2.2, as it was.

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

Sources: [ConnectionImp.java](../../../java/src/bergdb/pubimp/ConnectionImp.java),
[NodeCollection.java](../../../java/src/bergdb/core/NodeCollection.java),
`BufferedStream.read()` and `FileStream.read()/DbFile.read()`;
009-02, section 3.4; 005-46.

### 2.2. CPU and concurrent client work

005-81, section 2.3, but its first paragraph, which stays there: an RW
call runs the action synchronously, and user computation, reads, index
preparation and core transaction construction precede the serialized
commit, one thread to a connection.

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
batches. A change to avoid redundant monitor entries is in `52aeb04`;
the entry remains open for the specified quiet rerun. Frans accepted the
remaining scheduler delays at a full machine as outside the earlier
BergDB pause target. This investigation must respect that decision while
still measuring the total latency clients experience.

Sources: `ConnectionImp.rw()`, `RwTransaction.executeRw()`,
`Db.executeInner()/Internal.writersWaiting()`, `Eviction.EvictorRun`;
005-65, "Results", "Decision and fix" and "State"; 010-01, P1.

### 2.3. Total memory

005-81, section 2.4, its memory part; the watermarks and eviction's wait
for a load stay there.

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

Sources: [Residents.java](../../../java/src/bergdb/core/Residents.java),
`DatabaseBuilderImp` and `DbBuilder`;
009-02; 005-52; 005-65; 005-80; 010-01, P1.

## 3. The admission points of the client contract

005-81, section 3, holds the contract the retries need: refusal, the go
point, progress and observability. Its points 1 and 2, part of its
point 6, and the placement of admission are this topic's:

1. **Bound outstanding work.** Identify limits on running attempts,
   queued requests, bytes retained by waiting/prepared transactions and
   durability waiters. Blocking one caller provides backpressure only if
   the application also bounds its incoming work.
2. **State where waiting occurs.** Prefer any new admission wait before
   running the action or allocating large transaction state. Do not hold
   the database write lock while waiting for an admission permit. Define
   nested calls and maintenance exemptions to avoid self-deadlock.
3. **Recover.** After a burst, queued work and memory should drain and
   waits return towards baseline. (The rest of 005-81's point 6, to be
   observable, stays there.)

Tentative API placement: shared resource limits at the database level;
caller patience, a per-call option or connection default, is 005-81's.

An application-owned bounded executor is a candidate baseline, not an
assumption that BergDB must own another executor. Protect the first
admission queue as well as later database waits. Adding a global read gate
could penalize cheap cache hits, so justify placement by measured costs.

From 005-81, section 4: releasing an active-attempt permit before backoff
and reacquiring it before the next read is a candidate; waiting requests
still consume memory and need a bound. Shared admission limits are tested
only if the overload results justify them, after the retry variants.

## 4. Overload experiments

### 4.1. Workloads

As in 005-81, section 5.1, use one connection per worker and fixed,
reproducible data/operation sequences. Establish a sustainable baseline
for each case, then exercise below, near and above that rate. Start with
these separate pressures; the conflict and history cases are 005-81's:

| Case | Deliberate pressure | Important control |
|---|---|---|
| CPU    | Resident, independent RW actions with useful computation  | Tiny actions; varying concurrency |
| Write  | File appends with larger values and batches               | Unsynced execution versus ordinary sync |
| Read   | Random reads with a working set above cache budget        | OS-cache reads versus device reads |
| Memory | Small cache, loading reads and concurrent prepared writes | Fixed versus lowered cache budget |

Then combine read/write traffic, eviction and reclaim in a small number of
cases chosen by the isolated results, with short bursts followed by quiet
recovery.

Reuse 005-65's thread sweep and the existing `PauseProbe`/`LoadTest`
mechanisms where appropriate. Its existing write benchmark `Perf`
serializes part of transaction preparation, so do not use it unmodified to
judge parallel action admission.

### 4.2. Arrival model and attribution

005-81, section 5.2, as it was.

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

### 4.3. What to record

In addition to 005-81, section 5.3 (latency, retries, the time in each
wait, and the overhead check of diagnostic probes):

* Offered, admitted, completed, refused and still-outstanding requests;
  useful transactions/second and application/stream bytes/second.
* End-to-end latency (section 4.2), separately for successful and refused
  requests; drain/recovery time.
* Active/waiting threads, process and per-thread CPU (including maintenance),
  allocation, heap/GC pauses or stalls, resident/pinned bytes, buffer
  occupancy, eviction work and storage throughput/latency.

### 4.4. Reproducibility and correctness

As in 005-81, section 5.4. And:

The original STM benchmark used shorter synthetic runs with a warmed OS
cache. It is evidence to reuse, not evidence for cold-disk overload,
long-running resource bounds or all client workloads.

### 4.5. The aim

From 005-81, section 6. Acceptable overload need not mean constant latency
or successful admission of every request. The aim is bounded outstanding
work, useful throughput, understandable refusal/wait semantics and
observable progress. The old 20 ms internal-pause target is not a promise
of 20 ms end-to-end service under arbitrary CPU, storage or memory
pressure.

005-81, section 6, also holds the tests that a pre-go deadline or an
admission permit needs, and the report before a default is selected.

## 5. What would settle it

005-81's deliverables 2 and 4, as far as they are this topic's:

* A baseline overload/recovery report with raw results and correctness
  checks, identifying each bottleneck.
* An explicit decision on whether further database admission controls are
  needed; if so, their justified scope and cost rather than an automatic
  expansion of this topic.

005-81's "Done when" asked that the measurements support an overload
policy, and that every remaining implementation have a recorded decision
or linked follow-up; a completed plan alone does not close it. As a
long-term topic (017's rules), it has no fixed "Done when": the decision
above, or Frans's word that it is parked or dropped.

## 6. First step

When Frans takes the topic up (017's rules): after 005-81's diagnostic
harness and its hot-key and disjoint-key baselines, add bounded,
independently scheduled arrivals and a controlled slow-append case
(section 4.2), to test the measurement method before expanding to the
other resources or selecting a policy.

## 7. Related work

* [retries.md](retries.md) (005-81, then 015-88): the retries, and
  the wait-point map and client contract they need; its related work lists
  006-11, 005-46, 005-48, 005-70 and 005-76.
* [005-52](../../005-todo/52-cache-size-while-running.md), "Left to do":
  budget-change pause probe; reuse it without claiming it has passed.
* [005-65](../../005-todo/65-gets-with-8-readers.md), "State": the
  remaining quiet thread sweep after its monitor fix.
* [005-77](../../005-todo/77-cap-pace-factor.md): catch-up work after
  startup-distance changes, a potential additional source of commit cost.
* [005-80](../../005-todo/80-setbudget-race-record.md): eviction-budget
  race evidence.
* [016-07](../../016-release-2026-2/07-concurrency.md): today's
  synchronization, reviewed for release 2026.2 (005-07, the broader
  synchronization investigation, was dropped on 2026-11-04).
* [017-03](../03-replication/readme.md): replication, for a replicated
  overload policy.
* [010-01](../../010-principles/01-principles.md), P1 and P3:
  bounded internal pauses and calm when idle.

## 8. Transaction retries

[retries.md](retries.md), moved from 015-88 on 2026-11-05 at Frans's
decision (14:12), cited as "017-06, retries, section n": the retries'
purpose and scope, what the code does today (the exact retry policy, its
section 2.5, with a note on 2026.3's cap at 640 ms), the wait points of a
retrying attempt, the client contract and its draft (section 3.1), the
retry policies to compare, the experiments, the implementation checks,
the first step, the harness and the baselines on s1 with their findings,
and what is left (section 8.9). The harness stays in 005-81's directory.

At its top, the open question Frans raised that day: should `rw()` ever
give up, as a last resort under overload, like an `OutOfMemoryError`
("should never happen. But it can if we have overload."), with option A,
five attempts and then an exception, as one of the answers to weigh.
Whether overload shows to a client as a hang or as an exception is this
topic's question; release 2026.3 keeps the contract (the call retries
until it commits) and says in the Javadoc that under overload a
transaction may never commit.


## 9. Frans's notes

2026-11-04, 19:11, Frans's decision: "005-81, I like your idea to split
this. So, split it." The idea he approved: keep the retry fix in 005, as
005-81, narrowed to bounded work (the wait points and client contract the
retries need, the diagnostic harness, the hot-key and disjoint-key
baselines, the measured retry variants and a concrete `executeRw()`
proposal); move the broad part, whether BergDB needs database-wide
admission control and backpressure for CPU, reads and memory under
overload, here, as an open-ended, design-level topic.

2026-11-05, 14:09, on 015-88, to session bergdb-e8: "Getting cold feet.
This may be a more fundamental thing than I first thought. How about
keeping things essentially as is. We could just change to go to around
640 ms and then repeat there at that sleep time. Clients today count on
eventual success. This is a very small change. I hesitate. This should
always work. It is almost like an OutOfMemoryException, should never
happen. But it can if we have overload." And at 14:12, to cap the sleep
at 640 ms for 2026.3 and move the rest of the retries here: "Yes, do it."
The discussion is at the top of [retries.md](retries.md).

## 10. Log

2026-11-04. Split here from 005-81 at Frans's decision, with the parts of
005-81 named in the Status line, by Claude (Opus 5.5, Claude Code).

2026-11-05. The transaction retries moved here from 015-88 (sections 1 to
8, as they were, with their numbers) as retries.md, at Frans's decision
of 14:12, with his question whether `rw()` should ever give up under
overload at its top (section 8); 015-88 keeps only the cap of the retry
sleep at 640 ms for release 2026.3. By Claude (Opus 5.5, Claude Code).
