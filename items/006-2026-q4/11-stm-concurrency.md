# 006-11. STM and concurrent writers: status, value and cost

Created 2026-10-30 by Codex, at Frans Lundberg's request. Status: done.
The source investigation and 276 benchmark runs across 92 configurations are complete.
The results and keep/remove recommendation are in section 10.
The follow-up review of the single-writer critical section is in section 9.

Snapshot: `4685ab1d3611b9b3d8a20907c29253051be53fc6`.
Scope: inspect the implementation and evidence, measure source size, build
and verify benchmark controls, run the comparisons, and recommend whether to
keep STM. Production Java, Lean and the stream format were not changed.


## 1. Initial answer

BergDB already supports concurrent writer callers, with parallel preparation
and one serial commit lane. Its STM is application-level optimistic
concurrency control, not a general memory transaction system. A read-write
action reads a snapshot, computes its changes, and submits a read set and
write set. Under the write lock, BergDB validates the reads and applies the
changes. A conflict causes the application action to run again.

**The measured value is overlapping application reads, computation,
serialization and cache warm-up across transactions while preserving checked
read-modify-write operations.** That value depends on the workload. Small
blind puts have little application work to overlap; expensive actions on
independent keys can benefit much more. The initial source review left this
benefit unmeasured. Section 10 now measures it: approximately 1.7 times the
throughput with about 9 microseconds
of read-dependent computation, and 6.9 times with about 94 microseconds,
against a partially stripped serial control.

**The identifiable core conflict checker is small: 175 production code
lines.** The important cost is the surrounding protocol: tracking reads,
repeating actions, handling starvation and expired history, and maintaining
correctness across restart, eviction, reclaim and publication to readers.
Removing STM would not remove those other mechanisms automatically.

Recommendation after the benchmarks: **keep STM for the general read-write
API**. Its measured value is substantial for read-dependent computation and
for overlapping cache-miss work. Small resident operations and hot keys do
not automatically benefit from more writers. Section 10 separates these
cases and the measured runtime cost. The known restart-validation issue,
005-70, remains separate; these benchmarks do not cross a restart.


## 2. What actually runs in parallel

Sources: `pubimp/RwTransaction.executeRw`, `RwEnvironmentImp`,
`core/Trans.Builder.build`, and `Db.executeInner` / `warmup`.

| Phase | Current execution |
|---|---|
| Application `Action.run`: snapshot reads, computation, requested writes | Caller thread, outside `Db.writeLock`; different actions can overlap |
| Pub API index preparation, ordinary value serialization, transaction building, sorting and hashing | Before `Db.execute`; different callers can overlap |
| Size check and warm-up of the transaction's write keys | Before the write lock; warm-up can overlap other callers and a commit |
| State/limit checks, dirty-node preflight, read-set validation and transaction-time assignment | Under the one database write lock |
| Deferred key/value transformations, Dag mutation, publication of the new lookup time, recording modified key hashes | Under the write lock |
| Node selection and serialization, append to the buffered stream, statistics, listeners, eviction's transaction work and reclaim's completion work | Also inside the write lock |
| Buffered stream flush/force, and the caller's later `sync()` wait | Separate from the commit lane; permits group commit |

Thus the serial part is substantially more than the STM conflict check.
`Db.ExecuteData` is shared writer state protected by this lock, and the Dag
has one mutator at a time. Removing or splitting the lock is a new design,
not a small change to validation.

The Pub API requires one `Connection` per thread (`pub/Connection`). Core
callers must supply each transaction's read time and dependencies correctly;
`Trans` is mutable and is documented as reusable by the same thread.

Reads use MVCC and the published clock; they do not acquire the write lock
for a whole lookup. This reader/writer overlap is a separate benefit from
optimistically running multiple application actions. Some older comments
still describe readers taking `readSync`; the current reader path and the
2026 amendment in `Db` take precedence over those comments.


## 3. Validation and retry costs

`Db.stmCheckConflicts` asks `KeyModSet.modifiedAfter(readTime, hash)` for
every read hash. `stmRecordKeys` records the write hashes, including virtual
ones used by the Pub API. The set has four rotating bins, each covering
32,000 recorded additions. Capacity counts modifications, not distinct keys
or elapsed time; repeated writes also advance it. Reads older than the
remembered history are conservatively refused.

Consequences from the implementation:

* Validation work grows with the read set; recording work grows with the
  write set. Hash lookup buckets can grow, and allocation/rotation adds work.
* Different keys with the same hash can cause unnecessary conflicts.
* A long action can expire from the validation window even when none of its
  own keys changed. Continuous writes can keep making it retry.
* `RwTransaction.executeRw` retries without a count limit. It sleeps for
  10 ms after the first conflict, doubles the delay, and eventually sleeps
  10,240 ms per conflict. There is no jitter. End-to-end latency must include
  these sleeps and all failed attempts, not only the successful `execute`.
* An action may run repeatedly. Application side effects outside the
  database need to respect that contract. Outputs are cleared on retry and
  only the committed attempt's outputs are returned (005-12).
* Warm-up reads every write key before taking the lock. Its code comment
  estimates a 10–20 percent CPU saving if it were omitted for a single
  writer; this is an old estimate, not a current measurement. Eviction can
  also remove a warmed node before the commit uses it.

Two correctness boundaries need explicit attention:

1. **005-70 remains open.** Startup creates an empty `KeyModSet`, so a
   submitted read set referring to a time before restart can miss a write
   made before restart. The issue has a reproducer and recommends setting
   the validation history's lower bound at startup. The current source
   still matches the issue; its restart reproducer was not rerun here.
   This concerns stale read sets crossing restart, not every ordinary new
   `Connection.rw` call.
2. **Dependency coverage is part of the contract.** Before making a broad
   serializability claim, check point reads of missing keys, predicates and
   indexed/range reads, including virtual hashes and phantom insertions.
   This investigation has not established their complete coverage.

Lean's current model does not prove the STM or Java concurrency protocol.


## 4. Existing tests and measurements

There is more evidence than an entirely untested STM, but it does not yet
answer the value question.

| Evidence | What it establishes and its limit |
|---|---|
| `KeyModSet` unit tests; `DbTester.testRerun` | Bin/history behavior and rejection of a stale read set; not sustained writer contention |
| `PubTester.testRw2`; `PubTesterOutput.testRerun` | An intervening write reruns an action; only the successful outputs escape |
| `PubTesterOutput.testThreads` | Four threads increment one shared counter, 25 transactions each; checks the final count and unique committed outputs; a short correctness test |
| `Concurrency2`, `ReclaimReaders`, `PauseProbe` | Reader/writer overlap and maintenance behavior; one application writer, not STM writer scaling |
| `manual/TransThroughput`, registered in the perf test pack | A 1/2/4/8-writer benchmark exists; historical results in its comment are from 2013. It uses blind prebuilt puts, a shared non-atomic counter and unsynchronized stop flag, and stops when the first worker signals completion. Repair before using it as a reference |
| Props, rerun in 006-02 | Current-code measurements as of 2026-10-19, but its write test is single-threaded and its threaded test is reads |
| `stress/Perf` and the durable scenarios of `performance.suite` | Multiple callers and group-commit performance, but the harness's `timeLock` encloses `b.build()` and `db.execute(t)`, serializing warm-up too. Keys are partitioned among workers and there are no read dependencies: no STM conflict workload |
| 005-48 and 005-64 | Recent evidence for group commit and buffer settings. This is evidence for overlapping durable waits, not for STM's validation or parallel application computation |

The `Perf.timeLock` does not invalidate group-commit measurements: `sync()`
runs outside it, so many durable callers can share a force. It does make
that harness unsuitable for measuring the parallel preparation available
inside `Db.execute`. Do not simply remove it: its simulated clock and shared
statistics currently depend on the serialization.

For scale, 005-48's recorded s1 results after its change were 213 durable
commits/s with one caller and 6,429 with 64. These are historical measurements
of that commit and machine, not a new run or a 30-fold STM speedup. A serial
commit service can also collect multiple requests into a durable group.

On 2026-10-30 the selected conflict-set, Core rejection and Pub API retry/output
tests all passed, including the four-writer counter test. They were rebuilt
from the snapshot in an isolated temporary directory with JDK 27 and
`--release 17`; tests used `-ea`. The three filtered unit runs and their
database-stop checks printed `SUCCESS`. See
[verification.txt](11-stm-concurrency/verification.txt).
These were the source review's focused checks. The later benchmark
measurements and full unchanged-baseline gate are in section 10; neither
establishes a concurrency proof.


## 5. Code size and complexity

Fresh source counts at the snapshot, using 006-08's test stripper. A code
line has code on it; comments, blank lines and test methods are excluded;
imports, declarations and braces count. The stripper is a heuristic, not
a compiled feature-removal experiment.

| Code | Production code lines | Attribution |
|---|---:|---|
| `IKeyModSet`, `KeyModSet`, `RerunException` | 5 + 148 + 10 = 163 | Dedicated conflict machinery |
| `Db.stmCheckConflicts`, `stmRecordKeys` | 7 + 5 = 12 | Dedicated conflict machinery |
| **Identifiable core conflict machinery** | **175** | Excludes plumbing and synchronization elsewhere |
| `Action`, whole `RwTransaction` | 4 + 110 = 114 | Also includes outputs, transaction metadata and sync methods |
| Whole `Trans` | 197 | Also the general transaction builder and write representation |
| Whole `RwEnvironmentImp` | 442 | Also values, indexes, serialization and application outputs |
| Whole `DbClock` | 65 | MVCC lookup/publication and transaction ordering, not solely STM |
| `Db.warmup`, whole `executeInner` | 7 + 41 = 48 | Mixed-purpose orchestration; called mechanisms live elsewhere |

For context, the same heuristic gives 22,455 production code lines across
205 files of `java/src`. The narrow 175-line count is about 0.8 percent of
that total, not an estimate of STM's complete cost or removable code.
No saved jar/native bytes have been measured. A credible removal estimate
requires a compiling alternative with the same stated API and semantics.

The complexity is concentrated in dependencies between mechanisms, rather
than those 175 lines: complete read tracking; bounded history and restart;
retry lifetime and fairness; memory publication; and ordering failure,
append, eviction and reclaim around the commit. Single-writer Dag mutation
currently simplifies several of these. A design with multiple Dag mutators
would add another category of synchronization and recovery work.

Reproduce the counts with:

```sh
python3 -B items/006-2026-q4/11-stm-concurrency/size.py
```

The script and [size.txt](11-stm-concurrency/size.txt) preserve the method
and result. There is deliberately no claim that deleting all the
mixed-purpose files would be possible or desirable.


## 6. Value: what should justify keeping or changing it?

The useful comparison is equal application work and equal durability:

* **Current optimistic actions:** independent transactions prepare in
  parallel and serialize their validated commits. Best prospect: substantial
  useful preparation, few conflicting keys, short validation lifetimes.
* **Serialized application actions:** serialize the entire read-compute-write
  operation, while retaining snapshot readers and the existing storage path.
  This avoids competing actions invalidating each other. Best prospect:
  tiny actions or frequent conflicts. A fair control keeps `sync()` outside
  that application mutex when the optimistic case also allows overlapping
  sync waits.
* **Parallel Dag mutation:** a substantially different implementation.
  Consider only if the serial lane is measured to be the limiting cost and
  the achievable benefit justifies the additional protocol.

For an idealized workload, let useful parallel preparation take P seconds
and serial commit take S. One caller completes about `1 / (P + S)` per
second. N callers cannot exceed `min(N / (P + S), 1 / S)` without reducing
S. Conflicts, contention, maintenance and storage waits can lower that
ceiling. For example, P = 90 microseconds and S = 10 microseconds gives
10,000/s for one caller, at most 40,000/s for four and a serial ceiling of
100,000/s. These are illustrative values, not BergDB measurements.

STM's main benefit is therefore safe overlap of useful preparation. It
does not itself make the serial Dag update parallel, nor is it required
merely to have concurrent snapshot readers or group commit. Its main runtime
costs are validation/recording, extra allocations, repeated useful work,
warm-up and retry delay. Which side wins is still an empirical question.


## 7. Proposed starting work

This was the plan before benchmarking; section 10 records the execution
and results.

**First experiment: measure the current design against serialization of
whole application actions, with no production change.** Keep the benchmark
and any temporary instrumentation in this subitem. If the work grows beyond
a short investigation, give it a separate item and leave the result here.

1. **Establish the correctness boundary.** Use 005-70's reproducer and its
   proposed lower-bound fix as separate follow-up work under that issue.
   Reuse the existing counter/retry tests; add a known-total transfer or
   equivalent invariant workload to the benchmark. Audit dependencies for
   the read operations the benchmark actually exercises. Do not treat a
   throughput result as evidence for all transaction semantics.
2. **Build a small harness without a surrounding execution lock.** Use one
   Connection and transaction state per worker, a common start barrier,
   worker-local counters, checked worker failures and bounded joins. Use
   the production clock. Preload a fixed key set. Compare normal `c.rw`
   with an application mutex enclosing the complete `c.rw` call. Both
   still perform STM checks: this isolates overlap, not validation overhead.
3. **Run a small first matrix.** Use 1, 2, 4 and 8 workers; disjoint counters
   and one shared hot counter; negligible computation and a calibrated,
   useful CPU loop after the read. Start resident, with a small fixed data
   set and enough cache to avoid eviction. Add blind writes as a control.
   Consume computation results so the compiler cannot discard the work.
   Sleeping is not a substitute for CPU work.
4. **Measure the whole operation.** Successful transactions/s, p50/p95/p99
   and maximum latency including retries, attempts per commit, CPU use,
   allocation/GC and per-worker progress. In a separate diagnostic run,
   split callback/build/warm-up, lock wait, lock hold and durable wait.
   Account for instrumentation overhead. Check the final invariant and
   committed outputs after every run.
5. **Then extend where the first result points.** Disk append and durable
   modes separately, with equal sync policy; eviction/reclaim under load;
   larger read/write sets; validation-window exhaustion and hot keys. Use
   fresh JVMs, warm-up and repeated runs in alternating order, recording
   commit, machine, JDK, GC and parameters. Preserve raw results. A durable
   wait must not be confused with the CPU cost of STM.

Deliverable: a table showing when concurrent preparation helps, when retries
make it worse, and where the serial time goes. Include the saturated single
commit lane's capacity and per-worker latency/fairness, not just aggregate
throughput. Only then choose a change: retry policy, avoidable work under the
lock, single-writer optimization, or a more ambitious concurrency design.

To measure the cost of validation itself, a later scratch variant may omit
it only on a workload whose complete read-compute-write operation is already
serialized. It must preserve the applicable API and pass its correctness
checks before its runtime or code-size difference is meaningful.


## 8. Relation to other work and status

* **[005-07](../005-todo/07-transaction-synchronization.md)**, still open,
  owns the broader synchronization review. Its
  2026-10-19 description predates the current fail-stop go point, handles,
  gradual eviction, reader changes and group commit. This item uses the
  current source; those older concerns are not all still open as written.
* **[005-70](../005-todo/70-keymodset-after-start.md)** owns the restart
  validation defect; this report does not fix it.
* **[005-12](../005-todo/12-transaction-outputs.md)** owns transaction outputs
  and action lifetime; its current tests
  provide useful STM correctness coverage.
* **[005-48](../005-todo/48-group-commit.md) /
  [005-64](../005-todo/64-buffer-time-after-group-commit.md)** supply the
  group-commit and buffer-time evidence.
* **[010-01](../010-principles/01-principles.md)**, especially P1, P2, P7,
  P11 and P12, constrains future changes:
  bounded pauses, deterministic stream for a given committed order, fail-stop
  after the go point, simplicity and a small Core. Different concurrent
  schedules may select different transaction orders; byte equality should
  compare the same committed order.

2026-10-30. Created at Frans's request. Inspected source, tests and the
existing investigations; counted code and rebuilt/reran the focused tests
in isolation. Initial report and proposed first experiment complete at that point. The
performance comparison is now complete in section 10; keeping STM is the
recommendation, not an applied production change.


## 9. How small can the single-writer section be?

2026-10-30, follow-up requested by Frans: which code must have one writer,
whether the section has been minimized, and whether it could be smaller.
Source inspection only, at the same snapshot. No code changes or new timing
measurements. This review does not depend on resolving 005-70.

### 9.1. Assessment

**The critical section has deliberately been shortened, but I would not
call it minimized.** It is a single-writer database commit and maintenance
section, not just the STM check. Some of its work must stay serialized in
this architecture; some could be prepared outside it; other work could be
separated only by introducing additional state, ordering and failure rules.

Already outside the normal write-lock interval: application actions, Pub API
preparation, transaction construction, the value-size check, write-key
warm-up, the storage consumer's writes/forces, and the caller's durable wait.
File deletion after a reclaim cut is also on its own thread. Reader
publication was changed to avoid a shared monitor on every get. These are
real concurrency improvements, not an untouched serial implementation.

Nevertheless, cold node reads can still happen inside preflight, puts and
maintenance. The buffered append can also wait for disk progress while the
writer retains `Db.writeLock`. Disk forcing being on another thread does
not mean a commit can never wait on storage under this lock.

### 9.2. What needs serialization

| Work | Why it is serialized today | What could change |
|---|---|---|
| Check current database state, limits and read dependencies; accept a transaction; record its write hashes | Another writer must not change the checked state between validation and the accepted write. `KeyModSet` is not concurrent | Keep an atomic acceptance protocol; merely releasing the lock after validation is incorrect |
| Assign transaction time, update the shared Dag and publish a lookup time | One mutable Dag, one root/history sequence, shared node-id allocation and one `ExecuteData`; readers depend on the publication protocol | Parallel preparation is already possible. Parallel Dag mutation would need a different mutation/publication design |
| Decide the dirty nodes, take old transactions for storage and update startup bookkeeping | `TransSeq.take` consumes shared D/history state; nodes are cleaned and the still-dirty test can put them back; the next commit depends on the result | These state transitions remain ordered; prepare independent data around them |
| Assign stream positions, previous-version links and newest-written-top state | Positions depend on preceding records and meta blocks; the serializer writes positions into live nodes | Keep an ordered layout/reservation step; encoding a stable snapshot could run elsewhere |
| Append records and advance stream/meta-block state | Recovery, references and restart invariance require a coherent append order | One ordered append service could replace holding this particular monitor, but ordering remains serial |
| Change reclaim progress/cut state or detach live nodes for eviction | Both mechanisms share roots, nodes and writer bookkeeping | Run at safe transaction boundaries or introduce a reviewed finer-grained protocol; another thread alone is insufficient |

For example, two actions can both read counter 0. If both validate before
either accepted write is recorded, both can approve writing 1. The global
lock currently prevents that gap. An alternative protocol might close it
another way, but a smaller synchronized block around just
`stmCheckConflicts` would not.

The clock publication is also not the end of the current writer section:
`transactionEnd()` is before `stmRecordKeys()` and `store()`. Readers may
see the new lookup time while the committing writer still holds the lock;
the next writer cannot proceed until that transaction's bookkeeping and
record are ready. Treating `transactionEnd()` as a safe unlock point would
ignore those dependencies.

### 9.3. The strongest candidate: record encoding and checksums

`NodeStream.appendNodes` currently does all of this under `Db.writeLock`:

1. Choose the next stream position.
2. `StoredTrans.Serializer.prepareToSerialize`: compute the record layout,
   save previous positions, and set new positions in the live nodes.
3. `serializeToBuffer`: encode headers and node fields, copy value payloads,
   compute node checksums and write the end marker.
4. Append the bytes through `RecoverableStream`, inserting meta blocks as
   required.

Step 3 contains substantial work that is not inherently a shared-state
update. `StoredValueNode.toBytes` copies every value and then runs a
Fletcher-16 pass over its serialized node. Key/top encoding also computes
checksums. Once the exact record data is stable, byte conversion and
checksum calculation do not need to exclude another application's useful
preparation or, with an appropriate pipeline, its next commit work.

There is already a comment in `StoredTrans.Serializer.serializeToBuffer`
estimating serialization at **30–40 percent of PUT execution time**, and
suggesting another thread with care for `KeyNode.size` and transaction order.
This is historical evidence of an identified opportunity, not a measurement
of the current implementation. It is not evidence for a current 30–40
percent saving.

Two possible directions, in increasing complexity:

* Prepare more of a stable, untransformed value payload before taking the
  lock, potentially including its checksum contribution. Final node ids,
  offsets, timestamp-dependent fields, headers and the exact final checksum
  must still be resolved consistently. The existing checksum covers the
  entire serialized node, including padding: moving the current checksum
  call earlier verbatim would be wrong.
* Separate ordered node/layout bookkeeping from encoding an immutable record
  snapshot. A worker could encode it and an ordered consumer append it.
  A separate serializer instance is not enough: today's serializer reads
  live mutable key/top nodes, their sizes, pointers and previous positions.
  A next writer can change those. Capture exactly the record's version and
  retain its payloads before allowing the next mutation.

The second direction has material costs: snapshots and buffers, bounded
queueing/backpressure, preserving append order, retaining data until append,
and preventing later records after a storage/encoding failure. It must also
preserve what `execute()` returning means: currently its record has been
appended to the buffered stream, though not necessarily made durable.
Snapshot creation itself might duplicate much of serialization's work.
Moving all encoding to one different serial thread may relocate the
bottleneck rather than remove it.

### 9.4. Smaller improvements to work under the lock

**Refuse conflicts before expensive structural preflight.** In
`executeInner`, the current sequence is `checkDirtyNodes`, `x.begin`, then
`stmCheckConflicts`. The first check is often a cheap bound, but for a large
transaction its fallback calls `dag.dirtyNodeBound` and can walk/load tree
paths. A conflicting action then discards that effort. Checking conflicts
earlier is a plausible small improvement for contended workloads; moving
`x.begin` later also avoids allocating its `TransInfo` for a rejected action.
This shortens wasted lock-held work, not the fundamental accepted-commit
protocol. Review which exception takes precedence when more than one
precondition fails, and retain state checks and all refusals before the go
point.

**Split preflight into independent preparation and state-dependent checking.**
Key lengths and other transaction-only facts can be prepared outside the
lock. The expensive dirty-node bound depends on the current Dag and stream
size. A result from an earlier snapshot cannot simply be reused: another
writer can change the tree, including its shape through unrelated keys.
It needs a conservative bound or explicit revalidation. The ordinary
application read set does not by itself validate tree topology.

**Reduce late transformation work.** `putKvs` invokes key transformations
and previous-value transformations while holding the lock. An atomic
previous-value update belongs with the accepted mutation; moving it earlier
requires recording/revalidating the value it used. A timestamp-based key
cannot be fully finalized before its commit time is assigned. However,
constant template searching/encoding can be prepared earlier. The Pub API's
timestamp-key replacement currently converts/scans a key and formats the
timestamp inside its transformation. These are candidates for less serial
work, not justification for running arbitrary transformation callbacks
concurrently against the current Dag.

**Statistics and listeners are secondary candidates.** Some statistics
could be aggregated from immutable scalar results afterwards. But the
current listener receives the shared mutable `ExecuteData`, and `x.end`
clears its references. Calling it after unlocking with the same object
would race with the next transaction. A copied event would require an
ordering and exception contract; a listener exception currently fails the
database. The default listener does nothing, audits are test-only and
optional reclaim statistics are normally off, so these are not established
production bottlenecks.

### 9.5. Maintenance is a candidate for separation, with constraints

**Reclaim has preparation as well as commits inside the lock.**
`transactionCompleted` can start an iteration, scan a historical range,
read current values, build a rewrite transaction, serialize a progress row,
and recursively call `Db.execute` for internal transactions. Reentrant
monitor acquisition means the outer transaction retains the lock throughout
that scan and construction too. This is a stronger candidate than merely
moving a small notification call.

Its scan/value preparation could in principle happen outside the writer
gate, followed by a revalidated internal commit. The step already registers
read keys and catches `RerunException`, which offers part of that machinery.
It is not a ready-made asynchronous protocol: iteration ownership,
retention expiry/cuts, progress rows, dirty-byte accounting, pacing and
internal record ordering still need review. Moving steps opportunistically
between different user records can change the stream even with the same
user transaction order; preserve 010-P2 or justify a revised deterministic
schedule. The old comment saying reclaim need not fundamentally belong in
the lock is not sufficient evidence that it is safe to move today.

**Eviction already has a worker, but it takes the same lock.** Under the
normal budget schedule, `afterTransaction` can execute a sweep batch with a
nominal 2 ms budget, checked between sweep steps. The eviction worker also
takes `Db.writeLock` for its batches and gives way to waiting writers.
Removing the inline batch could shorten an individual commit, but may only
transfer the wait to the next lock acquisition. Under continuous writers,
it could also remove a source of eviction progress while the worker keeps
yielding. Compare total writer wait/hold time, cache budget and maintenance
progress, not just the length of `executeInner`.

**A full write buffer is a separate issue.** `BufferedStream.append` waits
on its own monitor for room; that wait releases the buffer monitor, not the
outer database write lock. Moving the wait out requires capacity reservation
or an ordered handoff before irreversible mutation. It cannot make a slow
disk drain faster, and an unbounded queue would exchange a wait for memory
growth. Physical forces and the expensive file deletions are already on
other threads.

### 9.6. Where I would start

First check how well warm-up keeps slow stream reads out of the writer
section, including under eviction and during reclaim (section 9.8). Then
obtain profiles of unchanged code for single small puts, large values,
larger transactions, and maintenance under pressure. Sampling the existing
single-writer performance workloads can identify CPU costs without changing
source; distinguish running time from buffer waits, node-load waits and
eviction-lock waits. This complements section 7's later writer-scaling
experiment. No profiles were run in this source review.

Then, in order of scope:

| Candidate | Expected scope/complexity | Reason to pursue |
|---|---|---|
| Validate before expensive preflight; reduce redundant late preparation | Small, subject to refusal semantics | Avoid wasted work under contention without a new commit protocol |
| Precompute stable payload work/checksum contributions | Small to medium, requires exact byte/checksum equivalence | Remove work proportional to value size from the serial lane |
| Prepare reclaim steps outside the gate, with revalidation and deterministic scheduling | Medium to large | Avoid serialized scans/building if reclaim dominates |
| Snapshot records and pipeline encoding/ordered append | Large, new ownership, queueing and failure rules | Substantial potential only if record encoding is measured to dominate |
| Multiple simultaneous Dag mutators | A new concurrency design | Consider only after cheaper improvements and measurements |

This is a proposed priority, not a speedup prediction. Shortening a source
block or moving it to another thread is not sufficient: reduce the total
serialized service time or the writers' queueing, preserve bounded memory
and maintenance progress, and keep the same correctness and stream rules.

### 9.7. Source navigation and verification

Line numbers are for the snapshot named above:

| Source | Relevant entry points |
|---|---|
| [Db.java](../../java/src/bergdb/core/Db.java) | `executeInner` 1851; `checkDirtyNodes` 2059; `store` 2102; `putKvs` 2241; `ExecuteData` 2500 |
| [StoredTrans.java](../../java/src/bergdb/core/StoredTrans.java) | `Serializer.serialize` 451; `prepareToSerialize` 589; `serializeToBuffer` 668 |
| [StoredValueNode.java](../../java/src/bergdb/core/StoredValueNode.java) | `toBytes` 171: payload copy and whole-node checksum |
| [NodeStream.java](../../java/src/bergdb/core/NodeStream.java) | `appendNodes` 137: shared serializer and ordered append |
| [Reclaim.java](../../java/src/bergdb/core/Reclaim.java) | `transactionCompleted` 322; `step` 405; `pretruncateIfPossible` 658; `storeTable` 732 |
| [Eviction.java](../../java/src/bergdb/core/Eviction.java) | `afterTransaction` 259; worker's write-lock acquisition 515; `sweep` 571 |
| [BufferedStream.java](../../java/src/bergdb/storage/BufferedStream.java) | `append` 459: wait for capacity while the caller holds the database lock |

Reviewed these call paths and their shared state; no runtime improvement or
concurrency proof is claimed. Documentation only was changed for this
follow-up. Production Java and Lean were not edited; the earlier test
results in section 4 remain the earlier results, not new verification of a
changed implementation.

### 9.8. Warm-up and reads inside the critical section

Frans emphasized that avoiding disk reads in this section matters more than
small CPU savings, and that the current code was designed for it. The source
confirms that design: `Db.warmup` explicitly says its purpose is to avoid
lengthy disk reads and cache misses under `writeLock`. For an ordinary user
transaction, `executeInner` reads each write key before acquiring the lock.
This loads the lookup paths, including paths for keys that do not yet exist,
so the later put can normally reuse resident nodes. The STM conflict check
itself consults the in-memory `KeyModSet`, not the disk.

That is a substantial existing optimization, and the initial priorities
should reflect it. The source does not, however, establish an absolute
no-storage-read guarantee:

* Warm-up does not retain a transaction-scoped pin on every node it loads.
  Another writer or the eviction worker can run before this transaction
  acquires the lock. The writer follower still has a real cache-miss path:
  `WriterFollower.followPointer` calls `followStreamPointer`, which can
  reach `nodeStream.readNode` through `readVersion`.
* A commit-time key transformation can change the key after warm-up. The
  path actually written is then not necessarily the one warmed.
* Reclaim scans and internal transactions currently run while the outer
  user transaction retains the reentrant lock. Even the internal
  transaction's call to `warmup`, textually before its own synchronized
  block, therefore runs with the outer database lock held.
* Large-transaction dirty-node preflight can load paths under the lock,
  although it should benefit from ordinary warm-up when those paths remain
  resident. It is a possible miss site, not evidence that every preflight
  performs disk I/O.

The next measurement should count and time **stream loads while
`Db.writeLock` is held**, separating ordinary mutation, preflight and reclaim,
on resident and eviction-pressure workloads. A stream load served by the
OS file cache is different from a resident-node access and from actual
device I/O; report those distinctions where observable. No fixed disk/RAM
latency ratio is assumed here, and this source review did not measure their frequency. Section 10.5
now supplies measurements for the benchmark's ordinary read-write workload.

If the ordinary write path already avoids slow loads reliably in practice,
preserve that result and evaluate CPU opportunities next. If it does not,
understand the miss source before redesigning serialization. A proposed pin
or preparation scheme must also account for the memory of large transactions
and maintenance progress; warm-up is already doing useful work today.



## 10. Benchmarked value of STM

Completed 2026-10-30 by Codex, with two subagents implementing and independently
reviewing the harness. Frans authorized coding and unattended runs to answer
whether to keep STM. All 276 measured runs passed their counter
and stored-computation checks. The code and evidence are in
[bench/](11-stm-concurrency/bench/README.md); complete aggregate tables are in
[results/summary.md](11-stm-concurrency/bench/results/summary.md).

### 10.1. Recommendation

**Keep STM for the general read-write transaction API.** It buys concurrency
of database reads and work that depends on those reads, while the shared
Dag still has a single mutator. That produced substantial throughput gains
when there was useful preparation to overlap, including with real conflicts
and under eviction. Removing it would trade away that generic capability
for a modest improvement to short serial transactions.

Use fewer writers, or serialize the relevant actions, for very small resident
operations and hot keys. STM is a capability, not a reason to run every
workload with eight competing writers. The current retry policy also needs
attention: the hot-key test exposed approximately ten-second tail latency.

The gain applies to **work dependent on database reads**. Independent request
processing can already run in parallel without STM. An application that
itself guarantees disjoint ownership can also coordinate without optimistic
validation. These tests compare a general optimistic transaction API with
whole-action serialization; they do not compare every possible partitioned
or lock-based transaction design.

### 10.2. Concurrent actions against a partially stripped serial control

Each action reads counters, performs a fixed amount of dependent computation,
and writes one 32-byte counter value. The computation seed/result are stored
and checked; the compiler cannot discard the work. Resident data uses 4,096
keys, infinite retention and no eviction. All rates below are medians of
three fresh JVMs, in successful transactions per second.

The serial control removes conflict validation/recording, warm-up and point
read/write hash tracking in a temporary source copy, while serializing whole
application actions. This measures more than putting a mutex around stock
STM. It remains a partial removal: empty tracking objects, some arrays and
retry scaffolding remain. It is not a complete replacement product.

| Independent-key action | Partially stripped serial, 1 caller | Best stock concurrent rate among 2/4/8 callers | Callers | Throughput ratio |
|---|---:|---:|---:|---:|
| 1 read, no added computation | 298,027 | 239,792 | 2 | 0.80x |
| 8 reads, no added computation | 141,847 | 130,956 | 2 | 0.92x |
| 8 reads + approximately 9.4 us computation | 61,100 | 104,427 | 4 | **1.71x** |
| 8 reads + approximately 93.6 us computation | 9,869 | 67,714 | 8 | **6.86x** |

Eight callers on the first two workloads were worse: 223,876/s and
122,586/s, respectively, or 0.75x and 0.86x the stripped control. Eight was
also less effective than four on the 9.4 us workload: 97,275/s versus
104,427/s. More threads are not automatically better.

Against the stock serial single-caller baseline, the 93.6 us case went from
9,597/s to 67,714/s, **7.06x**. Its three eight-caller rates were
67,694–68,405/s (CV 0.5%); all three repetitions of these independent-key
computation workloads met the original 90%-idle gate. The large gain is
not a consequence of comparing against an unfair many-caller mutex.

These are capacity gains, not equivalent reductions in one call's latency.
At saturation calls can wait at the commit gate. The 93.6 us eight-caller
case used about 7.77 CPU cores including JVM/GC work, versus 1.13 with one
optimistic caller. The 9.4 us four-caller case used about 2.55 cores.

### 10.3. Shared keys and the retry policy

`uniform` shares the same key universe between workers. `hot` writes one
counter in 90% of actions; each action still reads eight distinct counters.
These comparisons use stock STM in both modes, with a mutex enclosing the
complete action in the serial baseline.

| Workload | Stock serial, 1 caller | Optimistic, 8 callers | Ratio | Largest observed optimistic latency at 8 callers |
|---|---:|---:|---:|---:|
| Uniform keys, no added computation | 108,443/s | 122,064/s | 1.13x | 53.9 ms |
| Uniform keys, approximately 9.4 us computation | 55,357/s | 91,694/s | **1.66x** | 51.0 ms |
| Hot counter, approximately 9.4 us computation | 57,428/s | 54,621/s | 0.95x | **10,258.8 ms** |

Thus some benefit survives ordinary shared-key conflicts; the independent
case is not the only positive result. The uniform/computation case averaged
1.00432 attempts per commit at eight callers.

The hot case shows why averages are insufficient. Its median attempts per
commit was only 1.00067 and its median per-run p99 latency about 31.7 us.
Nevertheless, a worker completed only one action during one three-second
window, and the observed maximum was 10.26 seconds. Throughput including
all delayed completions fell to 29,573/s, versus 54,621/s when counting only
completions within the requested window. The production 10 ms, 20 ms, ...,
10,240 ms backoff can put most contenders to sleep while one writer does
almost all the work.

Whole-action serialization with eight callers obtained 50,838/s on that
hot case, with no retries; one serial caller obtained 57,428/s. The mutex
control is itself unfair: for example, its 93.6 us computation case had a
1.74-second maximum call latency and very uneven worker progress.
A properly queued single-writer service could
have different fairness. This is why the single-caller and stripped
controls are reported in addition to same-caller-count comparisons.

### 10.4. Runtime, allocation and code-size cost

The isolated controls were run in serial mode only. They retain the same
snapshot selection, Dag mutation, stream encoding/append and failure path.
No application writer, index builder or reclaim task runs outside the
application gate. The broader stripped build supports this experiment's
byte-array point reads/writes; it is not a safe general optimistic build.

| Independent action, one serial caller | Stock rate | Without validation/recording | Narrow gain | Broader partial removal | Broader gain |
|---|---:|---:|---:|---:|---:|
| 1 read, no computation | 245,622/s | 256,376/s | +4.4% | 298,027/s | +21.3% |
| 8 reads, no computation | 115,974/s | 131,262/s | +13.2% | 141,847/s | +22.3% |
| 8 reads + approximately 9.4 us | 56,298/s | 59,554/s | +5.8% | 61,100/s | +8.5% |
| 8 reads + approximately 93.6 us | 9,678/s | 9,654/s | no detectable gain | 9,869/s | +2.0% |

The narrow checker has a measurable cost for small actions. Hash tracking
and warm-up contribute too; the combination is not free. The intermediate
warm-up-only results are in the full tables and are not consistently
additive: removing warm-up after the narrow bypass did not improve the
eight-read resident workload. Do not interpret these JVM variants as
independent timings of individual functions.

Broader removal reduced worker allocation from approximately 2,580 to
2,448 bytes per one-read action, and from 5,558 to 4,562 bytes per eight-read
action. Retained database history is separate from this allocation rate.

Section 5's count still applies: **175 identifiable production code lines**
for the core checker/modified-key set, plus mixed-purpose plumbing. That is
not the total feature size. The experimental builds bypass calls rather
than implement a complete alternate product, so no jar-size or complete
removable-code saving is claimed. Much of the existing reader publication,
Dag synchronization, eviction and storage complexity remains even without
STM. Retry semantics, read-set coverage, the finite validation history and
005-70 remain real correctness/maintenance costs.

### 10.5. File storage, durability and the critical-section I/O concern

File-backed cases preserve the same public API and run each durable wait
outside the application gate in both action modes.

| Case | Serial, 1 caller | Serial, 8 callers | Optimistic, 8 callers |
|---|---:|---:|---:|
| File append, 8 reads + approximately 9.4 us computation | 55,283/s | 51,023/s | 98,476/s |
| Durable commit, 8 reads + approximately 93.6 us computation | 177/s | 763/s | 770/s |
| File eviction, 8 reads, no added computation | 19,910/s | 19,137/s | 39,166/s |

Four optimistic callers gave the best append rate, 108,229/s, about 1.96x
the stock serial single caller. Durable throughput was essentially equal
between eight serialized and eight optimistic callers: their approximately
1% difference is not meaningful evidence for STM. The large increase from
one to eight durable callers comes from overlapping sync waits/group commit,
which whole-action serialization also permits. It must not be credited to
optimistic validation.

Under eviction, optimistic actions achieved **1.97x** the serial single-caller
rate and **2.05x** the serial eight-caller rate without added computation.
This is another useful form of preparation overlap. The setup used 131,072
keys, a requested 8 MB resident-node budget and a 1 MB startup distance;
end-of-phase resident-node accounting was approximately 7.0–7.8 MB. The JVM
heap was larger; the node budget is not a whole-process memory limit.

**Frans's point about keeping reads outside the critical section was borne
out for this workload.** Across the three eight-caller optimistic runs,
each five-second measured phase made approximately 3.63–3.67 million
underlying FileStream read calls outside `Db.writeLock`, and only 24–44
inside it. The total time in those lock-held read calls was only
0.044–0.083 ms per phase: over 99.998% of the recorded read calls were outside
the lock.

These counters are actual underlying read calls, not counts of physical
SSD requests. Preload warmed the OS file cache, so this does not establish
cold-device performance or a fixed disk/RAM ratio. Also, each action reads
its write key already: the result supports the combined read/preparation
path, not an isolated causal measurement of `Db.warmup`. Blind writes,
transformed keys and reclaim scans remain distinct cases. It is not an
absolute no-I/O-under-lock proof. It does show that speculative pinning or
lock redesign is not needed to explain the useful overlap measured here.

### 10.6. Method, checks and limits

* F53: Apple M1 Pro, 8 performance and 2 efficiency cores, 32 GB;
  macOS 27.0.1. JDK 27, source compiled with `--release 17`.
  Fresh benchmark JVMs used `-Xms512m -Xmx2g -XX:+UseZGC`, assertions off.
* 168 resident main jobs, 60 serial-overhead controls, 36 file append/durable
  jobs and 12 instrumented eviction jobs: **276 accepted measurements**,
  three repetitions per configuration. Main/control/file windows were
  three seconds after two seconds of warm-up; eviction windows five seconds.
* One Connection and local counters/histograms per worker, common start
  barrier, identical fixed key universe across worker counts, fixed
  computation iterations, and alternating mode/build order. Existing
  in-flight actions drain in both modes. Latency includes gate waits,
  retries and the optional sync; active and drain-inclusive rates are both
  preserved. Percentiles are histogram upper bounds, not exact quantiles.
* The unchanged source passed `before-commit.sh`: 1,071 unit and 78 functional
  checks. Seventeen assertions-enabled harness smokes, its unsafe-build guard,
  four file/durable plumbing checks and two extended control/eviction checks
  passed. Every accepted measurement recomputed stored work and verified
  the counter total, including warm-up and delayed completions.
* The first 141 main jobs met a 90%-idle CPU gate. macOS media analysis then
  kept the machine busy, and the gate stopped before starting job 142.
  The remaining 27 main jobs and the 108 follow-up jobs used a documented
  80% threshold; no system processes were stopped. Original interrupted
  metadata/results and the resumed session are retained. All three
  independent-key computation repetitions were already in the clean prefix.
  A [separate clean-prefix summary](11-stm-concurrency/bench/results/clean-main-summary.md)
  preserves that comparison. These are comparative engineering results,
  not a uniformly idle laboratory reference; few-percent effects should
  be interpreted cautiously.
* The workload is synthetic, closed-loop and deliberately read-dependent,
  with small values and one write per action. It does not establish results
  for large write batches/values, indexes, long transactions, open-loop
  latency targets or every key layout. Infinite history grows during the
  windows; different-throughput configurations accumulate different amounts.
  OS file cache is warm. No cross-restart action is tested, and 005-70 is
  neither fixed nor disproved by these measurements.

### 10.7. Outcome and evidence

Keep the capability. The measured saving from removing its runtime work is
useful for tiny serial operations, but much smaller than the capacity lost
when read-dependent work can no longer overlap. Choose concurrency based
on useful preparation and conflicts, not the number of available threads
alone. Prioritize the retry policy for hot keys and the already registered
correctness boundary; these runs do not justify replacing the concurrency
design or making the shared Dag multi-writer.

The [benchmark instructions](11-stm-concurrency/bench/README.md) link the
plans, implementation and reproduction commands. The
[aggregate tables](11-stm-concurrency/bench/results/summary.md),
[per-run CSV](11-stm-concurrency/bench/results/all-runs.csv),
[verification checks](11-stm-concurrency/bench/results/verification.json) and
[raw evidence archive](11-stm-concurrency/bench/results/raw-evidence.tar.gz)
retain the measurements, original harness versions, commands, idle samples,
GC logs, source manifests and experimental diffs. SHA-256 checksums are in
[SHA256SUMS](11-stm-concurrency/bench/results/SHA256SUMS).

2026-10-30. Benchmark work complete. Production Java and Lean were not
edited; benchmark code lives in this subitem and source variants in
isolated temporary builds. No commit was made. Keeping STM is a
recommendation for Frans, not a production design change applied here.
