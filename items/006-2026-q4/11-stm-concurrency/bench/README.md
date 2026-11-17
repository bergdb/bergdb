# 006-11 benchmark artifacts

This experiment measures the benefit of concurrent public `Connection.rw`
actions against serialization of each whole action. The report is 006-11,
section 10. The production tree is unchanged; experimental source variants
are built in temporary directories from commit
`377ff7af628f1fc214fc5945f9eda9179161868f`.

Completed: **276 measured runs**, all with verified counter totals
and stored computation results. See [results/summary.md](results/summary.md),
[all-runs.csv](results/all-runs.csv),
[verification.json](results/verification.json) and the
[raw evidence archive](results/raw-evidence.tar.gz).

## Workload and controls

Each action reads one or eight distinct counters at the public API's
snapshot, computes a dependent arithmetic chain, and increments its first
counter. Each 32-byte value stores the count, computation seed, result and
integrity guard. Every read checks the guard. At the end, all computations
are recomputed and the sum of counters must equal every successful action,
including warm-up and delayed completions. This checks lost increments and
stored work, not all possible serializability histories.

The total key universe is fixed across thread counts. `partitioned` assigns
disjoint subsets to workers; `uniform` shares all keys; `hot` writes key zero
with probability 0.9 and otherwise chooses uniformly. Additional reads are
distinct and come from the applicable key domain. One Connection belongs to
each worker. No application output, progress counter or histogram is shared
in the measured inner loop.

* `optimistic`: stock `c.rw(action)` from concurrent workers.
* `serial`: an application monitor encloses the entire `c.rw(action)`.
  Each worker still has its own Connection. Durable `sync()` stays outside
  this monitor in both modes, allowing identical group-commit opportunities.
* `stock`: unchanged production implementation.
* `serial-bypass`: omit `Db`'s conflict-check and modified-key-record calls.
  All read/write-set plumbing and warm-up remain.
* `serial-bypass-no-warmup`: additionally omit the pre-commit warm-up and its
  follower assignment, for a single-writer optimization control.
* `serial-stripped`: additionally remove point-read hash encoding/tracking
  and construction of the write hashes. Snapshot lookup-time selection,
  Dag mutation, publication, storage and failure handling remain unchanged.

The last three builds run **only serialized whole actions**. The stripped
control supports this benchmark's fixed byte-array point reads/writes; it
does not support general ranges, indexes, virtual keys, key transformations,
reclaim or cross-restart transactions. It is a conservative partial runtime
removal, not a complete replacement product: empty read-set/array objects,
retry scaffolding and the unused conflict-set allocation remain. The harness
rejects an experimental variant labelled as such in optimistic mode.

## Measurement

Every plan job is a fresh JVM, after an idle-CPU check, with fixed flags and
a fixed workload seed for each paired repetition. Jobs run sequentially.
The mode/build order is reversed on alternate repetitions. CPU-work
iteration counts are fixed across runs; calibration is reported separately
and never changes the workload. The initial 3,000/30,000-iteration
calibration was approximately 9.4/93.6 microseconds.

The first 141 main jobs passed a 90%-idle CPU gate. Sustained macOS media
analysis then stopped the gate before job 142. The remaining 27 main jobs
and 108 follow-up jobs used an explicitly recorded 80% threshold. Original
interrupted metadata and the resumed session are preserved; no system
processes were stopped. All three independent-key computation repetitions
were already in the clean prefix. A
[separate clean-prefix summary](results/clean-main-summary.md) checks this
subset. Few-percent differences, especially in the follow-ups, should be
interpreted cautiously; the results are not a uniformly idle laboratory
reference.

The main phase lasts three seconds after two seconds of warm-up. An action
already admitted at the deadline finishes in both modes; there is at most
one pending action per worker. Results distinguish fixed-window completions
from throughput through the last delayed completion. Latency starts before
waiting for the application gate and includes all retries, backoff and the
optional durable wait. Key selection is outside the latency timer but
included in elapsed throughput. Percentiles are histogram-bin upper bounds;
histograms have 16 subdivisions per power of two. Maxima are exact observed
nanoseconds. Worker counts expose starvation that aggregate percentiles can
hide. Worker CPU/allocation and process CPU/GC are also recorded.

Resident cases use MemoryStream, infinite retention and disabled eviction.
This avoids conflating STM with storage durability. History grows during
warm-up and measurement, so this is a short retained-history workload,
not an equilibrium claim for every database size. File append and durable
cases supplement it; eviction diagnostics request an 8 MB cache and a 1 MB
startup distance on a larger key set. Their OS file cache is warm after
preload: stream reads are not measurements of cold-device I/O.

Optional `diagnosticLoads=true` wraps the underlying AppendOnlyStream and
counts/times read calls with and without the Db write lock held. It does
not replace the production eviction callback. These counters concern
underlying stream reads, not exact per-node attribution or physical disk
requests. Instrumented diagnostic rates are labelled separately.

## Files and reproduction

* `RwBench.java`: workload, timing, verification and diagnostics.
* `build.py`: source snapshots, explicit experimental diffs, build manifests
  and jar identities. No tracked production source is edited.
* `run.py`: sequential execution, environment identity, idle check, command
  and raw output capture, correctness enforcement and disposable data cleanup.
* `summarize.py`: per-run CSV and medians/ranges/variation by configuration.
* `aggregate-main.py`, `finish-runs.py`: this session's explicit continuation
  and aggregation record. They use its temporary paths; the generic
  build/run commands below are the normal reproduction route.
* `package-results.py`: validates every accepted result and preserves exact
  harness/runner versions, source diffs, manifests and raw logs in the archive.
* `*-plan.json`: all effective scenario overrides and repetition order.
* `baseline-gate.txt`: unchanged build's 1,071 unit and 78 functional checks.
* `harness-smoke.txt`, `file-smoke-output.txt`: assertions-enabled harness
  checks, the experimental-mode guard and file/durable plumbing checks.

From the BergDB root, choose new output directories:

```sh
python3 -B items/006-2026-q4/11-stm-concurrency/bench/build.py \
  --out /private/tmp/bergdb-stm-builds \
  --commit 377ff7af628f1fc214fc5945f9eda9179161868f
python3 -B items/006-2026-q4/11-stm-concurrency/bench/run.py \
  --builds /private/tmp/bergdb-stm-builds/builds.json \
  --plan items/006-2026-q4/11-stm-concurrency/bench/main-plan.json \
  --out /private/tmp/bergdb-stm-runs --quiet
python3 -B items/006-2026-q4/11-stm-concurrency/bench/summarize.py \
  --session main=/private/tmp/bergdb-stm-runs \
  --out /private/tmp/bergdb-stm-summary
```

`--quiet` needs permission to read macOS CPU activity. The source is frozen
for a session: the runner rejects a change to `RwBench.java` between jobs.
Each session preserves its exact harness copy and hash, plan, Java flags,
machine information, jar hashes, per-run commands, stdout/stderr, GC logs
and result JSON. Raw evidence may be compressed after completion; summary
JSON/CSV retains each checked result's session and directory identity.
