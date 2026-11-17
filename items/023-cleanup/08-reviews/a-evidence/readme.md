# 023-08 Review A evidence

Created 2026-11-10. The review is `review.md` at the clone's root.
No production source was changed. Nothing was committed.

## 1. Source copies

Scratch sources and builds were under `/private/tmp/bergdb-review-a`.
Each prototype was exported with `git archive`, then built with its
`java/build.sh`. There was no branch switch in the review clone.

- Main: `53c394b4`.
- P4: `023-p4-empty-key`, `0e66d1c9`.
- P5: `023-p5-merge`, `71e386de`.
- P6: `023-p6-memory`, `c46d607d`.
- P7: `023-p7-topnodes`, `cd81d789`; default (a), optional (b').
- P8: `023-p8-steptime`, `f56dca40`.
- Combo: P7's Java tree, with P5's `Dag`, `KeyNode` and `PutData`,
  and P8's `Reclaim`. It includes merges and (a). It does not include
  SE, P6 or maintain(). (b') is enabled only in logs that say so.
- Path-mark: P8's Java tree with those three P5 classes and
  `path-mark.diff`, run with `-Dbergdb.p5.merges=false`.

The probe classes here are in `bergdb.core`. Compile them against the
chosen build's `build/classes`; put the probe output first on the class
path. Assertions were enabled. Runs used JDK 27.0.1 on f53.

## 2. Counterexamples

`ReclaimBeforeEnd`, default 1,200 rounds. Its settings and workload are
in the source. Logs:

- `p8-before-end.txt`: unmodified P8.
- `p4-before-end-control.txt`: P4, the tStart scan control.
- `combo-before-end.txt`: merges and (a).
- `combo-bprime-before-end.txt`: also `-Dbergdb.p7.ruleb=true`.

`ReclaimTail`, default workload. Logs `p8-tail.txt` and
`path-mark-tail.txt`. Both are from the final probe source, which also
measures the maximum increase of the iteration's dirtied-byte counter
in one call. A call runs at most one reclaim step here.

`SegmentAge` depends on `RoutingAge.current`. Logs `segment-p8.txt` and
`segment-combo-bprime.txt`. The latter enables (b'). It tracks the
original node id with the old delete entry, not merely a total node
count. Existing entries at a committed time cannot disappear in-place;
compaction makes a new id. Each report verifies that f passed the delete.

`RoutingAge`, default delete range 2,048 to 4,095 and default run length:
`p8-routing-age.txt`, `combo-routing-age.txt`. Other `combo-routing-*`
logs are shorter exploratory ranges. They do not establish a general
merge cleanup bound.

`CacheCapacity`: P6 with `-Dbergdb.p6.replaced=false` and
`--add-opens java.base/java.util=ALL-UNNAMED`. Default count 100,000;
argument `0` for the fresh control. Logs `p6-cache-capacity.txt` and
`p6-cache-twin.txt`. The byte budget is 1 GB, not a 1 GB allocation.
The probe sums the slots of every `Cache3` map's backing array.

## 3. Focused checks

- `combo-unit.txt`: `bergdb.dev.Unit` with classes DagTester,
  KeyNodeTester and DbTesterRestart. 96 successes includes the harness's
  own test.
- `fuzz-random.txt`, `fuzz-long.txt`, `fuzz-fifo.txt`: P5's UnlinkFuzz
  against Combo, node size 8, 180 transactions, five seeds per shape,
  four scans and strict mode. Long-key and FIFO shapes are separate.
- `fuzz-core-fifo.txt`: merges off, two seeds, 100 transactions, 30
  keys, two scans, strict mode. It exercises the LE-b and take-back path.
- `combo-a2a3.txt`: P5's A2A3Check2 against Combo, node size 8, 100
  keys, 300 transactions per seed, five seeds, up to 20 operations,
  60% deletes, long keys. It reports both raw and net node sets.
- `combo-restart-every.txt`: RestartInvariance, seed 1, 1,000
  transactions, 150 keys, startup distance 2,000, size 8, restart after
  each transaction, 100-byte values, deletes, long keys, R = 1 s.
- `p6-memory-unit.txt`: dead-hand and replaced-queue unit checks.
- `p6-held-reader.txt`: held-reader f-test.
- `p8-reclaim-unit.txt`: the two new reclaim step tests.
- `p7-counter-a.txt`, `p7-counter-bprime.txt`,
  `p7-counter-unsound-b.txt`: DbTesterRestart's Rule B counterexample,
  with the default three seeds. The last uses
  `-Dbergdb.p7.ruleb=d` and fails as intended. The unit runner's exit
  status is not enough; its printed FAILURE was checked.

## 4. The rewrite-path experiment

`path-mark.diff` replaces the range walk by point reads of the keys
about to be put, including the reclaim row, using the writer's marking
listener. It retains `Trans.touch`, touch counters, test hooks and the
pre-put accounting. It does not address the moving-frontier problem or
the old-entry deadline. Comments and interfaces are not production work.

- `path-mark-reclaim.txt`: ReclaimStress, 20 rounds, 20 cuts, 160
  exhaustive checks.
- `path-mark-crash.txt`: CrashTest, seeds 1 to 3, 400 transactions,
  20 cuts, 2 meta cuts, 10 after-transactions, startup distance 2,000,
  node size 8, retain 1 s. No transaction happened to end exactly at a
  meta block position; this is not coverage of that special case.
- `path-mark-[1-3].trace` and `path-mark-trace-[1-3].txt`: TraceExport
  seeds 1 to 3, n=400, keys=60, maxnode=8, sd=1000, del=60, long=1,
  valsize=100, probe=17, retain=1, rune=random, ereads=2, erestart=30.
  Each was checked by tracecheck; 15 cuts in total.

The prebuilt checker was copied read-only from the main repository. Both
source trees' `HEAD:lean` tree ids were
`800220fbada51c5203e70226922f6a80d315167b`. This is source provenance,
not a proof rebuild or a claim that the binary was rebuilt today.

Earlier `no-touch*` files are a discarded experiment. They cleared
`Trans.touch` entirely. Their positive cut checks do not make that a
candidate: the flag also supplies required dirtied-byte accounting.
The path-mark experiment supersedes it.

## 5. Limits

All runs were focused and short. No level script, performance suite,
night run, C port, full CleanupRule matrix or Lean proof rebuild was
performed. No SE test was run here. The main repository and the other
reviewers' directories were not changed.
