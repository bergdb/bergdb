# Level 3 performance baseline (quick)

011-10. Moved here from `docs/level3-performance.md` on 2026-10-26 (006-07); history, not kept up to date.

Written by Claude (Sonnet 5.5) for Frans Lundberg, 2026-10-14.

A simple sanity baseline for Level 4, as defined in task 3 of
[level3-plan.md](06-level3-plan.md): after Level 4, run the same command and compare by
eye. A warm-read loss of more than about 10-20%, or a gross stall, needs an explanation.
This is not a regression gate and not a complete baseline; the fuller tooling is described
in [performance-harness.md](09-performance-harness.md).

**Status, 2026-10-16: the reference is `quick-2026-10-16-post-task1`** (next section), taken
on the code after task 1 and the Level 2 alignment, for bergdb item 001 (WP P1). The first
reference, taken before task 1 changed any production source (commit `2709e277`), follows it
and stays as the "before".

## Reference after task 1, 2026-10-16

* Tracked results: `java/bench/reference/quick-2026-10-16-post-task1/` (`summary.md` has every
  metric; `session.json` the source, JVM and machine).
* Source: the preserved build `l34-base` of bergdb item 001 (`performance.sh build`, WP A1):
  commit `dee7ad60` plus a working-tree diff that changed only test code
  (`java/stress/StreamDigest.java` and `A2A3Check2.java`); production source as at `8f37d88`
  (task 1, D0's topPos, D1's in-place splits). Jar SHA-256 `45037cbae774cb33...`.
* Command: `BUILD=l34-base JAVA_HOME=/opt/homebrew/opt/openjdk java/stress/performance.sh
  quick post-task1`, then `performance.sh promote`.
* Environment: as below (MacBookPro18,3, Apple M1 Pro, 10 cores, 32 GB, OpenJDK 27, G1,
  `-Xms8g -Xmx8g`, assertions off, OS file cache warm). 96.1% CPU idle at the start. Ran
  16:46-16:54 CEST.

| Measure | Before task 1 | After task 1 | Change |
|---|---|---|---|
| Warm latest gets, 200k keys, resident | 1.14 M/s | 1.28 M/s | +12% |
| Warm historical gets | 1.10 M/s | 1.26 M/s | +15% |
| Warm long-key gets (120-byte keys) | 0.87 M/s | 0.95 M/s | +10% |
| Gets from 4 threads | 2.40 M/s | 3.42 M/s (CV 7.9%) | +42% |
| Forward / backward scans (100 KVs) | 3.53 / 3.70 M KVs/s | 3.70 / 3.88 M KVs/s | +5% |
| Updates, infinite retention | 87.6k commits/s | 90.1k commits/s | +3% |
| Bytes appended per user byte, infinite | 1.22 | 1.22 | 0 |
| Updates, finite retention | 55.6k commits/s | 58.4k commits/s | +5% |
| Bytes appended per user byte, finite | 1.69 | 1.68 | -0.4% |
| Append commit latency, finite: p50 / p99.9 / max | 10.7 us / 128 us / 270 ms | 9.3 us / 116 us / 271 ms | |
| Startup after restart (50 MB section) | 0.70 s | 0.65 s | -7% |
| Mean of first 300k reads after restart / same reads again | 2.99 us / 0.65 us | 2.69 us / 0.56 us | -10% |
| Mixed phase (1 writer, 2 readers): commits/s, gets/s | 42.8k, 1.62 M | 47.3k, 1.86 M | +11%, +15% |
| Resident set size at the peak: reads, restart, finite writes | 1.63, 1.97, 2.69 GB | 1.62, 1.99, 2.84 GB | |

Nothing collapsed; reads and writes are a little faster. The reasons are not
established: D1's in-place splits write 1 to 14 percent fewer stream bytes
(docs/level2-alignment.md, 10.4), and the two sessions ran on different days on the
same machine and JDK. One session each, so differences under about 10 percent are not
meaningful. The worst pauses are again G1 young-generation pauses (85 to 162 ms
maxima), as described below.

## Reference before task 1, 2026-10-14

* Tracked results: `java/bench/reference/quick-2026-10-14-pre-task1/` (`summary.md` has every
  metric; `session.json` the source, JVM and machine; per-run compact results).
* Source: commit `2709e277220745626f31e1632df7f990bb9766ba` plus an uncommitted working-tree
  diff (the new performance files only; production source unchanged). Manifest SHA-256
  `fbee5ba77ed9a0b65e96e84498d1fb912bd35e42faf6079d04b8f8ef204f6479`, jar SHA-256
  `c907f156cc020e625373da9c622b7b4f527b1ae78430c2859ebd69b0fef74a73`.
* Command: `JAVA_HOME=/opt/homebrew/opt/openjdk java/stress/performance.sh quick baseline1`
  (suite `java/stress/performance-quick.suite`; the workload parameters are in that file and
  in every result).
* Environment: MacBookPro18,3, Apple M1 Pro, 10 cores, 32 GB, macOS 27.0.1 (26A434), APFS, on
  AC power; OpenJDK 27 (Homebrew build), G1, `-Xms8g -Xmx8g`, assertions off. 93% CPU idle at
  the start. OS file cache warm. Simulated clock; retention K = 1 update per key per window.
  Ran 11:27-11:43 CEST.
* Data: 200,000 keys (plus 20,000 long keys) or 100,000 keys, 1,000-byte values, 4-byte keys,
  default startup distance 50 MB. Finite-retention runs went on until at least 6 physical cuts.

## Results (median of 3 runs; spread = CV between runs)

| Measure | Median | Spread |
|---|---|---|
| Warm latest gets, 200k keys, resident | 1.14 M/s (0.79 us mean) | 2.0% |
| Warm historical gets | 1.10 M/s | 1.9% |
| Warm long-key gets (120-byte keys) | 0.87 M/s | 2.9% |
| Gets from 4 threads | 2.40 M/s | 0.5% |
| Forward / backward scans (100 KVs) | 3.53 / 3.70 M KVs/s | 1.1% |
| Updates, infinite retention | 87.6k commits/s | 0.5% |
| Bytes appended per user byte, infinite | 1.22 (write efficiency 0.82) | 0% |
| Updates, finite retention | 55.6k commits/s | 1.7% |
| Bytes appended per user byte, finite | 1.69 (write efficiency 0.59, store efficiency 0.446) | 0% |
| Append commit latency, finite: p50 / p99.9 / max | 10.7 us / 128 us / 270 ms | 0.3% / 6.9% / 2.3% |
| Startup after restart (50 MB section, 32k transactions rerun) | 0.70 s | 2.4% |
| Mean of first 300k reads after restart / same reads again | 2.99 us / 0.65 us | 0.8% / 7.5% |
| Mixed phase (1 writer, 2 readers): commits/s, gets/s | 42.8k, 1.62 M | 2.5%, 4.5% |
| Resident set size at the peak | 1.6-2.0 GB | <1% |

## Worst pauses

The slowest commits (270 ms with finite retention; 7 ms median of the maxima, one run 140 ms,
with infinite retention) coincide with G1 young-generation pauses of 85-155 ms (the log lists
them with the commits they overlapped). They are collector pauses of this heap and workload,
not database stalls; compare the pause maxima with the same collector after Level 4, since
eviction changes memory behaviour. Observed maxima are measurements, not latency guarantees.

## Limits

One machine, one JDK, one collector; asserts off; warm OS file cache (restart reads are not
device reads); simulated time; durable (synced) commits and 10 KB / 100-byte values are not in the
quick suite (see `performance.suite`). Timer resolution is 41.7 ns, so per-get percentiles
are coarse; use the throughput figures for warm reads.
