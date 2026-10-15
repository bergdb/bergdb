# Level 3 performance baseline (quick)

Written by Claude (Sonnet 5.5) for Frans Lundberg, 2026-10-14.

A simple sanity baseline for Level 4, as defined in task 3 of
[level3-plan.md](level3-plan.md): after Level 4, run the same command and compare by
eye. A warm-read loss of more than about 10-20%, or a gross stall, needs an explanation.
This is not a regression gate and not a complete baseline; the fuller tooling is described
in [performance-harness.md](performance-harness.md).

**Status: taken before task 1 (power-loss repairs) changed any production source.** It
describes the Level 3 code as of commit `506510d9`. After task 1, run the command again and
promote the result under a new name (`quick-DATE-post-task1`); this one stays as the "before".

## Reference

* Tracked results: `java/bench/reference/quick-2026-10-14-pre-task1/` (`summary.md` has every
  metric; `session.json` the source, JVM and machine; per-run compact results).
* Source: commit `506510d9196bbf940a8bf6f4df3d5571699e845b` plus an uncommitted working-tree
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
