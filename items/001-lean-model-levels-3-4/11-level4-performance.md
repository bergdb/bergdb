# BergDB Level 4: performance against Level 3

001-11. Moved here from `docs/level4-performance.md` on 2026-10-26 (006-07); history, not kept up to date.

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-18. WP J10 of
bergdb item 001
([01-plan.md](01-plan.md)),
against the targets of its Q13. The baseline and the tool are in
[level3-performance.md](../011-docs-archive/10-level3-performance.md) and
[performance-harness.md](../011-docs-archive/09-performance-harness.md).

## Result

Level 4 meets Q13's targets against Level 3, with eviction off and with a
budget larger than the data: warm gets and scans within 5 percent (most
within 2), commits within 1.2 percent, startup 6.5 to 9.7 percent slower
(the target allows 20). No alert in either matched run. Under pressure (a
budget of 40 MB, a fifth of the read scenario's latest values), reads are
30 to 90 times slower, as they load from the stream; no target.

## The runs

`SUITE=quick java/stress/performance.sh ab l34-base current`, matched (ABBA,
3 runs a scenario each), on the quiet machine (95.9 and 95.4 percent idle at
the start; nothing else of this work ran): `l34-base` is the Level 3 code of
the reference `quick-2026-10-16-post-task1`; `current` is bergdb `52da9e6`
(J1 to J9) with `performance.sh`'s `JFLAGS`. Perf's databases are built with
`DbBuilder.noEvict()`, so:

1. **Eviction off** (05:48 to 06:03): the capacity controller's budget is
   `Long.MAX_VALUE`; the registry's accounting and the load listener run,
   no sweep.
2. **A budget larger than the data** (06:03 to 06:17):
   `JFLAGS=-Devictbudget=4000000000`, 4 GB, eviction on; the heap in use was
   at most 2.5 GB in every run, so the resident bytes stayed below the
   budget (Perf does not report the sweeps).
3. **Under pressure** (06:18 to 06:55): `JFLAGS=-Devictbudget=40000000`,
   `performance.sh quick` on `current` alone; the first run of the read
   scenario (it took 37 minutes; the whole suite would have taken hours, so
   the session was stopped after it).

The machine: MacBookPro18,3, Apple M1 Pro, 10 cores, 32 GB, macOS 27.0.1,
OpenJDK 27, G1, `-Xms8g -Xmx8g`, assertions off, the OS file cache warm.
Sessions in `java/build/perf/runs/` (not tracked):
`50a2a7be-d92fa83-20261018T054858-quick-g1-8g-ref` and
`4a2fc725-dc7faf3-20261018T054858-quick-g1-8g-cand` (off),
`...T060331-...-ref` and `...-cand` (budget),
`4a2fc725-dc7faf3-20261018T061806-quick-g1-8g-pressure40mb`.

## Against Q13

Medians of 3 runs; the change is the candidate's against `l34-base` in the
same matched session.

| Measure | Q13 | Eviction off | Budget 4 GB |
|---|---|---|---|
| Warm latest gets (1.30 M/s) | 10 % (investigate above 5) | +0.7 % | +2.0 % |
| Warm historical gets (1.27 M/s) | 10 % | -0.2 % | -0.1 % |
| Warm long-key gets (0.96 M/s) | 10 % | +0.4 % | +4.4 % |
| Gets from 4 threads (3.5 M/s) | 10 % | +4.0 % | +4.2 % |
| Forward scans (3.7 M KVs/s) | 10 % | +1.1 % | +0.5 % |
| Backward scans (3.9 M KVs/s) | 10 % | +1.1 % | -0.5 % |
| Historical forward scans (3.5 M KVs/s) | 10 % | +0.7 % | +1.9 % |
| Commits, infinite retention (90.7 k/s) | 10 % | -0.4 % | +0.2 % |
| Commits, finite retention (58.3 k/s) | 10 % | -1.2 % | -1.2 % |
| Startup after a restart (0.65 s) | 20 % | +7.9 % | +8.6 % |
| Startup in the write scenarios (0.57, 0.60 s) | 20 % | +9.7 %, +7.9 % | +8.9 %, +6.5 % |
| Mixed phase: commits, gets | — | +1.6 %, +13.4 % | +1.1 %, +12.6 % |
| Bytes appended per user byte | — | the same (1.22, 1.68) | the same |

All within the targets. The startup is slower by about 0.05 s, as in R8's
comparison (+6 to +8 percent there), whose candidates were rule 4's links
by node id and the loader's checks at startup; not looked at further, as it
is within the target. The mixed phase's gets are faster, as since R8's
change 4.

**Flagged to explain** (maxima, no threshold):

* The slowest of the first 300,000 gets after a restart: 259 to 275 µs
  against 112 to 118 µs. It is one get of 300,000: their mean is 2.7 to 2.8
  µs in both builds (+2 percent), their median 0.71 µs in both; the very
  first get takes 114 to 126 µs against 91 to 96 µs (the new classes'
  first use).
* The slowest commit with infinite retention, with the 4 GB budget: 154
  and 168 ms in two of the candidate's three runs, against 14 to 16 ms.
  Both builds have the same young collection of about 165 ms in every run
  (the scenario keeps all it writes in memory; the heap grows to 1.7 GB); in
  those two runs it fell inside a commit, in the reference's runs between
  commits.

## Under pressure

A budget of 40 MB, a fifth of the read scenario's 200 MB of latest values
(200,000 keys of 1,000 bytes and 200,000 historical versions, 20,000 long
keys): every read below the root's top levels loads from the stream (the
OS file cache warm, so these are memory copies and checks, not disk reads).

| Measure | Under pressure | Eviction off | Ratio |
|---|---|---|---|
| Latest gets | 40,370/s (p50 10.4 µs, p99 63 µs) | 1.30 M/s | 32 |
| Historical gets | 38,963/s | 1.27 M/s | 33 |
| Long-key gets | 15,354/s (p50 59 µs) | 0.96 M/s | 63 |
| Gets from 4 threads | 60,257/s | 3.66 M/s | 61 |
| Forward scans | 42,427 KVs/s (p50 0.99 ms per 100 KVs) | 3.76 M KVs/s | 89 |
| Backward scans | 42,716 KVs/s | 3.96 M KVs/s | 93 |
| Historical forward scans | 42,304 KVs/s | 3.54 M KVs/s | 84 |

Every value read was checked and the final verification of 220,000 keys
passed (`PERF OK`). The heap after a collection stayed below 600 MB (G1's
young collections: 822 in the run, 29.5 s in all, 121 ms at most; three
full collections). Reads under pressure are this slow because a get loads
about two versions, each read twice from the stream (the node's header for
its id, then the node: [level4-evidence.md](10-level4-evidence.md), the
limits), and a scan loads every leaf and value it passes. Four reader
threads read only 1.5 times as fast as one (not looked at further; a
sweep after a load holds the write lock, and the other readers' loads that
pass the budget wait for it).
Larger-than-memory runs on disk, with writes, are in level4-evidence.md.

## What it does not show

One machine, one session per configuration; differences under about 5
percent are within the sessions' variation. The quick suite's data fit in
memory; only the pressure run evicts. Writes under pressure are not in the
quick suite's run here (J8's runs measure them).
