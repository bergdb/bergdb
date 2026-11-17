019-35. Investigate: the Core's warm reads lost 1 to 6 % in the night of 5 to 6 November
=========================================================================================

Status: done 2026-11-07 (traced; the losses accepted for 2026.3, Frans,
2026-11-06, 12:31). Kind: Investigate. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: the night 006-12 landed about 50 fixes of the Core on `main`
(1068442..7cf665f). Its performance check, Q-B (006-12, section 3, W2),
found the warm reads and the restart of the quick suite slower, in each
of its three ABBA passes. Which commits cost it, and can it be won back
without undoing their fixes?

Why: 006-12's rule for Q-B: "No scenario may lose more than its CV; a
loss is traced to its commit and written up for Frans, not reverted."
Not traced in the night: the block ended at 05:49, and F53 had no second
quiet hour before Frans's morning.

Q-B: `performance.sh ab` with the quick suite on F53, quiet (load below
1.5 at the start, `mediaanalysisd` paused), 2026-11-06 05:08 to 05:49;
reference 1068442 (`main` at 15:00 on 2026-11-05), candidate 7cf665f
(`main` at 04:58). The summary in
`/Users/f/fl/bench/006-12/qb/out/summary.txt`, each pass in `ab1/` to
`ab3/`. "ABDIGEST: 4 scenarios, 66 metrics, 38 losses, 10 in every pass".
The change of the candidate's median against the reference's, a pass
each, and the larger CV of the two in brackets:

| Scenario, metric                 | Pass 1        | Pass 2        | Pass 3        |
|---|---|---|---|
| read-1k get_historical.ops_per_s | -2.3 % (0.6)  | -1.8 % (0.5)  | -2.4 % (0.6)  |
| read-1k get_latest.ops_per_s     | -1.6 % (0.3)  | -1.1 % (0.9)  | -1.0 % (0.7)  |
| read-1k get_latest_mt4.ops_per_s | -0.6 % (0.2)  | -0.3 % (0.2)  | -0.3 % (0.4)  |
| read-1k get_longkey.ops_per_s    | -6.4 % (1.5)  | -3.9 % (1.6)  | -3.0 % (1.2)  |
| read-1k scan_back.kvs_per_s      | -2.9 % (0.5)  | -2.1 % (1.5)  | -1.5 % (1.2)  |
| read-1k scan_fwd.kvs_per_s       | -3.6 % (0.5)  | -3.4 % (1.3)  | -1.9 % (1.6)  |
| read-1k scan_fwd_hist.kvs_per_s  | -3.1 % (0.6)  | -2.4 % (0.8)  | -2.5 % (1.5)  |
| w-uni-1k-inf restart.startup_sec | +2.6 % (0.7)  | +2.7 % (1.1)  | +2.3 % (0.4)  |
| w-uni-1k-fin restart.startup_sec | +4.3 % (1.2)  | +6.8 % (1.6)  | -0.9 % (1.4)  |
| r-1k-fin startup.sec             | +1.6 % (6.9)  | +1.6 % (2.2)  | +3.0 % (1.2)  |

The writes (`w-uni-1k-fin`, `w-uni-1k-inf`: commits and puts per
second) and `r-1k-fin`'s mix are within 0.7 %, mostly within their CV.

Leads, by reading only (nothing measured yet). `read-1k` reads through
the Core (`java/stress/Perf.java`, `getReads`: `db.getOne` with a
`GetData`), warm, so the Pub API's key checks (b1dbb32, 015-49) are not
on its path, nor the stream reads for the most part:

* 7bf7074 (015-35, 015-81): `Db.assertDbStateIsActive` reads
  `storageManager.hasFailed()` (the field `mainFailure`) in every call
  while the state is ACTIVE.
* The cache and its accounting on a hit: `Cache3` and `Eviction` (015-66
  to 015-70: 55d29a9, 9869ad0, eccd17a, 98c2ce0, 1155c9f; 019-22:
  c40e6c7), `Residents` (019-20, 019-21: 52f3286, 4efb703).
* The stream's reads of a cold node: 774940e (019-02, range checks),
  f8669c9 (015-83), 4c017a3 (019-10, a read's exceptions caught), e41df14
  (015-80, the lock around the calls to the stream below).
* The restart: review R5's F5 of the night (`/Users/f/fl/bench/006-12/
  review-r5.md`) measured the start's recount of 019-21 (52f3286, 4efb703)
  at about 0.7 µs per object, 110 ms of a 2.98 s restart at 1M keys,
  3.7 %, of the size of the loss.

Frans: none. If a loss is the price of a fix (the fault cannot be fixed
cheaper), the options go to Frans then, with their numbers.

Done when: each loss in the table that holds in every pass is traced to
its commit or commits by quiet A/B runs, and for each either a change
that wins it back, gated (`before-commit.sh`) and shown by an A/B run
against 7cf665f, or, if it is the price of a fix, the options for
Frans in this entry; the result in Q-B's form, here and in 018-01's
performance line if it changes.

First step: on a quiet F53, `performance.sh ab` with `ONLY=read-1k`
(RUNS as the quick suite) between 1068442 and 7cf665f again, to see the
loss alone, then bisect the commits that change `java/src/bergdb/core`
or `storage` in between (about a dozen on the read path, so four A/B
steps): first 7bf7074^ against 7bf7074. For the restart, `ONLY` its two
`w-uni-1k` scenarios between 52f3286^ and 4efb703.


Log
---

2026-11-06, 06:15. Registered by the coordinator of night 006-12
(coord-1105), from Q-B's summary.

2026-11-07, 06:10. Traced in block-q of 006-13 (00:30 to 04:15 on F53,
quiet; `/Users/f/fl/bench/006-13/night/out/summary.txt`): read-1k and
w-uni-1k-inf, `performance.sh ab` in eight segments that cover
1068442..7cf665f (each neighbouring builds), three passes each, and one
pass of the whole range again (tot).

* The whole range (tot, one pass): only w-uni-1k-inf's restart is
  slower, +1.7 %; the warm reads' losses of Q-B (1 to 6 %) did not come
  back beyond the CV.
* Losses in every pass: segment s69 (4c017a3..7cf665f: 52f3286, c40e6c7,
  4efb703, the 019-21 recount, R5's F5): the restart +3.9, +1.7, +1.6 %;
  segment s58 (774940e..4c017a3: e41df14, 015-80's lock, and 4c017a3,
  019-10's first fix): `scan_back` -0.9, -2.0, -1.8 %. No other segment
  lost in every pass (7bf7074's check in every call, s18, did not).
* Today's error model (s86, 7cf665f against cdabbcf): no loss in every
  pass.

So the losses are small and come from fixes of faults (the restart's
recount, the lock of 015-80); Frans, 2026-11-06, 12:31: the loss is
"accepted for 2026.3 unless the cause is cheap and clear". Neither is
cheap to win back without the fix it pays for. Closed as accepted; a
later look at the recount's cost (4efb703) could go to 017-07 if Frans
wants. Closed by coord-1106.
