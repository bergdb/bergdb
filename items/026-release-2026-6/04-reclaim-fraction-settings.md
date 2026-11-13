# 026-04. Reclaim's fraction: three recommended values and one default

Created 2026-11-12 by Frans Lundberg. Status: open.

For release 2026.6. Frans, 2026-11-12, 14:07: "QF1. My conclusion is
that 1/4 is good for this release, keep it. But this requires more
investigation before next release. Add this to some item to ensure we
look at it for 2026.6. It should be measured for larger databases. We
should define three settings as recommended fractions and one default.
The measurements could be done tonight, if there is time. Even though it
is for 2026.6. This is mostly just machine time. To make the
measurements for larger databases, that is."


## 1. Where it stands

* 2026.5 keeps the default 0.25 (024-05, QF1, decided 2026-11-12,
  14:07), as since 2013 (024-29, section 3). The Pub API has no setter;
  the Core API's `Db.setReclaimInternalFraction` takes 0.001 to 0.90
  (Frans, 11:13: one default that works for every workload is good;
  advanced users set it through the Core API).
* Measured at 1M keys (024-29, section 9; 2026-11-12): against 1/4, 3/8
  keeps 8 to 29 % less stream beyond the history within R and cuts the
  lag after a mass delete by 58 %, for 15 to 27 % more bytes written,
  1.3 to 1.7 times the loads a put and 23 % fewer puts a second (one
  timing pass, data 245 MB over a 200 MB cache); 1/2 more so. Every
  other iteration is paced by the 16 kB step cap, not by f.
* The gates: 024-30's G3 gates the stream kept at 6 times the live data
  (4.41 at 1/4, workload (a)); the queue and the cold workloads reach
  6.18 and 6.46 at 1/4.


## 2. To do for 2026.6

1. **Measure at larger databases**: 024-29's four workloads (uniform
   overwrites, a queue, a cold set with 1 % hot, back to empty) at 10M
   keys and, if the disk and the heap allow, 50M, at 1/4, 3/8 and 1/2;
   counts first (WA_r, K_space, largest record, loads a put, lag), one
   timing pass. Mostly machine time; on F53 when it is free, or on s1
   (check `ps` there first). The program: `java/stress/FracRuns.java`
   on branch 024-29-fraction-runs (bundle in
   /Users/f/fl/bench/2026-11-12/fracm/clone until it lands).
2. **Three recommended fractions and one default**, exact in units of
   2^-16 (e.g. 1/4, 3/8, 1/2; 0.40 is not exact), named in the Core
   API's Javadoc and covered by the tests (each at least in level3's
   reclaim runs); whether the setter accepts other values (024-29, QF29-3).
3. **The limits that decide** (024-29, QF29-1): the stream kept beyond
   the history, reclaim's extra writes, throughput against 1/4, and the
   lag; with them G3's limit.
4. The step cap at large transactions (024-29, QF29-4).


## 3. Measured at 10M keys, 2026-11-12 night

On commit A of 2026.5 (bf9ab5af), in the release night (024-38, step
frac, 23:20 to 00:25), with 024-29's program at 10M keys; counts. Outputs
in `04-reclaim-fraction-settings/10m-work-*.txt`. K = the stream kept
beyond the user's records within R, in units of the twin's fresh stream
(peak and mean); WA_r = reclaim's extra stream bytes a user byte.

| Workload | f | WA_r | K peak | K mean | loads a step |
|---|---|---|---|---|---|
| a, uniform overwrites | 1/4 | 0.44 | 1.98 | 1.38 | 75.8 |
| a | 3/8 | 0.64 | 1.67 | 1.01 | 78.9 |
| a | 1/2 | 0.74 | 1.56 | 0.87 | 86.8 |
| b, a queue | 1/4 | 0.40 | 5.58 | 3.97 | 69.0 |
| b | 3/8 | 0.71 | 5.05 | 3.60 | 67.5 |
| b | 1/2 | 1.12 | 3.90 | 2.74 | 68.7 |
| c, cold, 1 % hot | 1/4 | 0.45 | 2.23 | 1.64 | 66.1 |
| c | 3/8 | 0.83 | 1.73 | 1.10 | 66.9 |
| c | 1/2 | 1.43 | 1.55 | 0.84 | 67.9 |

Back to empty (d), the lag in transactions of drive until the stream kept
is within twice the twin's: 8,064 at 1/4, 33,501 at 3/8, 33,181 at 1/2
(the twin's first cut at about 1,200 in each).

First reading (the coordinator's, for Frans): at 10M keys K is much lower
than at 1M (024-29, section 9: workload a 4.41 at 1/4, here 1.98), so the
stream kept beyond the history is well within G3's 6 at every f but in
the queue; a higher f costs reclaim's writes in proportion (0.44 to 0.74
in a, 0.45 to 1.43 in c); and back to empty is about four times faster
at 1/4 than at 3/8 or 1/2 here, the opposite of 1M's result: to be
understood before a default changes. Not measured: times (counts only).


## 3. State

2026-11-12, 14:07: registered. 2026-11-13, 01:15: the runs at 10M keys done
(section 3); next: understand the back-to-empty lag, times, then the
three values and the default.
