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


## 3. State

2026-11-12, 14:07: registered. The larger measurements may run tonight
if the machine has time beside the release night of 2026.5.
