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


## 4. Back to empty: why the lag is 8,064 at 1/4 and 33,501 at 3/8

By the agent "frac" of coord-1113, 2026-11-13, 07:29 to 07:45: reasoning
from `Reclaim` and counting runs of workload (d) with the iterations
printed. In short: **the lag is the rest of one iteration's scan, which
walks every key that was live at the iteration's start, 75 keys a user
transaction whatever f; which iteration that is, and how many keys it
holds, is a phase of the iterations against n, not a property of f.**
The 1/4 against 3/8 order flips with n (1/4 shorter at 3M, 4M and 10M,
3/8 at 1M, 2M and 6M). The runs are deterministic: the reruns gave the
night's counts at 1M and 10M exactly.

### 4.1 The mechanism

G4's workload (024-30, section 8): n keys filled in key order, 100 puts
a transaction; all deleted in key order, 100 a transaction; then the
drive, one put of 1 kB a transaction; R = 1,000 transactions, sd 100 kB.

* **A step scans at its iteration's start time** (`Reclaim.step`,
  `g.lookupTime = it.tStart`): an iteration walks every KV that was live
  at tStart, deleted since or not, at most 16 kB of scan a step
  (`MAX_STEP_SIZE`, 75 KVs here: 8 bytes a key segment, 100 of value, 100
  a KV) and at most one step a user transaction.
* **A step that finds the keys deleted charges nothing.** The charge is
  what a step writes; a KV deleted since tStart is not rewritten (024-34).
  So the allowance `fractionOf(growth since pStart, f) - rewritten` stays
  above the 16 kB cap, and the step cap paces the iteration: 75 KVs a
  user transaction, whatever f.
* **The iteration X that runs when the deletes end** began with K KVs live
  and ends about K/75 transactions after its start. Begun during the
  deletes, which remove 100 keys a transaction, it outlasts them by
  K/75 - K/100 = **K/300 transactions of drive**; begun in the fill, by
  its start + K/75 - the deletes' n/100.
* **Then two more cuts.** The cut that leaves only the drive's records is
  the one at the pStart of the iteration Y that begins when X ends; it
  comes when the iteration after Y (begun R/4 after Y, about 25
  transactions long) is older than R: **lag = X's end + 1,265 to 1,281**
  in every run (X's own cut keeps the deletes' records written after X's
  start, 61 MB at 1M and 1/4).
* **Which iteration is X: a chain through the fill.** Each iteration of
  the fill scans the keys live at its start while the fill adds 100 a
  transaction. One paced by the step cap, begun at K keys, lasts K/75
  transactions, so the next begins at K + 100 K/75 = 7/3 K keys. At 3/8
  and 1/2 the fill's iterations run at the cap (10M, 3/8: 56,822 steps
  in 56,824 transactions), so both have the same chain at every n:
  335,304, 782,604, 1,826,304, 4,261,604, 9,944,004 keys. At 1/4 the
  fill's iterations are paced by f (92,049 steps in 113,562
  transactions at 10M), and the chain is 410,704, 1,067,704, 2,614,704,
  6,610,004 (2.45 to 2.6 times). Where n falls in its chain decides K.
* **At 10M**: 3/8's chain began an iteration at 9,944,004 keys, 560
  transactions before the fill's end; it is X, scans 9.94M KVs in 132,634
  steps and ends 32,233 transactions into the drive, about the worst case.
  1/4's iteration of 6,610,004 keys ended 79,662 transactions into the
  deletes; X began with 2,033,804 keys left and ended at 6,787. **At 1M**
  the other way: 1/4's X began with 932,304 keys (end 3,116), 3/8's with
  173,704 (end 584).

So it is neither f's size, nor the startup distance, nor rounding, nor
noise: f changes only which chain (paced by f or by the cap) and so the
phase. The database's size enters through the phase and through the
bound: K is at most n, so **the lag is at most about n/300 + 1,280
transactions** with deletes of 100 a transaction (more with larger
deletes: up to n/75 for one delete of everything), and at least about
1,280. Until then the stream keeps about all it held before the deletes,
2.6 GB at 10M.

### 4.2 The runs

FracRuns work=d with `g4its=1` (CountGates' G4 prints its iterations and
cuts; branch `026-04-lag`, head 9859a419, in the clone
/Users/f/fl/bench/2026-11-13/frac/clone; one slot, 07:30 to 07:42). X's
start and end in drive transactions (the deletes are the n/100 before 0,
the fill the n/100 before them). Every lag below n/300 + 1,280. The
lags at 2M, 3M, 4M and 6M at 3/8 were predicted from the chain before
the runs: 3,890, 7,070, 13,740, 8,130; measured 3,971, 7,068, 13,736,
8,128. Output: `04-reclaim-fraction-settings/lag-iterations.txt` (X and
the iterations up to it, every run), `lag-run.sh`, `lag-an.py`.

| n   | f   | X's start | X's KVs   | Steps   | X's end | Lag    | n/300 + 1,280 |
|---|---|---|---|---|---|---|---|
| 1M  | 1/4 | -9,323    | 932,304   | 12,432  | 3,116   | 4,395  | 4,613  |
| 1M  | 3/8 | -1,737    | 173,704   | 2,317   | 584     | 1,857  | 4,613  |
| 1M  | 1/2 | (night)   |           |         |         | 1,850  | 4,613  |
| 2M  | 1/4 | -13,853   | 1,385,304 | 18,472  | 4,626   | 5,907  | 7,946  |
| 2M  | 3/8 | -21,737   | 1,826,304 | 24,374  | 2,700   | 3,971  | 7,946  |
| 2M  | 1/2 | -21,746   | 1,825,404 | 24,339  | 2,594   | 3,860  | 7,946  |
| 3M  | 1/4 | -33,853   | 2,614,704 | 35,351  | 3,240   | 4,521  | 11,280 |
| 3M  | 3/8 | -17,384   | 1,738,404 | 23,180  | 5,800   | 7,068  | 11,280 |
| 3M  | 1/2 | -17,405   | 1,740,504 | 23,208  | 5,806   | 7,071  | 11,280 |
| 4M  | 1/4 | -8,353    | 835,304   | 11,139  | 2,792   | 4,066  | 14,613 |
| 4M  | 3/8 | -37,384   | 3,738,404 | 49,847  | 12,467  | 13,736 | 14,613 |
| 4M  | 1/2 | -37,405   | 3,740,504 | 49,874  | 12,472  | 13,737 | 14,613 |
| 6M  | 1/4 | -53,900   | 5,390,004 | 71,868  | 17,974  | 19,253 | 21,280 |
| 6M  | 3/8 | -20,560   | 2,056,004 | 27,415  | 6,859   | 8,128  | 21,280 |
| 6M  | 1/2 | -20,609   | 2,060,904 | 27,480  | 6,874   | 8,138  | 21,280 |
| 10M | 1/4 | -20,338   | 2,033,804 | 27,119  | 6,787   | 8,064  | 34,613 |
| 10M | 3/8 | -100,560  | 9,944,004 | 132,634 | 32,233  | 33,501 | 34,613 |
| 10M | 1/2 | (night)   |           |         |         | 33,181 | 34,613 |

3/8 and 1/2 are within 3 % of each other at every n: in this workload
a fraction above about 3/8 buys nothing, the step cap paces (as in the
empty iterations of 024-29, section 9.2).

### 4.3 What it means for the default and the three values

* **No change to the default from this.** The back-to-empty lag ranks
  1/4 and 3/8 by the phase of n, three sizes each way; it is no argument
  for or against any f with today's code. Keep 1/4 (Frans, QF1); choose
  the three values on the stream kept, reclaim's writes and the
  throughput (sections 2 and 3; 024-29, section 9.4), and leave the lag
  out of QF29-1's limits until P8 is in.
* **The cure is P8** (023-05 P8, "each reclaim step scans at its own
  time"; 024-05, OP9), already decided for 2026.6 (026's readme): a scan
  at the step's time does not walk the deleted keys, so X ends with the
  deletes (P8's runs: 0 steps after the deletes at 1M, against 2,995).
  Expected then: a lag of about 1,280 at every n and f.
* **G4's lag gate** (024-30, Q30-3; 026's readme): before P8, a gate
  must allow n/300 + 1.3 R, which grows with n; after P8, a bound
  independent of n (such as 2 R) is plausible.
* **An observation, not proposed**: a step that finds little to rewrite
  is paced by its 16 kB of scan, not by f; the same holds for every empty
  iteration (024-29, section 9.2: 13,335 steps at 1M, so about 133,000
  at 10M). A cap on what a step reads rather than on the KVs it scans
  would shorten them; P8 covers the deleted keys only.

### 4.4 What to measure next

1. After P8 is on a branch: workload (d) at 1M, 4M and 10M at the three
   fractions (counts, about 10 minutes in one slot); expected a lag of
   about 1,280 each. Then G4's lag gate.
2. The timing pass at 10M (section 2, item 1), not done.
3. Other delete orders (descending, random): the phase argument holds for
   any order, as the scan walks the keys live at tStart; P8 measured them
   at 1M.


## 5. State

2026-11-12, 14:07: registered. 2026-11-13, 01:15: the runs at 10M keys done
(section 3). 2026-11-13, 07:45: the back-to-empty lag explained (section
4): a phase of the iterations against n, at the step cap, not a property
of f; it does not change the default (1/4) or the choice of the three
values; P8 is its cure. The instrumentation is on branch `026-04-lag`
(9859a419, CountGates' `g4its=1`) in /Users/f/fl/bench/2026-11-13/frac/clone,
not to land; the raw outputs in /Users/f/fl/bench/2026-11-13/frac/. Next:
the timing pass at 10M, then the three values and the default (section
2); workload (d) again after P8.
