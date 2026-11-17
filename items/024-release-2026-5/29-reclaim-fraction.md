# 024-29. Reclaim's fraction: previous work, how to compare, the default

Created 2026-11-12 by Frans Lundberg. Status: decided (Frans,
2026-11-12, 14:07): 1/4 kept for 2026.5; larger databases and the other
values in 2026.6, 026-04.

Frans, 2026-11-12, 11:04 (006-23, section 5): "I want to investigate
0.25, 0.40, 0.50 for this factor. As default. There has been studies of
this before. What were the conclusions from them? And how to judge the
result, how to compare. [...] It a good setting, a good tradeoff for the
user. It was designed a long time ago and early in the process. I
believe it is needed. But the default is important. [...] we might need
guidance in the documentation for end users on this. Perhaps even just
allow a few distinct settings to keep things simpler and make testing
easier [...]. Let's start with previous work on this reclaim factor, or
whatever it is called." His frame from 10:42 and 10:56 (006-23, section
5): compare like with like, a database that keeps the same history (the
same retain duration R), and with R forever the stream follows the
history kept ("cost follows value").

Frans's direction, 2026-11-12, 11:13, after the coordinator told him the
Pub API has no setter: "a Pub user can't change it today. Oh, I forget.
This may not be so bad actually. If we can find a internal fraction that
always works, that is good. Advanced users could still set it using core
layer if really needed. So, not too bad as is. But for the sake of
testing, it still seems right to define three recommended values
somehow." So this item looks for (a) one default that works for every
workload, the Pub API keeping no setter, and (b) three recommended values
in the Core API that the tests cover.

Read only: the code of `main` at `9b75f819`, the items and notes named
below, and the 2013 to 2017 Git history (the bundle in F1-007). Nothing
built or run. By the agent "frac" of coord-1112, 11:05 to 11:20.


## 1. In short

* **What it is.** f, `internalFraction`, is the most reclaim may write
  while an iteration runs, as a share of the stream's growth since the
  iteration began: 0.25 by default, 16,384 units of 2^-16. It sets how
  fast reclaim moves the live data forward, and so how often the front
  can be cut. Core API only (`Db.setReclaimInternalFraction`, and JMX);
  the Pub API has no setter (checked: `Database`, `DatabaseBuilder`).
* **Where 0.25 came from.** Frans's note of July 2012 (010-02, P4) put
  the share at "something between 0.4 and 0.7" of the user's writes, as
  a fixed value, "not needed as a setting for the end user programmer",
  and named 0.25 as the "small factor" that writes less and keeps more.
  The code had 0.25 at the first commit of the 2013 Git (`1f4d0b6`,
  2013-06-06), as a share of all writes, and it has never changed. No
  note gives a reason or a measurement for it.
* **What was measured.** Only once was another value tried: 0.5 against
  0.25 on 2026-10-13 (011-04, "Level 3 cost"), before three of reclaim's
  later changes: the stream 22 to 32 % smaller, reclaim's extra writes
  3 to 5 times larger, updates a second about 45 % lower; "0.25 is the
  better default for that comparison; broader tuning remains open". All
  other numbers are at 0.25: reclaim is 26 to 38 % of all writes (W4),
  and the stream kept is 4.5 to 6 times a fresh database's under
  overwrites (024-05, ST3).
* **The sketch, corrected.** kept ≈ G(R) + j·W, with W = L'/f the growth
  while an iteration rewrites L' bytes, and j from 2 to 3 when f paces
  reclaim. With 011-04's share rewritten (about half for cold data),
  that is 1/f to 1.5/f times the live data, which fits ST3. But f paces
  reclaim only in one of four regimes: with a long R, a small database,
  or large transactions, reclaim is paced by R / 4, by twice the
  startup distance, or by its step cap of 16 kB scanned a transaction,
  and f then changes little or nothing (section 4.2).
* **A finding.** The step cap: one step a user transaction, 16 kB of
  scan. 024-03's runs of 100 KVs a transaction were at that cap (their
  iteration lengths fit it within a few percent), so a higher f would
  not have shortened them, and transactions of 1,000 puts would make
  iterations ten times longer than f allows. A measurement of f must use
  small transactions; a user with large ones gets less than f.
* **How to compare.** Two numbers a run, each against a run with the
  same workload and R forever: the extra stream bytes written a user
  byte (SSD wear, throughput), and the stream kept beyond the history
  of R, in units of a fresh stream of the live data. Then commit p99.9,
  reclaim's reads, and the lag after a mass delete (section 5).
* **The plan.** ReclaimCost's grid at f = 1/4, 3/8 (and 0.40 once), 1/2
  (30 MB, bytes only, about 1 hour), then Perf at 1M and 10M keys with
  10 puts a transaction (about 2 to 2.5 hours), then one timing pass
  (about 1 hour): about 4 to 5 hours of F53, best as a night (section
  6). 0.40 is 26,214 units, 0.399994; 0.375 is exact.
* **Measured** (2026-11-12, 13:12 to 13:33, section 9): at 1M keys, 10
  puts a transaction, R short. From 1/4 to 3/8 to 1/2, K_space's worst
  6.46, 5.70, 4.60; WA_r's worst 0.57, 1.00, 1.47; puts a second (uniform
  overwrites) −23 % and −38 %; the lag back to empty 4,395, 1,857, 1,850
  transactions. None meets all of QF29-1's proposed limits; recommended
  3/8 with the throughput limit at 25 %, else 1/4 with c = 7 (section
  9.5). Seven tests expect 0.25 (section 9.6).
* **Recommendation** (after Frans's 11:13 direction). The Pub API keeps
  no setter; one default chosen as the value that works in every regime
  (section 6, "How to decide"). The Core API names three recommended
  values, exact in units of 2^-16: 1/4, 3/8 and 1/2 (16,384, 24,576 and
  32,768), and the level 3 tests run at each in `night.sh`. The Core's
  setter keeps accepting 0.001 to 0.90, documented as untested outside
  the three (section 7). f is not in the Lean model, so the model does
  not change. The default: decided after the plan's numbers; the 2012
  note and the space side lean towards 3/8, the writes side to 1/4
  (section 8 asks Frans the weights).


## 2. What it is and what it is called

### 2.1 The mechanism

Reclaim runs only with a finite retain duration R (`setRetainDuration`;
the default is forever). It works in iterations (`Reclaim`'s class
comment; `docs/levels.md`, section 6):

* **An iteration starts** at an external transaction's commit when no
  iteration runs, the stream has grown by more than twice the startup
  distance sd since the last one started, and R / 4 has passed since then
  (`Reclaim.transactionCompleted`, `ITERATION_DIVISOR`). pStart is the
  stream length then; the cut point pCut is the previous iteration's
  pStart.
* **Steps.** After each external transaction (the user's; reclaim's own
  are internal and ignored), `allowed = fractionOf(length - pStart, f) -
  rewritten`. If `allowed` is above 10,000 bytes (`MIN_STEP_SIZE`), one
  step runs, with a scan target of `min(allowed, 16,000)`
  (`MAX_STEP_SIZE`): it scans live KVs from `lastKey` until it has
  scanned that many bytes (8 a key segment, the value, and 100, a KV),
  and in one internal transaction puts again each value stored before
  pCut. Its charge (`rewritten`) is the value nodes it writes and the
  stream size of the index nodes it makes dirty (011-04, items 2 and 3).
  So f is the most of the growth that reclaim's charge may take; at most
  one step a user transaction.
* **The cut.** When the scan reaches the end, the iteration is done
  (pEnd, tEnd). The stream is cut at pCut when tEnd is older than R, the
  startup position has passed pEnd and then pSafe (about one startup
  distance more of growth), and the table is durable.
* **Relation to sd and R.** f decides the growth an iteration needs,
  W = L'/f, where L' is what it rewrites and charges. sd and R set the
  least spacing between iterations (2 sd of growth, R / 4 of time). The
  slowest of the three (and the step cap, section 4.2) paces reclaim.
* **Reach.** f is kept in the stream since 015-87, in the internal KV
  `/#i/dreclaim/-settings.txt` (`fraction=16384`), with R; a setter call
  that changes either writes both, and a start reads it. A stream without
  the KV has the defaults. So a database that set R already keeps
  `fraction=16384` in its stream and keeps 0.25 after a release with
  another default; only those that set R later get the new default.
  The range is 0.001 to 0.90 (since 2013; NaN refused since 005-73), in
  units of 2^-16 since 005-79 (66 to 58,982 units).

### 2.2 Its names

| Where                       | Name                                                    |
|---|---|
| Core API                    | `Db.setReclaimInternalFraction`, `Db.getInternalFraction` |
| JMX                         | `getReclaimInternalFraction`, `setReclaimInternalFraction` |
| `Reclaim`                   | `internalFraction` (units), `DEFAULT_INTERNAL_FRACTION`   |
| the stream                  | `fraction=` in `/#i/dreclaim/-settings.txt`              |
| C clone (012-11, 022)       | `bergdb_set_reclaim_internal_fraction`, `rc_fraction_of` |
| `docs/levels.md`, 011-04    | "the internal fraction", f, "the allowance"              |
| 006-19, 024-05, 006-23      | "reclaim's fraction", "the quarter", "reclaim's pace"    |
| Frans, 2012-07              | "a factor of the ordinary transaction size"              |
| Frans, 2026-11-12           | "the reclaim factor"                                     |
| Pub API                     | none: `Database.setRetainDuration`'s Javadoc says "a quarter" |

"Internal" means reclaim's transactions are internal ones; a user does
not know that word. **Proposed for users: "reclaim share"**, the share
of the database's writes that reclaim may use while it runs ("reclaim
may use up to 25 % of the writes"). It says what the user pays, and its
direction is plain: a larger share keeps less on disk. With no Pub
setter (Frans, 11:13), the name is for the documentation: the Pub API's
`setRetainDuration` Javadoc says what the share is and its cost, and the
Core's Javadoc keeps `internalFraction` as the method's name.


## 3. Previous work and its conclusions

### 3.1 Frans's notes, 2009 to 2013 (010-02, P4)

* **2009-11-03** (010-02, P4): "We write W*0.5 amount of data to refresh
  old data and W to write new data": reclaim at half the user's writes,
  f = 1/3 in today's terms.
* **2012-07, `doc/2012/2012-07-space-reclaim.txt`, lines 79 to 89**
  (010-02, P4 and "A fixed share, not a setting"): the reclaim writes
  limited to "a factor of the ordinary transaction size", for example 5
  MB of reclaim for 10 MB of user transactions (50 %). "A high factor,
  say 1.0 would decrease the total file system space occupied by the DB,
  but increases the write throughput. A small factor (0.25) would reduce
  the write throughput, but increase the total size the files will
  occupy in the filesystem. I believe this can be hardcoded to something
  between 0.4 and 0.7. Needs testing/experience. But probably not needed
  as a setting for the end user programmer." That factor is reclaim
  over the user's writes, r; today's f is reclaim over all writes, so
  f = r / (1 + r): 0.4 to 0.7 is f = 0.29 to 0.41.
* **The same note, its algorithm of 2012-07-23** (lines 127 to 160): "Let
  40% (example) of the transaction size appended to the stream be
  dedicated to this process", and "the rewrite transaction will not
  occupy more than 40% of the stream": f = 0.4 as a share.
* **2012-08 notes**: "DONE! Stream space reclaim". **2013-06-06**, the first
  commit of the 2013 Git (`1f4d0b6`, `KissDB/src/kissdb/core/Reclaim.java`):
  `DEFAULT_INTERNAL_FRACTION = 0.25`, "the fraction of the stream allowed
  to be occupied by internal transactions compared to the total stream
  size while a reclaim iteration is running. A small internalFraction
  will reduce the stream writes [...] but increase the total stream
  size", `setInternalFraction` from 0.001 to 0.90 inclusive, a default R
  of 7 days. `git log -S` finds no later change of the value up to 2017
  (the bundle's 525 commits), and today's code has the same value.
* **Not found**: a reason for 0.25, or a measurement of it, in
  `doc/2012` to `doc/2016`, `log-old/` (grep for fraction, 0.25,
  quarter, reclaim, garbage, compaction). The 2013-01 notes and
  "BergDB features" of 2013 ask for few settings and sensible defaults
  (010-02, "No administration, few settings").

So 0.25 is the low end that the 2012 note named, not its recommendation;
in today's terms it is below all three of Frans's early values (1/3,
0.29 to 0.41, 0.4). The setting existed from the start, against the
note's "not needed as a setting".

### 3.2 Level 3 cost, 2026-10-13 (011-04, "Level 3 cost" and W4)

The source of `Database.setRetainDuration`'s Javadoc numbers.
`ReclaimCost` and `reclaimgrid.sh`: 30 MB of live data, 4-byte keys,
values of 100, 1000 or 10,000 bytes, uniform, hot and cold workloads,
single-put transactions, sd 6 MB, K (updates a key within R) from 0.01 to
10, simulated time, a CutStream in memory. Measures defined by Frans: WE
(user bytes / stream bytes appended) and SE (user bytes accessible within
R / stream kept).

* **First grid, f = 0.25**: WE 20 to 35 % below no reclaim at K up to 1,
  up to 39 % at K = 10 (the Javadoc's "23 to 38 percent lower" is the
  range at K up to 1); SE 0.09 to 0.62 (the Javadoc's "0.09 to 0.75"
  includes the later grids). Iterations ran back to back whatever K,
  at the rate f allows.
* **f = 0.5 against 0.25, first grid, 100-byte values** (and
  `docs/log.md`, 2026-10-13): the stream 22 to 32 % smaller ("about a
  quarter"), reclaim's extra writes 3 to 5 times larger, updates a
  second about 45 % lower. "0.25 is the better default for that
  comparison; broader tuning remains open." The only measurement of
  another value in the record. It was before step 3 (R / 4 pacing),
  option 3 (pCut one iteration older) and items 2 and 3 (the charge
  counts index nodes; the 16 kB step cap), and in memory.
* **After those changes** (still f = 0.25): with K up to 1 iterations
  still run back to back, WE 20 to 33 % below no reclaim; with K = 10
  the R / 4 pacing applies and WE is 3 to 18 % below. Option 3 halved
  the share rewritten an iteration: uniform 24 to 35 %, hot 43 to 46 %,
  cold 45 to 50 %. "So the choice left with a short retention is WE
  against SE, through f (or a target for one of them)."
* **W4, where the bytes go** (10 MB live, sd 2 MB, K = 1): reclaim is 26
  to 38 % of all stream writes, 34 to 61 % on top of the run without
  reclaim. The charge's cap is 25 % of the writes (a third on top); the
  measured share is within a factor 1.5 of it, larger for small values,
  as index nodes made dirty by a step are written again later and not
  all are charged. "So the allowance tracks the real cost well enough
  that a controller for WE or SE (D3, options B and C) is not needed
  now."
* **Q8** (011-04, the first finding): the stream kept is "about L/f to
  2L/f plus the retained history", measured, not derived.

### 3.3 The write amplification study (006-19, sections 3.4 and 6.8)

* Reclaim's share is held near f, "at most about f/(1-f) = a third more
  than the user's records"; the measured 26 to 38 % (W4) quoted.
* At 100M keys of 100-byte values an iteration rewrites about 19 GB and
  needs about 76 GB of growth at 0.25: "unless R / 4 holds that much,
  reclaim runs at its cap". Its larger cost at large sizes is space.
* 6.8: "a lower f makes iterations longer; fewer bytes a put, more
  stream kept". M4, reclaim at 10M keys on disk with Perf, was planned
  (section 7.2) and has not run (not found in any item). Its suite
  uses 1,000 puts a transaction, which puts reclaim at its step cap
  (section 4.2): rerun with small transactions if it is used for f.

### 3.4 Cleanup, 023 (R13 and the reviews)

* **023-02, R13**: with R finite, the stream at most c1 times the twin's
  stream plus c2 times the records of R plus a bounded number of
  iteration spans; 011-01's R5 with the spans a cut needs. The form of
  024-05's BD10.
* **023-06, section 4, item 4**: "one step a user transaction"; at a mass
  delete 1M keys need about 7,500 transactions before the cuts resume.
* **023-08 (the reviews' check)**: fault 13, a step counts every KV it
  scans against its 16 kB; review C's alternative, "a quota in
  proportion to the transaction", ended the probes too but wrote 30 to
  35 % more stream. And (023-08, review C, section 5.5): P8's bytes
  "within the internal fraction" were 10 % more in total.
* **023-01, section 9.2** describes the step as today, with the quarter.

### 3.5 The FIFO (021-25)

021-25, part 2: under the FIFO the touch of each step was charged to
`rewritten`, so the next step waited until the stream had grown by 4
times that (0.25); steps became rare and the iteration did not end.
Fixed by 024-07 (the touch follows the step's own puts). A lesson for
any change of f: the charge, not only f, decides the pace.

### 3.6 2026.4 at 1M and 10M keys (024-03) and the known cases (024-05)

* **ST3** (024-05, section 2; 024-03, sections 3, 4 and 7): with R of
  1,000 transactions (1 s on a test clock), 100 KVs of 100 bytes a
  transaction, sd 50 MB: under steady overwrites at 10M keys the twin
  keeps 1.45 to 1.95 GB against 0.33 GB fresh, 4.5 to 6 times; after a
  random fill of 10M keys 6.79 GB for about 1.13 GB of data; in the FIFO
  kept rose from 2.34 to 6.43 GB in 200,000 transactions and had not
  levelled off. "By design: [...] an iteration that rewrites the live
  data needs four times its bytes of growth."
* **The lag** after a 90 % delete: about 4 iterations at 10M (60,000
  transactions, 2.5 GB written), 3 at 1M (024-03, section 4).
* **BD10** (024-05, section 4): the stream kept at most c times the
  twin's plus R's records and two spans; c = 6 proposed as a gate on
  today's. **QF1** (024-05, section 7): accept the constant for 2026.5,
  "decide the fraction after OP1's fix and GM7". OP1 is fixed (024-07);
  GM7 (100M keys) has not run.
* **New reading of 024-03's numbers: they are at the step cap.** A step
  scans at most 16 kB, about 75 KVs of 13-byte keys and 100-byte values
  (16 + 100 + 100 = 216 bytes each), and there is one step a user
  transaction. 10M live keys / 75 = 133,000 transactions an iteration;
  024-03 measured about 130,000 in the FIFO. 1M keys left after the
  delete / 75 = 13,300; measured about 13,000 (23 in 300,000). At f =
  0.25 the allowance a transaction is about the same as the cap's (a
  quarter of about 42 kB of growth plus reclaim's own, against about 11
  kB of value nodes and the index nodes of a capped step), so both limits
  meet there; at 0.40 or 0.50 that workload would be held by the cap,
  and gain little. An inference from the code and the counts, not
  measured.

### 3.7 The C clone (012-11, 022)

012-11, done-when 1: iterations and steps as `Reclaim`, "each external
transaction allows a step within `internalFraction` of the growth"; the
fraction in units of 2^-16 (`rc_fraction_of`, 022's readme), the same
range, kept in the stream (015-87). No measurement of f. The C clone
follows release 2026.2 (015-02), so a change in Java reaches it only
when it is brought up to date.

### 3.8 Principles (010-01, 010-02)

* 010-02, P4, "Maintenance proportional to the user's work": f is that
  proportion. 010-02, "A fixed share, not a setting": the 2012 note.
* 010-01, P2 (a deterministic stream): f is an integer in units of 2^-16
  (005-79) and kept in the stream (015-87), so the stream's bytes do not
  depend on a double or on a restart.


## 4. The sketch: kept ≈ H(R) + k·L

The coordinator's sketch (006-23, 10:42): kept ≈ H(R) + k·L, k about 1/f
to 2/f; reclaim adds about f/(1-f) stream bytes a user byte. What the
code says.

### 4.1 When f paces reclaim

Let G(x) be the stream's growth in time x (the user's records with their
index, and reclaim's own), L' what an iteration charges (the values
stored before pCut and the index nodes its puts make dirty), W = L'/f the
growth while an iteration rewrites, and S the growth between iteration
starts, S = max(W, G(R/4), 2 sd). The cut of iteration i, at pCut = the
pStart of iteration i-1, comes when tEnd is older than R and about sd
has followed pEnd. So:

* right after a cut, kept ≈ max(G(R), sd) + S + W;
* just before the next cut, kept ≈ max(G(R), sd) + 2S + W.

When f paces (S = W): **kept ≈ G(R) + 2W to 3W**. With option 3, an
iteration rewrites about half the live data when it is cold, a quarter
to a third under uniform overwrites (011-04, option 3), so L' ≈ r·L with
r of 0.25 to 0.5, L the live data with its index, and **k ≈ (2 to 3)·r/f:
1/f to 1.5/f for cold data, 0.5/f to 1/f under overwrites**. At 0.25:
4 to 6 for cold data, which fits ST3's 4.5 to 6 (the twin's L is its
fresh stream, 0.33 GB; G(R), 1,000 transactions of 42 kB, is 0.04 GB).

| f     | units of 2^-16  | cap f/(1-f) | W in L' | k, cold (r = 0.5) | k, overwrites (r ≈ 0.3) |
|---|---|---|---|---|---|
| 0.25  | 16,384          | 0.33        | 4       | 4 to 6            | 2.4 to 3.6 |
| 0.375 | 24,576          | 0.60        | 2.7     | 2.7 to 4          | 1.6 to 2.4 |
| 0.40  | 26,214 (0.399994) | 0.67      | 2.5     | 2.5 to 3.75       | 1.5 to 2.25 |
| 0.50  | 32,768          | 1.00        | 2       | 2 to 3            | 1.2 to 1.8 |

Reclaim's writes when f paces: the charge is at most f of the growth,
f/(1-f) on top of the rest; W4 measured 1.0 to 1.8 times the charge's
cap at 0.25 (34 to 61 % on top). If that factor holds, 0.40 adds about
0.7 to 1.2 and 0.50 about 1.0 to 1.8 stream bytes a user stream byte:
**halving k costs about three times reclaim's writes**. Not measured
since 011-04's first grid.

### 4.2 Where the sketch is right, wrong or too simple

* **Right**: the form (the history of R plus a multiple of the live
  data), k proportional to 1/f while f paces, and f/(1-f) as the charge's
  cap.
* **H(R) is G(R)**: the stream written in R, with the index nodes and
  reclaim's own records, not the user's history alone; and at least
  about sd, as the cut waits for the startup position.
* **k depends on the share rewritten** (r, above) and on the index the
  touch makes dirty; "2/f" is high for overwrites and low for cold data
  just before a cut (3r/f).
* **f does not pace reclaim in three regimes**, and there k does not
  follow 1/f:
  * **A long R**, G(R/4) > W: iterations start R / 4 apart, kept ≈ 1.25
    to 1.5 G(R) + W, and reclaim writes L' an R / 4, whatever f. f only
    makes each iteration finish sooner (burstier writes). The ITERATION_
    DIVISOR comment: "about 1.25 times what the retention needs".
  * **A small database**, 2 sd > W: L' below 2 f sd, at sd = 50 MB about
    25 MB at 0.25 (some 150,000 KVs of 100 bytes). Iterations are 2 sd
    apart, whatever f.
  * **Large transactions, the step cap**: one step a user transaction,
    at most 16 kB of scan. Reclaim rewrites at most about 11 kB of value
    nodes (100-byte values) a transaction, so with transactions of more
    than about 30 to 45 kB of growth (100 small puts or more) f no longer
    decides: an iteration takes (live KVs / 75) transactions, and W
    grows with the transaction's size. At 10M keys and 1,000 puts a
    transaction that is about 56 GB of growth an iteration, kept about
    110 to 170 GB for 1.1 GB of data (an estimate from the code, not
    measured). 024-03 sat at this cap (section 3.6). A user who batches
    gets less than f and more disk; 023-08's quota "in proportion to the
    transaction" would remove the cap's effect, at the price of the
    commit's size.
* **f/(1-f) is the charge, not the cost**: 1.0 to 1.8 times it measured
  (W4); and it holds only while iterations run back to back.
* **After a mass delete**, kept falls back after 3 to 4 iterations
  (024-03, section 4), so the lag in bytes is about 4W, also 1/f.


## 5. How to judge and compare

### 5.1 The baseline: the same history

Frans (10:42): "By fresh, we must mean one that keeps the same history,
same retain period." 024-03's "fresh" was the live state alone. The
baseline for a run with R is the same workload with R forever, measured
over the same transactions:

* **G0(R)**: the stream that the user's records of the last R take
  without reclaim (the no-reclaim run's growth over R's transactions).
* **L0**: the stream of a fresh database of the live keys (the twin's
  fresh stream: the least that holds the live data and its index).

A stream that keeps exactly R's history and the live data holds about
G0(R) + L0. That is the denominator.

### 5.2 The quantities

| Quantity                    | Definition                                 | Who cares     |
|---|---|---|
| WA_r, reclaim's write cost  | stream bytes a user byte, with R over R forever, - 1 | SSD, speed |
| K_space, kept beyond R      | (kept − G0(R)) / L0, its mean and its peak  | disk, backups |
| SE (011-04)                 | user bytes accessible within R / kept      | both          |
| reclaim's reads             | node and value loads of steps a user byte  | cold cache    |
| commit p99.9, largest record | from Perf; steps a commit                  | latency       |
| lag                         | growth until kept is in the twin's range, 90 % deleted | disk |
| updates a second            | throughput, timing runs only               | speed         |

Ideal: WA_r = 0 and K_space = 1. Today, at 0.25: WA_r 0.34 to 0.61
(W4), K_space about 4 to 6 (ST3).

### 5.3 The workloads

* **Overwrites**, uniform and hot (90 % on 1 %): the common case.
* **Cold**: 90 % of the data never changes, rewritten every other
  iteration; the worst case of r.
* **FIFO / time order** (021-25's shape, 024-03, section 7): keys put in
  order, the oldest deleted.
* **Mass delete** and the lag (024-03, section 4).
* **R short and long**: K (updates a key within R) of 0.1, 1 and 10;
  only the short ones are paced by f, and K = 10 shows that f costs
  nothing there.
* **Values** of 100 and 1,000 bytes (10,000 bytes behaves as 1,000 in
  011-04).
* **Transaction size**: 1 to 10 puts a transaction for the f grid; one
  run with 1,000 puts to show the step cap.
* **Size**: 30 MB of live data (ReclaimCost), 1M and 10M keys.

### 5.4 What a user would weigh

* **SSD writes.** A consumer SSD is rated for about 600 TB written a TB
  of capacity. An application writing 10 GB of user data a day under R
  writes about 13 to 16 GB a day at 0.25, and about 20 to 28 GB at 0.50
  (with W4's factor): 7 to 10 TB a year at the most, far below the
  rating. Writes matter more as throughput and latency on a busy disk
  than as wear.
* **Disk space.** For 10 GB of live data, at 0.25 the stream holds R's
  history and about 40 to 60 GB more (cold data), at 0.50 about 20 to 30
  GB more, and so do backups and copies. The user sees this number
  first, and aim 3 (024-04: storage proportional to the KVs stored)
  speaks to it.
* So for most users space is the dearer side, and a larger default fits
  them, if throughput holds; for write-heavy users on slow disks the
  writes are. With no Pub setter (Frans, 11:13), the default must be
  acceptable on both sides in every workload of section 5.3, not best in
  one; the Core's setter is the way out for the few it does not suit.
  The weights are a judgment, not a measurement (section 8, QF29-1).

## 6. A measurement plan for f = 1/4, 3/8 (or 0.40), 1/2

The three values Frans named were 0.25, 0.40 and 0.50; the plan uses
3/8 for 0.40 so that all three are exact in units of 2^-16 (the
coordinator's suggestion after Frans's 11:13 direction), and adds 0.40
in step 1 only, as a check that 3/8 stands for it.

On a clone of `main` (format 7, merges, option 2), as 024-03 did. All
three steps count bytes, exactly and repeatably; only step 4 times.

1. **The grid, small (about 1 hour, one slot).** `reclaimgrid.sh` with
   `-Df=0.25`, `-Df=0.375`, `-Df=0.5`: WORK uniform hot cold, SIZES 100
   1000, K 0.1 1 10, and the K = 0 baselines once: 3 × 18 + 6 = 60 runs
   of `ReclaimCost` (single puts, 30 MB live); and `-Df=0.40` with K =
   0.1 only (6 runs, 10 minutes). P=2 (10 GB of heap each, at most 4
   cores in a hold), one f a hold, about 20 minutes each (an estimate:
   the grid's times were not recorded). Gives WE, SE,
   SE offered, `keptMB`, the share rewritten, W4's bytes by kind. First
   check that `ReclaimCost` still runs on today's main (not run since
   011-04; untried).
2. **Perf at 1M keys (about 30 minutes, one slot).** `performance.sh`
   with FORCE=1, RUNS=1, write mode, 13-byte keys, 100-byte values,
   **tsize=10**, uniform, retain=1 (R = the live data's writes) and
   retain=10, `mincuts` so that at least four cuts are measured, and
   retain=inf for G0. Perf has no f yet: add an `f=` property that
   calls `db.setReclaimInternalFraction` (a few lines, a code change in
   a clone branch, `before-commit.sh` once). It reports
   `bytes_appended_per_put`, `rec.step_bytes_per_put`, `se`,
   `kept_mb_max`. Plus 024-03's mass delete at 1M (`runs.sh 1m`'s
   delete and drive, with f set in the probe, outside `java/`) for the
   lag: 3 × 6 minutes.
3. **Perf at 10M keys (about 75 to 90 minutes, two or three holds, one
   slot).** The same lines at n=10,000,000, 16 GB of heap, for 0.25 and
   the two others; one random fill of 10M keys (4 to 5 minutes, 024-03),
   copied for each f. An iteration at 10M needs about 4L' of growth at
   0.25 (L' about 1.5 to 1.8 GB), so four cuts mean about 25 to 30 GB
   written at 0.25 and 14 at 0.50: 15 to 25 minutes a run at 30,000 to
   50,000 puts a second (estimate). The disk needs about 10 GB free for
   kept, 30 GB written.
4. **One timing pass (about 1 hour, both slots, take-timing).** At 10M,
   0.25 against the best candidate, RUNS=3: updates a second, commit
   p99.9 and the largest commit, within the "no stop-the-world" guide
   (F53 under 50 ms).
5. **One run at the step cap**: 1M keys, tsize=1,000, 0.25 and 0.50,
   to measure what section 4.2 estimates (10 minutes).

Total about 4 to 5 hours of F53, fit for a night (020-31's scripts), with
nothing else timing. 100M keys (GM7) is not in the plan; the scale law of
006-19 (sd / K) stands in. Every f is kept in units: 0.40 is 26,214 units
(0.399994), 3/8 is 24,576 exactly; both are deterministic in the stream,
which keeps the units, but only exact values can be written in the
Javadoc as they are used.

**How to decide: one default that always works.** Per workload and
regime (f-paced, R-paced, sd-paced, capped), take K_space and WA_r for
the three f. A value "works" in a cell when K_space is within BD10's c
(6 today; QF1) and WA_r within a stated limit (QF29-1, for example 1.0:
reclaim at most doubles the writes), with updates a second at 10M no
more than a stated loss below 1/4's and commit p99.9 within the guide.
The default is the value that works in every cell, and of those the one
with the lowest worst-cell K_space. Cells where f does not pace (long R,
small databases, the cap) count only for their latency: f changes little
there by section 4.2.


## 7. A few distinct settings or a continuous value

Frans, 11:13: no Pub setter is "not too bad as is", if one value
"always works"; "for the sake of testing, it still seems right to define
three recommended values somehow". The options, Pub API first:

| Option | What                                                           | Tests         |
|---|---|---|
| A      | as today: Core and JMX, 0.001 to 0.90, no recommended values    | extremes only |
| A3     | as A, the Javadoc names 1/4, 3/8, 1/2; tests run at each        | the three     |
| C3     | the Core's setter takes only 1/4, 3/8 and 1/2                   | the three     |
| B      | three named levels in the Pub API too (a Pub setter)            | the three     |
| D      | the Pub API takes a double from 0.10 to 0.75                    | sampled       |

* **Test coverage.** Correctness does not depend on f: the cut's safety
  is checked at every cut Java decides (T-SCHEME, `docs/levels.md`,
  section 6), the Lean model has no f (`lean/SIS/Reclaim.lean` models
  what a cut leaves and when a cut is safe, not the pace). What f
  changes is the interleaving: how often a step runs, how long an
  iteration lasts, when the cap binds. With three values the level 3
  tests (ReclaimStress, RestartInvariance and CrashTest with reclaim,
  the conformance traces with reclaim) can run at each in `night.sh`,
  the default alone in `before-commit.sh` (before-commit must stay
  fast). A continuous range is tested at its ends and a sample.
* **The three values, exact.** 1/4, 3/8 and 1/2 are 16,384, 24,576 and
  32,768 units of 2^-16: `Math.round(f × 65536)` gives them exactly, and
  `fractionOf` is floor(g/4), floor(3g/8), floor(g/2). Frans's 0.40
  would be 26,214 units, 0.399994; 3/8 stands in for it (section 6
  checks that it behaves as 0.40 within the step's granularity).
* **The stream.** `fraction=` keeps units in every option; a stream of
  2026.4 with any value in range must still open. A3 keeps that. C3 must
  either still accept a stored value outside the three (then the start
  runs an untested value anyway) or refuse it, a format rule that 2026.5
  may add but that refuses databases a user made with the Core today.
* **The C clone** has the setter with Java's range; A3 needs nothing
  there, C3 a check when the clone follows.
* **The Pub API** has no setter (checked). Frans (10:42) called the
  fraction "one of the few settings a user should know"; at 11:13 he
  accepted no setter if one default always works. A3 and C3 keep it so;
  `Database.setRetainDuration`'s Javadoc then states the default share
  and its cost (the numbers of section 6), and names the Core setter for
  advanced users.
* **Tests.** In A3 and C3: the level 3 runs with reclaim (ReclaimStress,
  RestartInvariance, CrashTest, the conformance traces with reclaim) at
  each of the three in `night.sh`; the default alone in
  `before-commit.sh`, which must stay fast; `LimitsTester` keeps the
  range's ends (A3) or checks the refusals (C3).
* **Digests.** A new default changes the bytes of new databases with R
  finite: `StreamDigest` and any test that expects bytes under reclaim
  with the default change, a changed expected value that needs Frans's
  approval (the brief's rule). A database that already set R keeps
  16,384 in its stream (section 2.1).

**Recommended: A3.** The Pub API keeps no setter and gets one default,
the value of section 6's "How to decide". The Core's Javadoc names the
three recommended values, 1/4, 3/8 and 1/2, as the tested ones, with
what each trades (fewer writes, more disk: 1/4; less disk, more writes:
1/2), and the tests run at each. The setter keeps accepting 0.001 to
0.90: the Core API is the low-level, less safe one (Frans, 2026-11-09),
old streams and the C clone stay as they are, `LimitsTester` keeps its
ends, and nothing refuses a database. A value outside the three is the
advanced user's own risk, said in the Javadoc. C3 is the stricter
choice if Frans wants every value a database can run with to be tested;
its cost is the rule for stored values above. Whether reclaim should
also lift the step cap for large transactions is a separate question
(QF29-4).


## 8. Questions for Frans

* **QF29-1. The limits of "always works".** For the one default: the
  most stream kept (BD10's c, today 6), the most reclaim may add to the
  writes (WA_r, for example 1.0), and how much lower throughput at 10M
  than at 1/4 is acceptable? Recommended: c = 6, WA_r at most 1.0, up to
  20 % lower throughput; that likely picks 3/8.
* **QF29-2. Run the plan** (section 6, about 4 to 5 hours of F53, a
  night) before deciding QF1? Recommended: yes, steps 1 to 3 first
  (bytes only, one slot), step 4 after.
* **QF29-3. The Core's range.** With 1/4, 3/8 and 1/2 as the recommended,
  tested values: does `Db.setReclaimInternalFraction` keep accepting
  0.001 to 0.90 (A3), or only the three (C3)? Recommended: A3, the range
  kept, the three named in its Javadoc, the Pub API without a setter;
  "reclaim share" as the word in the user documentation.
* **QF29-4. The step cap.** With transactions of more than about 100
  small puts, reclaim is held by its 16 kB a transaction, not by f, and
  keeps more stream than f says (section 4.2, an estimate). Measure it
  (step 5) and, if confirmed, make it a known case of 024-05 (a step
  scan in proportion to the transaction, 023-08's review C)?
  Recommended: measure first.
* **QF29-5. 3/8 for 0.40?** 0.40 is 26,214 units (0.399994); 3/8 is
  exact. Recommended: 3/8, with 0.40 measured once beside it (section 6,
  step 1).


## 9. Measurements, 2026-11-12

Frans, 2026-11-12, 12:59: "I don't see a reason this should take
several hours. Do the measurement now. It is ok to limit database size
so it takes less than 60 minutes to do this." By the agent "fracm" of
coord-1112, 12:59 to 14:15. Counts only, from one program; section 6's
plan (ReclaimCost's grid, Perf at 10M) is replaced by this.

### 9.1 What was run

* **`FracRuns`** (`java/stress/FracRuns.java`, package `bergdb.core`,
  built on 024-30's `CountGates`, which takes an `f=` property for it),
  on the branch `024-29-fraction-runs` of the clone
  `/Users/f/fl/bench/2026-11-12/fracm/clone`. No product code changed.
* **The databases**: as G3's (024-30, section 3.3): a `FileStream`, the
  builder's defaults (sd 50 MB, cache indicator 200 MB, eviction on), a
  test clock of 1 ms a transaction, R = 1 s = 1,000 transactions, n = 1M
  keys `/k/%010d` (13 bytes), values of 100 bytes, **10 puts a
  transaction** (so that the step cap does not decide, section 4.2).
  f is set with `Db.setReclaimInternalFraction` right after the start:
  16,384, 24,576, 26,214 (0.40, in (a) only) and 32,768 units.
* **The workloads**, each until the third cut (as G3):
  * (a) uniform overwrites: a fill in random order, then puts of
    uniformly random keys (G3's workload, draw for draw);
  * (b) a queue: a fill in key order, then each transaction puts 10 new
    keys after every key and deletes the 10 oldest (n keys stay live);
  * (c) mostly cold: a fill in random order, then puts of random keys
    among the first 1 % in key order (a contiguous hot range: the other
    99 % and their key nodes are never written again, the worst case of
    r);
  * (d) back to empty: G4 (024-30, section 8) with f set in both the
    emptied database and its hello-world twin (sd 100 kB there).
* **The twin of the writes** (Frans: the same workload with R forever):
  the same transactions, draw for draw, without R. **WA_r** = the
  stream's growth over the window / the twin's growth over the same
  transactions − 1, the window from the transaction at which the first
  iteration is complete to the last. **K_space** = (kept − H_R) / L0
  after each transaction of the window, its peak and mean, with H_R and
  L0 as in G3 (the bytes of the user's records within R; the stream
  after the fill). **The largest record**: the largest record of the
  phase after the fill, user, step or table. **Loads**: the versions the
  steps loaded (`Reclaim.Stats.Iteration.loads`), over the run.
* **Machine time**: one slot, 13:12 to 13:17, two JVMs at a time (4.6
  minutes for all 17 runs and their twins). The run of (a) at 1/4 is
  G3 itself: it gives G3's peak, 4.410 at transaction 164,062, to the
  byte (024-30, section 4).
* Outputs in `29-reclaim-fraction/`: `work-a.txt` to `work-d.txt` (the
  `RESULT` lines and one line an iteration), `run.sh` (the command).

### 9.2 The numbers

Workloads (a) to (c); n = 1M, 10 puts a transaction, R = 1,000
transactions. "Steps a tx": steps a user transaction over the run.

| Work | f    | WA_r  | K_space peak | K_space mean | Largest record | Loads a put | Steps a tx |
|---|---|---|---|---|---|---|---|
| a    | 1/4  | 0.567 | 4.410 | 3.234 | 35,176 | 2.44 | 0.41 |
| a    | 3/8  | 0.996 | 3.589 | 2.709 | 37,136 | 3.73 | 0.62 |
| a    | 0.40 | 1.091 | 3.472 | 2.640 | 49,096 | 4.03 | 0.66 |
| a    | 1/2  | 1.469 | 3.078 | 2.402 | 43,984 | 5.47 | 0.79 |
| b    | 1/4  | 0.367 | 6.178 | 4.459 | 15,480 | 1.72 | 0.28 |
| b    | 3/8  | 0.644 | 5.704 | 4.121 | 22,008 | 2.29 | 0.38 |
| b    | 1/2  | 1.005 | 4.602 | 3.324 | 22,616 | 3.48 | 0.57 |
| c    | 1/4  | 0.358 | 6.458 | 4.748 | 33,304 | 0.87 | 0.14 |
| c    | 3/8  | 0.559 | 4.578 | 3.428 | 42,616 | 1.44 | 0.24 |
| c    | 1/2  | 0.781 | 3.649 | 2.819 | 38,504 | 2.17 | 0.36 |

Workload (d), back to empty at 1M keys (G4): the lag (the drive
transaction from which kept stays within twice the twin's), the first
cut in the drive, kept at 4 R of drive (T1's point), and G4's M1.

| f   | Lag, tx | First cut | Twin's first cut | Kept at 4 R, bytes | M1 over the twin's |
|---|---|---|---|---|---|
| 1/4 | 4,395   | 4,117     | 1,214            | 262,180,912        | 1.072 |
| 3/8 | 1,857   | 1,585     | 1,202            | 2,093,152          | 0.982 |
| 1/2 | 1,850   | 1,587     | 1,196            | 2,230,840          | 1.077 |

* **Iterations and cuts**: every run of (a) to (c) had 5 iterations, 4
  complete, and 3 cuts (the stop rule). The first and third are *full*:
  they rewrite most live values (a: 59 to 91 % of the KVs scanned; b:
  55 to 100 %; c: 99 %). The second is *empty*: it rewrites none, as the
  first moved every live value past its own pStart, the second's cut
  point (option 3, 011-04). The fourth rewrites 11 to 30 % (c: none).
  An empty iteration takes 13,335 steps, one a transaction: 1M KVs at 75
  a step, the step cap paces it, W = 0.14 to 0.47 L0 whatever f.
* **The largest record** is always a step's record, 15 to 49 kB, about
  the twin's largest user record (30 kB in a and c, 8 kB in b) and far
  below G1's 1 MB. f does not change it much: a step scans at most 16 kB
  whatever f; a larger f makes steps more frequent, not larger.
* **Loads**: 4.1 to 4.5 million in every run, about 60 a step, 0.8 a KV
  scanned (the cache, 200 MB, holds less than L0, 245 MB). They
  depend on the iterations, not on f; but a larger f runs the same
  iterations in fewer user transactions, so the loads a put rise with
  the steps a transaction: 1/2 has 2.0 to 2.5 times 1/4's.

### 9.3 Against the sketch (section 4)

* **W follows 1/f where f paces.** The full iterations' growth W: cold
  (c) 2.81, 1.87, 1.40 L0 at 1/4, 3/8, 1/2, that is 0.70/f each time; (a)
  1.92, 1.50, 1.24 L0 (0.48/f, 0.56/f, 0.62/f: a shorter iteration
  leaves fewer keys overwritten since its cut point, so it rewrites
  more, 69 %, 83 %, 91 %).
* **K_space follows the upper end of section 4's 1/f to 1.5/f, plus a
  part that f does not move.** Cold (c): 6.46, 4.58, 3.65. Taking away
  about 0.55 L0 that does not depend on f (2 sd = 0.41 L0, the cut's
  wait for the startup position and pSafe; and the empty iteration's
  0.14 L0, paced by the step cap), the rest is 5.9, 4.0, 3.1 = 1.48/f,
  1.51/f, 1.55/f. A reading of the numbers, not derived. At 10M keys
  the sd part is ten times smaller in L0, so K_space would be about 0.4
  lower; not measured.
* **Overwrites: the sketch was low.** Section 4.1 predicted 2.4 to 3.6
  at 1/4 and 1.2 to 1.8 at 1/2 for overwrites (r ≈ 0.3); measured 4.41
  and 3.08. r is not 0.3 an iteration but 0.6 to 0.9 and 0 in turns,
  and the peak comes after a full one. From 1/4 to 1/2, K_space falls
  by 30 % (a), 25 % (b), 43 % (c), not by half.
* **Reclaim's bytes against f/(1-f)** (0.33, 0.60, 0.67, 1.00): WA_r is
  0.9 to 1.1 times it in (b) and (c) (0.78 of it at 1/2 in (c), where the
  empty iterations write little), and 1.5 to 1.7 times it under uniform
  overwrites (a), as W4 found (1.0 to 1.8): a step's index nodes are
  written again by the user's records and not all of them are charged
  (011-04, W4).
* **Where f does not decide.** R = 1,000 transactions is short: G(R/4)
  is about 1 MB, far below W, so R never paces (a) to (c). 2 sd (0.41
  L0) is below every full iteration's W (at least 1.04 L0): sd does not
  pace either. The step cap paces every empty iteration (above). At 1/2
  in (a) the full iterations come close to it: 16,222 and 13,334 steps
  for 13,335 at the least, each step at its 16 kB, but about 0.6 steps
  a transaction in them; a larger f than 1/2 would hit the cap in this workload
  at 10 puts a transaction. In (d) the lag is the same at 3/8 and 1/2
  (1,857, 1,850): from 3/8 on, R and the twin's pace decide (the
  twin's first cut is at about 1.2 R), and f no longer does.
* **0.40 against 3/8** (a): K_space 3 % lower, WA_r 9 % higher, the
  largest record 32 % larger (49 kB, one step). 3/8 stands in for it
  (QF29-5).

### 9.4 Throughput

One timing pass of (a) at 1/4, 3/8 and 1/2, with both slots
(`take-timing`), 13:31 to 13:33, one JVM, 4 GB of heap, the runs one
after the other, `Reclaim.Stats`' touch count off (`timing=1`); output
`29-reclaim-fraction/timing-a.txt`, command `timing.sh`. The counts are
those of section 9.2, to the byte (the loads differ by a few hundred in
4.3 million: they depend on the eviction thread's timing). Puts a
second in the window (from the first iteration's end to the third cut):

| f    | Puts a second | Against 1/4 | Loads a put |
|---|---|---|---|
| 1/4  | 60,981        |             | 2.44        |
| 3/8  | 47,023        | −23 %       | 3.73        |
| 1/2  | 37,885        | −38 %       | 5.47        |
| twin | 164,359       | (R forever, the whole phase) |  |

* One pass, not repeated: its noise is not known.
* The loss follows the steps a transaction and their loads, not the
  bytes: a step's scan loads about 60 versions here, as the data (245
  MB) does not fit the cache (200 MB). This is a worst case for f: a
  database whose live data is in the cache pays less for each step;
  with a long R, which paces reclaim (section 4.2), f does not change
  the total work, only how soon an iteration ends.

### 9.5 Recommendation, against QF29-1's proposed limits

QF29-1's proposed limits (not yet decided by Frans): K_space at most 6
(BD10's c), WA_r at most 1.0 (reclaim at most doubles the writes),
updates a second at most 20 % below 1/4's.

| f    | Worst K_space | Worst WA_r | Lag (d) | Within the limits?                          |
|---|---|---|---|---|
| 1/4  | 6.458 (c)     | 0.567 (a)  | 4,395   | no: K_space above 6 in (b) and (c)           |
| 3/8  | 5.704 (b)     | 0.996 (a)  | 1,857   | no: −23 % puts a second in (a), limit −20 %  |
| 0.40 | 3.472 (a)     | 1.091 (a)  |         | no: WA_r above 1.0 in (a)                    |
| 1/2  | 4.602 (b)     | 1.469 (a)  | 1,850   | no: WA_r above 1.0 in (a) and (b)            |

Updates a second (9.4, (a) only): 1/4 the reference, 3/8 −23 %, 1/2
−38 %. **None of the three is within all three proposed limits.** 1/4
misses the space limit by 3 to 8 % (6.18 and 6.46 against 6, at 1M; at
10M the sd part is smaller, section 9.3, so about 5.8 to 6.1); 3/8
misses the throughput limit by 3 points in one unrepeated pass, and is
at the edge of the writes limit (0.996); 1/2 misses the writes and the
throughput limits by far.

**Recommendation: 3/8 as the default (24,576 units), with the
throughput limit at 25 %.** What it buys over 1/4, at 1M keys: the
stream kept 19 % (a), 8 % (b) and 29 % (c) smaller at its peak, and the
lag back to empty 58 % shorter (1,857 against 4,395 transactions; T1's
4 R passes). What it costs: 27 % more stream written in (a) (WA_r 0.996
against 0.567), 20 % in (b), 15 % in (c); 1.3 to 1.7 times the loads a put;
23 % fewer puts a second in the worst case measured (uniform overwrites,
the data larger than the cache, a short R). Aim 3 of 2026.5 (storage
proportional to the KVs stored, 024-04) and the back-to-empty lag speak
for it; optimizing for large databases and worst cases first, space and
the lag are the user's first view. 0.40 behaves as 3/8 within 3 to 9 %
and crosses the writes limit: not it.

**The alternative**, if Frans holds 20 %: keep 1/4 and set BD10's c to 7
for 2026.5 (G3's limit can stay 6: G3 is workload (a), 4.41), the lag
of 4.4 R accepted (G4 drives 40 R). That costs nothing now. The choice
between the two is QF1 and QF29-1, Frans's: the numbers above are the
evidence, the weights are his.

### 9.6 What changing the default would cost

* **Tests that expect 0.25.** A trial build with
  `DEFAULT_INTERNAL_FRACTION = 24576` (branch `024-29-default-trial` of
  the clone, `0d8bf189`, not for `main`), `before-commit.sh` once in a
  slot (13:17 to 13:19): BEFORE COMMIT FAILED with these, each an
  expected value that names the default (a changed expected value: its
  own commit, Frans's approval):
  * `DbTester.testReclaimInternalFractionValidation` ("default", 16384);
  * `DbTesterRestart.testReclaimSettingInForceWritesNothing`,
    `testStreamWithoutSettingsHasDefaults`,
    `testReclaimSettingAtEndOfOrdinals`,
    `testReclaimSettingRefusedAtGoPoint` (0.25 as a new database's or
    an unchanged value);
  * `Reclaim.Tester.testUserTransactionLeavesTimesForReclaim` ("the put
    made a step": its workload is sized to the pace at 0.25);
  * the f-test `DbTesterRestart.testReclaimSettingsSurviveCuts` (the
    settings KV's text, `fraction=16384`);
  * `NanotestForBergDB.databasesStopped` in both groups, a consequence
    (the failed tests left their databases).
  * `StorageFaultTester.testStopWhileReading` failed too ("the read did
    not meet the closed stream"), a race; the other slot ran a level 3
    gate. Not judged related; to be rerun alone before it is believed.
* **Digests.** `StreamDigest`'s configurations with reclaim (the l3-*
  ones, `level3.sh` step 3) get other streams with R finite: an
  expected-value change for Frans. No digest is stored in the tree
  (they are compared with a preserved build), so no file changes; the
  conformance traces with reclaim are made at run time and f is not in
  the Lean model (section 7).
* **Gates.** G3 measures K_space at the default: 4.410 at 1/4, 3.589
  at 3/8 (margin 1.36 to 1.67); its limit of 6 can stay or go down
  (c = 5 would keep a margin of 1.39 at 3/8; that is QF1's choice). G4's
  lag falls from 4,395 to 1,857 transactions: T1's drive of 4 R would
  pass at 1M (Q30-3's runs at 100,000 and 3M keys should use the new
  default). G1 and G2 do not depend on f by design; not rerun.
* **Documentation.** `Db.setReclaimInternalFraction` ("0.25 by
  default"), `Reclaim.DEFAULT_INTERNAL_FRACTION`'s comment,
  `Database.setRetainDuration`'s Javadoc ("at most a quarter", "four
  times the live data", the measured sizes of 020-24-06), and
  `docs/levels.md`, section 6 ("a quarter", 16,384 units).
  `LimitsTester` follows the constant.
* **Existing databases.** A database that has set R keeps
  `fraction=16384` in its stream (section 2.1) and keeps 1/4; only
  those that set R after the change get 3/8. The C clone (012) keeps
  0.25 until it follows.


## 10. State

* **Measured** (2026-11-12, 12:59 to 14:15, the agent "fracm"; section
  9): f = 1/4, 3/8, 1/2 (and 0.40 in (a)) at 1M keys in four
  workloads, counts only, 4.6 minutes of one slot; a trial of the
  default at 3/8 against `before-commit.sh` (section 9.6).
  One timing pass of (a) with both slots (13:31 to 13:33, section 9.4).
* **The code**: clone `/Users/f/fl/bench/2026-11-12/fracm/clone`, branch
  `024-29-fraction-runs` from `main` at `d81bc79b`, head `d7bd3bb5`, in
  Frans's name: `java/stress/FracRuns.java` (new) and `CountGates`'s
  `f=` property. `before-commit.sh` on `d7bd3bb5`: BEFORE COMMIT OK
  (65 s, in a slot, 13:34 to 13:35). Not on `main`: the coordinator
  lands the branch (it adds a stress program only). The trial branch
  `024-29-default-trial` (`0d8bf189`, worktree `fracm/dflt`) is not for
  `main`.
* **Done before** (11:05 to 11:20, the agent "frac"): sections 2 to 8,
  read only. Section 6's plan is replaced by section 9's runs; its 10M
  step was not run.
* **Not done**: 10M keys (K_space about 0.4 lower there by the sd
  part, section 9.3, not measured); values of 1,000 bytes; the step cap
  at 1,000 puts a transaction (QF29-4); commit p99.9.
* **To continue**: Frans decides QF29-1's limits and QF1 (section 9.5).
  If 3/8: one commit with `DEFAULT_INTERNAL_FRACTION = 24576` and the
  documentation of section 9.6, and a separate commit with the changed
  expected values of the seven tests listed there (Frans's approval),
  then `count-gates.sh` (G3's new value) and `before-commit.sh`. To
  rerun: `sh 29-reclaim-fraction/run.sh` from the clone's layout (it
  builds and writes `out/`), one slot, about 5 minutes.

**Decided** (Frans, 2026-11-12, 14:07): "1/4 is good for this release,
keep it." Larger databases, three recommended fractions and one default
for 2026.6: 026-04.

2026-11-13. Status set after the release (coord-1113).
