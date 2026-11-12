# 024-05. The aim against what is known

Created 2026-11-11 by Frans Lundberg. Status: open.

Aims 2 and 3 of release 2026.5 (024-04, section 1: operations are
proportional, storage is proportional) against everything measured or
argued so far: the known cases that break them or might, a proposed list
of bounds that make "proportional" exact, what nobody has measured, a
proposed order of work, and questions for Frans. A read-only study: no
code changed, nothing built, nothing measured. Aim 4 is 024-06's.

Cases are OP1 to OP11 (aim 2) and ST1 to ST11 (aim 3), bounds BD1 to
BD14, measurements GM1 to GM8, questions QF1 to QF8; cite them as
"024-05, OP1".


## 1. In short

* **Two cases break the aims by a wide margin, both measured at 10M
  keys.** OP1, the last touch of a reclaim iteration (CL7): one record of
  191 to 206 MB and a commit of 20.6 to 22.2 s, in a workload whose mean
  record is 25 kB. OP2 with ST2, the underfill after scattered deletes
  (CL2): 11 to 16 times the twin's key nodes, 3.3 times the bytes a
  transaction, scans 4.6 times slower, and reclaim does not heal it.
* **OP1 may be worse than a pause at 100M keys.** If it grows linearly,
  the record is about 2 GB, and the record limit is 2^31 - 9 bytes
  (`StoredTrans.MAX_RECORD_SIZE`). What reclaim's step does at the limit
  is not known here; to be read before any run at 100M (section 5).
* **MEM at 10M KVs (327 against 129.6) has an explanation by reading the
  code, not yet by a run.** MEM's keys are `"" + i`; a key of exactly 7
  bytes is two segments (`Keys.toSegments`: "a key of size 7 will be
  *two* segments long"), and 9M of the 10M keys are 7 bytes long, each
  with a segment tree of its own. So the figure is a cost of the key's
  shape, not of the number of keys: ST1. One run confirms it (GM1).
* **A correction of 024-03.** Its "a get reads about 25 versions from the
  stream (25.6M loads in 1M gets)" (sections 3 and 8) reads a counter
  that is cumulative since the start, the fill included
  (`cacheStats().loads` in PF1's `gets`). The second million gets added
  1,924,301 loads: 1.9 loads a get at 10M keys. Gets are within the aim.
* **Proportional, with a constant nobody has decided:** the stream kept
  under reclaim, 4.5 to 6 times a fresh database of the same keys (ST3),
  and a put's stream bytes, which grow with the logarithm of the keys at
  a fixed startup distance (OP3). Both are by design (QF1, QF3).
* **Small and cheap:** ST6 (the cache's tables), ST7 (the key access
  path's arrays), ST8 (11 MB of heap a database), OP4 (the pace after a
  decrease of the startup distance), OP8 (reclaim's value reads). **A
  named allowance that can stay:** ST5, the dirty top-node window.
  **With CL2's decision:** ST4, dead klongs in live nodes.
* **The three bounds that matter most** (section 4): BD1, no record
  over the larger of 1 MB and 5 times its run's mean, the transaction's
  own values apart; BD13, a reachable index of at most twice the twin's
  key nodes; BD10, the stream kept at most c times the twin's, c decided.
* **Nothing is known at 100M keys**; 024-03's figures are one run each.
* **Proposed order** (section 6): the tests as code and GM1 to GM3;
  then OP1 with the reclaim step's other changes in one batch of stream
  bytes; then strict (ST2, ST4), which costs a record format; the
  constants of ST3 and OP3 by measurement beside it.


## 2. Aim 2: operations

"The proportional one" is what the same operation costs where the case
does not arise: the same run's median or mean, or the twin (023-02,
section 3.2). Sizes are 024-03's unless said: 10M keys of 13 bytes, 100
bytes a value, 100 KVs a transaction, a startup distance (sd) of 50 MB.

| ID   | Operation                     | Measured                        | Proportional one     |
|---|---|---|---|
| OP1  | a commit with the last touch  | a record of 191 to 206 MB, 21 s | 25 kB, 0.76 ms       |
| OP2  | work after sparse deletes     | 3.3 x bytes, 4.6 x scan time    | the twin's           |
| OP3  | a put's stream bytes          | 867 B at 10M, 1,244 B at 50M    | the same at every K  |
| OP4  | a decrease of sd              | records of 13 to 15 MB at 50M   | 3.3 to 3.6 MB at 10M |
| OP5  | a single put's record         | 209 kB; 0.23 to 0.29 MB at 10M  | 576 B; 0.9 kB        |
| OP6  | a put of a long key           | 2.6 to 5.8 s; 29 to 48 s        | linear in the key    |
| OP7  | a cold start                  | 46 s on s1 at 10M keys          | 2 to 7 s warm        |
| OP8  | a reclaim step's reads        | every live value read           | those before pCut    |
| OP9  | reclaim after a mass delete   | 4 iterations of lag             | 2 cuts (023-02, F6)  |
| OP10 | the slowest commit of a run   | 94 to 129 ms, p99.9 3 to 6 ms   | under 50 ms (P1)     |
| OP11 | the check before the go point | 142,243 nodes counted           | 15,422 made dirty    |

| ID   | Breaks | Described in              | Evidence                 | Fix; it changes      |
|---|---|---|---|---|
| OP1  | yes    | 024-03, 7; 023-08, 4      | measured; cause read     | prototype; bytes     |
| OP2  | yes    | 024-03, 5; 023-04, X3     | measured, counts exact   | prototype; format    |
| OP3  | might  | 006-19, 3.5 and 4         | measured to 50M, a model | levers; none, format |
| OP4  | yes    | 007-07, 11; 015-84        | measured, bytes          | known, small; bytes  |
| OP5  | might  | 007-07, 7.1; levels.md, 5 | measured, bytes          | known, large; bytes  |
| OP6  | yes    | 021-16, Q1                | measured, times          | known; none          |
| OP7  | might  | levels.md, 5; 007-05      | measured; T4 not proved  | none known           |
| OP8  | might  | 024-01, 9.3; 023-05 P8, 8 | argued, not measured     | known, small; none   |
| OP9  | no     | 024-03, 4 and 8           | measured                 | P8; bytes            |
| OP10 | might  | 024-03's outputs          | measured, not attributed | none known           |
| OP11 | no     | 023-09, 5.3               | measured by a probe      | none needed          |

"bytes": the fix changes the bytes a database writes, so new StreamDigest
digests and a new pin for the C clone, but no record format. "format":
it changes the record format or the rerun. "none": neither.

* **OP1, the last touch (CL7).** The last step of an iteration touches
  from its scan's end with no end key (`Reclaim.step`: `t.touchTo =
  eod[0] ? null : lastKeyOfStep[0]`, on `main`), so with keys in time
  order it makes dirty the nodes of every key put since the iteration
  began, in one internal transaction of the user's commit.
  * Measured (024-03, section 7; `out/10m-fifo/fifo4.txt`): records of
    191,137,072 and 206,065,600 bytes, commits of 20,627 and 22,243 ms,
    two in 200,000 transactions whose mean record is 24,865 bytes and
    commit p50 0.76 ms: about 8,000 times the mean. At 1M live keys
    16.9 MB and 1.7 s; in a fill of 10M keys in key order 29.7 MB and
    5.7 s. About 20 bytes a live key. Not with random overwrites (the
    drive's largest record is 170 kB). 2026.3 the same.
  * Evidence: exact bytes, one run each; the cause is read, not counted
    at 10M (024-03 says so). Review A's `ReclaimTail` shows it small:
    one step dirtied 81,018 nodes, 5.8 MB (review A, section 2.6).
  * Fix: mark only the paths of the step's rewrites and its row, in
    place of `Db.touchRange`; A's prototype: 27 nodes, 20 rounds of
    cuts, three traces with C-CUT (review A, section 4.2). It needs the
    cut's argument again. The touch is not rerun: bytes, no format.
* **OP2, after scattered deletes (CL2).** All but every 30th key
  deleted, then 300,000 transactions of overwrites, against the twin:
  86,651 against 26,351 bytes a transaction, commit p50 2.66 against
  0.85 ms, the scan 1,777 against 390 ms, a get right after the deletes
  7.33 against 1.42 µs (024-03, section 5). At 1M keys the bytes do not
  show (1.17 times). The shape is ST2. Fix: merges at the delete (P5,
  545 lines, two faults of its own found) or a rebuild by reclaim's
  touch (023-04, X3); either is a rule of the rerun.
* **OP3, a put's stream bytes.** 24-byte keys, 8-byte values, uniform
  updates: 867 bytes at 10M keys, 1,244 at 50M (measured), 1,383 at 100M
  (a model, within 15 % where checked), for 32 user bytes. 024-03's
  fill: 328 bytes a put at 1M, 722 at 10M. The cost follows sd / K
  alone: 854 at 1M and 5 MB against 867 at 10M and 50 MB. So it is
  constant if sd follows the keys, and grows by 400 to 650 bytes for
  each tenfold K if not (006-19, section 4.2). Levers: sd (none); a
  compact key node encoding, 35 to 40 % fewer index bytes, estimated
  (format); delta writes, 2 to 3 times fewer, estimated (format, high
  risk) (006-19, section 6). Whether it breaks the aim is QF3.
* **OP4.** After a decrease from 1000 to 100 MB the largest record grows
  with the keys; the cause is the pace's factor S/sd, up to 10 (007-07,
  section 11). Fix: cap it (015-84, open); `T3_take` holds for any share.
* **OP5.** The take writes whole transactions. Single puts with a batch
  of 500 now and then: a put's record reaches 209 kB against a mean of
  576 bytes (007-07, 7.1; sd 1 MB, 20,000 keys). Single puts alone at
  10M keys: 0.23 to 0.29 MB at most, the mean under 1 kB (levels.md,
  section 5). Large as a ratio, small in bytes; it grows with the batch.
  Accepted for now (Frans, 2026-10-28; 010-01, P4). A pace by nodes
  would avoid it and changes the model's step.
* **OP6.** The writer's still-dirty passes are as many as a long key's
  chain: 2.6 to 5.8 s for a key of 1 MB after one of 100 kB (021-16,
  Q1); 29 to 48 s for 4 MB next to 1 MB (020-11, section 11). 021-16's
  fix gives the same nodes in the same order; it is Rule A's test.
* **OP7.** A start follows sd, not the keys: the section is below twice
  the setting (`T3_take`, proved), and a start after 22 GB written took
  1.7 s warm (024-03, section 6; 2.1 s after the fill). Not bounded by a
  proof: the records at the section's ends (T4) and a cold start's reads
  into older records, 46 s on s1 (005-57). A transaction larger than sd
  makes every start read all of it (020-24-13, U13-7).
* **OP8.** A step reads each live KV's value, also one stored at pCut or
  later; `Kvt.spos` would tell before the read ("halve the step's
  reads", 023-05 P8, section 8). Not measured (024-03, section 8).
* **OP9.** Within the aim, as I read it: the lag is paid by later writes
  in proportion to what was deleted, the stream peaks at 1.1 times, and
  scans, gets and commits are right at once. P8 saves one iteration.
* **OP10, OP11.** 024-03's runs at 10M have a slowest commit of 94 to
  129 ms under G1: likely the collector's, which P1 does not count; not
  shown. `dirtyNodeBound`'s over-count only lowers the largest
  transaction accepted.
  **Decided** (Frans, 2026-11-12, 12:10): in 2026.5, "Want this in
  place for solid internal algos."; made in 024-34.
  **Decided** (Frans, 2026-11-12, 12:10): P8 moves to 2026.6 (026); G4
  (024-30) shows back to empty converging without it, in about 4.4 R.

Within the aim on the numbers: a get at 10M (1.9 loads and 7.8 µs,
against 0.37 loads and 2.2 µs at 1M); scans after a mass delete (101 key
nodes against the twin's 87); the mass delete itself (largest record
126 kB, slowest commit 94 ms); the take (the section at 1.00 to 1.14
times the setting); eviction and the dead hand (steps of at most 2 ms
by design, levels.md, section 7); `close()` (1 to 2 ms).


## 3. Aim 3: storage

| ID   | Storage                        | Measured                        | Proportional one     |
|---|---|---|---|
| ST1  | heap a KV, one-key segments    | MEM 327 at 10M KVs              | 129.6 at 1M          |
| ST2  | key nodes after sparse deletes | 420,636 for 333,334 live keys   | 37,084, the twin     |
| ST3  | the stream kept under reclaim  | 1.45 to 1.95 GB; 6.79 GB filled | 0.33 GB fresh        |
| ST4  | dead klongs in live nodes      | up to 30 a node; after 700 cuts | none, eventually     |
| ST5  | dirty top nodes after a delete | up to 152                       | 48 to 66, the twin   |
| ST6  | the cache's tables             | 219,104 slots                   | 22,144, the twin     |
| ST7  | the key access path's arrays   | the longest path ever followed  | the last one         |
| ST8  | heap of an empty database      | 11 MB                           | near nothing         |
| ST9  | a start's heap                 | 3.3 to 4.9 x sd                 | the running one      |
| ST10 | D, pinned                      | 1.6 to 2.9 x sd; now about 1.1  | sd                   |
| ST11 | disk beyond the kept stream    | 6 to 9 % more                   | the kept stream      |

| ID   | Breaks | Described in              | Evidence                 | Fix; it changes      |
|---|---|---|---|---|
| ST1  | might  | 024-03, 3; 006-19, 4.2    | measured; cause read     | none proposed        |
| ST2  | yes    | 024-03, 5; 023-02, R12    | measured, counts exact   | prototype; format    |
| ST3  | might  | 024-03, 3, 4, 7, 8        | measured, one run        | a policy; bytes      |
| ST4  | yes    | 023-08, 3 and Q5; 024-01  | a probe; an allowance    | options; format      |
| ST5  | no     | 023-10, 6; 023-09, 5.1    | measured, does not grow  | P7; bytes            |
| ST6  | yes    | 023-08, 4                 | a probe, small           | known, small; none   |
| ST7  | yes    | 023-02, K16; 023-04, 2.11 | read in the code         | known, small; none   |
| ST8  | yes    | 020-24-10, U10-2          | measured                 | known, small; none   |
| ST9  | no     | levels.md, 7; 019-45      | measured; by design      | none                 |
| ST10 | no     | levels.md, 7; 007-07, 11  | measured; T4 not proved  | none                 |
| ST11 | no     | levels.md, 6; 023-02, K17 | measured (011-04)        | a non-goal           |

* **ST1, a segment of its own.** MEM's method (no eviction, a
  `DummyStream`, empty values, keys `"" + i`) gives 129.6 bytes a KV at
  1M KVs and 327.0 (2026.3) and 327.1 (2026.4) at 10M (024-03, section
  3; `out/10m/mem4.txt`).
  * The explanation, by reading: `Keys.toSegments` cuts a key into
    segments of 7 bytes and gives a key of exactly 7 bytes a second,
    empty segment. Keys "1000000" to "9999999" are 9M of the 10M, each
    with a first segment no other key has, so each gets a segment tree
    of one key. At 1M every key is at most 6 bytes: one segment. My
    arithmetic: (327 - 129.6) / 0.9 = 219 bytes for each such tree (a
    key node, its handle, its table entry). No class histogram (GM1).
  * So the case is not "MEM grows with K" but **a key whose segment no
    other key shares costs a key node of its own**: about 220 bytes of
    heap, and in the stream "three one-key segment leaves a key", about
    480 bytes a put, for random 24-byte keys (006-19, section 4.2,
    point 6); 023-03's "hashed" shape is the same. Keys that share
    their prefixes, as 024-03's, do not pay it. No item I read proposes
    a fix; inlining a one-key tree would be a format change.
  * With eviction, the default, the heap follows the budget, not the
    keys: 195 MB after the random fill of 10M keys, 259 MB after the
    fill in key order, 225 MB after the mass delete's run; budget 200 MB.
* **ST2, the underfill (CL2).** 419,680 key nodes after the deletes
  against the twin's 26,746 (15.7 times); after 55 reclaim iterations
  420,636 against 37,084 (11.3 times), KEY klongs 3,664,200 against
  544,651, kept 1.04 against 0.39 GB: under one live key a key node,
  where the twin has about 9. 2026.4's bounded allowance (in the keys
  ever put; Frans, 2026-11-10, 10:38: "Bounded is ok", strict "if we
  find a good Strict solution") permits it; aim 3's "in proportion to
  their count" does not. Milder shapes are not measured.
* **ST3, the stream kept.** With R of 1,000 transactions: after a random
  fill of 10M keys 6.79 GB for about 1.13 GB of keys and values; under
  steady overwrites of 1M keys 1.45 to 1.95 GB against 0.33 GB fresh,
  4.5 to 6 times; in the FIFO at 10M live keys kept rose from 2.34 to
  6.43 GB in 200,000 transactions and had not levelled off. By design: a
  step runs while reclaim's bytes are below a quarter of the growth, so
  an iteration that rewrites the live data needs four times its bytes of
  growth, and the stream holds R's records and one or two iteration
  spans (006-19, section 3.4). Measured, not derived (017-04, Q8).
  Proportional to the live data; the constant is QF1.
* **ST4, dead klongs.** A leaf with a live key keeps its deleted and
  shadowed keys' klongs until its next time split: at most B = 30 a
  node, in time unbounded (an old delete entry stayed after 700 cuts in
  a cold chain, review A's `SegmentAge`), and for ever with R forever.
  A named allowance of 2026.4 (023-08, Q5). After the mass delete at 10M
  there is no excess (208,143 against the twin's 214,754); most of ST2's
  3.66M klongs are these (my arithmetic). Fix: compaction at the delete,
  or with the rebuild (024-01, section 4.4).
* **ST5.** About a hundred nodes whatever the size, set by one
  disturbance and not growing (023-10): a constant, so within the aim
  as I read it. Fix (a) changes the take and the Lean model's step.
* **ST6.** The slots are references: under 2 MB here (my arithmetic);
  at 10M the heap after a GC is 225 MB against the twin's 218 MB, all
  causes together. A shrink at a resize.
* **ST7.** `KeyAccessPath.clear()` nulls the used entries and keeps the
  arrays (read on `main`), so after OP1's touch they hold its range.
  OP1's fix removes the cause, AP (023-04, section 2.11) the rest.
* **ST8.** The 10 MB write buffer, allocated at the start (024-01, PA7).
* **ST9, ST10.** Both follow sd, not the keys. D's 1.6 to 2.9 times is
  005-38's, before the paced take; since, the debt is at most 1.10 sd at
  50M keys. In the heap D takes 2 to 2.5 times its stream bytes (006-19).
  **Decided** (Frans, 2026-11-12, 12:10): fixed in 2026.5, 024-33; G4
  (024-30) measured 3.76 times a hello-world twin's slots after back to
  empty.
  **Closed as negligible** (Frans, 2026-11-12, 11:52: "There may be a
  performance reason for KeyAccessPath.clear() to work as it does. It is
  better to close ST7 as neglectable than to degrade performance.");
  G4 prints it (665 entries against 16), not gated.
  **Decided** (Frans, 2026-11-12, 12:10): moved to 2026.6 (026).
* **ST12, found 2026-11-12 by G4 (024-30, section 9).** With eviction
  off (the Core's test setup, no budget), the cached objects of deleted
  keys stay resident after back to empty: 15,082 against the twin's
  1,017 at 100,000 keys. With eviction on (the Pub API's default) they
  go. **Not a case** (Frans, 2026-11-12, 12:12: "Eviction off is a test
  mode not use in production at all! Only for testing."): closed.

Not cases: the history with R forever (023-02, R8) and the memory of
ended versions with `noEvict()` (levels.md, section 7), both by design.


## 4. Bounds proposed

**Decided already**, and where:

* A scan is O(n) amortized at every available time, in 023-02's form
  R9 (Frans, 2026-11-10, 08:29 and 10:44). Its constants c = c' = 2 are
  023-03's proposal (Q3), not answered.
* The startup section without its last record is below twice the
  startup distance (007-03, D1; `T3_take`, proved).
* BergDB's own code holds no call for about 20 ms or more, a guide:
  under 50 ms on F53 and 100 ms on s1 is good (010-01, P1; 023-02, R21).
* Reclaim's steps are charged at most a quarter of the stream's growth;
  a step scans about 16 kB of KVs; eviction and the dead hand work in
  steps of at most 2 ms (levels.md, sections 6 and 7).
* After deletes, 2026.4 gates on the bounded allowance, twin + 10 +
  L h_fill nodes, with dead klongs at most B a node and the window
  (023-03, sections 2.6 and 10; 023-08, Q5).
* MEM at most 131 and SS at most 1.52 at 1M KVs (`level1.sh`).

**Proposed here** (mine; none is decided). "Checked today" names what
runs in a gate or a night; "by hand" means a probe kept in an item.

* **BD1. A commit's record** (put, delete, a reclaim step, the take's
  share). No record over the larger of 1 MB and 5 times the mean record
  of its run, the transaction's own values apart. Data: largest over
  mean 1.3 to 4.0 in 024-03's put runs without OP1, at most 2.3 at 50M
  keys (007-07, section 11); where the ratio is more (19 in the mass
  delete, about 300 for single puts) the record is under 0.3 MB. Broken
  by OP1 and OP4. Checked today: nothing; by hand, PF1's count of
  records over 1 MB.
* **BD2. A commit's time.** P1's guide, measured under ZGC; its
  constant is decided. Checked today: nothing at 1M keys or more; by
  hand, P4's soak and the pause probe (009).
* **BD3. A get.** At most H key nodes followed (023-02, R10) and H + 1
  loads. Data: 1.9 loads a get at 10M. Checked today: nothing; by hand,
  023-03's M6.
* **BD4. A scan.** R9 as decided, and at most 2 times the twin's key
  nodes for the same scan. Data: 1.10 to 1.16 after a mass delete, 11 to
  16 after sparse deletes. Checked today: nothing (T3 is a probe; its
  1,000 rounds never ran).
* **BD5. A put's stream bytes**, R forever: a function of sd / K alone.
  For 24-byte keys and 8-byte values, at most 900 bytes at 5 bytes of
  sd a key, 550 at 20, 200 at 100. Data: 854 and 867; 524; 190 (006-19,
  sections 3.5 and 4.2). Reclaim adds at most a third. Checked today:
  SS at a small size; `performance.sh` reports bytes a put at 1M keys
  or fewer, with no limit.
* **BD6. A start.** The section: decided. Time: at most 0.1 s a MB of
  sd, warm (62 to 104 ms a MB in 007-05; 42 here). Heap: at most 5 sd
  above the running database's (3.3 to 4.9, 019-45). A cold start: no
  constant yet. Checked today: `T3_take`; `performance.sh`'s restart
  scenarios at 100,000 keys.
* **BD7. A reclaim step.** Its record within BD1; the nodes it makes
  dirty at most a constant times the paths of the KVs it rewrites (27
  against 81,018 in review A's prototype); its loads at most its KVs'
  paths and the values it rewrites (OP8). Checked today: two liveness
  tests of `Reclaim.Tester`; `ReclaimStress` checks answers, not costs.
* **BD8. Reclaim's lag.** A dead version is gone within R and K
  iterations. Data: 3 iterations at 1M, 4 at 10M after 90 % deleted;
  023-02's F6 recommends K = 2, not answered. Proposed: K = 4 as the
  gate, since P8 is not asked for. Checked today: nothing; by hand, T1.
* **BD9. `close()` and `stop()`.** Work in the buffered bytes only, no
  index node written. Data: 1 to 2 ms here. Checked today: nothing.
* **BD10. The stream kept**, R finite: at most c times the twin's fresh
  stream, plus R's records and two iteration spans (023-02, R13's form).
  Data: c of 4.5 to 6. Proposed: c = 6 as a gate that guards today's; a
  lower target is QF1. Checked today: nothing; `performance.sh` reports
  `kept_mb_max` for 100 MB of data.
* **BD11. The heap, with eviction.** At most the budget, D (2.5 sd) and
  a fixed part; no term in the keys. Data: 195 to 259 MB at 10M keys, a
  budget of 200 MB, sd 50 MB. Checked today: LargerThanMemory
  (`level4.sh`), pass or fail.
* **BD12. The heap a KV, without eviction.** At most 131 bytes for a key
  that shares its segments, at every K, and a stated cost for each
  segment tree of one key (about 220, to be measured). Checked today:
  `level1.sh` at 1M KVs with keys of at most 6 bytes.
* **BD13. The reachable index.** At most 2 times the twin's key nodes,
  after one or more reclaim iterations (023-02, R12 (b); Frans's
  "strict"). Data: 11 to 16 times the twin after sparse deletes, 1.10
  after a mass delete. Checked today: nothing; by hand, T2's "sparse".
* **BD14. Small structures.** A table at most 4 times its live entries;
  a path array at most 4 times its last use (023-04's AP); an empty
  database at most 1 MB of heap. Checked today: nothing.

No test in `java/` checks a bound of aim 2 or 3 at more than 1M keys:
023-03's T1 to T4 and PF1 are probes in their items (024-01, TT1).


## 5. Where nothing is known

* **100M keys**: nothing is measured (024-03, section 9). The nearest:
  50M keys for a put's bytes and a warm start (007-07, section 11;
  007-05: 26 and 86 s at 200 and 1000 MB), 20M keys six times the budget
  (001-10), 006-19's model, and 024-03's extrapolation of OP1.
* **OP1 at the record limit.** About 20 bytes a live key gives 2 GB at
  100M keys in time order; `StoredTrans` refuses a record over 2^31 - 9
  bytes with a `DbException`. Whether the check before the go point
  counts a touch, and whether a refused or failed step fails the
  database or stops reclaim, I have not read. It may be a case of aim 1.
  At 10M its cause is read, not counted (`Reclaim.Stats` was off), and
  keys put ahead of the scan at random are not measured at scale.
* **Milder underfill**: every 2nd, 3rd or 10th key deleted; deletes
  spread over time with puts between (024-03, section 5).
* **Times and settings**: one run each, G1, a warm OS cache, F53, sd 50
  MB, values of 100 bytes, one thread, no sync. No ZGC, no s1.
* **The applications' workloads on 2026.4**: the metrics store (U18-1)
  and the index churn (U14-1) were not run again (2026.4's release
  notes; 023-03, T5). T3's 1,000 rounds and C11 (no value node of a
  deleted key once dead; the record walker H2) were never run.
* **A cold start after a mass delete** (the rerun reads each delete's
  path, 023-07, section 7); reclaim's loads a step (OP8).

The measurements that would close them, cheapest first:

* **GM1.** MEM's method at 1M KVs with 7-byte keys (i + 1,000,000),
  and at 10M with keys of at most 6 bytes (i in hexadecimal); a class
  histogram of one (006-02's `Probe006 histo`). Minutes; no quiet
  machine. About 350 and about 130 would confirm ST1's explanation.
* **GM2.** Read `Db.checkDirtyNodes` and `Reclaim.step` for a touch at
  the record limit; then PF1's FIFO at 10M with `Reclaim.Stats` on, and
  at 20M and 50M, bytes only: OP1's cause and its growth.
* **GM3.** PF1's sparse run at 10M with every 2nd, 3rd and 10th key
  left: counts only. It sets BD13's constant and says how common ST2 is.
* **GM4.** 006-19's M1 and M2 (bytes only): the format levers priced on
  real nodes, and 10M keys at 5, 20 and 100 MB standing for 100M.
* **GM5.** 023-03's T5 workloads (U18-1, U14-1), T3's rounds and the
  record walker H2 on 2026.4. Counts only.
* **GM6.** 024-03's set under ZGC on a quiet F53, three runs, with the
  slowest commits attributed (the pause probe's method): BD2, OP10.
* **GM7.** 100M keys on F53 at night: a fill in key order (about 24 GB
  at 244 bytes a put) and the FIFO, after OP1's fix or GM2's reading. A
  random fill at 50 MB writes 72 GB or more (024-03, section 9) on a
  disk with 119 GB free: only at a startup distance of 500 MB or more.
* **GM8.** s1: a cold OS cache at 10M keys (start, gets, reclaim's
  loads a step with and without OP8's change).


## 6. A proposed order of work

Largest disproportion first; a case with a cheap fix rides with the
larger one that touches the same code.

1. **Guards and three cheap answers.** 023-03's tests as code (024-01,
   TT1) with PF1's record counter as a night step, so that BD1, BD4,
   BD8 and BD13 have a test before anything changes; GM1, GM2, GM3.
2. **OP1, the last touch**, by rewrite paths. With it, in the same
   code and one batch of stream bytes: OP8 (reclaim's value reads), ST7
   (the path arrays), OP4 (the pace's cap), and TE if the cut's argument
   gives it free (024-01, CL8). P8 (OP9) changes the same step: not
   needed by 024-03's numbers, so it stays out unless GM2 shows keys put
   ahead of the scan at random to be a case.
3. **The small ones, no stream change**, any time: ST6 (the tables),
   ST8 (the write buffer), OP6 (long keys; with a level2 run).
4. **ST2 with OP2, and ST4: strict.** The largest change and the only
   one with a record format. A design study first, merges at the delete
   against reclaim's rebuild, with GM3's numbers: the rebuild takes ST4
   too, merges do not. It waits for QF2, and comes after step 2, as both
   touch what reclaim's step rewrites.
5. **The constants: ST3 and OP3.** By measurement (GM4, GM7), then a
   decision: reclaim's fraction, a startup distance that follows the
   keys, or a format lever. No code before the numbers.
6. **Left as they are**, named: OP5, ST5, ST9 to ST11, OP7 until T4.

| Fix           | Code                         | Bytes | Format | Lean model          |
|---|---|---|---|---|
| OP1, OP8, TE  | `Reclaim.step`, `touchRange` | yes   | no     | C-CUT's argument    |
| P8 (OP9)      | `Reclaim.step`               | yes   | no     | T-SCHEME, checked   |
| OP4, OP5, ST5 | `TransSeq.take`              | yes   | no     | the take (OP5, ST5) |
| OP6           | the still-dirty passes       | no    | no     | Rule A's test       |
| ST2, ST4      | `Dag`'s delete, the rerun    | yes   | yes    | 024-06's            |
| OP3's levers  | `StoredKeyNode`              | yes   | yes    | none (M10, argued)  |
| ST6, ST7, ST8 | cache, path, write buffer    | no    | no     | none                |

* **Same code:** OP1, OP8, TE, P8 and `maintain()` (024-01, CL5) all
  change reclaim's step: one design, changed once. OP4, OP5 and fix (a)
  of ST5 all change the take, whose bound is proved for any share.
* **Same format:** ST2, ST4 and a compact key node encoding each cost a
  record or node format. 2026.5 need not open 2026.4's databases
  (024-04, section 5), so one new format can carry what is decided;
  024-02's Q1 (the merge switch) is decided with QF2.
* **Every change of bytes** needs new StreamDigest digests and a pin for
  the C clone (024-01, section 12): two batches, step 2's and step 4's.
  ST2's mechanism is also what 024-06's model must cover.


## 7. Questions for Frans

* **QF1. The stream kept under reclaim.** Today 4.5 to 6 times a fresh
  database of the same keys, by the quarter that reclaim may write. Is
  that constant within aim 3, or is a lower one wanted, at the price of
  more bytes a put? Recommended: accept it for 2026.5 as BD10 with c =
  6, a gate on today's; decide the fraction after OP1's fix and GM7.
* **QF2. Does aim 3 make strict the gate?** BD13 (twice the twin's key
  nodes) in place of 2026.4's bounded allowance, with ST4's dead klongs.
  Recommended: yes, as the aim reads; in 2026.5 after OP1, by a design
  study that chooses between merges and the rebuild with GM3's numbers,
  taking a new record format.
* **QF3. A put's bytes that grow with the logarithm of the keys.**
  Within aim 2, when stated as a function of the startup distance a key
  (BD5)? Recommended: yes; no format lever in 2026.5, GM4 run to price
  them, and the startup distance a key in the documentation.
* **QF4. Which memory figure gates?** Recommended: both: BD11 (the heap
  with eviction has no term in the keys) and BD12 (MEM a KV at 1M and
  at 10M, with the cost of a one-key segment tree named), after GM1.
* **QF5. One-key segment trees (ST1).** A cost of the key's shape to
  document, or a case to fix (a format change)? Recommended: document
  it in 2026.5; a fix only as a study, if QF2 brings a new format.
* **QF6. Counts or times?** Recommended: the bounds gate on counts
  (the largest record's bytes, key nodes, loads), as 023-03 did; times
  are reported, and BD2 is checked under ZGC in a night step.
* **QF7. 100M keys.** Shown at 100M, or at 10M with the scale law and
  one run at 100M in key order (GM7)? Recommended: the latter; F53's
  disk does not hold a random fill at 50 MB.
* **QF8. The take's bursts.** Recommended: OP4's cap, small; OP5 stays
  a named allowance, as its fix changes the model's step and its proofs.


## 8. State

2026-11-11, by an agent of coord-1111; read only at `main` `b3faaffa`.

* **Done.** Sections 1 to 7, each figure checked at its source: 024-01,
  024-03 with its outputs, 024-04, 023-02, 023-03, 023-07 (3.2, 7),
  023-08 with review A (2.6, 4.2), 023-09 (5, 6), 023-10, the open lists
  of 015, 019 (none open) and 021 (021-27, not a case of these aims),
  007's readme, 007-07 (7), 006-19, 017-04, 010-01 (P4, P5), levels.md,
  2026.4's release notes; in the code `Keys.toSegments`,
  `KeyAccessPath.clear`, `Reclaim.step`, `StoredTrans`'s limit,
  `level1.sh`'s limits and PF1's `gets`.
* **Found on the way.** 024-03's "25 versions a get" is a cumulative
  counter (1.9 loads a get); its "20 records of 17 MB" (section 7) are
  20 records over 1 MB, the largest 17 MB, in the FIFO run on the
  mass-deleted database (`out/10m/log4.txt`). 024-03 is not changed.
* **Not done.** Nothing measured: ST1's explanation and OP1's cause at
  10M are by reading. Not read: 023-04 beyond X3 and 2.11, 023-05,
  023-06, 007-01 to 007-06 and 007-08 in full, 006-02 and 006-16 beyond
  their MEM figures, 005-38, 011-04. The bounds' constants rest on one
  run each. The readme's line for this file is the coordinator's.
* **Next.** Frans's answers to QF1 to QF8; GM1 to GM3; then the bounds
  that stand become tests (section 6, step 1).
