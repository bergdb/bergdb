# 024-30. Count gates for aims 2 and 3 at 1M keys

Created 2026-11-12 by Frans Lundberg. Status: open (built and gated on a branch; not yet on `main`).

Release 2026.5's aims 2 and 3 (024-04, section 1): operations and
storage are proportional. 024-04, section 4: each aim becomes bounds with
tests. Until this item no test in `java/` checked a bound of aims 2 or 3
above 1M keys; the probes were in items (024-05, section 4). Frans
approved the plan on 2026-11-12, 11:35 ("Step 2. Yes, start it."). The
gates are on counts (bytes, key nodes), not times (024-05, QF6).

By the agent "gates" of coord-1112, from 11:36. Clone
`/Users/f/fl/bench/2026-11-12/gates/clone`, branch `024-30-count-gates`
from `main` at `e404dab7`.


## 1. In short

* **Three count gates at 1M keys**, `java/stress/CountGates.java`, run by
  `java/stress/count-gates.sh` as a step of `java/night.sh` after
  `level4`: G1 (BD1, a commit's record), G2 (BD13, the reachable index),
  G3 (BD10, the stream kept). Limits at 024-05's constants: 1 MB or 5
  times the mean; 2 times the twin; 6 times the twin's fresh stream.
* **All three pass on `main`** (section 4): G1 108,912 bytes against
  1 MB (margin 9.18); G2 1.296 times the twin (margin 1.54); G3 4.410
  (margin 1.36). About 130 s on F53 for the three.
* **G1 and G2 fail on release 2026.4** (section 5), as they should: the
  last touch's record of 16.7 MB (024-07's number at 1M keys, to the
  kB), and 16.0 times the twin's key nodes after the sparse deletes
  (023-03 measured 15.3 at 1M keys). G3 passes there too (4.605): it guards today's level,
  as 024-05 proposed c = 6, and needs no fix to pass.
* Every count is deterministic (fixed seeds, a test clock): a rerun on
  the same code gives the same numbers.


## 2. What was built

* **`java/stress/CountGates.java`** (package `bergdb.core`, to reach
  `Reclaim.Stats` and the maintenance follower; compiled by `build.sh`
  into `build/stress/` as the other stress programs). Three gates, run
  one after another (`all`) or one at a time (`g1`, `g2`, `g3`). Each
  prints one line, `Gx BDy QUANTITY value V limit L margin M PASS|FAIL`,
  where the margin is limit / value (above 1 passes); the detail lines
  start with two spaces. Exit status 1 if a gate fails. Built from three
  probes: CleanupRule's counting follower and its twin (023-03, sections
  2 and 3), PF1's keys, values, records and drives (024-03), and
  ReclaimCost's stream kept under reclaim.
* **`java/stress/count-gates.sh`**: builds, runs `CountGates all` with
  4 GB of heap and no `-ea`, prints the gate lines and the time, and ends
  with `COUNT GATES OK` or `COUNT GATES FAILED` (status 1). Output in
  `java/build/count-gates/count-gates.txt`; the databases in
  `java/build/count-gates-data/`, deleted at the end.
* **`java/night.sh`**: the step `count-gates` after `level4`. Not in
  `before-commit.sh`: it takes minutes (before-commit must stay fast).

Every database is a `FileStream` with the builder's defaults (startup
distance sd = 50 MB, cache indicator 200 MB, eviction on), a test clock
that advances dt = 10,000 units (1 ms) a transaction, and
`Reclaim.Stats` on. Where a gate sets a retain duration, R = 1 s of the
test clock, 1,000 transactions. Keys are PF1's, `/k/%010d` (13 bytes);
values 100 bytes. Every run is deterministic (fixed seeds, test clock):
its counts repeat.


## 3. The quantities, exactly

### 3.1 G1, BD1: a commit's record

**Workload.** A new database with R set; a fill of n = 1M keys in key
order, 100 a transaction (keys in time order, with reclaim on); then
60,000 transactions of the FIFO (024-03, section 7; 024-07, section 8):
each puts 100 new keys after every key so far and deletes the 100
oldest, so n keys stay live; then 20,000 transactions of 100 overwrites
of random live keys.

**The quantity.** For every record written, user or internal (a reclaim
step, the table), from `Reclaim.Stats`, which `Db` updates after it
writes each record (`Reclaim.recordWritten`): x = the record's stream
bytes (`nextPos - tpos`) minus the bytes of the value nodes in it
(`StoredValueNode.getByteSize`: the key, the value and the node's
overhead). The value nodes are the transaction's own values: the user's
puts, or the values a step rewrites. The index nodes, the take's share
and the rest stay in x. CountGates reads the three counters (user,
step, table) after each user transaction; if it sees two records of the
same writer at once, it counts them as one of their summed size, which
can only make the largest larger (printed as `together`).

**The gate.** max x ≤ max(1 MB, 5 · mean x), the mean over every record
of the run (fill, FIFO and overwrites).

### 3.2 G2, BD13: the reachable index

**Workload.** Two shapes, each on its own new database with R set: a
fill of n = 1M keys in random order (seed 1), 100 a transaction; then
deletes in key order, 100 a transaction, of (a) "sparse": every key but
every 30th (33,334 live; 024-03, section 5, OP2 and ST2's shape), (b)
"mass": the first 90 % of the keys (100,000 live; 024-03, section 4).
Then transactions of 100 overwrites of random live keys until two
reclaim iterations that started at or after the stream position where
the deletes ended are complete (`Stats.Iteration.pStart` at or after
it, `pEnd` set), at most n / 20 transactions.

**The quantity.** The reachable key nodes: the distinct key nodes (by
id) that a scan of every user key (from `/k/`, at the latest time)
follows, counted by CleanupRule's follower, which wraps
`NodeCollection.maintenance()` (it loads without installing). The scan
must return exactly the live keys. **The twin**: a new database, R
forever, the same live keys put in key order, 100 a transaction, the
same values' size (024-21's twin), counted the same way.

**The gate.** keyNodes / twin's keyNodes ≤ 2 for both shapes; the gate
line has the worse. Fewer than two iterations within the cap is a
failure.

### 3.3 G3, BD10: the stream kept

**Workload.** A new database, R forever: a fill of n = 1M keys in
random order, 100 a transaction. Then R is set, and transactions of 10
overwrites of uniformly random keys (small transactions, so that the
step cap of 16 kB of scan a user transaction does not pace reclaim;
024-29, section 4.2), until the third cut, at most 2n transactions.

**The quantities.**

* **L0, the twin's fresh stream**: the stream length after the fill and
  a sync, before R is set. That fill is exactly a twin's build: a new
  database with every live key, and the live keys and the values' sizes
  never change after it.
* **kept**: `getStreamLength() - getFirstAvailablePos()`, the stream
  from the decided cut (a function of the transactions, not of timing).
* **H_R, the bytes of the records within R**: the stream bytes of the
  user's records (`Reclaim.Stats.user.bytes`, values and index nodes
  that the user's transactions wrote) committed at or after now - R:
  with one transaction a dt and R = 1,000 dt, those of the last 1,001
  transactions. Reclaim's own records within R are not in H_R: they are
  overhead (Frans, 2026-11-12: the history within R is the user's
  value, the rest is reclaim's overhead). The detail line also prints
  all records within R (the stream's growth over them) for comparison.

**The gate.** From the transaction at which the first reclaim iteration
is complete until the third cut, after every transaction:
peak (kept - H_R) ≤ 6 · L0 (c = 6, 024-05, BD10 and QF1).


## 4. Calibration on `main`

One run of `count-gates.sh` on the branch (`main`'s code at `e404dab7`
with the three new files), 2026-11-12, 11:42 to 11:45, in a slot;
output in `30-count-gates/calibration-main.txt`.

| Gate | Quantity                         | Value         | Limit     | Margin | Result |
|---|---|---|---|---|---|
| G1   | largest record, values apart     | 108,912 B     | 1,000,000 | 9.18   | PASS   |
| G2   | key nodes over the twin's, worst | 1.296         | 2         | 1.54   | PASS   |
| G3   | (kept - H_R) / L0, peak          | 4.410         | 6         | 1.36   | PASS   |

* **G1**: 172,473 records, mean x 4,416 bytes; so 5 times the mean is
  22 kB and the 1 MB floor is the limit. The largest is a user record of
  100 overwrites (transaction 10,187 of the overwrites): 109 kB of index
  nodes, the take's share. No record of a step comes near it.
* **G2**: sparse, 3,401 key nodes against the twin's 2,624 (1.296);
  mass, 9,735 against 7,873 (1.237). Two iterations after the deletes
  took 8,880 and 9,933 drive transactions. With merges at the delete the
  sparse shape had 3,397 key nodes right after the deletes, before any
  iteration. Not gated: 11,924 of the 48,661 KEY klongs that the sparse
  scan follows are dead (deleted or shadowed), 24 % (ST4's dead klongs).
* **G3**: L0 = 245,216,944 bytes; the peak at transaction 164,062 of
  179,127: kept 1,085 MB, H_R 3.8 MB (all records within R: 7.2 MB),
  so kept - H_R = 4.41 L0. 024-29, section 4, expected 2.4 to 3.6 for
  overwrites at f = 0.25, plus the startup distance's share (sd is 0.2
  L0 here); 4.41 is just under ST3's measured 4.5 to 6 (024-05).
* **Limits kept at the BD constants**: the run shows no reason to move
  them. G3's margin, 1.36, is the smallest: a change that makes reclaim
  keep 36 % more fails it.


## 5. The gates can fail: release 2026.4

The same `CountGates.java`, unchanged, built on the tag `release-2026.4`
(before the last touch's fix, 024-07, and the merges, 024-21), run in a
slot at 11:46 to 11:49; output in `30-count-gates/release-2026.4.txt`.

| Gate | Value on 2026.4   | Limit     | Margin | Result | On `main` |
|---|---|---|---|---|---|
| G1   | 16,693,984 B      | 1,000,000 | 0.06   | FAIL   | 108,912 B |
| G2   | 16.028            | 2         | 0.12   | FAIL   | 1.296     |
| G3   | 4.605             | 6         | 1.30   | PASS   | 4.410     |

* **G1**: the largest record is a user record of the FIFO (transaction
  9,544), 16.7 MB of index nodes: the last step's touch over every key
  put since the iteration began, written by the next take. 024-07,
  section 8, measured 16.7 MB for this shape at 1M keys.
* **G2**: sparse, 42,170 key nodes against the twin's 2,631 (16.03;
  023-03 measured 15.3 at 1M, 024-03 15.7 at 10M), with 282,401 of 357,907 KEY klongs dead;
  mass, 1.407. Merges fixed the first.
* **G3** passes on 2026.4. It is a guard of today's level, not of a
  fix; a lower c waits for 024-29 (QF1).


## 6. Not done, and for later

* **A 10M variant** (`count-gates.sh n=10000000`), not a step: the
  three would write about 10 times the bytes (G1's FIFO alone 600,000
  transactions, G3's stream peak about 11 GB on disk) and take, by the
  1M run's 130 s, half an hour or more. A by-hand run before the
  release, or a weekly step; not run here (out of scope).
* **Other bounds** (BD3 to BD9, BD11, BD12, BD14), time gates (BD2), and
  other workloads for G3 (hot, cold, 1,000-byte values, 024-29, section
  5.3): out of scope.
* **ST4's dead klongs** are printed (G2's detail lines), not gated.


## 7. Questions for Frans

* **Q30-1. G1's floor.** At 1M keys the mean record without its values
  is 4.4 kB, so the 1 MB floor decides, and a record of 0.99 MB would
  pass. Keep BD1 as stated (recommended: yes; the gate catches the
  faults known, 16.7 MB), or a lower floor such as 256 kB?
* **Q30-2. H_R, the user's records only.** Reclaim's own records within
  R count as overhead (section 3.3). Recommended: keep it so; it is the
  stricter reading.


## 8. State

* **Done** (2026-11-12, 11:36 to 11:53): `CountGates.java`,
  `count-gates.sh` and the night step, committed on the branch
  `024-30-count-gates` of the clone
  `/Users/f/fl/bench/2026-11-12/gates/clone`, head `bfba0928` (from
  `main` at `e404dab7`), in Frans's name. Calibrated on `main` (section
  4, all pass), shown failing on release 2026.4 (section 5, G1 and G2
  fail). Gates on `bfba0928`: `before-commit.sh` BEFORE COMMIT OK (65 s,
  in a slot); `count-gates.sh` COUNT GATES OK
  (11:49 to 11:52, in a slot; 125 s for the gates, the same counts as
  section 4 to the byte; `30-count-gates/gate-bfba0928.txt`).
* **Not done**: the 10M variant (section 6, for later); Q30-1 and
  Q30-2 for Frans (section 7). Not on `main`: the coordinator lands the
  branch.
* **To continue**: merge the branch; the night's `count-gates` step
  then runs the three gates. To change a limit or a workload, edit
  `CountGates.java` and section 3 together. The 2026.4 build is a
  worktree of the clone at `/Users/f/fl/bench/2026-11-12/gates/r264`
  (removed when done; `git worktree add ../r264 release-2026.4` and a
  copy of `CountGates.java` make it again: it builds there unchanged).
