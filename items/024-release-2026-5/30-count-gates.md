# 024-30. Count gates for aims 2 and 3 at 1M keys

Created 2026-11-12 by Frans Lundberg. Status: done (2026-11-12): G1 to
G3 on `main` since `8e163bbc`, G4 since `5c4ef762`; Q30-1 to Q30-4
decided.

Release 2026.5's aims 2 and 3 (024-04, section 1): operations and
storage are proportional. 024-04, section 4: each aim becomes bounds with
tests. Until this item no test in `java/` checked a bound of aims 2 or 3
above 1M keys; the probes were in items (024-05, section 4). Frans
approved the plan on 2026-11-12, 11:35 ("Step 2. Yes, start it."). The
gates are on counts (bytes, key nodes), not times (024-05, QF6).

By the agent "gates" of coord-1112, from 11:36. Clone
`/Users/f/fl/bench/2026-11-12/gates/clone`, branch `024-30-count-gates`
from `main` at `011aa9bf`.


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
* **G4, back to empty** (Frans, 2026-11-12, 11:47 and 11:52; sections 8
  and 9): 023-03's T1 at 1M keys, put and deleted, then a drive of 40 R
  against a hello-world twin. On `main` kept, key nodes, dead klongs,
  resident objects, handles and the heap after a GC are 1.00 to 1.46
  times the twin's (limit 2). Two findings: **the cache's table slots
  (ST6) stay at 3.76 times the twin's** (226,400 against 60,272;
  reported, not counted, the fix is a separate decision), and **the
  emptied database needs 4.4 R of drive to converge** (its first cut at
  transaction 4,117, the twin's at 1,214), so T1's fixed drive of 4 R
  would fail it at 1M. ST7 is printed only: closed as negligible by
  Frans's word.


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

One run of `count-gates.sh` on the branch (`main`'s code at `011aa9bf`
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
* **G4**: ST6 is reported, not counted; the lag is printed, not gated
  (Q30-3); no 10M run.


## 7. Questions for Frans

* **Q30-1. G1's floor.** At 1M keys the mean record without its values
  is 4.4 kB, so the 1 MB floor decides, and a record of 0.99 MB would
  pass. Keep BD1 as stated (recommended: yes; the gate catches the
  faults known, 16.7 MB), or a lower floor such as 256 kB?
  **Decided by the coordinator under Frans's delegation** (2026-11-12,
  12:33: "Handle the other ones for me."): keep BD1 as stated.
* **Q30-2. H_R, the user's records only.** Reclaim's own records within
  R count as overhead (section 3.3). Recommended: keep it so; it is the
  stricter reading.
  **Decided by the coordinator under Frans's delegation** (2026-11-12,
  12:33: "Handle the other ones for me."): keep it so.
* **Q30-3. Gate G4's lag?** The emptied database converges after 4.4 R
  of drive at 1M keys (section 9). A gate such as "within twice the
  twin's kept from 8 R on" would catch a cleanup that falls further
  behind. Recommended: yes, after one run at 100,000 and 3M keys shows
  how the lag grows with n.
  **Decided by the coordinator under Frans's delegation** (2026-11-12,
  12:33: "Handle the other ones for me."): yes, after the runs at 100,000
  and 3M keys, in 2026.6 (026); printed, not gated, until then.
* **Q30-4. ST6.** The handle tables keep their peak size (section 9).
  Fix it (shrink at a removal below a quarter of the capacity), or
  close it as negligible like ST7 (about 0.9 MB at 1M keys)? Not
  decided here; the gate line reports it.
  **Decided** (Frans, 2026-11-12, 12:10): fixed in 2026.5, 024-33.


## 8. G4, back to empty: the quantities

Frans, 2026-11-12, 11:47: "I think a general test is the back-to-empty
test. Big database, then all kvs removed, check eventual resource
consumption. Does it go towards something similar to a fresh empty
database?" Approved as a fourth gate at 11:52. It is 023-03's T1 (the
hello-world convergence test, section 2; its prototype CleanupRule) at
1M keys, with the memory side added: the cache's tables (ST6, 024-05),
KeyAccessPath's arrays (ST7) and the heap after a GC.

**Workload**, two databases one after the other (`CountGates g4`), each
on a `FileStream`, startup distance 100 kB (T1's), R = 1 s of a test
clock that advances 1 ms a transaction, the test id, and the builder's
default cache (indicator 200 MB, eviction on):

* **The emptied database**: set R; put "/a.txt" = "Hello world!"; fill
  n = 1M keys `/k/%010d` in key order, values of 100 bytes, 100 a
  transaction; delete them all in key order, 100 a transaction; then
  **the drive**: 40,000 transactions (40 R), each one overwrite of
  "/a.txt" with 1,000 bytes.
* **The twin**: the same without the fill and the deletes: R, "/a.txt",
  the same drive.

**Two choices against T1, from the calibration:**

* **A drive of 40 R, not T1's 4 R.** At 1M keys the emptied database's
  first cut in the drive comes at transaction 4,117: after 4 R it still
  keeps 262 MB against the twin's 2.0 MB, and every measure fails
  (`30-count-gates/g4-drive-4R-evict.txt`). By 40 R it has converged
  (section 9). The lag is printed, not gated (Q30-3).
* **Eviction on, not T1's `noEvict`.** With eviction off the resident
  objects of the deleted keys stay after the stream has converged: at
  100,000 keys after 4 R, kept 1.01 times the twin's, but 15,082
  resident objects against 1,017 (a trial, not kept as a file); at 1M
  after 4 R, 143,915 against 1,017 (`g4-drive-4R-noevict.txt`). The
  eviction's own passes drop them; users run with eviction on, so the
  gate does too (`g4evict=0` gives T1's setting).

**The measures**, taken at the end of the drive, under the write lock,
the other gates' databases closed:

* **M1, kept**: `getStreamLength() - getFirstAvailablePos()`, the most
  after each of the last 1,001 transactions of the drive (the last R).
* **M4, reachable key nodes; M5, dead KEY klongs**: CleanupRule's
  counting follower on a scan of every key (the internal ones too) at
  the latest time, as in G2: the distinct key nodes, and the KEY klongs
  in them that are deleted or shadowed. The scan must find exactly one
  user key, "/a.txt".
* **M11**: the resident index objects (`Residents.objects()`) and the
  live handles (`Cache3.handles()`), in the running database (T1 takes
  them after a restart and a probe).
* **ST6, the cache's table slots**: the sum of the table lengths of
  `Cache3`'s `HashMap`s, read by reflection (024-05's "slots"; A's
  `CacheCapacity`, 023-08). Needs `--add-opens java.base/java.util`,
  which `count-gates.sh` passes.
* **ST7, KeyAccessPath's arrays**: the lengths of the writer's
  `PutData.keyAccessPath` arrays (klongs and nodes), by reflection.
  **Printed, not gated, and KeyAccessPath unchanged**: Frans, 11:52,
  "There may be a performance reason for KeyAccessPath.clear() to work
  as it does. It is better to close ST7 as neglectable than to degrade
  performance." ST7 is closed as negligible by Frans's word.
* **The heap after a GC**: the used heap after four `System.gc()` calls
  with the database open, minus the same before it was made.
* **The lag** (printed): the first drive transaction after which kept
  stays at most twice the twin's M1, and the first cut in the drive.

**The gates**: each measure of the emptied database over the twin's at
most 2 (`g4kept`, `g4nodes`, `g4slots`, `g4heap`). The factor: the
calibration's ratios are 1.00 to 1.46; 2 leaves a margin of 1.37 or
more, and at 4 R it fails M1, M5, M11 and the heap. ST6 fails on `main`; its line says
FAIL and the next line "known ... not counted", and it does not change
the exit status (`g4st6=gate` counts it), so that the night step stays
green for the other gates until ST6's fix is decided.


## 9. G4 on `main`: the numbers

One run of `count-gates.sh` (all four gates) on `177178ce`, 11:57 to
12:00, in a slot; output `30-count-gates/gate-ce1c932c.txt`. G1 to G3
gave the same counts as section 4, to the byte. G4 took 8 s; the four
gates 136 s.

| Measure                     | Emptied     | Twin        | Ratio | Limit | Margin | Result  |
|---|---|---|---|---|---|---|
| M1, kept, most in last R    | 2,618,568   | 2,442,256   | 1.072 | 2     | 1.87   | PASS    |
| M4, reachable key nodes     | 6           | 6           | 1.000 | 2     | 2.00   | PASS    |
| M5, dead KEY klongs         | 24          | 18          | 1.333 | 2     | 1.50   | PASS    |
| M11, resident objects       | 469         | 434         | 1.081 | 2     | 1.85   | PASS    |
| M11, live handles           | 469         | 434         | 1.081 | 2     | 1.85   | PASS    |
| ST6, table slots            | 226,400     | 60,272      | 3.756 | 2     | 0.53   | known   |
| heap after a GC, bytes      | 19,094,584  | 13,066,920  | 1.461 | 2     | 1.37   | PASS    |
| ST7, path arrays (printed)  | 665, 665    | 16, 16      |       |       |        |         |
| first cut in the drive      | 4,117       | 1,214       |       |       |        |         |
| lag, transactions           | 4,395       |             |       |       |        |         |

* **Back to empty holds, eventually, but for the tables.** After 40 R
  the database that held 1M keys keeps the stream, the index and the
  resident objects of a fresh hello-world database within 0 to 33 %;
  its heap is 6 MB larger (ST6's extra slots are about 0.7 MB of it;
  the rest is not broken down).
* **ST6, a finding, not fixed here**: the handle tables keep the size
  they reached with 1M keys, 226,400 slots, 3.76 times the twin's (its
  own tables grew to 60,272 in the drive). In references that is about
  0.9 MB with compressed pointers (my arithmetic). 024-05: "A shrink at
  a resize". The fix is a separate decision.
* **The lag, a finding**: the emptied database's first cut comes 2,903
  transactions after the twin's, and kept is within twice the twin's
  from transaction 4,395 (4.4 R). T1's fixed drive (4 R; 023-03, section
  2.3) would fail at 1M on `main` by a little. Whether the lag grows
  with n is not measured here (at 100,000 keys it was within 4 R).
* **ST7**: the writer's path arrays have 665 entries after the fill and
  the deletes, against 16; about 8 kB. Closed as negligible (above).


## 10. State

* **G4** (2026-11-12, 11:53 to 12:03): on the branch `024-30-g4` of
  the same clone, from `main` at `f64b33ca`, head `177178ce`, in
  Frans's name: G4 in `CountGates.java`, `count-gates.sh` (G4, the
  `--add-opens`), `night.sh`'s header. Gates on `177178ce`:
  `count-gates.sh` COUNT GATES OK (136 s, in a slot); `before-commit.sh`:
  BEFORE COMMIT OK (66 s, in a slot, 12:00 to 12:01). Not on `main`: the coordinator lands the branch. Open:
  ST6's fix and Q30-3, Q30-4 (section 7).
* **G1 to G3, done** (2026-11-12, 11:36 to 11:53): `CountGates.java`,
  `count-gates.sh` and the night step, committed on the branch
  `024-30-count-gates` of the clone
  `/Users/f/fl/bench/2026-11-12/gates/clone`, head `93da1e8f` (from
  `main` at `011aa9bf`), in Frans's name. Calibrated on `main` (section
  4, all pass), shown failing on release 2026.4 (section 5, G1 and G2
  fail). Gates on `93da1e8f`: `before-commit.sh` BEFORE COMMIT OK (65 s,
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

2026-11-13. Status set after the release (coord-1113).
