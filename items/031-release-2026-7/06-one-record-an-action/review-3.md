# 031-06. Review 3: the pace, the review's fixes, 028-67's start

2026-11-27, 22:20 to 23:15, by an agent of lead-1127 on Fable, the part on
028-67 with a second agent on Opus, in a clone outside the repository
(branch `031-06-review-3`). Reviewed, in the order of their weight:

1. **Step 3, the pace**, not on `main`: the branch `031-06-pace` at
   `f32fc321`, as `git diff 734f05a2 f32fc321` of `java/` (4 files, 551
   lines added): the charge after the batch, a commit's step sized by its
   allowance, the warm-up of a step's reads before the lock (`landing.md`,
   "Step 3").
2. **The fixes of `review-main.md` on `main`** (`97954827`): R1, and R2
   with R5.
3. **Step 4 on `main`** (`b0aac3a9`, `53ff486f`): 028-67's C1 and C3.

Against the principle of section 1 of the readme: every accepted action
appends one record, a function of the stream before it and the action;
nothing else is appended; a restart or a stop changes no byte; a crash
leaves a partial append only; a record always fits.

The probes are in `review-3-probes/`, their runs in
`review-3-probes/runs/`; `review-3-probes/run.sh` says how each was run.
On F53, functional runs only (counts and bytes), other work on the
machine; no time was measured.


## 1. Result

* **Step 4 has a fault that refuses a valid database (T1, high).** A
  start refuses the tail that the start before it made when it completed
  a record that a crash had cut in its header. On a file database: a
  crash that cuts the last append 1 to 4 bytes into a record, a start
  that recovers it, a stop with no commit in between, and every later
  start fails with a `BadTailException`. `b0aac3a9`'s parent, `b0cb561c`,
  starts all of these. Shown by four probes, each run on both.
* **Step 3: no probe changed a byte, and the reading found no record
  that depends on anything but the stream before it and the action.**
  The stream is the same without eviction, with a cache budget, with
  every object evicted after every record, without the warm-up, and with
  restarts, in steps of up to 128 KiB (section 3). Three findings of low
  weight: two of cost (W1, W2) and one of text (D1).
* **The fixes R1, R2 and R5: found right.** The two stated assumptions
  were looked at; neither failed in a run (section 4).


## 2. Findings, ranked

### T1. A start refuses a tail that recovery itself wrote (high; `main` since `b0aac3a9`; shown)

* **Where.** `RecoverableStream.walkTail`, the branch of a record that
  the end of the stream cuts (`RecoverableStream.java`, lines 308 to
  317), with `StoredTrans.RECORD_CHECK.tornHeaderFits` and
  `headerChecks` (`StoredTrans.java`, lines 163 to 172); the completion
  that it does not accept is `fixLastTransactionIfNeeded` and
  `transHeaderFixBytes` (lines 556 to 620, `TORN_HEADER_FILLER`, line
  88); `FileStream`'s tail of zeros (028-60, part 2; `ZERO_TAIL_MAX`).
* **The rule's gap.** Since 028-67 a record that the end cuts must have
  a header that checks (32 bytes or more of it in the stream) or that
  fits (fewer: a size the writer writes, and the format byte 9 if it is
  there). Recovery's own completion of a header cut at 1 to 31 bytes
  meets neither: a header cut at 1 to 4 bytes gets the filler, 4, at
  byte 4 and zeros after it; one cut at 5 to 31 bytes gets zeros in the
  rest of its 32 bytes, so its check does not hold. A completed record
  is whole, aborted, and the walk passes over it (its Javadoc). It is
  refused when the end of the stream cuts it again:
  * **(a) A file database, a stop and a start, no second crash.**
    `FileStream` leaves a run of zeros at the end of the last file out of
    the stream at every open (028-60), so the zeros of the completion
    are gone at the next start if nothing was appended after them: the
    record cut at 1 to 4 bytes is then 5 bytes with the format byte 4,
    and `tornHeaderFits` is false.
  * **(b) The same when the completion crossed a meta block**, for a
    header cut at up to 24 bytes: the fill wrote the block inside the
    record; the zeros after the block are left out, the record is cut
    after the block, and its 32 header bytes hold the fill's zeros.
  * **(c) A kill during the start's completion**, between its appends
    (the fix bytes, then the zeros 10 kB at a time), on any storage.
  * **(d) A run of zeros that begins inside the last record's header**
    (bytes 4 to 24) on a storage that keeps it, for `FileStream` a run of
    more than 8 MB; 027-11, section 1.3, and `FileStream`'s Javadoc say
    that such a run is recovered as a cut.
* **What happens.** `BadTailException`, "The record at P, of size N,
  which the end of the stream cuts, has a header that is not one of this
  database's records at its place", P the torn record, nothing written;
  the same at every later start. The data is there: the exception's way
  out, a cut at P, starts the database. In (a) and (b) the first start
  after the crash works, and a commit in that session hides the fault
  (the aborted record is then whole for good); a session that only
  reads, or a second kill before the first commit, does not.
* **Valid streams.** A crash may leave any prefix of an append (014-01;
  `AppendOnlyStream`, "CRASHES"; `FileStream`'s Javadoc for APFS), and
  recovery's own appends are a start's (the principle, rule 1).
* **Shown** (`run.sh OUT tail`, `runs/tail.txt`; "before" is the same
  probe on `b0cb561c`, `b0aac3a9`'s parent, built beside it):
  * `S4RestartAfterTornSizeProbe` (FileStream, the last record cut 1 to
    8 bytes in, three starts): cut at 1 to 4, start 1 ok and start 2
    refused; cut at 5 to 8, three starts ok. Before: all ok.
  * `S4TornSweepFileProbe` (FileStream, 1,016 prefixes of five records
    of about 90 kB, three starts each): 58 refused at start 2, the cuts 1
    to 4 bytes into a record and 1 to 24 bytes into the record whose
    fill crosses a block (at 180,696). Before: 1,016 ok.
  * `S4TornFillProbe` (MemoryStream; a kill during the completion, and
    runs of zeros from inside the header): 92 ok, 216 refused. Before:
    308 ok.
  * `S4TornFillFileProbe` (FileStream, a kill during the completion):
    85 ok, 24 not. Before: 109 ok.
* **Why the tests pass.** `DbTesterTail`'s torn headers are started once,
  on a MemoryStream; `P2CrashProbe`'s torn records are on a CutStream,
  which keeps the zeros, and are continued with commits; the kill tests'
  applications commit after every start.
* **A fix, for the decision of 028-67.** The walk accepts what recovery
  writes, where the end cuts a record: with fewer than 32 bytes, the
  format byte 9 or the filler followed by zeros only; with 32 or more
  that do not check, a header that fits up to a point and is zeros from
  there on. Other bytes of another file then pass only if they have that
  shape. Or recovery marks its completion so that a later walk knows it
  (a header that checks cannot be made from 1 to 4 bytes of the size).
  A test of each of (a) to (d), with two starts, on FileStream.
* **Beside it, not of this change:** on a file database every start
  after such a completion leaves the zeros out and appends them again
  (028-60), so a start that changes no byte still writes; the bytes are
  the same.

* **Fixed (2026-11-28)** in `b7f21db4`: zeros at the end of a cut record
  count as bytes not written; a cut record is taken if its header holds
  its check, or if its bytes up to the last non-zero byte are fewer
  than 32, begin a valid header and only zeros follow; recovery's
  completion writes only zeros after a cut size field (the filler at
  byte 4 gone, the smallest completed record 48 bytes). The four probes
  start every case; `DbTesterTail` restarts after a cut at each of a
  record's first 40 bytes, alone and over a meta block, and after a
  kill during the completion (028-67, Built).

### W1. The warm-up with several writers misses some steps (low; step 3; measured)

* **Where.** `Reclaim.warmup` (`Reclaim.java`, line 1402) reads the row
  and the stream's length that the last applied record published
  (`publishWarm`, line 1378). A writer that makes its warm-up while
  another holds the lock sees the state before that one's record: it
  warms the range that the lock's holder is copying, or none (the
  allowance one record earlier is at or under `MIN_STEP_SIZE` when the
  step is the first after it passes it), and its own plan then scans the
  next range under the lock.
* **Measured** (`MwWarmProbe`, `run.sh OUT mw`, `runs/mw.txt`:
  `WarmProbe`'s first case, 100,000 values of 200 bytes, a budget of
  5 MB, 20,000 commits, 1,156 steps; the steps whose scan loaded any
  version under the lock): without the warm-up 91.5 % in every run; with
  it, one writer 0; two and four writers 5.2 % and 6.7 %; two, four and
  eight writers that pause up to 200 us between commits, the lock held
  50 us longer, 5.6 %, 9.9 % and 7.7 % (1.2 to 2.8 versions a step,
  against 30 without the warm-up). The figures vary from run to run with
  the threads (0.1 % to 12 % seen). `WarmCostProbe` (`run.sh OUT cost`:
  every object evicted after every transaction, so that every read is a
  load; 10,000 commits, 880 steps): with one writer the run's loads go
  from 45,855 to 41,683 with the warm-up and no scan loads under the
  lock; with four writers, in two runs (the second is in `runs/mw.txt`),
  from 45,968 to 46,360 and from 45,888 to 53,705, with 4,427 and 10,052
  of the scans' 29,084 loads still under the lock.
* **What it means.** The warm-up's evidence (`WarmProbe`, `P1Probe`) has
  one writer. With more, a tenth to a third of the steps' reads stay
  under the lock, as before step 3, and the writers that wait make scans
  that no plan uses (up to 17 % more reads in all, when nothing is in
  memory). The stream does not depend on it. For the timing run (section
  5).

### W2. maintain() scans again at every handover (low; step 3; by reading)

* `Db.maintain` (`Db.java`, lines 912 to 915) calls `warmupStep(null)`
  after `giveWayToWriters()` and before the lock in every round of its
  loop, also the rounds that take the lock, find a commit waiting and go
  round again. Under commits without a pause the call so scans the next
  step's range, about 16 kB of KVs in memory, once for every round, for
  as long as it waits. A scan once after a round that made a part would
  do.
* `Reclaim.apply` makes a copy of the running row for the warm-up at
  every record while an iteration runs (`publishWarm`). Small; named for
  CORE in the timing run.

### D1. Section 3's arithmetic and three comments still say 16 kB (low; text)

* The readme's section 3 derives the record's bound at the release's
  limits from a step of "16,000 / 8" segments and one KV, 2,060: a dirty
  set of 350 MB at node size 8 by 024-17's count, and 86.9 % of
  2^31 - 9 for the record. A commit's step is now up to 128 KiB: 16,444
  segments by the same count, 2.79 GB at node size 8, over the limit by
  itself. So that derivation does not hold for a commit's step.
  `Reclaim.MAX_COMMIT_STEP_SIZE`'s Javadoc and the landing say that the
  record "stays within `recordCap()` as section 3 derives it": that holds
  for the record's own bytes (42.3 MB and 115 kB more), not for its dirty
  set.
* What bounds the set is step 2's check, not arithmetic:
  `Db.recordDirtyFits` before the go point (15/16 of the limit, by the
  cheap count of 3 nodes a level and segment, or the walk) and
  `checkTakeable` before the append. By that count a step of 16,444
  segments is 1.78 million nodes at a stream of 1 TB, within the 3.7
  million of node size 30: a step alone fits by the cheap count, and
  beside an action near its 7/8 the walk decides. No failure follows; the
  text should say which bound is derived.
* The same 16 kB: rule 5 of section 2 ("the scan's other KVs, 16 kB"),
  section 3's "the row and the table together are at most 240 kB" (now
  128 KiB, `STEP_FIXED_ROOM` / 2), and `StoredTrans.STEP_FIXED_ROOM`'s
  Javadoc ("the scan's KVs but the last (Reclaim.MAX_STEP_SIZE)").


## 3. Step 3: what was checked and found right

* **The charge is a function of the record's KVs and the state before
  it.** `Db.chargeStep` (`Db.java`, line 4349) counts nodes of the
  record's got-dirty list, which the stream stores and a start rebuilds;
  a node's size is 32 + 16 a klong (`StoredKeyNode.getByteSize`), with no
  pointer in it that a reader could have changed (Rule R); the walk
  follows the writer's objects of dirty nodes, which are not evicted. The
  first `touched` entries keep their places through `endOfTrans()`.
* **The patch reaches the record.** The row's and the table's bytes are
  the arrays that the value nodes hold; the charge is written before
  `store()` serializes and before the record's time can be read. The
  table holds the step's row (`planStep` puts it into the plan's rows),
  so `dueAt` finds one place in each. A row whose charge was never made
  is refused at a start (`deserialize`).
* **The step's size** (`Reclaim.commitStepSize`, line 744) is of L0 and
  a. a after a start is the running database's for a commit's record, a
  setter's, the settings' and a part's (`apply`, `initFromDb`). After a
  large commit the cap comes down over the next commits by half each
  (twice the fraction of a record that held the step before), a function
  of the stream too.
* **The warm-up decides nothing.** The plan's counts are by node id and
  by KV (`MaintenanceFollower.indexNodes`, `planStep`'s `size` and
  `readBytes`), whether the object was in memory or read; the value's
  position decides the copy, before the follow (`GetMany.valuesBefore`).
  The warm-up's read is a reader's, at the latest time; a cut that
  overtakes it ends it; an error of the storage in it fails the database
  as a read's does; while the database stops it can throw what the
  transaction's own warm-up throws. `StopWarmProbe` (`run.sh OUT stop`,
  `runs/stop.txt`): 300 stops under four writers with an iteration
  running, without and with the warm-up: `execute()` threw
  `DbStoppingException` 1,200 times in each (in one earlier run without
  the warm-up also 2 `StreamIoException`, "Stream being closed"), no
  other class with the warm-up.
* **A record fits.** A step's copies but the last are within 128 KiB by
  the scan's count (a KV counts 100 bytes besides its key and value, a
  value node has about 40), the last one value node, the row and the
  table the other half of `STEP_FIXED_ROOM` (assumed, as before); the
  index nodes by step 2's checks (D1). At lowered limits 015-50's rule
  holds the copies within `valueLimit()`.
* **Shown** (`EvictChargeProbe`, `run.sh OUT evict`, `runs/evict.txt`):
  one workload on one thread (commits of one large value, of 50 puts at
  cold keys, of 20 deletes; `maintain(300)` every 40 commits), run with
  no eviction, with a cache budget, with every object evicted after
  every transaction, and with the budget without the warm-up: the same
  stream (length, first position, SHA-256) in all four, in each of nine
  runs of six workloads at node sizes 8 and 30, with commits of 2 kB to
  1 MB and 883 to 5,377 steps a run; the largest steps hold 119,888
  bytes of copies of 1,000 bytes, about 850 copies of 30 to 40 bytes,
  and 602,472 bytes where the step's last copy is a value of 600 kB.
  Three workloads were run with and without a stop and a start every 53,
  97 or 211 commits: the same stream.
* Not run again here: the item's sweep, RestartInvariance, ConcProbe and
  FaultProbe on this tree (`landing.md`, "The determinism checks").


## 4. The fixes R1, R2 and R5: what was checked

* **R1.** `Db.executeLocked` sets the plan's fields of the Trans at every
  go point, whatever the plan, before `putKvs` (`Db.java`, lines 3073 to
  3087). Found right by reading.
* **R2.** `TransSeq.SetRoom` (line 463) is reduced by `take()` and then
  by `takeTo()`, each transaction counted as `checkTakeable` counts it;
  a transaction that does not fit is not taken, also after the deadline.
  Found right by reading; `RmRoomProbe`'s cases were not run again.
* **The liveness that R2 assumes** (a set near `takeRoom()` gets room in
  a later record): a record's room for a set is `takeRoom()` less its own
  got-dirty nodes. A probe of 20,000 actions (single puts, every tenth an
  empty commit, startup distance 2 MB, then `maintain()` calls; not
  kept) counted the sets, with the nodes that the take kept dirty: 1,990
  of 2,000 empty commits and 15,133 of 18,000 puts had an empty set, and
  no top node in most; M4's records had sets of 3 nodes and more. So a
  set of up to `takeRoom()` is taken by the next commit whose paths are
  dirty already, as most are. Under `maintain()` alone, by reading, a set
  within M4's own nodes of `takeRoom()` costs one record that takes
  nothing: its table's path is then dirty, and the next part's own set
  has few nodes or none. No hole found. In the runs of `review-main.md` after the fix the largest
  set was 65 % of `takeRoom()`.
* **That M4's table fits `TABLE_ROOM`** (256 KiB): not checked by the
  code, as its Javadoc says. A row holds its endKey and lastKey in
  decimal, up to 20 characters a segment; step 3 adds 18 bytes a row
  (the fixed width). A table passes 256 KiB only with rows whose keys
  are among the longest the Core accepts (O1), as before.


## 5. For the timing run

1. `probes/p1.sh` as the landing gives it: the time under the lock and
   of `execute()` for the commits with a step, the warm-up off and on
   (in the small run `execute()`'s median went from 0.119 to 0.369 ms
   with the warm-up's scan in it, the time under the lock's p99.9 from
   9.3 to 2.7 ms).
2. A commit that carries a step of 128 KiB of small values: commits of
   512 kB or more among small ones, cold values of 20 to 30 bytes, so
   that a record holds 900 to 1,200 copies (their touch, their puts and
   the charge's walk under the lock); the longest time under the lock
   against P1's 20 ms, and against `main` at `734f05a2` (16 kB).
3. CORE, with an iteration running: the warm-up's check and
   `publishWarm`'s copy at every record (W2).
4. Two to four writers on a database larger than its budget, the
   warm-up off and on: the time under the lock of the steps' records and
   the throughput (W1).
5. For step 4: the time of a start whose last record is large (100 MB
   and more); `walkTail` parses the stream's last record whole, and the
   start parses it again.


## 6. Not done

* No timing; no run of `before-commit.sh` or the level scripts (the
  landing has them on this tree).
* Step 4's other paths were read, not probed beyond the sweeps above:
  every record parse goes through `StoredTrans.Parser.parse` with the
  ID; the ID is the first block's, set before any record is read; a
  stream of meta version 155 is refused with nothing written (probed at
  eight lengths, `S4Version155Probe`); 5,835 prefixes of valid appends on
  a MemoryStream, with every byte around the meta blocks, start and
  restart with nothing written (`S4TornSweepProbe`; its 2 others are cuts
  inside the creation's records, the same before the change).
* 028-67's recorded finding (a record whose header is its own and whose
  later nodes are another file's) was not looked at again.
