# 031-04, Q9 (b): the handoff of the write lock

2026-11-26, by an agent of lead-1126, on the branch `031-04` of the clone c314. Frans
chose option (b) of Q9 on 2026-11-26 (031-04, section 9): a handoff. This file holds its
prototype, its measurements, and the fix of Codex's finding 1 (review of 031-04,
2026-11-26), which came with it.


## 1. What was built

* **The count.** `Db` already had `writersWaiting`, an `AtomicInteger` of item 009, step
  3d, which the eviction thread gives way to. The handoff uses it, and no second count:
  a writer adds 1 before `synchronized (writeLock)` and takes 1 away as the first thing
  under it.
* **The paths that count.** Every commit that a user's call makes:
  * `Db.executeInner`, and so `Db.execute`: the Core API's transactions, the Pub layer's
    (`WTransaction`, `RwTransaction`, the index jobs), and the internal transactions that
    run inside another writer's lock. These add 1 while their thread holds the lock and
    take it away at once, as the monitor is reentrant.
  * `setStartupDistance`, `setRetainDuration` and `setReclaimInternalFraction`, which
    take the lock themselves and commit inside it: added by this change.
  * Not counted: the getters that take the lock (`getStreamLength`, `getTransactionCount`
    and others), `start`, `close`, `sync`'s lock, `checkNodes`, the eviction thread, and
    `maintain(int)` itself, which is the one that gives way.
* **The wait.** `Db.maintain(int)`, before each part and before the cut after a sync
  outside the lock, calls `giveWayToWriters()`: while the count is above 0, 100 spins of
  `Thread.onSpinWait()`, then parks of 20 µs. It waits without the lock: the count falls
  as each waiting writer gets the lock.
* **The recheck at the part's boundary.** Under the lock, before the part, the call looks
  at the count again. A writer that came between the wait and the lock makes the call let
  the lock go and wait again, with nothing done. A writer that comes after the recheck
  waits for that one part: the bound.
* **What the handoff bounds.** The call's share of a commit's wait: at most one part.
  Not GC pauses, the storage, the commits before it, the commit's own maintenance, or a
  part that is long by itself.
* **Codex's points** (review of 031-04, section 5):
  * acquisition races: the recheck under the lock, above;
  * internal reentrant `execute` calls: they add and take away 1 under the lock they
    hold. The calling thread never waits while it holds the lock: a `maintain(int)` from
    a thread that holds the lock already (none in BergDB) does not give way, since its
    writers could not get the lock;
  * exceptions: nothing runs between the add and the `synchronized`, and the decrement is
    the first statement under the lock, before the state check, so a writer that fails
    there has already taken its 1 away;
  * stops: a stop or close takes the lock; the writers that wait get it after it, take
    their 1 away and fail on the state; the call's wait then ends, and its own state
    check under the lock refuses the part;
  * several threads calling maintain(int) at once: none counts, each gives way to the
    writers, and they share the lock between them as before (the monitor's order).
  * A cost: under commits that never pause, a call waits as long as they come. Its
    Javadoc says so.
* **The test.** `ReclaimMaintainTester.testCommitGoesBeforeTheNextPart`: the test holds
  the lock, starts a commit, waits until it counts, starts two calls of
  `maintain(100000)`, waits until both are parked in the handoff, and lets the lock go.
  The first record after that is the commit's, the calls then write, and the count is 0
  at the end. It passed 5 runs of 5, and in the gate.
* **The Javadoc** of `Db.maintain(int)` says the call hands the lock over, and that a
  commit that comes during a part waits for that part only, of the call's work.

The code: `prototype.diff` (the branch's `java/` against `main` at `9e72d0d5`).


## 2. Measurements

* **The setup**, as in 031-04, section 6.5: `PassProbe 10000000 100 B 50000000 1 CALLS`,
  10 million keys of 100 bytes, all live (1.63 GB kept), then calls of `maintain(B)`, a
  call a millisecond of the test clock, while a thread commits a put of 10 bytes every
  millisecond of wall time. `-Xmx12g`, JDK 27, `-Xlog:gc*` with the JVM's uptime.
  * CALLS bounds a run to about one pass: 4,000 calls at a budget of 1,000 (the pass is
    done after 2,937 to 2,939, its cut 1,001 calls later), 400 at 10,000 (the pass is not
    done), 40 at 100,000 (not done).
  * "Before" is the prototype at `cc02ccff`, without (b) and without the fix of section 3;
    "after" is `15e791f6`. The fix does not touch this case: the stream is the
    prototype's from its start.
  * One run at a time, 10:51 to 11:23. F53 ran `week.sh`: the 1-minute load was 9.5 to
    20.3 during the runs; each figure below has its run's load, at the calls' start and
    end. The figures are indicative.
* **The longest commit**, in ms, of each run:

  | budget | before, G1 | before, ZGC | after, G1 | after, ZGC |
  |--------|------------|-------------|-----------|------------|
  | 1,000   | 148             | 182, 187, 192   | 281, 66, 82   | 101, 47, 131 |
  | 10,000  | 255             | 511, 584, 382   | 99, 130, 119  | 29, 45, 49   |
  | 100,000 | 590, 908, 1,281 | 893, 894, 1,112 | 102, 103, 120 | 66, 36, 43   |

  * "before, G1" at 100,000 is 031-04's section 6.5 (three runs, the same setup without
    CALLS); at 1,000 and 10,000 one run each here.
  * The loads, in the order of the runs above:
    * before, G1: 11.3-10.7; 10.3-10.4.
    * before, ZGC: 14.3-13.1, 13.1-14.9, 9.5-10.9; 13.2-13.3, 13.2-13.2, 11.0-10.6;
      12.1-17.4, 12.1-11.1, 10.1-11.6.
    * after, G1: 14.7-15.0, 18.3-17.1, 10.7-11.5; 13.2-13.4, 14.3-12.4, 10.7-10.7;
      12.7-14.5, 12.1-12.2, 10.7-10.6.
    * after, ZGC: 16.0-15.4, 16.7-13.5, 11.1-10.1; 12.4-13.0, 11.9-12.8, 10.3-11.2;
      13.5-12.4, 11.8-12.3, 10.5-10.2.
* **The longest GC pause** (`Pause` lines of `-Xlog:gc*`, during the calls):
  * G1, after: 279, 204, 185 ms at 1,000; 213, 170, 248 at 10,000; 287, 172, 182 at
    100,000. Before: 131 at 1,000 and 182 at 10,000; at 100,000 (section 6.5) 250, 250
    and 608.
  * ZGC: at most 0.3 ms in every run, before and after; no allocation stall.
* **The commits alone**, the same database and committer with a sleep of 1 ms in place of
  each call (`-Dnocalls=true`, 40,000 sleeps, made for this file): the longest commit
  8.9 and 4.4 ms with ZGC (load 10.6-9.9, 8.2-6.9), 4.1 and 32.6 ms with G1 (load
  10.0-7.6, 6.9-13.3). This is the commit's own work, its maintenance included, on the
  loaded machine.
* **Where the longest commit came, at a budget of 1,000** (PassProbe now prints the call
  it came in; two more runs each with ZGC):
  * after: 34.2 ms in the call that made the cut (load 16.4-19.8), and 45.5 ms in a call
    between the pass's end and its cut (15.6-11.8);
  * before: 124.0 ms in the call after the cut (20.3-16.3), and 272.8 ms in call 590,
    during the pass (11.2-9.6).
* **What the figures say:**
  * **The lock, not GC, made the long waits.** With ZGC, whose pauses stay under 1 ms,
    the commit waited up to 273 (of five runs, the two of the next point included), 584
    and 1,112 ms before (b), at 1,000, 10,000 and 100,000; after (b) up to 131 (of five),
    49 and 66 ms. Before, the wait grew with the budget:
    the call kept the lock for several parts. After, it does not.
  * **After (b) with G1**, the longest commit (66 to 281 ms) is at or below the longest
    G1 pause of its run (170 to 287 ms): G1's pauses decide it, as section 6.5's yield
    experiment found (259 ms).
  * **What is left with ZGC after (b)**, 29 to 131 ms against 4 to 9 ms for the commits
    alone: a part's length (one step, a take, a filler, or the cut with the dead hand's
    batch; the calls of 1,000 units last up to 235 ms, with several parts each) and the
    load of 10 to 20 on 10 cores. At 1,000 one of the two longest came with the cut,
    which the runs at 10,000 and 100,000 do not reach. Not examined further.
  * **The call's own length** after (b), with ZGC: the longest call 137 to 235 ms at
    1,000 (five runs), 330 to 406 at 10,000, 2,005 to 2,896 at 100,000 (before: 116 to 130 in five runs,
    293 to 385, 1,822 to 1,968). A call gives the lock away, so it lasts longer while commits
    come, as expected.
* **Not run:** `timing.sh`'s pause probe, and a quiet machine.


## 3. Codex's finding 1: the current row's a after a one-way upgrade

* **The finding.** A table without `a`, from `main` or 2026.6, with this design's current
  row after it: `Reclaim.initFromDb` took the current row's `a` only when the table had
  one, and otherwise the position of the last record, also when that record is
  reclaim's. A restart between two completed calls then changed the stream (P2).
* **The fix**, as Codex's throwaway change: the current row's `a`, when present, counts
  whether or not the table has one (`storedA = max(storedA, c.a)`, with `storedA` at
  `Long.MIN_VALUE` when the table has none).
* **Codex's case**, `UpgradeRestartProbe` (now in `probes/`) on its streams of
  `UpgradeProbe write F 314 250 10000`, written with `main`'s jar and with 2026.6's:
  * before the fix (Codex's logs): after the first call the restarted copy read
    a = 1,502,216, the other 1,474,616; after the second call the two streams had the
    same length, 1,579,912, and other bytes;
  * after it: 30 calls of `maintain(100)`, with a restart of one copy after each, give the
    same a (1,474,616) and the same bytes, ending at 1,692,096, for both streams.
* **The broader probe**, `UpgradeProbe open F 2718 250` on the same streams (250 random
  operations, a start from the stream cut after each record):
  * before the fix (Codex's logs): 21 starts with another a in 452;
  * after it: 0 in 452 for each stream (1 skipped); the stream kept goes to 837,288 bytes
    idle and 47,448 emptied, as in Codex's runs.
* **Not fixed here:** Codex's finding 2, the converse mixture (a table of this design and
  a current row of an older writer, after a writable downgrade). It is a question of Q8.


## 4. Gate

* `java/before-commit.sh` on `15e791f6`: `BEFORE COMMIT OK (126 s)` (10:49, load 12 to 15). The
  probes are not in the gate.


## 5. State

2026-11-26, 11:30, by an agent of lead-1126.

* **Done:** (b) in the prototype (`15e791f6`, `prototype.diff`), with its test; the
  measurements of section 2; the fix of Codex's finding 1 with Codex's two probes run
  again (section 3).
* **Not done:** `timing.sh`'s pause probe; a run on a quiet machine; 031-04's readme
  (section 9, Q9, and section 4.5) is not updated here: it says what was measured before
  (b).
