015-09. Fix: Reclaim.Tester.testCrashBeforeIterationEnd depends on timing under load
====================================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For release 2026.2: the test is in `java/before-commit.sh`, the only
commit gate (Frans, 2026-11-03, 15:40), so a test that fails under load
blocks or confuses the commits.

What: `bergdb.core.Reclaim.Tester.testCrashBeforeIterationEnd` failed once
in a `before-commit.sh` of 005-80's clone on F53, under the load of other
agents' gates: "truncate to 241352, before the length at the last cut,
246952". It passed 5 of 5 alone, and 005-80's change does not touch it.
The physical cut waits for durability (005-72), so under load it can land
after the record the test truncates to.

Why: a gate's test must not depend on timing.

Done when: the test waits for the cut it depends on, or truncates
relative to the cut's position, so that it does not depend on when the
cut lands; it passes under load (for example, 20 runs beside a stress
run); `BEFORE COMMIT OK`.

First step: read the test against 005-72's account of the physical cut.

Found 2026-11-03 by F1 in 005-80's gate (016-05).

State
-----

2026-11-03, 19:45: done. A fault of the test, not of BergDB: under load
the buffer's clock flush could reach the stream before the cut in the
iteration's last transaction. The test now flushes only by its syncs.
Reviewed by the coordinator and committed after the combined gate.

Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:16 to 17:24, by F1 (016-05), in
`/Users/f/fl/bench/016/015-09/repo` from `main` at `f04cefe`:

* **Why it could fail.** After the transaction `t` that ends an
  iteration, the test truncates a copy of the stream at the table record
  that follows the iteration's last step (`crashPos`), as a crash between
  the two. `CutStream.truncate` refuses a length below the stream's length
  at its last physical cut (`lengthAtCut`): a cut is made only after the
  bytes before it are durable (005-72; `Reclaim.cutIfDurable`), so a crash
  cannot lose them. The cut that `Reclaim` decided earlier is made in
  `t`'s own `transactionCompleted` (`cutIfDurable`, after the steps), and
  `CutStream` records the length that the main stream's `BufferedStream`
  has flushed by then. With the tests' buffer time of 10 ms
  (`DbBuilder.testSetup`), the buffer's consumer can flush `t`'s records,
  the last step and the table, before that cut, when the writer is
  descheduled in between under load: the cut then records a length past
  `crashPos` (246,952 against 241,352 in 005-80's gate), and the truncate
  is refused. Alone, the flush comes after the cut: the writer runs the
  whole transaction in well under 10 ms.
* **The fix** (test code only, `Reclaim.Tester`): the test starts its
  databases with `startForCrashTest`, as `startForCutTest` but with a
  buffer time of 60 s, so that the buffer is flushed only by a sync (or
  when full, 100 kB, which one transaction's records do not reach), and
  it syncs (`SyncLevel.ORDINARY`) after each transaction. Durability, and
  so the cuts (`cutIfDurable`), follow the transactions, not the clock: a
  cut made in `t`'s transaction records at most the length synced before
  `t`, so `lengthAtCut <= crashPos`. The test's Javadoc says so. The other
  users of `startForCutTest` do not truncate, and are unchanged. The test
  takes about 0.5 s instead of 0.25 (2,500 syncs).
* **The check**: 20 runs of the test beside two full `bergdb.dev.Unit`
  runs on F53 (load 22 to 33), 17:22:14 to 17:22:49: 20 passed, 0 failed
  (`/Users/f/fl/bench/016/015-09/load20.sh`, outputs in
  `/Users/f/fl/bench/016/015-09/load-fixed/`).

Result of the runs on `main`'s jar (17:27:17 to 17:27:52, load about 22 to 30): 20 passed, 0 failed of 20; the old test did not fail here, so the failure stays shown only by 005-80's gate of 16:13 (its log: `/Users/f/fl/bench/016/005-80/unit-1.txt`).

2026-11-03, 19:45, by the coordinator (016-05, H5): reviewed, no faults.
The change is the test's only (`Reclaim.Tester`); with a buffer time of
60 s and a sync after each transaction, a cut made in a transaction
records at most the length synced before it, so it cannot pass the
crash position. Gated with 015-16 on `main` at `b9ba427` (the gate line
in the commit).
