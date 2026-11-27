# 031-06. An independent review of the prototype

2026-11-27, 13:10 to 14:30, by a review agent of lead-1127 (model
Fable), on a clone of `031-06` at `fa11d15f`, on F53; no other review was
seen. A statement is **ran** (the built jar), **read** (the code) or
**inferred**. The probes: `review-probes/` (`run.sh`, `runs.txt`).

## 1. Verdict

No probe broke the prototype: no live value lost, no acknowledged commit
missing, no refused commit in the stream, no reader with a wrong state,
no start that differs from the running database. The findings are of
cost, margin and scope: the abstract model's checks do not run on mixed
records (F1); reclaim writes 29 to 40 % of the growth where its fraction
says 25 % (F2); sustained large commits keep 36 times the live data
(F3); the scan before the go point hides a commit for up to 9 ms in
memory (F4); a mixed record's limit rests on arithmetic that no check
enforces, and an input the Core accepts passes it (F5, F6).

(e) is the one for `main`, after the fixes of section 6: only it meets
the principle, its new mechanisms hold no state between records, and the
Lean change for the cut's safety is one conjunct. As built it is not
ready: F1 leaves `level2.sh`, `level3.sh` and `night.sh` red.

## 2. Findings

**F1. The model's checks do not run on a record that carries a step**
((e) only; ran: `level3.sh`, `level2.sh quick`).
* Where: `java/stress/TraceExport.java`, C-STEP (`lean/TraceCheck.lean`),
  the tree model's C-T5 and C-T9, `StepTx` (`Contract/ReclaimSteps.lean`).
* Case: `level3.sh` stops at "C-STEP's fault test" (16 cases wrong,
  "TRACECHECK FAILED: exporter"), the first check of its step 8: the rest
  of that conformance (the cuts, the reads after a cut) has never run on
  the prototype. `level2.sh quick` stops at the tree model's reclaim set:
  C-T5 (touch) 92 failures, C-T9 (run) 150; C-T1 to C-T4, C-T6, C-T8: 0.
* Consequence: the writer's nodes agree with the model, but the abstract
  model does not check a transaction that carries copies: reclaim's part.

**F2. Reclaim writes more than its fraction** (both; ran, `RvPace`).
* Where: `Reclaim.RecordPlan.finish`: the row is charged with the
  touch's bytes only (028-26's after-row charge is not made).
* Case: 20,000 cold keys, commits of one hot key, no `maintain()`;
  reclaim's bytes are the growth less that of the same run with
  `DbBuilder.maintenanceNone()`. Its share of the growth and the write
  amplification: 0.305, 1.44 (200-byte values); 0.301, 1.43 (node size
  8); 0.397, 1.66 (10 bytes, node size 8); 0.291, 1.41 (7-segment keys).
* Consequence: the fraction 0.25 means 1.33. 031-05's jar in D2 wrote
  within 1.5 % of the same bytes. (c) can make the exact charge only with
  028-26's second row record, a crash window; (e) by an estimate (Q2).
* Built (2026-11-27): the landing's step 3, the fixed-width patch
  (Frans, 14:00 to 14:09): the row's `rewritten` at 19 digits, written
  after the batch with the index nodes that the record makes dirty on the
  step's paths (`Db.chargeStep`, `RecordPlan.charge`). A pass of parts
  leaves 0.0 % uncharged (25.7 and 39.5 % before); in `RvPace`'s cases
  the share is 0.281, 0.264, 0.283 and 0.275 (`landing.md`, step 3).

**F3. Large commits: 16 kB of reclaim a commit, and the stated bound of
the stream kept does not hold** (both, `main` too; ran, `RvPace`).
* Where: `Reclaim.planCommit` (one step a record); `SafetyProbe.bound`.
* Case: 4,000 cold keys of 1,000 bytes (live 4.2 MB), a commit every
  200 ms of database time, retain duration 1 s. Commits of 20 kB: share
  0.257, the stream kept 7.7 x live; 100 kB: 0.171, 13.8 x live, 75.7 %
  of the bound as `SafetyProbe.bound` computes it with CAP 2.2 MB (a
  1 MB record limit); 300 kB: 0.063, 36.4 x live, 188.0 %. Steady from
  third to third; 35.8 x live on 031-05's jar in D2.
* Consequence: the stream kept is about 2 x (live / 16 kB) x the commit's
  size, not 8 x live. The item's runs stay under the bound because 6 %
  of their actions are large, and by its 2 x CAP, 4.3 GB at the
  release's limits. The step's room is its own now (rule 5), so (e) can
  size a commit's step by its allowance; F4 is the price.
* Built (2026-11-27): the landing's step 3 (028-71): a commit's step scans
  up to its allowance, at most the larger of 16 kB and twice the
  allowance that the application's last record added
  (`Reclaim.commitStepSize`). Commits of 20, 100 and 300 kB: the stream
  kept 8.1, 7.2 and 7.8 x live, the share 0.248, 0.279 and 0.237
  (`landing.md`, step 3).

**F4. P1: a commit is not readable while its plan scans** ((e) only;
ran, `RvP1`; figures, in memory).
* Where: `Db.executeLocked` (plan, then `transactionEnd`); `planStep`.
* Case: 60,000 cold keys of 1,000 bytes, then 600,000 new keys put ahead
  of a running iteration's scan (stored after pStart: walked, not counted
  toward the 16 kB, so the scan ends at the step reserve). Of 3,395
  commits with a step the plan took 0.01 ms at the median, 0.05 ms at
  p99, at most 4.8 to 6.4 ms in three runs (8.0 and 8.6 ms with a cache
  of 30 MB); one scan met 36,902 KVs. A copy of a 1 MB value: about 1 ms.
* Consequence: the worst scan follows the step reserve's 2,759 index
  nodes at node size 30 (9,039 at 8) before the go point, each maybe a
  read of the storage on a database larger than memory (inferred). (c)
  and `main` hold the write lock as long, but the commit is readable
  first. The warm-up is not built.
* Built (2026-11-27): the landing's step 3: the warm-up of a step's reads
  before the write lock (`Maintenance.warmup`, `Reclaim.warmup`), for a
  commit and a part. On databases larger than their cache budget the
  records that carry a step read 0 to 0.01 versions a step from the
  stream under the lock, against 15 to 32 without it, with the same
  stream; P1 on a database larger than its cache budget is a probe for
  the lead's timing run (`probes/P1Probe.java`, `p1.sh`; `landing.md`,
  step 3).

**F5. The admission of dirty nodes does not count the step's** ((e)
only; read, inferred).
* Where: `Db.checkDirtyNodes` (the user's KVs against
  `StoredTrans.dirtyLimit()`, 15/16 of the record limit, as before);
  `TransSeq.take` (`if (bytes + cost > maxBytes) break`: a transaction's
  dirty set is taken whole or not at all).
* Case: at the release's limits the check admits 2.013 GB; with the
  step's 0.35 GB the record's transaction may reach 2.36 GB, and a later
  record takes at most 2.147 GB less its own bytes. Only 024-17's count
  keeps it away (1.47 GB within L1 to L5; TP26, not proved): 1.82 GB
  against 2.105 GB, a margin of 16 %; `main` has about 43 %, and a
  refusal past 2.013 GB.
* Consequence: past the margin nothing fails: the take stops at that
  transaction for good, the startup pos stands, no cut is decided again.
  Ran with the limit lowered under a dirty set already in the stream
  (`RvLong -Dlimit=100000`): the startup pos stayed at 512 through 400
  commits, no cut, a stream of 31.9 MB against 7.2 MB, no exception.

**F6 to F9.**
* **F6** ((e) only; ran, `RvLong`): a key of 6,000 segments (42 kB) under
  BergDB's prefix "/#" was accepted through the Core API
  (`Trans.Builder.putLongKey`; `Db.checkLimits` lets `Kv.longKey` pass L2,
  up to L3) and copied by a commit's step, whose record made 6,009 index
  nodes dirty. The item assumes at most 60 segments for the step's last
  key, which only the Pub layer's L6 gives. By the item's count (882
  nodes a segment at node size 8) such a key alone is about 1 GB, and
  section 3's 1.87 GB does not stand; `main`'s step, a record of its
  own, stays within the limit by the same count.
* **F7** (both, `main` too; ran, `RvP1`): the step reserve, a builder's
  setting (`DbBuilder.reclaimStepReserve`), changes the bytes at its
  default: in F4's case 4 MiB split 16 steps and 1 MiB split 65; the same
  actions gave streams of 328,668,424 and 265,554,968 bytes.
* **F8** (both; read): the principle holds for the Core only:
  `IndexManager.start` begins cleanup and build threads that commit by
  themselves (031-05's N9; not among the item's questions).
* **F9** ((e) only; read): `Db.getTrans` gives a user's record with other
  keys' copies and reclaim's row and table; `transactionInfo` omits them.

## 3. What held

* **A copy dropped at a key the action writes** (ran, `RvFront`): actions
  aimed at the keys after the iteration's lastKey, in records that may
  carry a step: a put of the same bytes, a value transformation that returns
  the previous array or deletes, a delete, a key transformation onto the
  key, a Trans executed again; eviction; values of up to 3 MB. Eleven
  runs, 52,000 actions, 2,268 copies dropped, 999 cuts, 2,073 restarts,
  27.5 million historical reads: the model's.
* **`stop()` and `close()` from another thread** (ran, `RvStop`): 300
  rounds; 233,793 commits returned and are in the stream, 528 threw and
  are not, among 184,718 parts' records; a start changed no length.
* **Readers** (ran, `RvRead`; writers, `maintain()`, cuts, eviction):
  523,026 scans with the invariant sum, 173,053 at earlier times; 235,714
  walks from a value to its writing record through 1,552,670 copies.
* **Read:** `Reclaim.plan` works on `row.copy()` and changes no memory of
  reclaim's. The startup pos is the position of the last record taken
  (`TransSeq.take`: `newSp = first.tpos`), below L0: a row made done at
  L0 is not marked in its own record, nor a row marked at L0 cut in it;
  the conditions are `main`'s one record later, never earlier.
  `KeyModSet.forgetUpTo(tEnd)` answers "modified" for a read before tEnd.
  The Core appends in `Db.store` (once in `executeLocked`), the
  primordial record, the meta blocks and recovery's fill only.
* **Reproduced** (ran): `before-commit.sh`: OK (62 s); `sweep.sh`: 27,720
  interruptions, 0 different, the memory other at 0, 16,634 records, 567
  torn, the item's digests; `sweep2.sh`, 26 of its 36 runs: 36,675, 0
  different; `faults.sh`: the item's output line for line; `conc.sh`: ten
  replays, the same stream; `SafetyProbe`: configuration 1 as the item's,
  seven runs with other seeds OK; `UndercountProbe 30000`,
  `CommitTimeProbe`: the item's (`runs/undercount.txt` begins with a
  stray exception); `level4.sh quick`, `apps.sh quick`: OK.
* **Not in the item** (ran): `level3.sh` in full, steps 1 to 7 OK (the
  LoadTest with reclaim, a restart at every cut, among them); `night.sh
  tests`: 26 tests; `transcheck.sh`, `core-build.sh unit f` and
  `kill-restart.sh 150` (kills of the Pub layer on files): OK.

## 4. (e) against (c)

* **Both:** F2, F3, F7, F8. **Only (e):** F1, F4, F5, F6, F9; the copy
  mark (a format change); a record up to 8.4 MB larger than its action.
* **Only (c):** a start that appends (it can fail, its append can tear,
  a tool that opens a stream changes it); after a crash between a
  commit's record and each of its up to three records of maintenance, a
  stream that no uninterrupted run has, until a start completes it; the
  clock held for readers during every call that writes; the trigger.
* **Mechanisms.** (e) adds seven: plan and apply on copies of the rows;
  the merge, with the drop at the action's keys; the copy mark; the
  record cap with the step's room; the witness of reclaim's own record;
  a part as an action through the commit's path; the refusal by a stop
  during the plan. It removes four of `main`'s: reclaim's transactions
  inside a commit's go point, the second row record, the done table's
  record, the need for the kept times. (c) adds six (the catch-up from
  the stream, the trigger, the predicates of what would be written, the
  maintenance times, the hold, the start that writes), removes two. All
  of (e)'s live within one record; (c)'s trigger, hold and start's write
  are state between records. (e) is simpler, safer at crashes and
  starts, less safe in its margins (F4 to F6) until they are fixed.
* **For `main`: (e).** (c) cannot meet "a start appends nothing", and
  what it keeps (the trace format, `StepTx`) is cheap to restate. If (c)
  is taken, first: the start's write decided from the stream alone and
  safe when torn, and the hold shown free of failures by an argument.

## 5. The proof, and what was not checked

* **(e), the cut's safety.** `iterationOK_of_stepsOK` already takes a
  step as the transaction after the state its scan read, and `WrittenIn`
  counts any operation at a key. `StepTx`'s first conjunct becomes "every
  old KV met is written by the record" (`kv.1 ∈ ops.map Op.key`: a copy,
  or the action's put or delete); `step_covers` uses it in one place.
  `reclaim_java_reads_steps`, `pe_reclaim_reads_steps`: unchanged. Small.
* **(e), the users' values** (`ReclaimValues.lean`): `maintenance` goes
  from a transaction to an operation (the copy mark, the reserved keys);
  `StepOpOK` gains the action's operations; `StepTx.no_delete` goes;
  `StepTx.preserves_users` becomes "the record's effect on user keys is
  its action's", by `applyOps_existing`. A few hundred lines; with the
  trace format, `TraceExport`, C-STEP with its fault test (the unmarked
  operations compared with the action as submitted), C-T5, C-T9: days.
* **(e), the principle.** New: the record as a function `rec(S, a)`, and
  the theorem that the run of `rec(S_k, a_k)` with a restart anywhere is
  the run without: `T12_restartCut` and `T3_take_restarts`, with one
  hypothesis in the style of `PolicyCutOK`: `rec` reads only what they
  preserve; `apply` against a start stays tested (`P2CrashProbe`).
* **(c):** `StepTx`, the trace and the checkers stay. The principle needs
  a run whose restart writes (`runRestartsCut`'s does not), the proof
  that a start writes what the interrupted call would have, once, and
  maintenance times from the stream: more theory, a weaker statement.
* **Not checked:** storage that is cold or larger than memory (F4); a
  record near the release's limits (F5); `week.sh`, `timing.sh`,
  `night.sh` whole, the count gates; 024-17's count; the Lean statements
  (read, none written or built); (c) itself: 031-05's jar in D2 stood for
  it, in F2 and F3 only.

## 6. The first three things to fix

1. **The conformance** (F1): the trace format with the copy mark,
   `TraceExport`, C-STEP, C-T5, C-T9, `StepTx`; the level scripts whole.
2. **The record's room by a check** (F5, F6, F7): the admission counts
   the step's nodes, or the transaction's limits leave the room (Q3 (b));
   the Core bounds its own long keys; the step reserve a constant.
3. **The pace** (F2, F3, F4): the charge (Q2) and a commit's step sized
   by its allowance, with the warm-up before the lock and P1 measured on
   a database larger than memory.
