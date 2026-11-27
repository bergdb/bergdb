# 031-06. Landing notes: steps 0 and 1

2026-11-27, on the branch `031-06-landing` of a clone of `main` (outside the
repository), from `05c002ad`. Notes of the landing's work for the lead, who
lands the item's text; this file does not replace the item's `readme.md`.

## Step 0: the port

* **What came:** the prototype's `java/` as one change: the diff from the
  merge base of `031-06` and `main`, `9e72d0d5` (main of 2026-11-26), to
  `fa11d15f`, which carries 031-04's `maintain(int budget)` and the witness
  a, 031-05's maintenance decided from the stream, and 031-06's one record
  an action with the copy mark. The prototype changed nothing in `lean/` or
  the scripts. Applied with a three-way merge on `main` at `05c002ad`.
* **Conflicts with today's `main`:** one, the Javadoc of
  `Database.maintain(int)`, where 028-62 had corrected `maintain()`'s
  400 kB to the stream's; the prototype's text is taken, which describes
  the pass by parts. 028-69 (the crypto code removed) and 028-60's part 2
  (the tail of zeros) touched none of the prototype's lines; the build and
  the tests found no other conflict.
* **Prototype-only code removed:**
  * `Db.maintain(int budget, int maxParts)`, which the probes called by
    reflection: now the test hook `Db.TestHooks.maintainMaxParts()`, read
    once at a call's start (default: no limit). The probes `P2CrashProbe`,
    `FaultProbe` and `ConcProbe` need a small change for it (a field
    `maxParts` and the hook in place of the reflective call). The item's
    `probes/` land with the item, not in this branch; the change that the
    gate below ran is the appendix's diff.
  * `DbBuilder.maintenanceNone()` is package-private: for the Core's tests
    and probes, not in the API.
  * Two comments that named "031-05's prototype" name 031-05 and 031-06.
  * No system property of the prototype was left in `java/src`
    (`proto315.*` went with 031-05's D1/D2 switch in 031-06's prototype).
  * Kept: the hooks `TestHooks.beforePlan` and `beforeApply` (the probes use
    them; `TraceExport` uses `beforeApply` since step 1), and
    `Reclaim.rowsForProbe()` (the unit tests use it).
* **Gates:** `BEFORE COMMIT OK (63 s)`. `P2CrashProbe` with the item's
  `sweep.sh` (its 23 configurations) on the ported jar: 27,720
  interruptions, 27,720 the same, 0 different, the start's memory the
  running database's at every one; 567 torn records continued the same; the
  23 reference streams have the digests of the item's `runs/sweep.txt`, one
  for one. With the same adapted probes on the jar of step 1: `faults.sh`
  (`FaultProbe`, six seeds, faults at four points), the item's
  `runs/faults.txt` line for line, its six reference digests the same, bad
  0; `conc.sh` (`ConcProbe`, threads, then a one-thread replay whose parts
  are `maintain(B)` calls with `maintainMaxParts()` 1): ten runs, the replay
  gave the same stream in all ten.

## Step 1: the conformance (review, F1)

The checks of a record that carries a step, as they are now. A mixed record:
a commit's record (or a part's) that holds its action's operations, a step's
copies, reclaim's row and maybe its table, one operation a key.

* **The trace format** (027-02, updated with the code): a copy is an `OP C
  key v` line, a put whose value node has the copy mark; the exporter reads
  the mark from the record's bytes (`StoredValueNode.isCopy`) and fails the
  trace (an `ERROR` line) unless the marked keys are the plan's copies
  (`Maintenance.Plan.copyKeys`). With `steps=1` every record has its action
  as submitted, `ACT P key v` and `ACT D key` lines, after its OP lines: a
  user transaction's as the exporter's workload built it, before Db sees it;
  BergDB's own actions (a setter's, the creating start's) from the Trans that
  Db executed; none for a part. `OP C` is in the grammar of the contract's
  checkers; `ACT` is not (as `STEP`, only in `steps=1` traces, which those
  checkers do not read). The comment line of a TX gives `kind=step|user|part|
  table` and `copies=N`. The trace's version stays 3.
* **TraceExport:** the OP C and ACT lines; the STEP line made in the step's
  own record, with lastKey before the step from the row before the record
  (`Db.TestHooks.beforeApply`, the hook kept from the prototype) and L' and
  eod from the plan's row (`Reclaim.RecordPlan.next`, `eod`), checked
  against the row after the record; `crash=K` after the K-th step's record
  of any kind (commit or part), and no deferred STEP line after a crash.
  `tracecheck` filters the ACT lines before its pinned parser
  (lean/Check/Trace.lean), as it does RESTART and RESUME.
* **C-STEP** (lean/Check/Steps.lean, `reclaimStepFailures`), per STEP line,
  at the state before the record (after T(i - 1), which the scan reads):
  STEP-chain, STEP-c and STEP-range as before; STEP-puts: every old KV of
  the range up to L' is written by the record, by a copy, or by an operation
  of the action at its key (a put or a delete), or by reclaim's row or table
  there; STEP-values: every copy writes the value the scan read; STEP-ops:
  one operation a key, the row put (not as a copy), every copy of an old KV
  met. **STEP-action** (new, `actionFailures`), for every record of the
  trace, against its ACT lines: the operations that are not copies are the
  action's, each operation of the action among them as submitted (a put with
  its value, a delete as `OP D` or `OP N`), and every other one is a put at
  a key of reclaim's reserved prefix `/#i/dreclaim/` (`reclaimReserved`, the
  contract's `reclaimKey`); no copy at a key the action writes; copies only
  in a record with a TOUCH line. So on a mixed record C-STEP verifies that
  the record's effect outside reclaim's keys is its action's, as submitted,
  plus copies that put back the values the scan read, and that every old KV
  met is written.
* **C-STEP's fault test** (lean/test-traces/step-faults.sh): the 18 faults
  of before, adapted (the copies are OP C lines; `del` and `put` now fail by
  STEP-action, not STEP-ops), and 5 new ones: `unmark` (a copy without the
  mark), `mark` (an action's put marked as a copy), `actval` (an action's
  put with another value), `actdrop` (an action's put left out), `copyuser`
  (a copy in a record without a step); the good trace must have a step in a
  commit's record with an action. The second good trace (restarts and
  crashes) is now conformance.sh crash's c-vals: with one record an action,
  the old small configuration ends every iteration in one step, so no
  iteration spanned a restart. `STEP FAULTS OK`: the good trace has 16 STEP
  lines in 11 iterations, 310 old KVs met, 301 copies, 303 records checked
  against their actions (1,300 operations); the second, 31 STEP lines, 88
  restarts (10 crashes), 14 iterations with a step before a restart and the
  next after it.
* **The tree model** (lean/Check/Tree.lean, TreeRun.lean): `OP C` is a put,
  and its key is a copy (`TTx.copies`); a step's touch keys are its copies'
  and reclaim's row (`stepTouchKeys`, Java's `Plan.touchKeys`): C-T5 compares
  `touchOf` of those with the TOUCH line, C-T9 runs the model with them. The
  other checks take the copies as puts, as the writer does. `treeconf.sh
  reclaim 1`: TREECONF OK, 105 touches, C-T5 and C-T9 0 failures.
* **The contract checkers** (`contractcheck`, `bridgecheck`; Contract/Trace.lean
  and Contract/Complete.lean): `OP C` read as a put, in the grammar.

* **The contract** (lean/contract, with Mathlib), proved, no `sorry`:
  * `StepTx` (Contract/ReclaimSteps.lean): every old KV the step's scan met
    is written by the record, `kv.1 ∈ ops.map Op.key` (a copy, or the
    action's put or delete; it was `∈ putKeys ops`); the row put; one
    operation a key. Its fourth conjunct, `StepOpOK` of every operation (a
    put of an old KV met with its value before, or the row; no delete), is
    gone from it, and with it StepTx's index j, which only that conjunct used.
    `step_covers` takes the key as written from the first conjunct directly.
    `iterationOK_of_stepsOK`, `reclaim_java_reads_steps`,
    `pe_reclaim_reads_steps`: proofs unchanged; their statements change
    only through `StepTx`.
  * Contract/ReclaimValues.lean: maintenance is marked per operation,
    `maintenance : Nat → Op → Bool` (the copy mark; until now per
    transaction). `StepOpOK` (moved here) is a copy: a put of an old KV met
    with the value the key had before the record; never a delete.
    `MaintenanceOK`: every record has one operation a key, and every marked
    operation is a copy of some step's scan at that record. The reference
    `userTransactions` keeps, of each record, the operations outside
    reclaim's prefix that are not copies: the action's. New:
    `applyOps_drop_copies` (on a map in key order, with one operation a key,
    marked puts of pairs the map holds change nothing) and
    `record_preserves_users` (a record's effect on the user keys is that of
    its operations without the copies). `user_contents_at`, `user_refMap`,
    `reclaim_user_reads_steps` and `pe_reclaim_user_reads_steps` are proved
    with the per-operation marks; the last two take `CutsMeetSteps`, as
    `CutsMeetMaintenanceSteps` (steps marked as maintenance transactions)
    has no meaning with marks per operation and is gone. Gone:
    `StepTx.put_value`, `StepTx.no_delete`, `StepTx.preserves_users`,
    `reserved_preserves_users`, `applyOps_existing` (unused now).
  * What is proved and what is tested: proved, that removing the copies
    (marked operations that put back the values before the record, at keys of
    no other operation) leaves every user read as the reference of the
    unmarked operations; tested, not proved, that the unmarked operations of a
    record are its action as submitted (C-STEP's STEP-action on traces) and
    that Java's marks are the copies (the exporter's check against the plan,
    and STEP-values, STEP-ops).
  * Examples (Contract/ReclaimStepsExample.lean, ReclaimValuesExample.lean):
    the second step is a commit's record, whose action deletes an old KV the
    step meets (so no copy of it) and puts a key above E; the steps still
    follow the model and give `IterationOK`; the reference holds the action's
    delete and put. `wrong_value_rejected`, `unmet_copy_rejected`,
    `delete_copy_rejected` (on `StepOpOK`), `missing_row_rejected`,
    `unwritten_rejected` (on `StepTx`), `mixed_step` (the commit's record
    meets `StepTx`).
  * The parsers: `OP C` in Contract/Trace.lean (a put) and
    Contract/Complete.lean (the grammar).
  * `gate.sh`: GATE OK; 254 theorems, as before, on the standard axioms only
    (`propext`, `Classical.choice`, `Quot.sound`: the gate's list is
    unchanged). Axioms.lean's list of theorems: removed `StepTx.put_value`,
    `StepTx.no_delete`, `StepTx.preserves_users`,
    `CutsMeetMaintenanceSteps.cutsMeetSteps`,
    `ValuesExample.extra_put_rejected`, `ValuesExample.extra_delete_rejected`;
    added `applyOps_drop_copies`, `record_preserves_users`,
    `ValuesExample.unmet_copy_rejected`, `delete_copy_rejected`,
    `unwritten_rejected`, `mixed_step`. `statements.pin` (pin.sh): five
    pinned files changed (Axioms.lean, Contract/Complete.lean,
    ReclaimSteps.lean, ReclaimValues.lean, Trace.lean); 123 files of the main
    theorems' closure, 144 pinned, as before.
* **Lines changed** (added, removed), from the port's commit: lean/Check/Steps.lean
  130, 65; lean/Check/Tree.lean 56, 4; lean/Check/TreeRun.lean 4, 2;
  lean/TraceCheck.lean 18, 11; lean/TreeCheck.lean 3, 1;
  lean/test-traces/step-faults.sh 51, 23; lean/contract/Contract/ReclaimSteps.lean
  37, 40; ReclaimValues.lean 133, 118; ReclaimStepsExample.lean 11, 7;
  ReclaimValuesExample.lean 55, 34; Contract/Trace.lean 6, 0;
  Contract/Complete.lean 4, 0; Axioms.lean 6, 6; statements.pin 5, 5;
  java/stress/TraceExport.java 132, 73; java/stress/conformance.sh 5, 4;
  027-02 86, 28.

**Gates** (on F53, 2026-11-27, from 15:25; other sessions' work on the
machine; functional runs):

* `lean/test-traces/step-faults.sh`: `STEP FAULTS OK`, 23 faults found.
* `java/stress/treeconf.sh reclaim 1`: `TREECONF OK`; C-T5 and C-T9 0
  failures over 2,515 transactions with 105 touches.
* `java/stress/level3.sh` (full, 10:51 min): `LEVEL 3 OK`. Step 8:
  conformance reclaim, 40 traces, TRACECHECK OK 40, C-CUT 0 of 869 CUT lines
  fail; C-STEP 0 of 23,127 transactions fail, 1,370 STEP lines (557 of them
  in commits' records, the rest in parts' records of the `maint` sets), 1,042
  iterations, 14,954 old KVs met and written by their record, 14,679 copies
  with the value read, 23,087 records against their actions as submitted
  (55,718 operations); 30 of the 40 traces have a step in a commit's record
  with an action. Crash: 15 traces, TRACECHECK OK 15, C-STEP 0 of 5,593
  fail, 409 STEP lines (209 in commits' records), 8,785 copies, 5,578 records
  against their actions; STEP-resume 925 restarts (135 crashes), 68
  iterations with a step before a restart and the next after it. (The copy and
  action counts are from the run's check files, summed with the summary of
  `conformance.sh` as committed after the run; the run printed the old
  summary's words.)
* `lean/contract/gate.sh`: `GATE OK` (above).
* `java/stress/level2.sh` (full, 12:56 min): `LEVEL 2 OK`. Step 0, the pins:
  144 files with their pinned hashes. Step 8, treeconf: reclaim 7,545
  transactions with 310 touches, C-T5 and C-T9 0 failures (with small 7,240
  and drain 14,120 transactions). Step 8b, `check.sh small drain`: CONTRACT OK,
  with its fault tests, bridge-faults.sh among them on the reclaim trace
  `r-del-1` (193 `OP C` lines). Step 8c, pecmp: 0 differ in the small, drain
  and reclaim sets. A first run of level2 (15:44) failed at its unit tests, in
  `ReclaimMaintainTester.testCommitGoesBeforeTheNextPart` (031-04's test of the
  lock's handover: "the call gives way, expected TIMED_WAITING, got
  RUNNABLE"); the test passed alone six times, six runs at once, in both runs
  of before-commit.sh, in level3's unit tests and in the second level2 run.
  It decides by sampling a thread's state, which a loaded machine can keep
  RUNNABLE (a thread that waits for a core); it is the prototype's test, not
  changed here (later steps).
* `java/before-commit.sh` at the end: `BEFORE COMMIT OK (65 s)`.

## What depends on Frans's two answers

Frans decided at 14:36: `maintain(int budget)` replaces `maintain()` in the
Core and Pub API in 2026.7; 2026.7 does not open a 2026.6 database (a new
format version, refused with a clear message, no upgrade path).

* `maintain(int budget)` in place of `maintain()`: as the prototype has it.
  `Db.maintain(int)`, `Database.maintain(int)` and `DatabaseImp`, `Db`'s and
  `Database`'s `getStreamSize()`, the stress apps (`BackToEmpty`,
  `KillEmpty`, `SlowDrive`, `D2ScanHistory`, `D3ObjectIndex`), `AppRecord`,
  `CountGates`, `TraceExport` (`maintain(Reclaim.MAINTAIN_MIN_BUDGET)`).
  Nothing to change in the code; the Javadoc still says `maintain()` in a
  few places as the method's name (`Database`, lines 367, 553, 589). The
  documents (027, README, releases/next.md) are not part of this landing.
* 2026.7 refuses a 2026.6 database: not built. The prototype writes
  `StoredTrans.RECORD_FORMAT` 8, as 2026.6 does, and marks a copy in byte 6
  of a value node (`StoredValueNode`), which 2026.6 skips: today this code
  opens a 2026.6 stream, and 2026.6 opens one of this code and reads its
  copies as plain values (`transactionInfo()` differs). What the decision
  needs: `RECORD_FORMAT` 9 (`StoredTrans`, checked in `NodeStream` and the
  parser, written in the header), whose refusal message exists
  (`StoredTrans.formatRefused`: an older or a newer BergDB); 2026.6 reads
  format 8 only and so refuses format 9; the tests and `CorruptStreamTester`
  that build records of format 8 by hand; the item's question Q5 then has
  its answer (the record's format, not the value node's or the meta
  block's, unless Frans wants those too).

## For the later steps

What this work met that bears on the steps not taken here (F2 to F7, the
kept times, the documents):

* **The step's size (F3, F4).** With one record an action a step rides on a
  commit whenever the commit's allowance passes `MIN_STEP_SIZE`: in the
  small configurations every iteration now ends in one step. C-STEP's fault
  test's second trace (30 keys of 20 bytes, restarts every 10 actions) no
  longer had an iteration across a restart and now uses the crash set's
  c-vals; a change of the step's size or of its allowance should keep at least
  one configuration of each set with iterations of several steps (level 3
  prints the counts: 1,042 iterations for 1,370 STEP lines in the reclaim set).
  In the `maint` sets every step is a part's (0 in commits' records).
* **The admission and the record's room (F5, F6).** The contract's
  `MaintenanceOK` and C-STEP's STEP-ops require one operation a key in a
  record (`Db.merge`, which fails the database on a key in both): a change
  that admits or trims the step's KVs by the room must keep the merge's rule
  and the drop of a copy at a key the action writes.
* **What the trace reads of the prototype's code.** `TraceExport` takes
  lastKey before a step from `Db.TestHooks.beforeApply` and L' and eod from
  `Reclaim.RecordPlan.next` and `eod`, and the copy keys from
  `Maintenance.Plan.copyKeys` (checked against the copy marks of the record's
  bytes). A refactoring of the plan (F2's charge, F7's reserve as a constant,
  Q6's cheap first test) must keep these, or change the exporter with it.
* **The action as submitted.** STEP-action compares a record with the
  exporter's own copy of the workload's transaction, so a change in what Db
  writes for an action (a transformation, a merge) shows there; for BergDB's
  own actions (setters, the start's record) the exporter takes the Trans Db
  executed, which is weaker; a part's action is empty.
* **F9.** The copy mark is in the bytes, and the exporter reads it with
  `StoredValueNode.isCopy`; `Db.getTrans` and `transactionInfo` can tell a
  record's copies the same way.
* **The format (Frans, 14:36).** `RECORD_FORMAT` 9 is the change that
  refuses a 2026.6 database; the traces' format (`TRACE 3`) did not change, as
  `OP C` and `ACT` are new lines that the old checkers refuse or ignore
  (`tracecheck` filters ACT before its pinned parser).

## State

2026-11-27, 16:05.

* **Done:** step 0 (the port, gated, the crash probe 0 different) and step 1
  (the conformance: the trace format, TraceExport, C-STEP with STEP-action
  and its fault test, C-T5 and C-T9, the contract's checkers and proofs),
  with level2.sh and level3.sh whole, gate.sh and before-commit.sh. No proof
  left open; no `sorry`; no new axiom.
* **Not done** (not part of steps 0 and 1): the item's text and `probes/`
  (the lead's; the probes need the appendix's change); F2 to F7; the kept
  times; `RECORD_FORMAT` 9 for Frans's decision of 14:36; the documents
  beyond 027-02 (027-13 describes how Java's steps are checked and names
  C-STEP's old rules); night.sh, week.sh; level4.sh (its conformance with
  eviction reads the same traces' kinds; not run here).
* **Next:** the lead's review of the branch `031-06-landing`; the landing's
  later steps.

## Appendix: the probes for the test hook

The change of the item's probes (at `fa11d15f`) for `Db.TestHooks.maintainMaxParts()`, as the
gate of step 0 ran them:

```diff
--- probes/P2CrashProbe.java
+++ probes/P2CrashProbe.java
@@ -1,6 +1,5 @@
 package bergdb.core;
 
-import java.lang.reflect.Method;
 import java.security.MessageDigest;
 import java.util.*;
 import java.util.concurrent.atomic.AtomicLong;
@@ -29,7 +28,7 @@
  *   stop:     stopped there (transExecuted calls stop());
  * then a start from the stream, and the actions after record k's: the next action after
  * it, or for a part of a call that wrote p parts, the reference with that call ended after
- * p parts (Db.maintain(int, int)) and the action after the call. -Drestart=N restarts the
+ * p parts (Db.maintain(int) with Db.TestHooks.maintainMaxParts()) and the action after the call. -Drestart=N restarts the
  * continued database every N actions too. The continued stream must equal the reference:
  * the same length, the same decided cut, and the same bytes from the first position kept.
  *
@@ -66,7 +65,8 @@
     static final String CLOCK = System.getProperty("clock", "");
     static final boolean EVICT = Integer.getInteger("evict", 0) == 1;
     static long refusedCalls;
-    static Method maintainParts;
+    /** The most parts that write of the next maintain() call (Db.TestHooks.maintainMaxParts). */
+    static volatile int maxParts = Integer.MAX_VALUE;
 
     static final class Action {
         char kind;          // 'p' put(s), 'd' delete, 'e' empty, 'm' maintain, 's' sd, 'r' retain
@@ -188,7 +188,12 @@
             case 'r': d.setRetainDuration(a.arg * SEC); break;
             case 'm':
                 if (a.arg < 0) {
-                    maintainParts.invoke(d, B, -a.arg - 1);
+                    maxParts = -a.arg - 1;
+                    try {
+                        d.maintain(B);
+                    } finally {
+                        maxParts = Integer.MAX_VALUE;
+                    }
                 } else {
                     d.maintain(a.arg);
                 }
@@ -200,15 +205,6 @@
             return false;
         } catch (bergdb.storage.StreamIoException e) {
             return false;
-        } catch (java.lang.reflect.InvocationTargetException e) {
-            Throwable c = e.getCause();
-            if (c instanceof Crash || c instanceof DbStoppingException || c instanceof DbFailedException
-                    || c instanceof bergdb.storage.StreamIoException) {
-                return false;
-            }
-            throw new RuntimeException(c);
-        } catch (IllegalAccessException e) {
-            throw new RuntimeException(e);
         }
     }
 
@@ -224,6 +220,9 @@
 
     static void installHook() {
         Db.testHooks = new Db.TestHooks() {
+            public int maintainMaxParts() {
+                return maxParts;
+            }
             public void beforeApply(Db.ExecuteData x) {
                 if (countOn && mode.equals("pre") && records + 1 == stopAt) {
                     records++;
@@ -349,8 +348,6 @@
         int n = Integer.parseInt(args[1]);
         int sd = Integer.parseInt(args[2]);
         String modes = args.length > 3 ? args[3] : "all";
-        maintainParts = Db.class.getDeclaredMethod("maintain", int.class, int.class);
-        maintainParts.setAccessible(true);
         installHook();
         List<Action> as = workload(seed, n, sd);
         List<Rec> rs = new ArrayList<>();
--- probes/FaultProbe.java
+++ probes/FaultProbe.java
@@ -66,6 +66,9 @@
     static void installHook() {
         Db.testHooks = new Db.TestHooks() {
             boolean first;
+            public int maintainMaxParts() {
+                return P2CrashProbe.maxParts;
+            }
             public void beforePlan(Db.ExecuteData x) {
                 if (!P2CrashProbe.countOn) return;
                 first = true;
@@ -147,8 +150,6 @@
         int n = Integer.parseInt(args[1]);
         int sd = Integer.parseInt(args[2]);
         int perKind = args.length > 3 ? Integer.parseInt(args[3]) : 6;
-        P2CrashProbe.maintainParts = Db.class.getDeclaredMethod("maintain", int.class, int.class);
-        P2CrashProbe.maintainParts.setAccessible(true);
         installHook();
         List<P2CrashProbe.Action> as = P2CrashProbe.workload(seed, n, sd);
         List<P2CrashProbe.Rec> rs = new ArrayList<>();
--- probes/ConcProbe.java
+++ probes/ConcProbe.java
@@ -1,6 +1,5 @@
 package bergdb.core;
 
-import java.lang.reflect.Method;
 import java.util.*;
 import java.util.concurrent.atomic.AtomicLong;
 
@@ -18,7 +17,7 @@
  * records after them), on a clock that the threads move on together. Every record is
  * logged, in the order the write lock gave, with the action that wrote it and its time.
  * Then one thread replays the logged actions, each at its record's time (a part as
- * maintain(B, 1): the call's first part that writes, which is the part due), on a new
+ * maintain(B) with Db.TestHooks.maintainMaxParts() 1: the call's first part that writes, which is the part due), on a new
  * database: the stream must be the same, byte for byte from the decided cut, its length and
  * its decided cut the same. So the stream is a function of the accepted actions, in the
  * write lock's order, with their times, whatever the threads did.
@@ -158,8 +157,14 @@
         Db d2 = start(s2, node);
         d2.setStartupDistance(2000);
         d2.setRetainDuration(SEC);
-        Method mp = Db.class.getDeclaredMethod("maintain", int.class, int.class);
-        mp.setAccessible(true);
+        // A part as maintain(B) with at most one part that writes (Db.TestHooks.maintainMaxParts).
+        Db.testHooks = new Db.TestHooks() {
+            public int maintainMaxParts() { return 1; }
+            public void transExecuted(Db.ExecuteData x) {}
+            public void valueNodeCreated(ValueNode node, long[] key) {}
+            public void nodeTouched(Node node) {}
+            public void nodeReplaced(Node node) {}
+        };
         int parts = 0, commits = 0, setters = 0;
         for (Object[] e : log) {
             char kind = (Character) e[0];
@@ -176,7 +181,7 @@
                 commits++;
                 break;
             }
-            case 'm': mp.invoke(d2, (Integer) e[2], 1); parts++; break;
+            case 'm': d2.maintain((Integer) e[2]); parts++; break;
             case 'r': d2.setRetainDuration((Long) e[2]); setters++; break;
             case 's': d2.setStartupDistance((Integer) e[2]); setters++; break;
             default: throw new IllegalStateException();
@@ -185,6 +190,7 @@
         d2.sync(SyncLevel.ORDINARY);
         final long decided2 = d2.getFirstAvailablePos();
         d2.close();
+        Db.testHooks = null;
         P2CrashProbe.Image b = P2CrashProbe.image(s2, decided2);
         String why = P2CrashProbe.compare(a, b);
         System.out.println("seed " + seed + ", " + seconds + " s, " + writers + " writers, node "
```
