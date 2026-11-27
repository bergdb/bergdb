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
  for one.

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

(The gates' lines and the contract's proofs: below, as they ran.)

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

(Filled in at the end.)

## State

(Filled in at the end.)

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
