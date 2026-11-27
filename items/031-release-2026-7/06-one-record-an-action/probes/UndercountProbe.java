package bergdb.core;

import bergdb.pub.util.Clock;

/**
 * bergdb 031-06, rule 12: the after-row charge of 028-26 is not made. This measures what is
 * not charged: the bytes of the index nodes that a step's batch makes dirty after its row
 * was made (Reclaim.Stats.Iteration.dirtiedAfterRow), against the step's charge (the row's
 * rewritten). Since the landing's step 3 (the fixed-width patch, Db.chargeStep) the charge
 * holds them, and dirtiedAfterRow is the index bytes of the steps' records that the steps
 * are not charged; this version prints the step 3 figures (the run before it is
 * runs/undercount.txt). Measured on a pass of maintain() parts, whose records hold the step alone, so
 * that the nodes after the row are the step's own; a commit's step makes the same kind of
 * batch beside the action's KVs, whose nodes the record's counts cannot tell apart.
 * Workload of Reclaim.Tester.testAllowanceCountsNodesMadeAfterTheRow: N keys of 10 bytes put
 * in 100-key transactions, overwrites, then maintain() calls only.
 *
 * Usage: java -ea -cp OUT:build/bergdb.jar bergdb.core.UndercountProbe N
 */
public class UndercountProbe {
    public static void main(String[] args) {
        int n = Integer.parseInt(args[0]);
        for (int nodeSize : new int[] {8, 30, 0}) {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            DbBuilder builder = Db.builder().testSetup().clock(clock);
            if (nodeSize == 8) builder.maxNodeSize8();
            if (nodeSize == 30) builder.maxNodeSize30();
            Db db = builder.start();
            try {
                db.setStartupDistance(2000);
                Reclaim reclaim = db.internal().reclaim();
                for (int i = 0; i < n; i += 100) {
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    Trans.Builder b = db.trans();
                    for (int j = i; j < i + 100 && j < n; j++) b.put("/!k/" + j, new byte[10]);
                    db.execute(b.build());
                }
                db.setRetainDuration(Clock.UNITS_PER_SEC);
                java.util.Random r = new java.util.Random(6);
                for (int i = 0; i < 200; i++) {
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    db.execute(db.trans().put("/!k/" + r.nextInt(n), new byte[10]).build());
                }
                // Only parts from here: wait for the commits' iteration to end, then a pass.
                Reclaim.Stats stats = null;
                long charged0 = -1;
                long passStart = -1;
                for (int i = 0; i < 20000; i++) {
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    if (stats == null && reclaim.currentIteration() == null) {
                        stats = reclaim.enableStats();
                    }
                    db.maintain(1000);
                    if (stats != null && passStart == -1 && reclaim.currentIteration() != null) {
                        passStart = reclaim.currentIteration().pStart;
                    }
                    if (passStart != -1 && reclaim.currentIteration() == null) {
                        charged0 = reclaim.lastDoneRow().rewritten;     // before a cut drops it
                        break;
                    }
                }
                Reclaim.Stats.Iteration st = null;
                for (Reclaim.Stats.Iteration it : stats.iterations) if (it.pStart == passStart) st = it;
                long charged = charged0;
                // Since 031-06's landing, step 3: the charge is made after the batch
                // (Db.chargeStep), and dirtiedAfterRow is what the steps' records made dirty
                // and were not charged (the top nodes, the table's path; no action in a part).
                long recordDirty = st.charged + st.dirtiedAfterRow;
                System.out.println("node " + (nodeSize == 0 ? "default" : "" + nodeSize) + ", " + n
                        + " keys: a pass of " + st.steps + " steps (parts), " + st.values
                        + " copies; charged " + charged + " bytes (values " + st.valueBytes
                        + " + their nodes' overhead + index nodes " + st.charged + ", of them made by the"
                        + " batches after the touch " + st.madeCharged + "); the records' index bytes "
                        + recordDirty + ", not charged " + st.dirtiedAfterRow + " bytes, "
                        + String.format("%.1f", 100.0 * st.dirtiedAfterRow / charged) + " % of the charge"
                        + "; as Trans.dirtiedBytes counted them " + st.dirtiedStored);
            } finally {
                db.close();
            }
        }
    }
}
