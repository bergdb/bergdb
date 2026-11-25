package bergdb.core;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-01's probe of w after a crash: a crash between an application record that
 * changes w (the first after an iteration's start) and the store of w, the record after it.
 * R = 1 s, startup distance SD, CutStream and a test clock; 3,000 values of 100 bytes
 * overwritten, one key a transaction. At each record that changes w, the stream as it is
 * then (a copy, ending with that record) is started: its w must be the running one's and
 * stored by the start (031-01, section 12: the repair after Codex's review); and what the
 * start wrote must be, byte for byte, what the uninterrupted run wrote after that record.
 * Needs the prototype's fields (Reclaim.appW, appWStored).
 *
 *   javac -cp build/bergdb.jar -d OUT CrashW.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.CrashW SD
 * 031-01 ran SD 5000, 20000, 100000 and 1000000. A copy that the sync leaves short of the
 * record's end is skipped and counted.
 */
public class CrashW {
    public static void main(String[] args) throws Exception {
        final int sd = Integer.parseInt(args[0]);
        final CoreTestClock clock = new CoreTestClock();
        long time = Clock.UNITS_PER_SEC;
        clock.setTime(time);
        final CutStream stream = new CutStream();
        final Db db = Db.builder().testSetup(stream).clock(clock).start();
        db.setStartupDistance(sd);
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        final int[] crashes = {0};
        final long[] wrong = {0}, skipped = {0};
        final long[] pendingAt = {-1};
        final byte[][] pendingBytes = {null};
        final long[] differ = {0}, compared = {0};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (x.trans.isInternal()) return;
                Reclaim r = db.internal().reclaim();
                if (pendingAt[0] != -1) {
                    // What the start of the last copy wrote (w's store), against what the
                    // uninterrupted run wrote after the same record: byte for byte.
                    db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
                    byte[] b = new byte[pendingBytes[0].length];
                    try {
                        stream.read(pendingAt[0], b, 0, b.length);
                    } catch (java.io.IOException e) {
                        throw new RuntimeException(e);
                    }
                    compared[0]++;
                    if (!java.util.Arrays.equals(b, pendingBytes[0])) differ[0]++;
                    pendingAt[0] = -1;
                }
                if (r.appW == r.appWStored) return;
                long w = r.appW;
                db.sync(bergdb.pub.util.SyncLevel.ORDINARY);    // the buffer to the stream
                CutStream copy = stream.copy();
                if (copy.getLength() != x.trans.nextPos) {
                    skipped[0]++;       // the sync left the stream short of the record's end
                    return;
                }
                Db.testHooks = null;
                Db d2 = Db.builder().testSetup(copy).clock(clock).start();
                Reclaim r2 = d2.internal().reclaim();
                if (r2.appW != w || r2.appWStored != w) wrong[0]++;
                d2.close();
                try {
                    byte[] b = new byte[(int) (copy.getLength() - x.trans.nextPos)];
                    copy.read(x.trans.nextPos, b, 0, b.length);
                    pendingAt[0] = x.trans.nextPos;
                    pendingBytes[0] = b;
                } catch (java.io.IOException e) {
                    throw new RuntimeException(e);
                }
                Db.testHooks = this;
                crashes[0]++;
            }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        java.util.Random rnd = new java.util.Random(1);
        for (int i = 0; i < 30000; i++) {
            time += Clock.UNITS_PER_SEC / 200;
            clock.setTime(time);
            db.execute(db.trans().put("/k/" + rnd.nextInt(3000), new byte[100]).build());
        }
        Db.testHooks = null;
        System.out.println("sd " + sd + ": " + crashes[0] + " crashes after a record that changed w, "
                + wrong[0] + " starts with another w or w not stored, " + skipped[0] + " skipped; "
                + compared[0] + " starts' writes compared with the run's, " + differ[0]
                + " differ; iterations " + db.getReclaimIterationCount());
        db.close();
        if (wrong[0] != 0 || differ[0] != 0 || crashes[0] == 0) throw new AssertionError("CRASHW FAILED");
    }
}
