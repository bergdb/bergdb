package bergdb.core;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * 016-06/R7: stop() while a user transaction runs, after its record is appended and before
 * reclaim's work (Reclaim.transactionCompleted). The transaction is written and survives a
 * restart, but execute() throws DbStoppingException from reclaim's step (its getMany or
 * execute checks the state), which says the call was refused. The hook (Db.testHooks,
 * transExecuted, after store()) calls stop() as another thread would at that moment: stop()
 * sets STOPPING and returns at once; its closer waits for the write lock.
 */
public class R7StopDuringStepProbe {
    public static void main(String[] args) {
        long time = Clock.UNITS_PER_SEC;
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        MemoryStream ms = new MemoryStream();
        final Db db = Db.builder().testSetup(ms).clock(clock).startupDistance(2000).start();
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        final Reclaim rc = db.internal().reclaim();
        final boolean[] armed = {false};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (armed[0] && !x.trans.isInternal()) {
                    armed[0] = false;
                    db.stop();
                }
            }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        try {
            java.util.Random r = new java.util.Random(1);
            for (int i = 0; i < 4000; i++) {
                time += Clock.UNITS_PER_SEC / 20; clock.setTime(time);
                Reclaim.IterationInfo cur = rc.currentIteration();
                if (cur != null && Reclaim.fractionOf(db.getStreamLength() + Integer.getInteger("est", 150) - cur.pStart,
                        Reclaim.DEFAULT_INTERNAL_FRACTION) - cur.rewritten > 10000) {
                    armed[0] = true;      // this put's transactionCompleted makes a step
                }
                String key = "/k/" + r.nextInt(50);
                byte[] v = new byte[1 + r.nextInt(60)];
                v[0] = 42;
                Trans t = db.trans().put(key, v).build();
                try {
                    db.execute(t);
                } catch (RuntimeException e) {
                    System.out.println("put " + i + " of " + key + " threw " + e);
                    db.close();
                    Db d2 = Db.builder().testSetup(ms.copy()).start();
                    byte[] got = d2.getOne(Long.MAX_VALUE, bergdb.dag.Keys.toSegments(key),
                            d2.newGetData());
                    StoredTrans st = d2.getTrans(t.tpos);
                    System.out.println("after a restart: the value of " + key + " is "
                            + (java.util.Arrays.equals(got, v) ? "the put's" : "not the put's")
                            + "; the transaction at " + t.tpos + " has time " + st.tt
                            + " (the put's " + t.tt + ")");
                    d2.close();
                    return;
                }
            }
            System.out.println("no step was armed");
            db.close();
        } finally {
            Db.testHooks = null;
        }
    }
}
