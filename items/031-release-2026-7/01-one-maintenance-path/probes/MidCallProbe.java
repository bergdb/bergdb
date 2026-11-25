package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;

/**
 * bergdb 031-01's probe of P2 inside a call, on main (no w): a crash right after a user
 * record whose maintenance begins a reclaim iteration, before that begin's record. Two runs
 * from the same stream, with the same transactions at the same times after it: the
 * uninterrupted one, and one started from a copy that ends with the user record. Prints
 * whether the streams are the same and where they first differ. R = 1 s, startup distance
 * 10,000 bytes, CutStream and a test clock.
 *
 * In package bergdb.core; on the class path before the jar (from java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT MidCallProbe.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.MidCallProbe
 * 031-01 ran it on main at 4ce8f942 (and its prototype with -Dproto311.now=true).
 */
public class MidCallProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final AtomicLong time = new AtomicLong(SEC);
    static Db start(CutStream s) { return Db.builder().testSetup(s).clock(time::get).start(); }
    public static void main(String[] a) throws Exception {
        CutStream s = new CutStream(); Db d = start(s);
        d.setStartupDistance(10000); d.setRetainDuration(SEC);
        final long[] next = {0};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (!x.trans.isInternal() && next[0] == 0) next[0] = x.trans.nextPos;
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
        time.addAndGet(MS);
        d.execute(d.trans().put("/a", new byte[50000]).build());   // begins an iteration
        Db.testHooks = null;
        d.sync(SyncLevel.ORDINARY);
        System.out.println("after /a: length " + d.getStreamLength() + ", /a ends at " + next[0]
            + ", iteration " + (d.internal().reclaim().currentIteration() != null));
        CutStream copy = s.copy(); copy.truncate(next[0]);
        Db b = start(copy);
        System.out.println("crashed: iteration " + (b.internal().reclaim().currentIteration() != null));
        for (int i = 0; i < 20; i++) {
            time.addAndGet(SEC / 10);
            d.execute(d.trans().put("/c" + i, new byte[2000]).build());
            b.execute(b.trans().put("/c" + i, new byte[2000]).build());
        }
        d.sync(SyncLevel.ORDINARY); b.sync(SyncLevel.ORDINARY);
        byte[] x = new byte[(int) s.getLength()], y = new byte[(int) copy.getLength()];
        s.read(0, x, 0, x.length); copy.read(0, y, 0, y.length);
        int at = 0; while (at < Math.min(x.length, y.length) && x[at] == y[at]) at++;
        System.out.println("lengths " + x.length + " " + y.length + ", same bytes " + Arrays.equals(x, y) + ", first difference " + at);
        d.close(); b.close();
    }
}
