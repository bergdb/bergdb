package bergdb.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import bergdb.stream.MemoryStream;

/**
 * Probe for bergdb 007-02: can one transaction stop the startup pos for good? It makes
 * dirty more index nodes than one record can hold; TransSeq.take takes transactions whole
 * and does not take the first that does not fit in the record limit, "also when fewer than
 * two are". The record limit is lowered, as in DbTester.testRecordsWithinLimit.
 *
 * Arguments: the record limit in bytes (200000) and n (20): the large transaction updates
 * every n-th of the 40,000 keys. Run from java/ after build.sh, with the class first on the
 * class path (the jar's index hides the package otherwise):
 *
 *     javac -cp build/bergdb.jar -d /tmp/probe ../items/007-bounds/02-take-blocked/TakeStuckProbe.java
 *     java -ea -cp /tmp/probe:build/bergdb.jar bergdb.core.TakeStuckProbe 200000 20
 */
public class TakeStuckProbe {
    static String key(int k) { return String.format("/k/%06d", k); }

    public static void main(String[] args) {
        final long limit = Long.parseLong(args.length > 0 ? args[0] : "200000");
        final int every = Integer.parseInt(args.length > 1 ? args[1] : "20");
        StoredTrans.recordLimit = limit;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long time = 1000 * 1000;
        clock.setTime(time);
        final int sd = 20 * 1000;
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(sd).start();

        List<Integer> order = new ArrayList<>();
        for (int k = 0; k < 40000; k++) order.add(k);
        Collections.shuffle(order, new Random(7));
        for (int i = 0; i < 400; i++) {
            clock.setTime(time += 1000);
            Trans.Builder b = db.trans();
            for (int j = 0; j < 100; j++) b.put(key(order.get(i * 100 + j)), "v");
            db.execute(b.build());
        }
        for (int i = 0; i < 2000; i++) {
            clock.setTime(time += 1000);
            db.execute(db.trans().put("/x", "a" + i).build());
        }
        long sp0 = db.internal().getStartupPosForEvict();
        System.out.println("before: stream " + db.getStreamLength() + ", startup pos " + sp0
                + ", section " + (db.getStreamLength() - sp0));

        clock.setTime(time += 1000);
        Trans.Builder b = db.trans();
        for (int k = 0; k < 40000; k += every) b.put(key(k), "w");
        Trans big = b.build();
        db.execute(big);
        System.out.println("big: tpos " + big.tpos + ", record " + (big.nextPos - big.tpos)
                + " bytes, record limit " + limit);

        for (int i = 1; i <= 4000; i++) {
            clock.setTime(time += 1000);
            db.execute(db.trans().put("/y", "b" + i).build());
            if (i % 500 == 0) {
                long sp = db.internal().getStartupPosForEvict();
                long len = db.getStreamLength();
                System.out.println("after " + i + ": stream " + len + ", startup pos " + sp
                        + (sp < big.tpos ? " (before big)" : " (past big)")
                        + ", section " + (len - sp) + " = " + ((len - sp) / sd) + " x sd");
            }
        }
        long sp = db.internal().getStartupPosForEvict();
        db.sync(SyncLevel.STRONG);
        db.stop();

        // A restart starts from the same startup pos, and reruns everything after it.
        CoreTestClock clock2 = new CoreTestClock();
        clock2.setTime(time += 1000);
        long t0 = System.nanoTime();
        Db db2 = Db.builder().testSetup(stream.copy()).clock(clock2).startupDistance(sd).start();
        long ms = (System.nanoTime() - t0) / 1000000;
        System.out.println("restart: " + ms + " ms, startup pos " 
                + db2.internal().getStartupPosForEvict() + (db2.internal().getStartupPosForEvict() == sp
                ? " (the same)" : " (not the same as " + sp + ")"));
        db2.stop();
    }
}
