package bergdb.core;

import java.io.FileOutputStream;
import java.io.IOException;

import bergdb.dag.TopNode;
import bergdb.stream.MemoryStream;

/**
 * Bergdb item 002 (M46), probe of the int-to-long prototype (topNodeId a long below 2^48,
 * written in bytes 10 to 15 of the top node; widen-48.patch). Needs the scratch hook
 * -Dm46.firstTop=N (probe-hook-long.patch).
 * In-memory database (Db.builder().testSetup), one key put in every transaction.
 *
 * Usage: java -ea -Dm46.firstTop=N -cp bergdb.jar:. bergdb.core.M46Wide cross SD COUNT
 *          crosses the ordinals N to N + COUNT with startup distance SD (bytes), then checks
 *          every historical value, restarts from a copy of the stream, checks again and
 *          makes one more top node.
 *        ... bergdb.core.M46Wide end SD
 *          runs until the bound refuses a transaction, then checks and restarts.
 *        ... bergdb.core.M46Wide save SD COUNT FILE
 *          as cross, then writes the stream to FILE (for an older reader).
 */
public final class M46Wide {
    static CoreTestClock clock = new CoreTestClock();
    static long tick = 0;

    static void next() { tick++; clock.setTime(10L * tick); }
    static long superOrd(Db db) { return db.internal().superRoot().topNodeId; }
    static String str(byte[] b) { return b == null ? "null" : new String(b); }

    public static void main(String[] args) throws IOException {
        String mode = args[0];
        int sd = Integer.parseInt(args[1]);
        long first = Long.getLong("m46.firstTop", 0L);
        System.out.println("m46.firstTop=" + first + ", MAX_TOP_NODE_ID_VALUE=" + TopNode.MAX_TOP_NODE_ID_VALUE
                + ", mode " + mode + ", startup distance " + sd);
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(sd).start();
        if (mode.equals("cross") || mode.equals("save")) {
            int count = Integer.parseInt(args[2]);
            int n = 0;
            while (superOrd(db) < first + count) {
                next();
                db.execute(db.trans().put("/hot", "v" + n).build());
                n++;
            }
            report(db, n, "before the restart");
            db.sync(SyncLevel.STRONG);
            db.stop();
            if (mode.equals("save")) {
                byte[] b = new byte[(int) stream.getLength()];
                stream.read(0, b, 0, b.length);
                FileOutputStream out = new FileOutputStream(args[3]);
                out.write(b);
                out.close();
                System.out.println("saved " + b.length + " bytes to " + args[3]);
                return;
            }
            Db db2 = Db.builder().testSetup(stream.copy()).clock(clock).startupDistance(sd).start();
            report(db2, n, "after the restart");
            long s = superOrd(db2);
            int m = n;
            while (superOrd(db2) == s) {
                next();
                db2.execute(db2.trans().put("/hot", "v" + m).build());
                m++;
            }
            System.out.println("after the restart, the next top node has ordinal " + superOrd(db2)
                    + " (expected " + (s + 1) + ")");
            db2.stop();
        } else if (mode.equals("end")) {
            int n = 0;
            Throwable refused = null;
            String last = null;
            while (refused == null && n < 100000) {
                next();
                try {
                    db.execute(db.trans().put("/hot", "v" + n).build());
                    last = "v" + n;
                } catch (Throwable e) {
                    refused = e;
                }
                n++;
            }
            System.out.println("refused at transaction " + (n - 1) + ": " + refused);
            System.out.println("super root ordinal " + superOrd(db) + "; nodes left in the transaction's node list: "
                    + db.internal().x().transNodes.size() + "; read now: " + str(DbUtil.get(db, "/hot"))
                    + " (last committed " + last + ")");
            int again = 0;
            for (int k = 0; k < 3; k++) {
                next();
                try { db.execute(db.trans().put("/other", "x").build()); } catch (Throwable e) { again++; }
            }
            System.out.println("3 more transactions: " + again + " refused");
            report(db, n - 1, "before the restart");
            db.sync(SyncLevel.STRONG);
            db.stop();
            Db db2 = Db.builder().testSetup(stream.copy()).clock(clock).startupDistance(sd).start();
            report(db2, n - 1, "after the restart");
            next();
            try {
                db2.execute(db2.trans().put("/hot", "after").build());
                System.out.println("a transaction after the restart succeeded");
            } catch (Throwable e) {
                System.out.println("a transaction after the restart: " + e);
            }
            db2.stop();
        }
    }

    /** Every committed value at its own time, and the newest written top node. */
    static void report(Db db, int n, String when) {
        int bad = 0;
        for (int k = 0; k < n; k++) {
            byte[] v = DbUtil.get(db, 10L * (k + 1), "/hot");
            if (v == null || !new String(v).equals("v" + k)) bad++;
        }
        TopNode w = db.internal().newestWrittenTop();
        System.out.println(when + ": " + n + " transactions, super root ordinal " + superOrd(db)
                + ", newest written top " + (w == null ? "null" : "" + w.topNodeId)
                + "; historical lookups: " + bad + " of " + n + " wrong");
    }
}
