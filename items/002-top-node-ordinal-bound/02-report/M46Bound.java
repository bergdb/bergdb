package bergdb.core;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import bergdb.dag.KeyNode;
import bergdb.dag.TopNode;
import bergdb.stream.MemoryStream;

/**
 * Bergdb item 002 (M46), probe of what Java does at the top node ordinal bound. Needs the
 * scratch hook -Dm46.firstTop=N (the first top node's ordinal, see TopDs), so that the
 * bound 2^30 - 1 is reached after a few root changes. In-memory database
 * (Db.builder().testSetup), default node size 30.
 *
 * Usage: java -ea -Dm46.firstTop=N -cp bergdb.jar:. bergdb.core.M46Bound hot|two|many
 *   hot   one key, one put per transaction.
 *   two   keys /a and /b put in one transaction exactly when /a fits in the root in place
 *         and /b then makes the root split; a filler key /c otherwise. Shows what an
 *         exception in the middle of a transaction leaves behind.
 *   many  1,000 keys, one random put per transaction (a tree of more than one level),
 *         going on after the first failure, -Dm46.n transactions in all (default 30,000);
 *         then a restart from the stream.
 * The hook: probe-hook-int.patch (scratch only).
 */
public final class M46Bound {
    static CoreTestClock clock = new CoreTestClock();
    static long tick = 0;
    static final int MAX = 30;      // the default node size (DbBuilder, testSetup)

    static void next() { tick++; clock.setTime(10L * tick); }
    static int superOrd(Db db) { return db.internal().superRoot().topNodeId; }
    static String str(byte[] b) { return b == null ? "null" : new String(b); }

    public static void main(String[] args) {
        String mode = args[0];
        System.out.println("m46.firstTop=" + Integer.getInteger("m46.firstTop", 0)
                + ", MAX_TOP_NODE_ID_VALUE=" + TopNode.MAX_TOP_NODE_ID_VALUE + ", mode " + mode);
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        System.out.println("started: super root ordinal " + superOrd(db));
        if (mode.equals("hot")) hot(db, stream);
        else if (mode.equals("two")) two(db, stream);
        else if (mode.equals("many")) many(db, stream);
    }

    static void hot(Db db, MemoryStream stream) {
        String last = null;
        int i = 0;
        Throwable failure = null;
        for (; i < 100000 && failure == null; i++) {
            next();
            String v = "v" + i;
            try {
                db.execute(db.trans().put("/hot", v).build());
                last = v;
            } catch (Throwable e) {
                failure = e;
            }
        }
        report(db, failure, i - 1);
        System.out.println("read /hot now: " + str(DbUtil.get(db, "/hot")) + " (last committed " + last + ")");
        int fails = 0;
        for (int k = 0; k < 5; k++) {
            next();
            try { db.execute(db.trans().put("/hot", "w" + k).build()); } catch (Throwable e) { fails++; System.out.println("  retry " + k + ": " + e); }
        }
        next();
        boolean other = true;
        try { db.execute(db.trans().put("/other", "x").build()); } catch (Throwable e) { other = false; System.out.println("  /other: " + e); }
        System.out.println("after the failure: 5 more puts of /hot, " + fails + " failed; a put of /other "
                + (other ? "succeeded" : "failed"));
        restart(db, stream, new String[] {"/hot", "/other"});
    }

    static void two(Db db, MemoryStream stream) {
        String lastA = null, lastB = null;
        int i = 0, twos = 0;
        Throwable failure = null;
        String triedA = null;
        for (; i < 100000 && failure == null; i++) {
            next();
            KeyNode root = db.internal().superRoot().rootPointer;
            int s = root.size;
            try {
                if (s == MAX - 3 || s == MAX - 2) {
                    triedA = "A" + i;
                    twos++;
                    db.execute(db.trans().put("/a", triedA).put("/b", "B" + i).build());
                    lastA = triedA;
                    lastB = "B" + i;
                } else {
                    db.execute(db.trans().put("/c", "C" + i).build());
                }
            } catch (Throwable e) {
                failure = e;
            }
        }
        report(db, failure, i - 1);
        System.out.println("two-key transactions: " + twos + "; the failed one put /a = " + triedA);
        System.out.println("read now: /a = " + str(DbUtil.get(db, "/a")) + " (last committed " + lastA
                + "), /b = " + str(DbUtil.get(db, "/b")) + " (last committed " + lastB + ")");
        System.out.println("nodes left in the transaction's node list: " + db.internal().x().transNodes.size());
        restart(db, stream, new String[] {"/a", "/b", "/c"});
    }

    static void many(Db db, MemoryStream stream) {
        Random rnd = new Random(1);
        Map<String, String> model = new HashMap<String, String>();
        int i = 0, ok = 0, failed = 0, firstFail = -1;
        Throwable first = null;
        int leftoverSeen = 0;
        boolean shownRecord = false;
        Map<String, Integer> kinds = new java.util.TreeMap<String, Integer>();
        final int total = Integer.getInteger("m46.n", 30000);
        for (; i < total; i++) {
            next();
            String k = "/k/" + rnd.nextInt(1000);
            String v = "v" + i;
            int before = db.internal().x().transNodes.size();
            if (before > 0) leftoverSeen++;
            try {
                db.execute(db.trans().put(k, v).build());
                model.put(k, v);
                ok++;
                if (first != null && !shownRecord) {
                    shownRecord = true;
                    StringBuilder vals = new StringBuilder();
                    for (StoredValueNode svn : db.getTrans(db.internal().x().transInfo.tpos).getValueNodes()) {
                        vals.append(str(svn.getValueNode().value)).append(' ');
                    }
                    System.out.println("the first transaction committed after the failure (" + i + ", put "
                            + k + " = " + v + ") began with " + before + " nodes left over; its record holds"
                            + " the values: " + vals);
                }
            } catch (Throwable e) {
                failed++;
                if (first == null) { first = e; firstFail = i; report(db, e, i); }
                String msg = String.valueOf(e.getMessage());
                String key = e.getClass().getSimpleName() + ": " + (msg.length() > 120 ? msg.substring(0, 120) + "... (" + msg.length() + " chars)" : msg).replaceAll("[0-9]+", "N");
                Integer c = kinds.get(key);
                kinds.put(key, c == null ? 1 : c + 1);
                if (c == null && e != first) {
                    System.out.println("new kind of failure at transaction " + i + ": " + e.getClass().getName() + ": " + (msg.length() > 300 ? msg.substring(0, 300) + "... (" + msg.length() + " chars)" : msg));
                    StackTraceElement[] st = e.getStackTrace();
                    for (int q = 0; q < Math.min(6, st.length); q++) System.out.println("    at " + st[q]);
                }
            }
            if (i % 2000 == 0 && first != null) {
                Runtime rt = Runtime.getRuntime();
                System.out.println("  at " + i + ": committed " + ok + ", failed " + failed + ", left-over nodes "
                        + db.internal().x().transNodes.size() + ", heap used MB "
                        + (rt.totalMemory() - rt.freeMemory()) / 1000000);
            }
        }
        System.out.println("failure kinds: " + kinds);
        System.out.println("many: " + i + " transactions, " + ok + " committed, " + failed
                + " failed (the first at transaction " + firstFail + "); transactions that began with"
                + " nodes left over from a failed one: " + leftoverSeen);
        int wrong = 0;
        for (Map.Entry<String, String> e : model.entrySet()) {
            if (!e.getValue().equals(str(DbUtil.get(db, e.getKey())))) wrong++;
        }
        System.out.println("reads now against the committed values: " + wrong + " of " + model.size() + " differ");
        restartCheck(db, stream, model);
    }

    static void report(Db db, Throwable e, int i) {
        if (e == null) { System.out.println("no failure"); return; }
        System.out.println("FAILURE at transaction " + i + ": " + e);
        StackTraceElement[] st = e.getStackTrace();
        for (int k = 0; k < Math.min(8, st.length); k++) System.out.println("    at " + st[k]);
        System.out.println("super root ordinal " + superOrd(db) + ", newest written top "
                + (db.internal().newestWrittenTop() == null ? "null" : "" + db.internal().newestWrittenTop().topNodeId));
    }

    static void restart(Db db, MemoryStream stream, String[] keys) {
        StringBuilder before = new StringBuilder();
        for (String k : keys) before.append(k).append('=').append(str(DbUtil.get(db, k))).append(' ');
        try {
            db.sync(SyncLevel.STRONG);
            db.stop();
        } catch (Throwable e) {
            System.out.println("sync/stop FAILED: " + e);
        }
        MemoryStream copy = stream.copy();
        try {
            Db db2 = Db.builder().testSetup(copy).clock(clock).start();
            StringBuilder after = new StringBuilder();
            for (String k : keys) after.append(k).append('=').append(str(DbUtil.get(db2, k))).append(' ');
            System.out.println("restart: started; super root ordinal " + superOrd(db2));
            System.out.println("  reads before the restart: " + before);
            System.out.println("  reads after the restart:  " + after);
            next();
            try {
                db2.execute(db2.trans().put(keys[0], "after-restart").build());
                System.out.println("  a put after the restart succeeded");
            } catch (Throwable e) {
                System.out.println("  a put after the restart FAILED: " + e);
            }
            db2.stop();
        } catch (Throwable e) {
            System.out.println("restart FAILED: " + e);
        }
    }

    static void restartCheck(Db db, MemoryStream stream, Map<String, String> model) {
        try {
            db.sync(SyncLevel.STRONG);
            db.stop();
        } catch (Throwable e) {
            System.out.println("sync/stop FAILED: " + e);
        }
        try {
            Db db2 = Db.builder().testSetup(stream.copy()).clock(clock).start();
            int wrong = 0;
            for (Map.Entry<String, String> e : model.entrySet()) {
                if (!e.getValue().equals(str(DbUtil.get(db2, e.getKey())))) wrong++;
            }
            System.out.println("restart: started; super root ordinal " + superOrd(db2) + "; reads against"
                    + " the committed values: " + wrong + " of " + model.size() + " differ");
            db2.stop();
        } catch (Throwable e) {
            System.out.println("restart FAILED: " + e);
        }
    }
}
