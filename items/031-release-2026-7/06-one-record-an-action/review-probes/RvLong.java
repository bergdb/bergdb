package bergdb.core;

import java.util.*;

import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe of bergdb 031-06 (2026-11-27), F6: a key of BergDB's own prefix "/#", longer
 * than the 60 segments that the item's record limit assumes for a step's last KV, put
 * through the Core API (Trans.Builder.putLongKey), and copied by a commit's step.
 *
 * Usage: java -ea -cp OUT:JAR bergdb.core.RvLong SEGMENTS [NODE]
 *   -Dlimit=N: a lowered record limit (StoredTrans.recordLimit), to see what follows when a
 *   record's dirty set passes the room of every later record (F5's consequence).
 *   -Dwhen=after (the default): the limit lowered after the key's record, as the review ran
 *   it; before: in force from the start, as a limit is in production; plan: lowered after the
 *   key's transaction is admitted, before its plan (031-06's landing, step 2: the key's
 *   transaction is refused by 005-31 with before, and with plan its record is not written:
 *   Db.checkTakeable fails the database).
 */
public class RvLong {
    static long s0(Db db) {
        try { return db.getStreamLength(); } catch (Throwable e) { return -1; }
    }
    public static void main(String[] args) throws Exception {
        final long SEC = Clock.UNITS_PER_SEC;
        int segments = Integer.parseInt(args[0]);
        int node = args.length > 1 ? Integer.parseInt(args[1]) : 0;
        final long saved = StoredTrans.recordLimit;
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        DbBuilder b = Db.builder().testSetup(new CutStream()).clock(clock);
        if (node == 8) b.maxNodeSize8();
        Db db = b.start();
        db.setStartupDistance(2000);
        db.setRetainDuration(SEC);
        StringBuilder k = new StringBuilder("/#u");
        for (int i = 0; i < segments - 1; i++) k.append("/s").append(String.format("%04d", i % 10000));
        final long[] key = Keys.toSegments(k.toString());
        Random r = new Random(1);
        byte[] v = new byte[100];
        r.nextBytes(v);
        final String when = System.getProperty("when", "after");
        final long limit = Long.getLong("limit", 0);
        if (limit > 0 && when.equals("before")) StoredTrans.recordLimit = limit;
        if (limit > 0 && when.equals("plan")) {
            Db.testHooks = new Db.TestHooks() {
                public void beforePlan(Db.ExecuteData x) { StoredTrans.recordLimit = limit; }
                public void transExecuted(Db.ExecuteData x) {}
                public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
                public void nodeTouched(bergdb.dag.Node node) {}
                public void nodeReplaced(bergdb.dag.Node node) {}
            };
        }
        final long length0 = db.getStreamLength();
        try {
            db.execute(db.trans().putLongKey(key, null, v, null).build());
        } catch (Throwable e) {
            Db.testHooks = null;
            Throwable c = e;
            while (c.getCause() != null) c = c.getCause();
            System.out.println("RvLong: a key of " + key.length + " segments (" + Trans.keyBytes(key)
                    + " bytes) under \"/#\", the record limit " + limit + " " + when + ": "
                    + (e instanceof bergdb.pub.util.DbException ? "refused" : "failed") + ", "
                    + e.getClass().getSimpleName() + (c != e ? " (" + c.getClass().getSimpleName() + ")" : "")
                    + ": " + c.getMessage() + "; the stream's length " + length0 + " before, " + s0(db) + " after");
            try { db.close(); } catch (Throwable x) {}
            StoredTrans.recordLimit = saved;
            return;
        }
        Db.testHooks = null;
        // The limit is lowered after the key is in the stream: its own transaction is
        // admitted by the release's limit, as a transaction near that limit would be.
        if (limit > 0 && when.equals("after")) StoredTrans.recordLimit = limit;
        Reclaim.Stats stats = db.internal().reclaim().enableStats();
        long copies = 0, maxRecord = 0, maxDirtied = 0;
        boolean copied = false;
        for (int i = 0; i < 400; i++) {
            time += SEC / 20; clock.setTime(time);
            byte[] val = new byte[3000];
            r.nextBytes(val);
            long l0 = db.getStreamLength();
            db.execute(db.trans().put("/h/" + (i % 5), val).build());
            maxRecord = Math.max(maxRecord, db.getStreamLength() - l0);
            bergdb.dag.GetData gd = db.newGetData();
            byte[] got = db.getOne(Long.MAX_VALUE, key, gd);
            if (!Arrays.equals(got, v)) throw new AssertionError("the long key's value");
            if (gd.tpos > 0) {
                for (StoredNode sn : db.getTrans(gd.tpos).nodes) {
                    if (sn instanceof StoredValueNode && Arrays.equals(key, ((StoredValueNode) sn).getKey())
                            && ((StoredValueNode) sn).isCopy()) copied = true;
                }
            }
        }
        for (Reclaim.Stats.Iteration st : stats.iterations) { copies += st.values; maxDirtied = Math.max(maxDirtied, st.maxStepDirtied); }
        System.out.println("RvLong: a key of " + key.length + " segments (" + Trans.keyBytes(key) + " bytes) under \"/#\", put by "
                + "Trans.Builder.putLongKey: accepted; its value node is a copy of a commit's step: " + copied + "; " + copies
                + " copies in all, the most index nodes one record made dirty " + maxDirtied + ", the largest record " + maxRecord
                + " bytes; first available position " + db.getFirstAvailablePos() + ", startup pos "
                + db.internal().getStartupPosForEvict() + ", stream length " + db.getStreamLength()
                + (Long.getLong("limit", 0) > 0 ? " (record limit " + StoredTrans.recordLimit + ", cap " + StoredTrans.recordCap() + ")" : ""));
        db.close();
        StoredTrans.recordLimit = saved;
    }
}
