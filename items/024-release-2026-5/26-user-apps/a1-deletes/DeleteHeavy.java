import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.StoredTrans;
import bergdb.core.StoredValueNode;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.stream.FileStream;

import java.io.File;
import java.util.*;

/**
 * App 1 of 024-26: a delete-heavy workload against a Core Db. Bulk loads, scattered and
 * ranged deletes, deletes of most keys, refills, builders whose last call wins, over many
 * transactions and restarts, with keys of several shapes (short, shared prefixes, lengths
 * at the 7-byte segment edges, keys that extend each other, up to 111 bytes). Every state
 * is checked against an in-memory oracle: full scans, gets, range scans forward and
 * backward, reads at older times, and the transaction of a value (getTrans).
 *
 * Usage: java -cp bergdb-release.jar:out DeleteHeavy SEED NODESIZE N ROUNDS DIR [cacheBytes]
 */
public class DeleteHeavy {
    static Random rnd;
    static Db db;
    static File dir;
    static int nodeSize;
    static long cacheBytes;
    static final Common.Model m = new Common.Model();
    static long txCount, opCount, restarts, checks, refused;
    static final List<Long> oldTimes = new ArrayList<>();
    static int keyCounter;

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        nodeSize = Integer.parseInt(a[1]);
        int n = Integer.parseInt(a[2]);
        int rounds = Integer.parseInt(a[3]);
        dir = new File(a[4]);
        cacheBytes = a.length > 5 ? Long.parseLong(a[5]) : 0;
        rnd = new Random(seed);
        Common.rmrf(dir);
        dir.mkdirs();
        long t0 = System.currentTimeMillis();
        try {
            start();
            for (int r = 0; r < rounds; r++) round(r, n);
            restart("final");
            verifyAll("final");
            db.close();
        } catch (Common.Fail f) {
            System.out.println("FAIL seed " + seed + " node " + nodeSize + ": " + f.getMessage());
            System.out.println("  after " + txCount + " transactions, " + restarts + " restarts");
            try { db.close(); } catch (Throwable t) { }
            System.exit(1);
        } catch (Throwable t) {
            System.out.println("FAIL (exception) seed " + seed + " node " + nodeSize + ": " + t);
            t.printStackTrace(System.out);
            System.out.println("  after " + txCount + " transactions, " + restarts + " restarts");
            try { db.close(); } catch (Throwable x) { }
            System.exit(2);
        }
        Common.log("OK DeleteHeavy seed " + seed + " node " + nodeSize + " n " + n + " rounds " + rounds
                + ": " + txCount + " transactions, " + opCount + " operations, " + restarts + " restarts, "
                + checks + " checks, " + refused + " refused, live " + m.liveCount() + ", stream " + Common.dirBytes(dir) + " bytes, "
                + (System.currentTimeMillis() - t0) + " ms");
    }

    static void start() throws Exception {
        DbBuilder b = Db.builder().mainStream(new FileStream(dir, false));
        if (nodeSize == 8) b.maxNodeSize8();
        else if (nodeSize == 14) b.maxNodeSize14();
        else if (nodeSize == 62) b.maxNodeSize62();
        else b.maxNodeSize30();
        if (cacheBytes > 0) b.cacheSizeIndicator(cacheBytes);
        db = b.start();
    }

    static void restart(String why) throws Exception {
        if (rnd.nextInt(4) == 0) {
            db.stop();                 // stop, then close waits for it
        }
        db.close();
        start();
        restarts++;
    }

    // ---- keys ----

    static byte[] newKey() {
        int c = keyCounter++;
        int shape = rnd.nextInt(6);
        switch (shape) {
            case 0: { // 0x10 + 4 bytes: one segment
                return new byte[] {0x10, (byte) (c >>> 24), (byte) (c >>> 16), (byte) (c >>> 8), (byte) c};
            }
            case 1: { // 0x20 + 13 shared bytes + 4 bytes: 18 bytes, shared segment trees
                byte[] k = new byte[18];
                k[0] = 0x20;
                for (int i = 1; i < 14; i++) k[i] = (byte) ('a' + (c % 3));
                k[14] = (byte) (c >>> 24); k[15] = (byte) (c >>> 16); k[16] = (byte) (c >>> 8); k[17] = (byte) c;
                return k;
            }
            case 2: { // 0x30 + random tail, length 2..111
                int len = 2 + rnd.nextInt(Db.MAX_KEY_BYTES - 1);
                byte[] k = new byte[len];
                rnd.nextBytes(k);
                k[0] = 0x30;
                k[1] = (byte) (c & 0x0f);
                return k;
            }
            case 3: { // 0x40, exactly 7j bytes (ends with an empty segment), j = 1..15
                int j = 1 + rnd.nextInt(15);
                byte[] k = new byte[7 * j];
                k[0] = 0x40;
                for (int i = 1; i < k.length; i++) k[i] = (byte) (i * 31);
                int p = k.length - 1;
                k[p] = (byte) c; if (p - 1 > 0) k[p - 1] = (byte) (c >>> 8); if (p - 2 > 0) k[p - 2] = (byte) (c >>> 16);
                return k;
            }
            case 4: { // 0x50: keys that extend each other: 50 c c c then zeros, length 4..60
                int len = 4 + rnd.nextInt(57);
                byte[] k = new byte[len];
                k[0] = 0x50; k[1] = (byte) (c % 7); k[2] = 0x61; k[3] = (byte) ((c / 7) % 5);
                return k;
            }
            default: { // 0x60: dense small keys: 60 + 2 bytes
                return new byte[] {0x60, (byte) (c >>> 8), (byte) c};
            }
        }
    }

    static byte[] val() {
        int r = rnd.nextInt(100);
        if (r < 60) return Common.value(rnd, 16);
        if (r < 95) return Common.value(rnd, 200);
        return Common.value(rnd, 5000);
    }

    // ---- transactions ----

    /** Runs a transaction from a list of calls (key, value or DELETED), last call wins. */
    static void runCalls(List<Map.Entry<Common.K, byte[]>> calls) {
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        Trans.Builder b = db.trans();
        for (Map.Entry<Common.K, byte[]> c : calls) {
            if (c.getValue() == Common.DELETED) b.delete(c.getKey().b);
            else b.put(c.getKey().b, c.getValue());
            ops.remove(c.getKey());
            ops.put(c.getKey(), c.getValue());
        }
        Trans t = b.build();
        long len0 = db.getStreamLength();
        if (ops.size() > Db.MAX_OPERATIONS) {
            try {
                db.execute(t);
                throw new Common.Fail("transaction of " + ops.size() + " operations was accepted");
            } catch (bergdb.pub.util.DbException e) {
                Common.check(db.getStreamLength() == len0, "refused transaction changed the stream length");
                refused++;
                return;
            }
        }
        db.execute(t);
        m.apply(ops, t.tt);
        txCount++;
        opCount += ops.size();
        if (rnd.nextInt(50) == 0) oldTimes.add(t.tt);
    }

    static Map.Entry<Common.K, byte[]> e(Common.K k, byte[] v) { return new AbstractMap.SimpleEntry<>(k, v); }

    /** Runs the ops as transactions of 1 to 500 operations, with some noise calls. */
    static void runBatches(List<Map.Entry<Common.K, byte[]>> ops) {
        int i = 0;
        while (i < ops.size()) {
            int size = rnd.nextInt(4) == 0 ? Db.MAX_OPERATIONS : 1 + rnd.nextInt(Db.MAX_OPERATIONS);
            int end = Math.min(ops.size(), i + size);
            List<Map.Entry<Common.K, byte[]>> calls = new ArrayList<>(ops.subList(i, end));
            // Noise: calls on the same keys before the real ones; the last call wins.
            int noise = rnd.nextInt(3) == 0 ? rnd.nextInt(5) : 0;
            for (int j = 0; j < noise && !calls.isEmpty(); j++) {
                Common.K k = calls.get(rnd.nextInt(calls.size())).getKey();
                calls.add(0, e(k, rnd.nextBoolean() ? Common.DELETED : val()));
            }
            runCalls(calls);
            i = end;
        }
    }

    static List<Common.K> liveKeys() { return new ArrayList<>(m.latest.keySet()); }

    // ---- phases ----

    static void round(int r, int n) throws Exception {
        List<Map.Entry<Common.K, byte[]>> ops = new ArrayList<>();

        // 1. Bulk load: n new keys, in random order.
        for (int i = 0; i < n; i++) ops.add(e(new Common.K(newKey()), val()));
        // Edge keys: the empty key, zeros, 0xff runs, 7 and 8 bytes of zeros (Db, "Keys and values").
        byte[][] edge = {{}, {0}, {0, 0}, new byte[7], new byte[8], {(byte) 0xff}, {(byte) 0xff, (byte) 0xff},
                {(byte) 0xff, 0}, new byte[14], new byte[Db.MAX_KEY_BYTES]};
        for (byte[] k : edge) if (rnd.nextInt(3) > 0) ops.add(rnd.nextInt(ops.size() + 1), e(new Common.K(k), val()));
        runBatches(ops);
        phaseEnd(r, "load");

        // 2. Scattered deletes: a random third of the live keys, with a few puts mixed in.
        ops.clear();
        for (Common.K k : liveKeys()) if (rnd.nextInt(3) == 0) ops.add(e(k, Common.DELETED));
        Collections.shuffle(ops, rnd);
        for (int i = 0; i < ops.size() / 50; i++) ops.add(rnd.nextInt(ops.size()), e(new Common.K(newKey()), val()));
        runBatches(ops);
        phaseEnd(r, "scattered");

        // 3. Ranged deletes: a few contiguous runs of the sorted live keys, in key order.
        for (int j = 0; j < 4; j++) {
            List<Common.K> live = liveKeys();
            if (live.size() < 10) break;
            int from = rnd.nextInt(live.size());
            int len = Math.min(live.size() - from, 1 + rnd.nextInt(Math.max(1, live.size() / 5)));
            ops.clear();
            for (int i = from; i < from + len; i++) ops.add(e(live.get(i), Common.DELETED));
            if (rnd.nextBoolean()) Collections.reverse(ops);
            runBatches(ops);
        }
        phaseEnd(r, "ranged");

        // 4. Delete most: keep every 30th key (by key order).
        ops.clear();
        List<Common.K> live = liveKeys();
        for (int i = 0; i < live.size(); i++) if (i % 30 != 0) ops.add(e(live.get(i), Common.DELETED));
        if (rnd.nextBoolean()) Collections.shuffle(ops, rnd);
        runBatches(ops);
        phaseEnd(r, "most");

        // 5. Refill: keys deleted in this round put again, half with new values, and new keys.
        ops.clear();
        int refill = 0;
        for (Common.K k : m.hist.keySet()) {
            if (!m.latest.containsKey(k) && rnd.nextInt(3) == 0 && refill < n / 2) { ops.add(e(k, val())); refill++; }
        }
        for (int i = 0; i < n / 2; i++) ops.add(e(new Common.K(newKey()), val()));
        Collections.shuffle(ops, rnd);
        runBatches(ops);
        phaseEnd(r, "refill");

        // 6. Churn on a hot range: put, delete, put the same keys in successive transactions;
        // deletes of absent keys; transactions of 501 calls on 500 keys (last call wins).
        live = liveKeys();
        if (!live.isEmpty()) {
            int from = rnd.nextInt(live.size());
            List<Common.K> hot = new ArrayList<>(live.subList(from, Math.min(live.size(), from + 300)));
            for (int it = 0; it < 30; it++) {
                List<Map.Entry<Common.K, byte[]>> calls = new ArrayList<>();
                for (Common.K k : hot) {
                    int x = rnd.nextInt(3);
                    if (x == 0) calls.add(e(k, Common.DELETED));
                    else if (x == 1) calls.add(e(k, val()));
                }
                for (int j = 0; j < 5; j++) calls.add(e(new Common.K(new byte[] {0x70, (byte) j, (byte) it}), Common.DELETED));
                runCalls(calls);
            }
            // 501 calls, 500 keys: accepted.
            List<Map.Entry<Common.K, byte[]>> calls = new ArrayList<>();
            List<Common.K> keys500 = new ArrayList<>();
            for (int j = 0; j < 500; j++) keys500.add(j < live.size() ? live.get((from + j) % live.size()) : new Common.K(newKey()));
            Set<Common.K> distinct = new LinkedHashSet<>(keys500);
            for (Common.K k : distinct) calls.add(e(k, rnd.nextBoolean() ? Common.DELETED : val()));
            Common.K first = distinct.iterator().next();
            calls.add(e(first, val()));
            runCalls(calls);
            // 501 distinct keys: refused, nothing written.
            calls.clear();
            for (Common.K k : distinct) calls.add(e(k, Common.DELETED));
            while (calls.size() <= 500) calls.add(e(new Common.K(newKey()), val()));
            runCalls(calls);
        }
        phaseEnd(r, "churn");

        // 7. Delete everything of one shape, then all but a few keys.
        int shape = 0x10 * (1 + rnd.nextInt(6));
        ops.clear();
        for (Common.K k : liveKeys()) if (k.b.length > 0 && (k.b[0] & 0xf0) == shape) ops.add(e(k, Common.DELETED));
        runBatches(ops);
        phaseEnd(r, "shape" + Integer.toHexString(shape));
        if (r % 3 == 2) {
            ops.clear();
            live = liveKeys();
            for (int i = 0; i < live.size(); i++) if (i % 997 != 0) ops.add(e(live.get(i), Common.DELETED));
            runBatches(ops);
            phaseEnd(r, "nearly-all");
        }
    }

    static void phaseEnd(int r, String phase) throws Exception {
        String what = "round " + r + " " + phase;
        verifyLatest(what);
        if (rnd.nextInt(2) == 0) {
            restart(what);
            verifyAll(what + " after restart");
        } else if (rnd.nextInt(3) == 0) {
            verifyOld(what);
        }
        Common.log(what + ": live " + m.liveCount() + ", tx " + txCount + ", restarts " + restarts
                + ", stream " + db.getStreamLength());
    }

    static void verifyLatest(String what) {
        int cnt = Common.verifyFull(db, m, Long.MAX_VALUE, what + " full scan");
        Common.check(cnt == m.liveCount(), what + ": count");
        Common.verifyGets(db, m, Long.MAX_VALUE, rnd, 300, what);
        for (int i = 0; i < 20; i++) Common.verifyRange(db, m, Long.MAX_VALUE, rnd, what);
        for (int i = 0; i < 10; i++) Common.verifyPrefix(db, m, Long.MAX_VALUE, rnd, what);
        verifyTrans(what);
        checks += 322;
    }

    static void verifyOld(String what) {
        for (int i = 0; i < 3 && !oldTimes.isEmpty(); i++) {
            long t = oldTimes.get(rnd.nextInt(oldTimes.size()));
            Common.verifyFull(db, m, t, what + " full scan at old time " + t);
            Common.verifyGets(db, m, t, rnd, 100, what + " old " + t);
            for (int j = 0; j < 5; j++) Common.verifyRange(db, m, t, rnd, what + " old " + t);
            for (int j = 0; j < 5; j++) Common.verifyPrefix(db, m, t, rnd, what + " old " + t);
            // a time between two transactions
            Common.verifyFull(db, m, t - 1, what + " full scan at " + (t - 1));
            checks += 108;
        }
    }

    static void verifyAll(String what) {
        verifyLatest(what);
        verifyOld(what);
    }

    /** For sampled live keys: getOne's tpos names the transaction that wrote the value. */
    static void verifyTrans(String what) {
        List<Common.K> live = liveKeys();
        if (live.isEmpty()) return;
        GetData gd = db.newGetData();
        for (int i = 0; i < 10; i++) {
            Common.K k = live.get(rnd.nextInt(live.size()));
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(k.b), gd);
            Common.check(Arrays.equals(v, m.latest.get(k)), what + ": getOne " + k);
            StoredTrans st = db.getTrans(gd.tpos);
            long wt = m.writeTimeAt(k, gd.actualLookupTime);
            Common.check(st.tt == wt, what + ": getTrans(tpos).tt " + st.tt + " != write time " + wt + " of " + k);
            boolean found = false;
            for (StoredValueNode n : st.getValueNodes()) if (Arrays.equals(Keys.toBytes(n.getKey()), k.b)) found = true;
            Common.check(found, what + ": the transaction of " + k + " does not list the key");
        }
    }
}
