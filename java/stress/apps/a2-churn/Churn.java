import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.TestNodeSize;
import bergdb.core.StoredTrans;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

import java.io.File;
import java.util.*;

/**
 * App 2 of 024-26: long-running overwrite and delete churn with reclaim on and a finite
 * retain duration, a clock that the application moves, restarts, and reads at older times.
 * The oracle keeps each key's versions; every check compares the database with it:
 * the latest state, states inside the retain duration (which must be available), states
 * older than it (correct or LookupTimeNotAvailableException), the transaction of a value
 * followed back through reclaim's copies (getTrans), and the stream's size against the
 * live data.
 *
 * Usage: java -cp bergdb-release.jar:out Churn SEED NODESIZE KEYS TRANSACTIONS DIR
 *            [retainMs] [stepMsMax] [fraction] [cacheBytes] [startupDistance]
 */
public class Churn {
    static Random rnd;
    static Db db;
    static File dir;
    static int nodeSize;
    static long cacheBytes;
    static int startupDistance;
    static int startupDistanceSet = -1;
    static boolean queue, big;
    static int queueSize;
    static long qHead, qTail;
    static final List<long[]> keptHistory = new ArrayList<>();
    static Common.ManualClock clock;
    static final Common.Model m = new Common.Model();
    static long retain;           // units
    static double fraction;
    static long txCount, opCount, restarts, checks, oldOk, oldGone, chainSteps;
    static long maxLiveStream, maxRatioMilli;
    static List<Common.K> universe = new ArrayList<>();

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        nodeSize = Integer.parseInt(a[1]);
        int nKeys = Integer.parseInt(a[2]);
        long nTx = Long.parseLong(a[3]);
        dir = new File(a[4]);
        long retainMs = a.length > 5 ? Long.parseLong(a[5]) : 2000;
        int stepMsMax = a.length > 6 ? Integer.parseInt(a[6]) : 40;
        fraction = a.length > 7 ? Double.parseDouble(a[7]) : 0.25;
        cacheBytes = a.length > 8 ? Long.parseLong(a[8]) : 0;
        startupDistance = a.length > 9 ? Integer.parseInt(a[9]) : 500_000;
        queue = a.length > 10 && a[10].equals("queue");
        big = a.length > 10 && a[10].equals("big");
        queueSize = nKeys;
        retain = retainMs * Clock.UNITS_PER_SEC / 1000;
        rnd = new Random(seed);
        Common.rmrf(dir);
        dir.mkdirs();
        clock = new Common.ManualClock(1_778_000_000_000L * 10_000L);
        for (int i = 0; i < nKeys; i++) universe.add(new Common.K(key(i)));
        long t0 = System.currentTimeMillis();
        try {
            start();
            db.setRetainDuration(retain);
            if (fraction != 0.25) db.setReclaimInternalFraction(fraction);
            Common.check(db.getRetainDuration() == retain, "getRetainDuration after set");
            long nextRestart = 200 + rnd.nextInt(400);
            for (long i = 0; i < nTx; i++) {
                clock.advanceMillis(rnd.nextInt(stepMsMax + 1));
                transaction(i);
                if (i % 50 == 49) verify("tx " + i);
                if (i % 700 == 350 && rnd.nextInt(3) == 0) {
                    int sd = 400_000 + rnd.nextInt(4_000_000);
                    db.setStartupDistance(sd);
                    Common.check(db.getStartupDistance() == sd, "getStartupDistance " + db.getStartupDistance() + " after set " + sd);
                    startupDistanceSet = sd;
                }
                if (i == nextRestart) {
                    restart();
                    verify("tx " + i + " after restart");
                    nextRestart = i + 200 + rnd.nextInt(600);
                }
                if (i % 2000 == 1999) progress(i);
            }
            restart();
            verify("final after restart");
            progress(nTx);
            db.close();
            StringBuilder kh = new StringBuilder();
            for (long[] x : keptHistory) kh.append(" ").append(x[0]).append(":").append(x[1] / 1000).append("k");
            Common.log("stream kept (from the first available position) by transaction:" + kh);
        } catch (Common.Fail f) {
            System.out.println("FAIL Churn seed " + seed + " node " + nodeSize + ": " + f.getMessage());
            System.out.println("  after " + txCount + " transactions, " + restarts + " restarts; clock " + clock.getTime()
                    + ", first available " + safeFa());
            try { db.close(); } catch (Throwable t) { }
            System.exit(1);
        } catch (Throwable t) {
            System.out.println("FAIL (exception) Churn seed " + seed + " node " + nodeSize + ": " + t);
            t.printStackTrace(System.out);
            System.out.println("  after " + txCount + " transactions, " + restarts + " restarts");
            try { db.close(); } catch (Throwable x) { }
            System.exit(2);
        }
        Common.log("OK Churn seed " + seed + " node " + nodeSize + " keys " + nKeys + ": " + txCount + " transactions, "
                + opCount + " operations, " + restarts + " restarts, " + checks + " checks, old reads " + oldOk
                + " ok and " + oldGone + " cut, chain steps " + chainSteps + ", max live stream " + maxLiveStream + ", max ratio " + (maxRatioMilli / 1000.0) + ", "
                + (System.currentTimeMillis() - t0) + " ms");
    }

    static long safeFa() { try { return db.getFirstAvailableLookupTime(); } catch (Throwable t) { return -1; } }

    static byte[] key(int i) {
        // three groups: short keys, keys with a shared long prefix, keys in time order (a log)
        switch (i % 3) {
            case 0: return new byte[] {0x10, (byte) (i >>> 16), (byte) (i >>> 8), (byte) i};
            case 1: {
                byte[] k = new byte[24];
                Arrays.fill(k, (byte) 0x41);
                k[0] = 0x20;
                k[21] = (byte) (i >>> 16); k[22] = (byte) (i >>> 8); k[23] = (byte) i;
                return k;
            }
            default: {
                byte[] k = new byte[9];
                k[0] = 0x30;
                k[1] = (byte) ((i % 97) * 2);
                k[6] = (byte) (i >>> 16); k[7] = (byte) (i >>> 8); k[8] = (byte) i;
                return k;
            }
        }
    }

    static void start() throws Exception {
        DbBuilder b = TestNodeSize.builder(nodeSize).mainStream(new FileStream(dir, false)).clock(clock);  // TestNodeSize: since 026-08 the size setters are package-private (028-23)
        if (cacheBytes > 0) b.cacheSizeIndicator(cacheBytes);
        b.startupDistance(startupDistance);
        db = b.start();
    }

    static void restart() throws Exception {
        if (rnd.nextBoolean()) db.stop();
        db.close();
        start();
        restarts++;
        Common.check(db.getRetainDuration() == retain, "retain duration after restart: " + db.getRetainDuration());
        if (startupDistanceSet > 0) Common.check(db.getStartupDistance() == startupDistanceSet, "startup distance after restart: "
                + db.getStartupDistance() + ", set " + startupDistanceSet);
        Common.check(Math.abs(db.getInternalFraction() - fraction) < 1e-4, "fraction after restart: " + db.getInternalFraction());
    }

    static byte[] val(long i) {
        int r = rnd.nextInt(1000);
        byte[] v;
        if (r < 700) v = Common.value(rnd, 40);
        else if (r < 990) v = Common.value(rnd, 400);
        else if (r < 999) v = Common.value(rnd, 5000);
        else v = Common.value(rnd, 120_000);
        if (v.length >= 8) for (int j = 0; j < 8; j++) v[j] = (byte) (i >>> (8 * j));
        return v;
    }

    static byte[] qkey(long q) {
        return new byte[] {0x40, (byte) (q >>> 32), (byte) (q >>> 24), (byte) (q >>> 16), (byte) (q >>> 8), (byte) q};
    }

    /** A queue: new keys in time order at the tail, the oldest deleted at the head. */
    static void queueTransaction(long i) {
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        int puts = 1 + rnd.nextInt(60);
        for (int j = 0; j < puts; j++) ops.put(new Common.K(qkey(qTail++)), val(i));
        while (qTail - qHead > queueSize && ops.size() < Db.MAX_OPERATIONS) ops.put(new Common.K(qkey(qHead++)), Common.DELETED);
        Trans.Builder b = db.trans();
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
            if (e.getValue() == Common.DELETED) b.delete(e.getKey().b);
            else b.put(e.getKey().b, e.getValue());
        }
        Trans t = b.build();
        db.execute(t);
        m.apply(ops, t.tt);
        txCount++;
        opCount += ops.size();
    }

    /** Large values: 1 to 4 keys of 30 a transaction, values up to 8 MiB (L4), up to 32 MiB a transaction (L5). */
    static void bigTransaction(long i) {
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        int n = 1 + rnd.nextInt(4);
        long bytes = 0;
        for (int j = 0; j < n; j++) {
            Common.K k = universe.get(rnd.nextInt(Math.min(30, universe.size())));
            int x = rnd.nextInt(10);
            byte[] v;
            if (x < 2) v = Common.DELETED;
            else {
                int len = x < 5 ? rnd.nextInt(1000) : x < 8 ? rnd.nextInt(1 << 20) : Db.MAX_VALUE_BYTES - rnd.nextInt(10);
                if (bytes + len + 8 > Db.MAX_TRANS_BYTES) break;
                v = new byte[len];
                rnd.nextBytes(v);
                bytes += len + k.b.length;
            }
            ops.remove(k);
            ops.put(k, v);
        }
        Trans.Builder b = db.trans();
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
            if (e.getValue() == Common.DELETED) b.delete(e.getKey().b);
            else b.put(e.getKey().b, e.getValue());
        }
        Trans t = b.build();
        db.execute(t);
        m.apply(ops, t.tt);
        txCount++;
        opCount += ops.size();
    }

    static void transaction(long i) {
        if (queue) { queueTransaction(i); return; }
        if (big) { bigTransaction(i); return; }
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        int kind = rnd.nextInt(100);
        int n = kind < 70 ? 1 + rnd.nextInt(20) : kind < 95 ? 1 + rnd.nextInt(200) : 1 + rnd.nextInt(500);
        Trans.Builder b = db.trans();
        if (kind < 3 && !m.latest.isEmpty()) {
            // a ranged delete of up to 500 live keys from a random key on
            Common.K from = universe.get(rnd.nextInt(universe.size()));
            for (Common.K k : m.latest.tailMap(from, true).keySet()) {
                if (ops.size() >= n) break;
                ops.put(k, Common.DELETED);
            }
        } else {
            int hotFrom = (int) ((i / 500) * 37 % universe.size());
            for (int j = 0; j < n; j++) {
                Common.K k;
                if (rnd.nextInt(3) == 0) k = universe.get((hotFrom + rnd.nextInt(200)) % universe.size());
                else k = universe.get(rnd.nextInt(universe.size()));
                int x = rnd.nextInt(10);
                ops.remove(k);
                ops.put(k, x < 3 ? Common.DELETED : val(i));
            }
        }
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
            if (e.getValue() == Common.DELETED) b.delete(e.getKey().b);
            else b.put(e.getKey().b, e.getValue());
        }
        Trans t = b.build();
        db.execute(t);
        m.apply(ops, t.tt);
        txCount++;
        opCount += ops.size();
    }

    static void verify(String what) {
        long now = db.currentTime();
        long fa = db.getFirstAvailableLookupTime();
        // The retain duration's promise: the states of the last 'retain' units are available.
        // Asked with the model's transaction times: the newest one at or before now - retain.
        if (fa > now - retain) {
            throw new Common.Fail(what + ": first available lookup time " + fa + " is after now - retain (now "
                    + now + ", retain " + retain + "): " + (fa - (now - retain)) + " units inside the retain duration");
        }
        int cnt = Common.verifyFull(db, m, Long.MAX_VALUE, what + " latest");
        Common.check(cnt == m.liveCount(), what + ": count");
        Common.verifyGets(db, m, Long.MAX_VALUE, rnd, 100, what);
        for (int i = 0; i < 5; i++) Common.verifyRange(db, m, Long.MAX_VALUE, rnd, what);
        checks += 106;

        // Old reads: inside the retain duration they must work; before it, work or be cut.
        List<Long> ts = new ArrayList<>(m.times.keySet());
        for (int i = 0; i < 4 && !ts.isEmpty(); i++) {
            long t = ts.get(rnd.nextInt(ts.size()));
            if (rnd.nextBoolean()) t -= 1;
            boolean mustWork = t >= now - retain;
            try {
                Common.verifyFull(db, m, t, what + " old " + t + (mustWork ? " (inside retain)" : ""));
                Common.verifyGets(db, m, t, rnd, 30, what + " old " + t);
                Common.verifyRange(db, m, t, rnd, what + " old " + t);
                oldOk++;
                checks += 32;
            } catch (RuntimeException e) {
                if (!Common.isNotAvailable(e)) throw e;
                long fa2 = db.getFirstAvailableLookupTime();
                if (mustWork) throw new Common.Fail(what + ": read at " + t + " inside the retain duration (now " + now
                        + ") was cut; first available " + fa2);
                Common.check(fa2 > t, what + ": LookupTimeNotAvailable at " + t + " but first available is " + fa2);
                oldGone++;
            }
        }
        verifyChains(what);

        // Storage: the stream from the first available position, against the live data.
        long live = 0;
        for (Map.Entry<Common.K, byte[]> e : m.latest.entrySet()) live += e.getKey().b.length + e.getValue().length;
        long streamLive = db.getStreamLength() - db.getFirstAvailablePos();
        maxLiveStream = Math.max(maxLiveStream, streamLive);
        if (live > 0) maxRatioMilli = Math.max(maxRatioMilli, streamLive * 1000 / live);

        // Forget the model's history before the first available time.
        long fa3 = db.getFirstAvailableLookupTime();
        m.prune(Math.min(fa3, now - retain) - 1);
    }

    /** For sampled live keys, follow getTrans back through reclaim's copies to the write. */
    static void verifyChains(String what) {
        List<Common.K> live = new ArrayList<>(m.latest.keySet());
        if (live.isEmpty()) return;
        GetData gd = db.newGetData();
        for (int i = 0; i < 5; i++) {
            Common.K k = live.get(rnd.nextInt(live.size()));
            long wt = m.writeTimeAt(k, Long.MAX_VALUE);
            long t = Long.MAX_VALUE;
            for (int hop = 0; hop < 1000; hop++) {
                byte[] v;
                try {
                    v = db.getOne(t, Keys.toSegments(k.b), gd);
                } catch (RuntimeException e) {
                    if (Common.isNotAvailable(e)) break;     // the chain reached the cut
                    throw e;
                }
                Common.check(Arrays.equals(v, m.latest.get(k)), what + ": chain get of " + k + " at " + t + " gave "
                        + Common.hex(v) + ", expected " + Common.hex(m.latest.get(k)) + " (write time " + wt + ")");
                StoredTrans st;
                try {
                    st = db.getTrans(gd.tpos);
                } catch (RuntimeException e) {
                    if (Common.isNotAvailable(e)) break;
                    throw e;
                }
                if (st.tt == wt) break;
                Common.check(st.tt > wt, what + ": chain of " + k + " reached tt " + st.tt + " before the write " + wt);
                if (st.tt - 1 < db.getFirstAvailableLookupTime()) break;
                t = st.tt - 1;
                chainSteps++;
                if (t < wt) throw new Common.Fail(what + ": chain of " + k + " passed the write time");
            }
        }
    }

    static void progress(long i) {
        keptHistory.add(new long[] {i, db.getStreamLength() - db.getFirstAvailablePos()});
        Common.log("tx " + i + ": live " + m.liveCount() + ", stream " + db.getStreamLength() + ", first pos "
                + db.getFirstAvailablePos() + ", files " + Common.dirBytes(dir) + ", reclaim iterations "
                + db.getReclaimIterationCount() + ", old ok " + oldOk + ", cut " + oldGone + ", restarts " + restarts
                + ", ratio " + (maxRatioMilli / 1000.0));
    }
}
