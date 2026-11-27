import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

import java.io.File;
import java.util.*;

/**
 * B1 of 026-13: mass deletes and back to empty with reclaim (bergdb 026-05, P8: each reclaim
 * step scans at its own time), with restarts during the deletes and the drive after them,
 * written from the Javadoc of Db (setRetainDuration, maintain, getFirstAvailablePos,
 * getStreamLength), Trans.Builder and GetMany only.
 *
 * A round: a load of N keys of many shapes (the empty key, 00 and FF runs, keys of up to
 * 111 bytes, extensions of each other); a mass delete in key order, in reverse, at random,
 * or of all but every 100th key, with new keys put above the largest and below the smallest
 * meanwhile (and deleted too); then a drive of small transactions on a moving clock, or of
 * maintain() calls only (Db.maintain: "brings a database that has been emptied to about the
 * stream of a fresh one"). The oracle checks the database (full scans, gets, range and
 * prefix scans, reads at older times inside the retain duration) after every phase and
 * restart. The stream kept, getStreamLength() - getFirstAvailablePos(), is compared with a
 * fresh twin: a new database with the same settings and the same live KVs, given the same
 * drive. Printed: the lag, the first drive transaction from which the kept stream stays at
 * most twice the twin's largest, and the ratio at the end; a ratio over 2 at the end is a
 * FAIL (storage proportional to the KVs stored).
 *
 * Usage: java -cp bergdb-release.jar:out BackToEmpty SEED NODESIZE KEYS ROUNDS DIR [DRIVE] [cacheBytes] [startupDistance]
 */
public class BackToEmpty {
    static Random rnd;
    static File dir;
    static int nodeSize;
    static long cacheBytes;
    static int sd;
    static Db db;
    static Common.ManualClock clock;
    static Common.Model m = new Common.Model();
    static final long RETAIN = Clock.UNITS_PER_SEC;          // 1 s
    static long restarts, checks, txs;
    static long serial;
    static final boolean TRACE = Boolean.getBoolean("trace");
    static final boolean MAINTAIN = Boolean.getBoolean("maintain");

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        nodeSize = Integer.parseInt(a[1]);
        if (nodeSize != 30) throw new IllegalArgumentException("node size 30 only");  // 026-08: every database a user makes has the node size 30, and no public method sets another
        int n = Integer.parseInt(a[2]);
        int rounds = Integer.parseInt(a[3]);
        dir = new File(a[4]);
        int drive = a.length > 5 ? Integer.parseInt(a[5]) : 3000;
        cacheBytes = a.length > 6 ? Long.parseLong(a[6]) : 0;
        sd = a.length > 7 ? Integer.parseInt(a[7]) : 400_000;
        rnd = new Random(seed);
        Common.rmrf(dir);
        clock = new Common.ManualClock(1_778_000_000_000L * 10_000L);
        long t0 = System.currentTimeMillis();
        StringBuilder summary = new StringBuilder();
        try {
            db = open(dir, clock);
            db.setRetainDuration(RETAIN);
            db.setStartupDistance(sd);
            for (int round = 0; round < rounds; round++) {
                load(n);
                verify("round " + round + " after the load", true);
                int mode = rnd.nextInt(4);
                massDelete(mode);
                verify("round " + round + " after the delete (mode " + mode + ")", true);
                boolean maintainOnly = rnd.nextInt(3) == 0;
                String r = driveAndCompare(round, drive, maintainOnly);
                summary.append("\n  round ").append(round).append(", delete mode ").append(mode).append(maintainOnly ? ", maintain() only" : ", drive")
                        .append(": ").append(r);
            }
            db.close();
            db = open(dir, clock);
            verify("final", true);
            db.close();
        } catch (Common.Fail f) {
            System.out.println("FAIL BackToEmpty seed " + seed + " node " + nodeSize + ": " + f.getMessage());
            System.out.println("  after " + txs + " transactions, " + restarts + " restarts" + summary);
            try { db.close(); } catch (Throwable t) { }
            System.exit(1);
        } catch (Throwable t) {
            System.out.println("FAIL (exception) BackToEmpty seed " + seed + " node " + nodeSize + ": " + t);
            t.printStackTrace(System.out);
            try { db.close(); } catch (Throwable x) { }
            System.exit(2);
        }
        Common.log("OK BackToEmpty seed " + seed + " node " + nodeSize + " keys " + n + ": " + txs + " transactions, " + restarts
                + " restarts, " + checks + " checks, " + cutChecks + " cuts checked at the oldest state, " + (System.currentTimeMillis() - t0) + " ms" + summary);
    }

    static Db open(File d, Clock c) throws Exception {
        DbBuilder b = Db.builder().mainStream(new FileStream(d, false)).clock(c);
        if (cacheBytes > 0) b.cacheSizeIndicator(cacheBytes);
        Db db = b.start();
        db.setStartupDistance(sd);      // after the start since bergdb 028-13; nothing written if in force
        return db;
    }

    static void restart() throws Exception {
        if (rnd.nextBoolean()) db.stop();
        db.close();
        db = open(dir, clock);
        restarts++;
        Common.check(db.getRetainDuration() == RETAIN, "retain duration after a restart: " + db.getRetainDuration());
    }

    /** A key of one of many shapes; never under 01 25 (BergDB's). */
    static byte[] key() {
        long s = serial++;
        switch (rnd.nextInt(8)) {
            case 0: return new byte[] {0x10, (byte) (s >>> 16), (byte) (s >>> 8), (byte) s};
            case 1: { byte[] k = new byte[1 + rnd.nextInt(Db.MAX_KEY_BYTES)]; rnd.nextBytes(k); if (k[0] == 1) k[0] = 2; return k; }
            case 2: { byte[] k = new byte[7 * (1 + rnd.nextInt(15))]; Arrays.fill(k, (byte) 0xff); k[k.length - 1] = (byte) s; k[k.length - 2] = (byte) (s >>> 8); return k; }
            case 3: { byte[] k = new byte[1 + rnd.nextInt(20)]; k[k.length - 1] = (byte) s; return k; }   // 00 runs
            case 4: { byte[] k = new byte[3 + (int) (s % 60)]; Arrays.fill(k, (byte) 0x41); return k; }  // extensions of each other
            case 5: { byte[] k = new byte[24]; Arrays.fill(k, (byte) 0x55); k[21] = (byte) (s >>> 16); k[22] = (byte) (s >>> 8); k[23] = (byte) s; return k; }
            case 6: return new byte[] {(byte) 0xfe, (byte) (s >>> 24), (byte) (s >>> 16), (byte) (s >>> 8), (byte) s};
            default: return s % 50 == 0 ? new byte[0] : new byte[] {0x30, (byte) (s >>> 8), (byte) s};
        }
    }

    static void step() { clock.advanceMillis(1 + rnd.nextInt(20)); }

    static long lastFaPos, cutChecks;

    static void exec(Map<Common.K, byte[]> ops) {
        Common.exec(db, m, ops);
        txs++;
        afterCut();
    }

    /**
     * After each cut (getFirstAvailablePos() moved): the oldest available state, at
     * getFirstAvailableLookupTime(), and two states just after it must be whole (P8: a step
     * scans at its own time, so a value deleted after its iteration began is not rewritten;
     * the states before its delete that are still available must have it).
     */
    static void afterCut() {
        long pos = db.getFirstAvailablePos();
        if (pos == lastFaPos) return;
        lastFaPos = pos;
        long fa = db.getFirstAvailableLookupTime();
        cutChecks++;
        List<Long> ts = new ArrayList<>();
        ts.add(fa);
        Long t1 = m.times.ceilingKey(fa);
        if (t1 != null) { ts.add(t1); ts.add(t1 - 1); Long t2 = m.times.higherKey(t1); if (t2 != null) ts.add(t2); }
        for (long t : ts) {
            if (t < fa) continue;
            try {
                Common.verifyFull(db, m, t, "the oldest available state after a cut (time " + t + ", first available " + fa + ")");
            } catch (RuntimeException e) {
                if (Common.isNotAvailable(e)) throw new Common.Fail("LookupTimeNotAvailable at the first available time " + t + " after a cut");
                throw e;
            }
        }
    }

    static void load(int n) throws Exception {
        int left = n;
        while (left > 0) {
            int k = Math.min(left, 1 + rnd.nextInt(500));
            Map<Common.K, byte[]> ops = new LinkedHashMap<>();
            while (ops.size() < k) ops.put(new Common.K(key()), Common.value(rnd, rnd.nextInt(10) == 0 ? 2000 : 60));
            left -= ops.size();
            step();
            exec(ops);
            if (rnd.nextInt(200) == 0) restart();
        }
    }

    static void massDelete(int mode) throws Exception {
        List<Common.K> keys = new ArrayList<>(m.latest.keySet());
        if (mode == 1) Collections.reverse(keys);
        if (mode == 2) Collections.shuffle(keys, rnd);
        int i = 0, nextRestart = 50 + rnd.nextInt(200), tx = 0;
        List<Common.K> extra = new ArrayList<>();
        while (i < keys.size()) {
            Map<Common.K, byte[]> ops = new LinkedHashMap<>();
            int k = 1 + rnd.nextInt(500);
            while (ops.size() < k && i < keys.size()) {
                Common.K key = keys.get(i);
                if (!(mode == 3 && i % 100 == 0)) ops.put(key, Common.DELETED);
                i++;
            }
            // now and then, new keys above the largest and below the smallest, deleted later
            if (rnd.nextInt(10) == 0 && ops.size() < 490) {
                byte[] hi = new byte[1 + rnd.nextInt(Db.MAX_KEY_BYTES)];
                Arrays.fill(hi, (byte) 0xff);
                Common.K h = new Common.K(hi);
                if (!ops.containsKey(h)) { ops.put(h, Common.value(rnd, 40)); extra.add(h); }
                byte[] lo = new byte[1 + rnd.nextInt(5)];
                Common.K l = new Common.K(lo);
                if (!ops.containsKey(l)) { ops.put(l, Common.value(rnd, 40)); extra.add(l); }
            }
            step();
            exec(ops);
            if (++tx == nextRestart) { restart(); verify("during the delete", false); nextRestart = tx + 50 + rnd.nextInt(300); }
        }
        // the extra keys, and for modes 0 to 2 every key left
        Map<Common.K, byte[]> ops = new LinkedHashMap<>();
        for (Common.K key : new ArrayList<>(m.latest.keySet())) {
            boolean keep = mode == 3 && !extra.contains(key);
            if (keep) continue;
            ops.put(key, Common.DELETED);
            if (ops.size() == 500) { step(); exec(ops); ops = new LinkedHashMap<>(); }
        }
        if (!ops.isEmpty()) { step(); exec(ops); }
        Common.check(mode == 3 || m.liveCount() == 0, "the model is not empty after a delete of mode " + mode);
    }

    static final Common.K DRIVE_KEY = new Common.K(new byte[] {0x06, 0x01});

    /** The drive and its twin. Returns the lag and the ratio. */
    static String driveAndCompare(int round, int drive, boolean maintainOnly) throws Exception {
        // The twin: a fresh database with the live KVs, the same settings and the same drive.
        File tdir = new File(dir.getPath() + "-twin");
        Common.rmrf(tdir);
        Common.ManualClock tclock = new Common.ManualClock(clock.getTime());
        Db twin = open(tdir, tclock);
        twin.setRetainDuration(RETAIN);
        twin.setStartupDistance(sd);
        Map<Common.K, byte[]> ops = new LinkedHashMap<>();
        for (Map.Entry<Common.K, byte[]> e : m.latest.entrySet()) {
            ops.put(e.getKey(), e.getValue());
            if (ops.size() == 500) { tclock.advanceMillis(5); Common.exec(twin, new Common.Model(), ops); ops.clear(); }
        }
        if (!ops.isEmpty()) { tclock.advanceMillis(5); Common.exec(twin, new Common.Model(), ops); }
        Random dr = new Random(round * 7919L + 13);
        int dt = new int[] {1, 2, 5}[dr.nextInt(3)];             // ms a drive transaction
        int R = 1000 / dt;                                        // the retain duration in drive transactions
        // 8 R, and at least 6 startup distances of stream (values of 850 bytes on average): commits begin
        // a reclaim iteration after twice the startup distance of stream (Db.setStartupDistance),
        // so a shorter drive need not give the space back (U13-4; seed 145 of soak 1, sd 1 MB, R = 200)
        drive = Math.min(drive, Math.max(8 * R, 6 * db.getStartupDistance() / 850));   // in force: 200 kB asked is 400 kB
        long[] keptMain = new long[drive], keptTwin = new long[drive];
        int nextRestart = rnd.nextInt(Math.max(1, drive / 3)), nextVerify = 100;
        for (int i = 0; i < drive; i++) {
            int ms = dt;
            byte[] v = new byte[200 + dr.nextInt(1300)];
            dr.nextBytes(v);
            clock.advanceMillis(ms);
            tclock.advanceMillis(ms);
            if (maintainOnly) {
                { db.maintain(1000); afterCut(); }
                afterCut();
                twin.maintain(1000);
            } else {
                Map<Common.K, byte[]> d = new LinkedHashMap<>();
                d.put(DRIVE_KEY, v);
                exec(d);
                Common.exec(twin, new Common.Model(), d);
                if (MAINTAIN) {                                   // -Dmaintain=true: maintain() after each drive transaction, both
                    { db.maintain(1000); afterCut(); }
                    afterCut();
                    twin.maintain(1000);
                }
            }
            keptMain[i] = db.getStreamLength() - db.getFirstAvailablePos();
            keptTwin[i] = twin.getStreamLength() - twin.getFirstAvailablePos();
            if (TRACE && i % Math.max(1, R / 2) == 0) Common.log("  drive " + i + ": kept " + keptMain[i] / 1000 + " kB (stream " + db.getStreamLength() / 1000
                    + " kB, first available pos " + db.getFirstAvailablePos() / 1000 + " kB, iterations " + db.getReclaimIterationCount()
                    + "), twin " + keptTwin[i] / 1000 + " kB (iterations " + twin.getReclaimIterationCount() + ")");
            if (i == nextRestart) {
                restart();
                verify("drive " + i + " after a restart", true);
                nextRestart = i + 200 + rnd.nextInt(drive);
            }
            if (i == nextVerify) { verify("drive " + i, false); nextVerify = i + 300 + rnd.nextInt(300); }
        }
        verify("after the drive", true);
        twin.close();
        Common.rmrf(tdir);
        long twinMax = 0;                                         // the twin's M1: its most kept over the last R
        for (int i = Math.max(0, drive - R - 1); i < drive; i++) twinMax = Math.max(twinMax, keptTwin[i]);
        int lag = -1;
        for (int i = drive - 1; i >= 0; i--) { if (keptMain[i] > 2 * twinMax) { lag = i + 1; break; } }
        if (lag == -1) lag = 0;
        long endMain = keptMain[drive - 1], endTwin = keptTwin[drive - 1];
        String r = "kept at the end " + endMain / 1000 + " kB, twin " + endTwin / 1000 + " kB (twin's largest " + twinMax / 1000
                + " kB), lag " + (lag >= drive ? "not reached in " + drive : lag) + " (R " + R + ", lag/R "
                + String.format("%.2f", lag / (double) R) + "), live " + m.liveCount();
        Common.log("round " + round + (maintainOnly ? " maintain() only" : " drive") + ": " + r);
        if (endMain > 2 * Math.max(twinMax, endTwin) + 500_000)
            throw new Common.Fail("round " + round + ": the kept stream did not come back near the twin's: " + r);
        return r;
    }

    static void verify(String what, boolean full) {
        long now = m.lastTime;
        checks++;
        Common.verifyFull(db, m, Long.MAX_VALUE, what);
        Common.verifyGets(db, m, Long.MAX_VALUE, rnd, 200, what);
        for (int i = 0; i < 5; i++) { Common.verifyRange(db, m, Long.MAX_VALUE, rnd, what); Common.verifyPrefix(db, m, Long.MAX_VALUE, rnd, what); }
        long fa = db.getFirstAvailableLookupTime();
        // the duration's promise: every state of the last RETAIN units is available
        Common.check(fa <= clock.getTime() - RETAIN || fa <= m.times.firstKey(), what + ": first available " + fa
                + " after now less the retain duration " + (clock.getTime() - RETAIN));
        if (full) {
            // older states inside the retain duration
            for (int i = 0; i < 3; i++) {
                long t = clock.getTime() - rnd.nextInt((int) RETAIN);
                if (t < fa) continue;
                Long tt = m.times.floorKey(t);
                if (tt == null) continue;
                try {
                    Common.verifyFull(db, m, t, what + " at an older time");
                    Common.verifyGets(db, m, t, rnd, 50, what + " at an older time");
                } catch (RuntimeException e) {
                    if (Common.isNotAvailable(e) && t >= db.getFirstAvailableLookupTime())
                        throw new Common.Fail(what + ": LookupTimeNotAvailable at " + t + " inside the retain duration");
                    if (!Common.isNotAvailable(e)) throw e;
                }
            }
        }
        m.prune(Math.min(fa, clock.getTime() - RETAIN) - 1);
    }
}
