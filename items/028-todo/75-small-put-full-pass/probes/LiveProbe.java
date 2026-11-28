package bergdb.core;

import java.util.Random;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 028-75: the stream kept at rest, after maintain(budget) calls, against the live data
 * and the table's last done row, after each phase: a fill of KEYS values of VALUEBYTES random
 * bytes (100 a transaction, 10 ms apart; keys /c/(j mod 97)/j), one put of a byte, random
 * overwrites of 10 %, 30 % and 100 % of the keys, deletes of 90 %, deletes of all but 50.
 * Each phase is followed by calls a second apart until five in a row write nothing; the
 * retain duration 1 s, a CutStream, a test clock. "live" is the KVs' value node bytes (key
 * segments, value, StoredValueNode's overhead); "live stream bytes" the state's value and key
 * nodes, by the prototype's Reclaim.exactLive() (prototype.diff), so this probe compiles
 * against the prototype's jar only; without it, drop the exactLive() call (the runs on main
 * in runs/main.txt were made so).
 *
 * args: keys valueBytes budget startupDistance
 */
public class LiveProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static long time = SEC;
    static Db db;
    static CoreTestClock clock;
    static int budget;
    static long liveBytes;   // key bytes (8 a segment) + value + VALUE_NODE_BYTES of live KVs
    static long[] vlen;
    static int keys;

    static long[] rest() {
        long calls = 0, quiet = 0;
        final long l0 = db.getStreamLength();
        while (quiet < 5) {
            time += SEC;
            clock.setTime(time);
            final long before = db.getStreamLength();
            db.maintain(budget);
            calls++;
            quiet = db.getStreamLength() == before ? quiet + 1 : 0;
        }
        return new long[] {calls - 5, db.getStreamLength() - l0};
    }

    static long kept() { return db.getStreamLength() - db.getFirstAvailablePos(); }

    static String row() {
        Reclaim.IterationInfo r;
        synchronized (db.internal().getWriteLock()) {
            r = db.internal().reclaim().lastDoneRow();
        }
        if (r == null) return "no row";
        return "row pStart " + r.pStart + " pCut " + r.pCut + " rewritten " + r.rewritten
                + " kvCount " + r.kvCount + " pEnd-pCut " + (r.pEnd - r.pCut)
                + " pSafe-pCut " + (r.pSafe - r.pCut) + " cut " + r.cut;
    }

    static void report(String what, long[] m, long keptBefore) {
        final long k = kept();
        long x;
        synchronized (db.internal().getWriteLock()) {
            x = db.internal().reclaim().exactLive();
        }
        System.out.println(what + ": kept before " + keptBefore + ", calls " + m[0] + " wrote " + m[1]
                + ", kept " + k + ", live " + liveBytes + ", live stream bytes " + x
                + String.format(" (kept/that %.2f)", (double) k / x) + "; " + row());
    }

    static long keyBytes(int j) {
        return Reclaim.VALUE_NODE_BYTES + 8L * bergdb.dag.Keys.toSegments(key(j)).length;
    }

    static String key(int j) { return "/c/" + (j % 97) + "/" + j; }

    public static void main(String[] a) {
        keys = Integer.parseInt(a[0]);
        final int vb = Integer.parseInt(a[1]);
        budget = Integer.parseInt(a[2]);
        final int sd = Integer.parseInt(a[3]);
        vlen = new long[keys];
        final CutStream s = new CutStream();
        clock = new CoreTestClock();
        clock.setTime(time);
        db = Db.builder().testSetup(s).clock(clock).start();
        db.setStartupDistance(sd);
        db.setRetainDuration(SEC);
        final Random r = new Random(1);
        for (int i = 0; i < keys; i += 100) {
            Trans.Builder b = db.trans();
            for (int j = i; j < i + 100 && j < keys; j++) {
                byte[] v = new byte[vb];
                r.nextBytes(v);
                b.put(key(j), v);
                liveBytes += keyBytes(j) + vb;
                vlen[j] = vb;
            }
            time += SEC / 100;
            clock.setTime(time);
            db.execute(b.build());
        }
        long kb = kept();
        report(keys + "x" + vb + " sd " + sd + " filled, to rest", rest(), kb);
        kb = kept();
        time += SEC; clock.setTime(time);
        db.execute(db.trans().put("/one", new byte[] {1}).build());
        report("one put of a byte", rest(), kb);
        // Overwrites of a share of the keys, chosen at random, 100 a transaction.
        for (double share : new double[] {0.1, 0.3, 1.0}) {
            kb = kept();
            final int n = (int) (share * keys);
            for (int i = 0; i < n; i += 100) {
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 100 && j < n; j++) {
                    int x = r.nextInt(keys);
                    if (vlen[x] < 0) continue;
                    byte[] v = new byte[vb];
                    r.nextBytes(v);
                    b.put(key(x), v);
                }
                time += SEC / 100; clock.setTime(time);
                db.execute(b.build());
            }
            final long keptAfterWrites = kept();
            report("overwrites of " + share + " of the keys (kept after them " + keptAfterWrites + ")", rest(), kb);
        }
        // Deletes of 90 %, then of the rest but 50.
        kb = kept();
        for (int i = 0; i < keys * 9 / 10; i += 100) {
            Trans.Builder b = db.trans();
            for (int j = i; j < i + 100 && j < keys * 9 / 10; j++) {
                b.delete(key(j));
                liveBytes -= keyBytes(j) + vlen[j];
                vlen[j] = -1;
            }
            time += SEC / 100; clock.setTime(time);
            db.execute(b.build());
        }
        report("deletes of 90 % (kept after them " + kept() + ")", rest(), kb);
        kb = kept();
        for (int i = keys * 9 / 10; i < keys - 50; i += 100) {
            Trans.Builder b = db.trans();
            for (int j = i; j < i + 100 && j < keys - 50; j++) {
                b.delete(key(j));
                liveBytes -= keyBytes(j) + vlen[j];
                vlen[j] = -1;
            }
            time += SEC / 100; clock.setTime(time);
            db.execute(b.build());
        }
        report("deletes of all but 50 (kept after them " + kept() + ")", rest(), kb);
        db.close();
    }
}
