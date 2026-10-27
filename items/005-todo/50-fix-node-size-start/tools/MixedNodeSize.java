package bergdb.core;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Random;

import bergdb.stream.MemoryStream;

/**
 * Bergdb 005-50, question 3: is a start with another node size ever safe today? A
 * database is written with node size A and a small startup distance (100 bytes), so that
 * its startup section is short; it is stopped, and a copy is started with node size B.
 * If that start succeeds, every key is read back, the database writes as many keys again
 * with B, and is restarted: with B, then (a copy) with A. Run with and without -ea. The
 * rows with B = A are the control.
 */
public class MixedNodeSize {
    static DbBuilder size(DbBuilder b, int n) {
        if (n == 8) return b.maxNodeSize8();
        if (n == 14) return b.maxNodeSize14();
        if (n == 30) return b.maxNodeSize30();
        if (n == 62) return b.maxNodeSize62();
        throw new IllegalArgumentException("node " + n);
    }

    static byte[] key(int k) {
        byte[] b = new byte[24];
        System.arraycopy("/mixed/key/".getBytes(StandardCharsets.US_ASCII), 0, b, 0, 11);
        long v = k;
        for (int i = 23; i >= 11; i--) { b[i] = (byte) ('0' + v % 10); v /= 10; }
        return b;
    }

    static byte[] value(int k) {
        return new byte[] {(byte) k, (byte) (k >>> 8), (byte) (k >>> 16)};
    }

    static final CoreTestClock clock = new CoreTestClock();
    static long time = 10;

    /** Puts keys [from, to) in a random order, 100 a transaction. */
    static void put(Db db, int from, int to, long seed) {
        int n = to - from;
        int[] ord = new int[n];
        for (int i = 0; i < n; i++) ord[i] = from + i;
        Random rnd = new Random(seed);
        for (int i = n - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        for (int i = 0; i < n; i += 100) {
            Trans.Builder tb = db.trans();
            for (int j = i; j < Math.min(n, i + 100); j++) tb.put(key(ord[j]), value(ord[j]));
            clock.setTime(++time);
            db.execute(tb.build());
        }
    }

    /** The number of keys in [0, n) that do not read back. */
    static int bad(Db db, int n) {
        int bad = 0;
        for (int k = 0; k < n; k++) {
            byte[] v = DbUtil.get(db, Long.MAX_VALUE, key(k));
            if (v == null || !Arrays.equals(v, value(k))) bad++;
        }
        return bad;
    }

    static String fail(Throwable e) {
        String m = String.valueOf(e.getMessage());
        return "FAILED: " + e.getClass().getSimpleName() + ": " + (m.length() > 140 ? m.substring(0, 140) + "..." : m);
    }

    static Db start(MemoryStream s, int n) {
        return size(Db.builder().testSetup(s).clock(clock).startupDistance(100), n).start();
    }

    public static void main(String[] args) {
        final int keys = 20000;
        boolean ea = false;
        assert ea = true;
        System.out.println("assertions " + (ea ? "on" : "off") + "; " + keys + " keys written with A, "
                + keys + " more with B; startup distance 100 bytes");
        int[] sizes = {8, 14, 30, 62};
        for (int a : sizes) {
            MemoryStream s = new MemoryStream();
            Db db = start(s, a);
            put(db, 0, keys, 1);
            long section = db.getStreamLength() - db.internal().x().startupPos.get();
            db.sync(SyncLevel.STRONG);
            db.close();
            for (int b : sizes) {
                StringBuilder r = new StringBuilder("A " + a + ", B " + b + " (section " + section + " bytes): ");
                MemoryStream c = s.copy();
                try {
                    Db d = start(c, b);
                    r.append("started with B, " + bad(d, keys) + " bad");
                    put(d, keys, 2 * keys, 2);
                    r.append("; wrote " + keys + " with B, " + bad(d, 2 * keys) + " bad");
                    d.sync(SyncLevel.STRONG);
                    d.close();
                } catch (Throwable e) {
                    System.out.println(r.append(fail(e)));
                    continue;
                }
                for (int again : new int[] {b, a}) {
                    try {
                        Db d = start(c.copy(), again);
                        r.append("; restart with " + again + ": " + bad(d, 2 * keys) + " bad");
                        d.close();
                    } catch (Throwable e) {
                        r.append("; restart with " + again + ": " + fail(e));
                    }
                }
                System.out.println(r);
            }
        }
        System.exit(0);
    }
}
