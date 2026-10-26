package bergdb.core;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Random;

import bergdb.stream.MemoryStream;

/**
 * Does a database start with another maximum node size than the one it was written with
 * (bergdb 005-38)? The node size is not in the stream; startup reruns the transactions
 * after the startup position and finds D's nodes by their ids. A database is written with
 * node size A (random 24-byte keys, 100 a transaction, startup distance 1 MB), synced and
 * stopped (D is not written: the startup section is rerun), then a copy of its stream is
 * started with node size B, and every key is read back.
 */
public class RestartNodeSize {
    static DbBuilder size(DbBuilder b, int n) {
        if (n == 8) return b.maxNodeSize8();
        if (n == 14) return b.maxNodeSize14();
        if (n == 30) return b.maxNodeSize30();
        if (n == 62) return b.maxNodeSize62();
        throw new IllegalArgumentException("node " + n);
    }

    static byte[] key(int k) {
        byte[] b = new byte[24];
        System.arraycopy("/scale/key/".getBytes(StandardCharsets.US_ASCII), 0, b, 0, 11);
        long v = k;
        for (int i = 23; i >= 11; i--) { b[i] = (byte) ('0' + v % 10); v /= 10; }
        return b;
    }

    public static void main(String[] args) throws Exception {
        int keys = 20000;
        int[] sizes = {8, 14, 30, 62};
        for (int a : sizes) {
            MemoryStream s = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            long time = 10;
            clock.setTime(time);
            Db db = size(Db.builder().testSetup(s).clock(clock).startupDistance(1000000), a).start();
            int[] ord = new int[keys];
            for (int i = 0; i < keys; i++) ord[i] = i;
            Random rnd = new Random(1);
            for (int i = keys - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
            for (int i = 0; i < keys; i += 100) {
                Trans.Builder tb = db.trans();
                for (int j = i; j < i + 100; j++) tb.put(key(ord[j]), new byte[] {(byte) ord[j], (byte) (ord[j] >>> 8)});
                clock.setTime(++time);
                db.execute(tb.build());
            }
            long length = db.getStreamLength();
            long sp = db.internal().x().startupPos.get();
            db.sync(SyncLevel.STRONG);
            db.close();
            for (int b : sizes) {
                MemoryStream c = s.copy();
                String result;
                try {
                    Db d = size(Db.builder().testSetup(c).clock(clock).startupDistance(1000000), b).start();
                    int bad = 0;
                    for (int k = 0; k < keys; k++) {
                        byte[] v = DbUtil.get(d, Long.MAX_VALUE, key(k));
                        if (v == null || !Arrays.equals(v, new byte[] {(byte) k, (byte) (k >>> 8)})) bad++;
                    }
                    clock.setTime(++time);
                    d.execute(d.trans().put(key(keys), new byte[] {1}).build());
                    d.close();
                    result = bad == 0 ? "started, all " + keys + " keys read back" : "started, " + bad + " keys wrong";
                } catch (Throwable e) {
                    String m = String.valueOf(e.getMessage());
                    result = "FAILED: " + e.getClass().getSimpleName() + ": " + (m.length() > 160 ? m.substring(0, 160) + "..." : m);
                }
                System.out.println("written with node " + a + " (stream " + length + " bytes, startup section "
                        + (length - sp) + " bytes), started with node " + b + ": " + result);
            }
        }
        System.exit(0);
    }
}
