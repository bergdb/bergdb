package bergdb.core;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

import bergdb.stream.FileStream;

/**
 * Bergdb 005-50: the node size field across versions of BergDB, on a database in a
 * directory (FileStream), each step in a JVM of its own, with the jar of a version:
 *
 *   write DIR SIZE FROM TO   start (or create) with node size SIZE, put keys [FROM, TO),
 *                            100 a transaction, and a value of 200,000 bytes, which takes
 *                            the stream past a meta block; sync, close
 *   start DIR SIZE N         start with SIZE, read keys [0, N) back, close
 *   meta DIR                 the node size field (offset 44) of every meta block
 *
 * It uses only API that release 2026.1 has.
 */
public class CrossNodeSize {
    static DbBuilder builder(File dir, int size) throws Exception {
        DbBuilder b = Db.builder().testSetup(new FileStream(dir)).systemClock();
        if (size == 8) return b.maxNodeSize8();
        if (size == 14) return b.maxNodeSize14();
        if (size == 30) return b.maxNodeSize30();
        if (size == 62) return b.maxNodeSize62();
        throw new IllegalArgumentException("node " + size);
    }

    static byte[] key(int k) {
        return String.format("/cross/key/%08d", k).getBytes(StandardCharsets.US_ASCII);
    }

    static byte[] value(int k) {
        return new byte[] {(byte) k, (byte) (k >>> 8), (byte) (k >>> 16)};
    }

    public static void main(String[] args) throws Exception {
        File dir = new File(args[1]);
        String what = String.join(" ", args);
        try {
            if (args[0].equals("write")) {
                int from = Integer.parseInt(args[3]), to = Integer.parseInt(args[4]);
                Db db = builder(dir, Integer.parseInt(args[2])).start();
                for (int i = from; i < to; i += 100) {
                    Trans.Builder tb = db.trans();
                    for (int k = i; k < Math.min(to, i + 100); k++) tb.put(key(k), value(k));
                    db.execute(tb.build());
                }
                db.execute(db.trans().put("/cross/big", new byte[200000]).build());
                db.sync(SyncLevel.STRONG);
                long length = db.getStreamLength();
                db.close();
                System.out.println(what + ": OK, stream " + length + " bytes");
            } else if (args[0].equals("start")) {
                int n = Integer.parseInt(args[3]);
                Db db = builder(dir, Integer.parseInt(args[2])).start();
                int bad = 0;
                for (int k = 0; k < n; k++) {
                    byte[] v = DbUtil.get(db, Long.MAX_VALUE, key(k));
                    if (v == null || !Arrays.equals(v, value(k))) bad++;
                }
                db.close();
                System.out.println(what + ": started, " + bad + " of " + n + " keys bad");
            } else if (args[0].equals("meta")) {
                FileStream s = new FileStream(dir);
                StringBuilder r = new StringBuilder(what + ":");
                byte[] b = new byte[4];
                for (long pos = 0; pos + 128 <= s.getLength(); pos += 200000) {
                    s.read(pos + 44, b, 0, 4);
                    r.append(" " + ((b[0] & 0xff) | (b[1] & 0xff) << 8 | (b[2] & 0xff) << 16 | (b[3] & 0xff) << 24));
                }
                s.close();
                System.out.println(r);
            }
        } catch (Throwable e) {
            String m = String.valueOf(e.getMessage());
            System.out.println(what + ": FAILED: " + e.getClass().getSimpleName() + ": "
                    + (m.length() > 170 ? m.substring(0, 170) + "..." : m));
        }
        System.exit(0);
    }
}
