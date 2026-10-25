import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.RandomAccessFile;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Bergdb 005-40: a database written by one version of BergDB, started by another. Uses
 * only the Pub API that the 2017 code (195cf88) and today's code share; run.sh compiles it
 * against each.
 *
 *   create DIR N   creates a database in DIR with N puts, syncs it and stops it
 *   start DIR      starts the database in DIR and reads /k0; prints the outcome and what
 *                  the start did to the stream file
 *   cut DIR B      cuts the last B bytes off the stream file, as a crash in the last record
 */
public class CrossVersion {
    public static void main(String[] args) throws Exception {
        String c = args[0];
        File d = new File(args[1]);
        if (c.equals("create")) create(d, Integer.parseInt(args[2]));
        else if (c.equals("start")) start(d);
        else if (c.equals("cut")) cut(d, Long.parseLong(args[2]));
        else throw new IllegalArgumentException(c);
        System.exit(0);
    }

    static void create(File d, int n) throws Exception {
        Database db = Factory.database().dir(d.getPath()).start();
        Connection c = db.connection();
        for (int i = 0; i < n; i++) {
            c.put("/k" + i, "value " + i);
        }
        db.sync();
        db.stop();
        Thread.sleep(1000);     // stop() of 2017 does not wait; nothing is left after sync().
        System.out.println("    created, " + n + " puts; the stream file " + streamFile(d).length()
                + " bytes");
    }

    static void start(File d) throws Exception {
        File f = streamFile(d);
        byte[] before = bytes(f);
        String o;
        try {
            Database db = Factory.database().dir(d.getPath()).start();
            o = "started, /k0 = " + db.connection().get("/k0", String.class);
            db.sync();
            db.stop();
        } catch (Throwable e) {
            o = e.getClass().getName() + ": " + e.getMessage();
        }
        Thread.sleep(1000);     // A failed start of 2017 leaves its storage running (005-32).
        byte[] after = bytes(f);
        String s;
        if (!prefixEquals(before, after)) {
            s = "CHANGED before its old length";
        } else if (after.length == before.length) {
            s = "unchanged";
        } else {
            s = "grew by " + (after.length - before.length) + " bytes at " + before.length + ": "
                    + describe(after, before.length);
        }
        System.out.println("    " + o);
        System.out.println("    The stream file then: " + s + ".");
    }

    static void cut(File d, long b) throws IOException {
        File f = streamFile(d);
        RandomAccessFile raf = new RandomAccessFile(f, "rw");
        raf.setLength(f.length() - b);
        raf.close();
        System.out.println("    cut " + b + " bytes; the stream file " + f.length() + " bytes");
    }

    static String describe(byte[] b, int from) {
        int nonZero = 0;
        StringBuilder hex = new StringBuilder();
        for (int i = from; i < b.length; i++) {
            if (b[i] != 0) {
                nonZero++;
                if (hex.length() > 0) hex.append(", ");
                hex.append("byte ").append(i - from).append(" = ").append(b[i] & 0xff);
            }
        }
        return nonZero == 0 ? "all zero" : nonZero + " not zero (" + hex + ")";
    }

    static boolean prefixEquals(byte[] a, byte[] b) {
        if (b.length < a.length) return false;
        for (int i = 0; i < a.length; i++) {
            if (a[i] != b[i]) return false;
        }
        return true;
    }

    static File streamFile(File d) throws IOException {
        File found = null;
        File[] fs = d.listFiles();
        if (fs != null) {
            for (File f : fs) {
                if (f.getName().endsWith(".bergdb")) {
                    if (found != null) throw new IOException("two stream files in " + d);
                    found = f;
                }
            }
        }
        if (found == null) throw new IOException("no stream file in " + d);
        return found;
    }

    static byte[] bytes(File f) throws IOException {
        byte[] b = new byte[(int) f.length()];
        FileInputStream in = new FileInputStream(f);
        int off = 0;
        while (off < b.length) {
            int n = in.read(b, off, b.length - off);
            if (n < 0) break;
            off += n;
        }
        in.close();
        return b;
    }
}
