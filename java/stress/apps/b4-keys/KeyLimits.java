import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.*;
import bergdb.pub.Limits;      // not 024-26's app Limits, compiled beside it since 028-23
import bergdb.stream.FileStream;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * B4 of 026-13: bergdb.pub.Limits.keyBytes() and checkKey() (bergdb 026-02) against real puts
 * and deletes of odd keys, written from the Javadoc of Limits, Connection ("Keys"), WBuilder,
 * the package's Limits and Objects, and Db's "Limits" only.
 *
 * The oracle of a key's bytes: its UTF-8 and one byte more for each '/' (Limits.keyBytes);
 * of its form: starts with '/', at least one more char, does not end with '/', no "//", no
 * lone surrogate (Connection, "Keys"). For each key: keyBytes() equals the oracle or throws
 * for a bad form; checkKey() throws iff a bad form or over 111 bytes; a put, w().put,
 * rw() put, delete or w().delete of it throws the very IllegalArgumentException with the
 * same message iff checkKey() threw, and writes nothing then; a taken put reads back. At the
 * end, a restart and every key again. A Core part: a String key fits iff its UTF-8 is at
 * most Db.MAX_KEY_BYTES (Db, "Limits").
 *
 * Usage: java -cp bergdb-release.jar:out KeyLimits SEED KEYS DIR
 */
public class KeyLimits {
    public static class Note {
        public String s;
        public long n;
        public Note() {}
        public Note(String s, long n) { this.s = s; this.n = n; }
    }

    static Random rnd;
    static Database db;
    static Connection c;
    static final Map<String, Object> oracle = new HashMap<>();   // key -> String or Note
    static final Set<String> refusedKeys = new HashSet<>();
    static long taken, refused, badForm, deletes, msgChecks, replaced;

    static final String[] PIECES = {
        "a", "Z", "0", "-", ".", "_", "$", "{", "}", "#", " ", "~", "\u007f", "\u0000", "\u0001", "\u0002",
        "å", "é", "ß", "߿", "€", "中", "﻿", "￿", "", "ࠀ", "😀", "􏿿",
        "𝄞", "/", "/", ".txt", ".obj", ".bin", ".", "${transactionTime}"
    };

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        int n = Integer.parseInt(a[1]);
        File dir = new File(a[2]);
        rnd = new Random(seed);
        Common.rmrf(dir);
        long t0 = System.currentTimeMillis();
        try {
            db = Factory.database().create(new File(dir, "pub").getPath()).start();
            c = db.connection();
            fixedCases();
            for (int i = 0; i < n; i++) {
                oneKey(randomKey());
                if (i % 5000 == 4999) {
                    db.close();
                    db = Factory.database().open(new File(dir, "pub").getPath()).start();
                    c = db.connection();
                    verifyAll("restart at " + i);
                }
            }
            keyReplace(n / 20 + 10);
            db.close();
            db = Factory.database().open(new File(dir, "pub").getPath()).start();
            c = db.connection();
            verifyAll("final restart");
            db.close();
            core(new File(dir, "core"), n / 4 + 100);
        } catch (Common.Fail f) {
            System.out.println("FAIL KeyLimits seed " + seed + ": " + f.getMessage());
            try { db.close(); } catch (Throwable t) { }
            System.exit(1);
        } catch (Throwable t) {
            System.out.println("FAIL (exception) KeyLimits seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            try { db.close(); } catch (Throwable x) { }
            System.exit(2);
        }
        Common.log("OK KeyLimits seed " + seed + ": " + taken + " taken, " + refused + " refused for length, " + badForm
                + " bad form, " + deletes + " deletes, " + msgChecks + " messages compared, " + replaced
                + " key-replace puts, " + oracle.size() + " keys kept, " + (System.currentTimeMillis() - t0) + " ms");
    }

    /** The oracle's count: UTF-8 and one byte a '/'. */
    static long model(String key) {
        long n = key.getBytes(StandardCharsets.UTF_8).length;
        for (int i = 0; i < key.length(); i++) if (key.charAt(i) == '/') n++;
        return n;
    }

    static boolean goodForm(String key) {
        if (key == null || key.length() < 2 || key.charAt(0) != '/' || key.endsWith("/") || key.contains("//")) return false;
        for (int i = 0; i < key.length(); i++) {
            char ch = key.charAt(i);
            if (Character.isHighSurrogate(ch)) {
                if (i + 1 >= key.length() || !Character.isLowSurrogate(key.charAt(i + 1))) return false;
                i++;
            } else if (Character.isLowSurrogate(ch)) return false;
        }
        return true;
    }

    /** The name's suffix (the package's Objects): what follows the last part's last '.', or "". */
    static String suffix(String key) {
        String name = key.substring(key.lastIndexOf('/') + 1);
        int d = name.lastIndexOf('.');
        return d < 0 ? "" : name.substring(d + 1);
    }

    static boolean objectKey(String key) {
        String s = suffix(key);
        return s.isEmpty() || s.equals("obj");
    }

    static String randomKey() {
        StringBuilder sb = new StringBuilder();
        int dirs = rnd.nextInt(4);
        sb.append('/');
        String[] tops = {"k", "ä", "a.b", "d", "€x", "z"};
        sb.append(tops[rnd.nextInt(tops.length)]);
        for (int i = 1; i < dirs; i++) sb.append('/').append(PIECES[rnd.nextInt(16)]).append(i);
        sb.append('/');
        int target = 95 + rnd.nextInt(22);                 // around the limit of 111
        if (rnd.nextInt(10) == 0) target = 3 + rnd.nextInt(90);
        while (model(sb.toString()) < target) {
            String p = PIECES[rnd.nextInt(PIECES.length)];
            if (p.equals("${transactionTime}") && rnd.nextInt(4) != 0) continue;
            sb.append(p);
        }
        // odd forms, now and then
        switch (rnd.nextInt(40)) {
            case 0: sb.append('/'); break;                              // ends with '/'
            case 1: sb.insert(1 + rnd.nextInt(sb.length() - 1), "//"); break;
            case 2: sb.append('\ud800'); break;                          // lone high surrogate
            case 3: sb.insert(2, '\udc00'); break;                       // lone low surrogate
            case 4: sb.deleteCharAt(0); break;                           // no leading '/'
            case 5: sb.setLength(1); break;                              // "/"
            default:
        }
        String k = sb.toString();
        if (k.endsWith("/") && rnd.nextInt(3) != 0) k = k + "x";
        return k;
    }

    static void fixedCases() {
        // The Javadoc's example: "/customers/12345678" is 21 bytes.
        Common.check(Limits.keyBytes("/customers/12345678") == 21, "keyBytes of /customers/12345678: "
                + Limits.keyBytes("/customers/12345678"));
        Common.check(Limits.MAX_KEY_BYTES == 111 && Limits.MAX_KEY_BYTES == Db.MAX_KEY_BYTES, "MAX_KEY_BYTES");
        Common.check(Limits.MAX_OPERATIONS == Db.MAX_OPERATIONS && Limits.MAX_VALUE_BYTES == Db.MAX_VALUE_BYTES
                && Limits.MAX_TRANS_BYTES == Db.MAX_TRANS_BYTES && Limits.MAX_TRANS_KEY_BYTES == Db.MAX_TRANS_KEY_BYTES,
                "Limits' constants are not Db's");
        // Exactly 111 and 112, with 1-, 2-, 3- and 4-byte characters at the end.
        for (String tail : new String[] {"a", "å", "€", "😀", "\u0000", "\u0001"}) {
            for (int extra = -2; extra <= 2; extra++) {
                StringBuilder sb = new StringBuilder("/edge/");
                int tb = tail.getBytes(StandardCharsets.UTF_8).length;
                while (model(sb.toString()) + tb < 111 + extra) sb.append('x');
                sb.append(tail);
                oneKey(sb.toString());
            }
        }
        // bad forms
        for (String k : new String[] {"", "/", "a", "a/b", "/a/", "/a//b", "//a", "/a\ud800", "/\udc00b", "/a/b/"}) oneKey(k);
        try { Limits.keyBytes(null); throw new Common.Fail("keyBytes(null) taken"); } catch (IllegalArgumentException e) { }
        try { Limits.checkKey(null); throw new Common.Fail("checkKey(null) taken"); } catch (IllegalArgumentException e) { }
        // An object at a key with another suffix: checkKey takes the key, the put refuses ("Bad key").
        String k = "/objs/x.txt";
        Limits.checkKey(k);
        try { c.put(k, new Note("n", 1)); throw new Common.Fail("an object at " + k + " was taken"); }
        catch (IllegalArgumentException e) { }
        Common.check(c.get(k, String.class) == null, "a refused object put wrote " + k);
        // A w() with one key over the limit among good ones: spoiled, nothing written.
        StringBuilder lng = new StringBuilder("/w/");
        while (model(lng.toString()) < 112) lng.append('q');
        WBuilder w = c.w().put("/w/a.txt", "1").put("/w/b.txt", "2");
        try { w.put(lng.toString(), "x"); throw new Common.Fail("w().put of 112 bytes taken"); } catch (IllegalArgumentException e) { }
        try { w.execute(); throw new Common.Fail("execute() of a spoiled WBuilder returned"); } catch (IllegalStateException e) { }
        Common.check(c.get("/w/a.txt", String.class) == null && c.get("/w/b.txt", String.class) == null,
                "a spoiled w() wrote its other puts");
    }

    /** One key through keyBytes, checkKey and a real call. */
    static void oneKey(String key) {
        boolean form = goodForm(key);
        long kb = -1;
        String kbMsg = null;
        try { kb = Limits.keyBytes(key); } catch (IllegalArgumentException e) { kbMsg = e.getMessage(); }
        if (form) {
            if (kbMsg != null) throw new Common.Fail("keyBytes refused a key of good form " + show(key) + ": " + kbMsg);
            if (kb != model(key)) throw new Common.Fail("keyBytes " + show(key) + " = " + kb + ", expected " + model(key));
        } else if (kbMsg == null) throw new Common.Fail("keyBytes took a key of bad form " + show(key) + " = " + kb);
        String ckMsg = null;
        try { Limits.checkKey(key); } catch (IllegalArgumentException e) { ckMsg = e.getMessage(); }
        boolean shouldRefuse = !form || kb > Limits.MAX_KEY_BYTES;
        if (shouldRefuse != (ckMsg != null)) throw new Common.Fail("checkKey " + show(key) + " (" + kb + " bytes, form "
                + form + ") " + (ckMsg == null ? "took it" : "refused: " + ckMsg));
        if (!form && kbMsg != null && !kbMsg.equals(ckMsg)) throw new Common.Fail("keyBytes and checkKey give other messages for "
                + show(key) + ": " + kbMsg + " / " + ckMsg);
        // the real call
        int how = rnd.nextInt(10);
        boolean isDelete = how >= 8;
        Object value = objectKey(key) && rnd.nextBoolean() ? new Note("v" + rnd.nextInt(1000), rnd.nextLong()) : "s" + rnd.nextInt();
        String putMsg = null;
        Object before = form ? safeGet(key) : null;
        try {
            switch (how) {
                case 0: case 1: case 2: case 3: c.put(key, value); break;
                case 4: case 5: c.w().put("/other/" + rnd.nextInt(50) + ".txt", "o").put(key, value).execute(); break;
                case 6: case 7: c.rw(env -> env.put(key, value)); break;
                case 8: c.delete(key); break;
                default: c.w().delete(key).execute();
            }
        } catch (IllegalArgumentException e) {
            putMsg = e.getMessage();
        }
        if (how == 4 || how == 5) {
            // the other put of the w() is not tracked by the oracle when taken: forget it
        }
        if ((putMsg != null) != (ckMsg != null))
            throw new Common.Fail((isDelete ? "delete" : "put") + " (way " + how + ") of " + show(key) + " (" + kb + " bytes, form "
                    + form + ") " + (putMsg == null ? "taken" : "refused: " + putMsg) + ", checkKey " + (ckMsg == null ? "took it" : "refused: " + ckMsg));
        if (putMsg != null) {
            if (!putMsg.equals(ckMsg)) throw new Common.Fail("messages differ for " + show(key) + ": put \"" + putMsg
                    + "\", checkKey \"" + ckMsg + "\"");
            msgChecks++;
            if (!form) { badForm++; return; }
            refused++;
            refusedKeys.add(key);
            Object after = safeGet(key);
            if (!Objects.equals(str(before), str(after))) throw new Common.Fail("a refused call changed " + show(key));
            if (after != null) throw new Common.Fail("a key over the limit has a value: " + show(key));
            return;
        }
        if (isDelete) { deletes++; oracle.remove(key); }
        else { taken++; oracle.put(key, value); }
        check(key);
    }

    /** As Object.class (the package's Objects): a DbObject at an object key, a String at ".txt", else bytes. */
    static Object safeGet(String key) {
        Object o = c.get(key, Object.class);
        if (o == null) return null;
        if (o instanceof DbObject) return c.get(key, Note.class);
        if (o instanceof byte[]) return new String((byte[]) o, StandardCharsets.UTF_8);
        return o;
    }

    static String str(Object o) {
        if (o instanceof Note) return "Note(" + ((Note) o).s + "," + ((Note) o).n + ")";
        return String.valueOf(o);
    }

    static void check(String key) {
        Object exp = oracle.get(key);
        Object got = safeGet(key);
        if (!str(exp).equals(str(got))) throw new Common.Fail("get " + show(key) + " gave " + str(got) + ", expected " + str(exp));
        if (c.exists(key) != (exp != null)) throw new Common.Fail("exists " + show(key) + " is " + c.exists(key));
    }

    static void verifyAll(String what) {
        for (String k : oracle.keySet()) {
            try { check(k); } catch (Common.Fail f) { throw new Common.Fail(what + ": " + f.getMessage()); }
        }
        int i = 0;
        for (String k : refusedKeys) {
            if (i++ > 2000) break;
            if (c.get(k, String.class) != null || c.exists(k)) throw new Common.Fail(what + ": a refused key has a value " + show(k));
        }
    }

    /** Key replace: "${transactionTime}" counts as written, and is replaced by 18 digits. */
    static void keyReplace(int n) {
        Connection kc = db.newConnection();
        kc.setEnableKeyReplace(true);
        for (int i = 0; i < n; i++) {
            StringBuilder sb = new StringBuilder("/ev/");
            int target = 100 + rnd.nextInt(14);
            String rep = "${transactionTime}";
            int at = rnd.nextInt(3);
            if (at == 0) sb.append(rep);
            while (model(sb.toString()) + (at == 2 ? rep.length() + 4 : 4) < target) sb.append(PIECES[rnd.nextInt(10)]);
            if (at == 1) sb.append(rep);
            if (at == 2) sb.append(rep);
            sb.append(".txt");
            String key = sb.toString();
            long kb = Limits.keyBytes(key);
            boolean fits = kb <= Limits.MAX_KEY_BYTES;
            String v = "r" + i;
            Transaction t;
            try {
                t = kc.put(key, v);
            } catch (IllegalArgumentException e) {
                if (fits) throw new Common.Fail("key replace put refused a key of " + kb + " bytes: " + show(key) + ": " + e.getMessage());
                continue;
            }
            if (!fits) throw new Common.Fail("key replace put took a key of " + kb + " bytes: " + show(key));
            String digits = String.format("%018d", t.getTime().units());
            String real = key.replace(rep, digits);
            Common.check(model(real) == kb, "the replaced key's bytes " + model(real) + " differ from keyBytes " + kb);
            Common.check(Limits.keyBytes(real) == kb, "keyBytes of the replaced key");
            oracle.put(real, v);
            check(real);
            replaced++;
        }
    }

    /** The Core: a String key fits iff its UTF-8 is at most MAX_KEY_BYTES; a byte[] key iff its length is. */
    static void core(File dir, int n) throws Exception {
        Db cdb = Db.builder().mainStream(new FileStream(dir)).start();
        Map<String, String> m = new HashMap<>();
        try {
            for (int i = 0; i < n; i++) {
                StringBuilder sb = new StringBuilder("k");
                int target = 105 + rnd.nextInt(10);
                while (sb.toString().getBytes(StandardCharsets.UTF_8).length < target) sb.append(PIECES[rnd.nextInt(28)]);
                String key = sb.toString();
                int len = key.getBytes(StandardCharsets.UTF_8).length;
                boolean fits = len <= Db.MAX_KEY_BYTES;
                Trans.Builder b = cdb.trans();
                boolean taken;
                try {
                    if (rnd.nextBoolean()) b.put(key, "v" + i); else b.put(key, ("w" + i).getBytes(StandardCharsets.UTF_8));
                    taken = true;
                } catch (IllegalArgumentException e) {
                    taken = false;
                }
                if (taken != fits) throw new Common.Fail("Core put(String) of a key of " + len + " UTF-8 bytes was "
                        + (taken ? "taken" : "refused") + ": " + show(key));
                if (taken) {
                    Trans t = b.build();
                    cdb.execute(t);
                    m.put(key, "v" + i);
                    // the stored bkey has as many bytes (Db, "Limits")
                    Common.check(Keys.toBytes(key).length == len, "Keys.toBytes length " + Keys.toBytes(key).length + " != UTF-8 " + len);
                    byte[] got = cdb.getOne(Long.MAX_VALUE, Keys.toSegments(key), cdb.newGetData());
                    Common.check(got != null, "Core get of a taken String key gave null: " + show(key));
                }
                // a byte[] key of exactly 111 and 112
                byte[] bk = new byte[111 + (i & 1)];
                rnd.nextBytes(bk);
                bk[0] = 0x10;
                try {
                    cdb.trans().delete(bk);
                    if (bk.length > 111) throw new Common.Fail("Core delete of 112 bytes taken");
                } catch (IllegalArgumentException e) {
                    if (bk.length <= 111) throw new Common.Fail("Core delete of 111 bytes refused");
                }
            }
            GetData gd = cdb.newGetData();
            cdb.close();
            cdb = Db.builder().mainStream(new FileStream(dir)).start();
            gd = cdb.newGetData();
            for (String k : m.keySet()) {
                byte[] got = cdb.getOne(Long.MAX_VALUE, Keys.toSegments(k), gd);
                Common.check(got != null, "Core: after the restart no value at " + show(k));
            }
            Common.log("Core: " + m.size() + " String keys taken of " + n);
        } finally {
            cdb.close();
        }
    }

    static String show(String k) {
        StringBuilder sb = new StringBuilder("\"");
        for (int i = 0; i < k.length(); i++) {
            char ch = k.charAt(i);
            if (ch < 0x20 || ch > 0x7e) sb.append(String.format("\\u%04x", (int) ch)); else sb.append(ch);
        }
        return sb.append("\" (").append(k.length()).append(" chars)").toString();
    }
}
