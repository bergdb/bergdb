import bergdb.pub.*;
import bergdb.pub.util.*;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * ReplaceLimits (031-02, e5). Key replace ("${transactionTime}") in w() and rw()
 * transactions of objects in a directory with two indexes (an object there is up to five
 * operations) and of texts with the time in a directory's name, near and over the limits: 500
 * operations, 56 KiB of keys with the index entries of long keys and long string levels, a
 * level over 111 bytes. A transaction is taken or refused as a whole: the oracle, which
 * knows the keys once the time is known, checks every key of a taken one and that a refused
 * one left the listings and the index scans as they were. For the transactions whose key
 * bytes the app cannot count exactly (long levels), the largest taken and the smallest
 * refused of each shape must not cross. Also: two puts at one replaced key (the last
 * counts), a replaced object key in a directory refused at once, a connection without key
 * replace that puts the text as written, updates and deletes of earlier events, index
 * scans (eq, from, to, prefix, backward) and listings at older times.
 *
 * Usage: java ReplaceLimits DIR|mem SEED TRANSACTIONS
 */
public class ReplaceLimits {
    public static class Ev {
        public String kind;
        public long n;
        public String body;
        public Ev() {}
    }

    static void fail(String m) {
        System.out.println("REPLACELIMITS FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    static final TreeMap<Long, Map<String, Ev>> evHistory = new TreeMap<>();
    static final TreeMap<String, Ev> ev = new TreeMap<>(ReplaceLimits::cmpBytes);
    static final TreeMap<String, String> logs = new TreeMap<>(ReplaceLimits::cmpBytes);
    static Database db;
    static Connection c, plain;
    static Random r;
    static long nTakenAmbiguous, nRefusedAmbiguous;
    static final List<String> refusedNotes = new ArrayList<>();
    static long nTaken, nRefused, nRefusedL6, nRefusedOps, nRefusedKeyBytes, nDup, nBadKey;
    static final Map<String, long[]> shapes = new HashMap<>();   // shape -> {max taken m, min refused m}

    static int cmpBytes(String a, String b) {
        return Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));
    }

    static String time18(long units) { return String.format("%018d", units); }

    static String kind(int len) {
        StringBuilder sb = new StringBuilder("k" + r.nextInt(6));
        while (sb.length() < len) sb.append((char) ('a' + r.nextInt(26)));
        return sb.toString();
    }

    static final class Planned {
        String name;  // the name after "/ev/${transactionTime}-"
        Ev ev;
    }

    public static void main(String[] args) throws Exception {
        String dir = args[0];
        long seed = Long.parseLong(args[1]);
        int total = Integer.parseInt(args[2]);
        r = new Random(seed);
        System.out.println("ReplaceLimits seed " + seed + " transactions " + total);
        db = (dir.equals("mem") ? Factory.database().memory() : Factory.database().create(dir)).start();
        c = db.connection();
        plain = db.newConnection();
        c.setEnableKeyReplace(true);
        db.indexBuilder("by-n").dir("/ev/").type("long").field("n").start().join();
        db.indexBuilder("by-kind").dir("/ev/").type("string").field("kind").type("long").field("n").start().join();
        for (int i = 0; i < total; i++) {
            int op = r.nextInt(100);
            if (op < 45) eventTx(false);
            else if (op < 70) eventTx(true);
            else if (op < 80) longTx();
            else if (op < 88) churn();
            else if (op < 92) dupTx();
            else if (op < 95) badKey();
            else plainTx();
            if (i % 50 == 0) check(Long.MAX_VALUE, "after " + i);
            if (i % 120 == 0) checkOld("after " + i);
            if (i % 500 == 0) System.out.println("  " + i + ": taken " + nTaken + " refused " + nRefused
                    + " (ops " + nRefusedOps + ", key bytes " + nRefusedKeyBytes + ", L6 " + nRefusedL6 + ") events "
                    + ev.size());
        }
        check(Long.MAX_VALUE, "end");
        for (int i = 0; i < 10; i++) checkOld("end");
        if (!dir.equals("mem")) {
            db.close();
            db = Factory.database().open(dir).start();
            c = db.connection();
            check(Long.MAX_VALUE, "after restart");
            for (int i = 0; i < 10; i++) checkOld("after restart");
        }
        db.close();
        System.out.println("taken " + nTaken + ", refused " + nRefused + " (500 ops " + nRefusedOps + ", key bytes "
                + nRefusedKeyBytes + ", L6 " + nRefusedL6 + "), duplicates " + nDup + ", bad keys " + nBadKey);
        for (Map.Entry<String, long[]> e : shapes.entrySet()) {
            System.out.println("  shape " + e.getKey() + ": largest taken " + e.getValue()[0] + ", smallest refused "
                    + (e.getValue()[1] == Long.MAX_VALUE ? "none" : e.getValue()[1]));
        }
        System.out.println("between the counts of the Javadoc: taken " + nTakenAmbiguous + ", refused "
                + nRefusedAmbiguous + (refusedNotes.isEmpty() ? "" : " e.g. " + refusedNotes.get(0)));
        System.out.println("REPLACELIMITS OK");
    }

    // Objects at "/ev/${transactionTime}-name" and texts at "/log/${transactionTime}/name.txt".
    static void eventTx(boolean rw) {
        int m;
        int mode = r.nextInt(10);
        if (mode < 3) m = 150 + r.nextInt(100);       // near 500 ops: 2 or 3 each, plus texts
        else if (mode < 4) m = 90 + r.nextInt(20);    // near 500 ops if a put counted 5
        else m = 1 + r.nextInt(40);
        int texts = r.nextInt(mode < 3 ? 8 : 30);
        List<Planned> ps = new ArrayList<>();
        for (int i = 0; i < m; i++) {
            Planned p = new Planned();
            p.name = "e" + i;
            p.ev = new Ev();
            p.ev.kind = r.nextInt(8) == 0 ? null : kind(2 + r.nextInt(10));
            p.ev.n = r.nextInt(1000);
            p.ev.body = "b" + r.nextInt();
            ps.add(p);
        }
        // Operations: each new object 1 and its entries (1 or 2; a kind of null has no by-kind
        // entry), "up to 1 + 2k" by the Javadoc: between the two, either outcome is taken.
        long ops = texts, opsMax = texts;
        for (Planned p : ps) {
            int k = 1 + (p.ev.kind == null ? 0 : 1);
            ops += 1 + k;
            opsMax += 1 + 2 * 2;
        }
        boolean over = ops > 500;
        boolean surelyUnder = opsMax <= 500;
        Transaction t = null;
        boolean refused = false;
        try {
            if (rw) {
                t = c.rw(env -> {
                    // Reads that the action ignores, to give it a read set.
                    env.get("/ev/" + ev.size(), Ev.class);
                    for (Planned p : ps) env.put("/ev/${transactionTime}-" + p.name, p.ev);
                    for (int i = 0; i < texts; i++) env.put("/log/${transactionTime}/t" + i + ".txt", "text " + i);
                });
            } else {
                WBuilder w = c.w();
                for (Planned p : ps) w.put("/ev/${transactionTime}-" + p.name, p.ev);
                for (int i = 0; i < texts; i++) w.put("/log/${transactionTime}/t" + i + ".txt", "text " + i);
                t = w.execute();
            }
        } catch (DbException e) {
            refused = true;
            if (surelyUnder) fail("a transaction of " + ops + " to " + opsMax + " operations refused: " + e);
            if (!over) { nRefusedAmbiguous++; refusedNotes.add(ops + "/" + opsMax + ": " + e.getMessage()); }
            nRefusedOps++;
        }
        if (over && !refused) fail("a transaction of at least " + ops + " operations was taken (rw " + rw + ")");
        if (!over && !surelyUnder && !refused) nTakenAmbiguous++;
        if (refused) { nRefused++; checkUnchanged(); return; }
        taken(t, ps, texts);
    }

    static Map<String, Ev> lastSeen = null;

    static void taken(Transaction t, List<Planned> ps, int texts) {
        long tt = t.getTime().units();
        if (!evHistory.isEmpty() && evHistory.lastKey() >= tt) fail("time not increasing");
        Map<String, Ev> ch = new LinkedHashMap<>();
        for (Planned p : ps) {
            String key = p.name.startsWith("/") ? p.name : "/ev/" + time18(tt) + "-" + p.name;
            ch.put(key, p.ev);
        }
        for (int i = 0; i < texts; i++) logs.put("/log/" + time18(tt) + "/t" + i + ".txt", "text " + i);
        for (Map.Entry<String, Ev> e : ch.entrySet()) {
            if (e.getValue() == null) ev.remove(e.getKey()); else ev.put(e.getKey(), e.getValue());
        }
        evHistory.put(tt, ch);
        nTaken++;
        // Every key of it.
        for (Map.Entry<String, Ev> e : ch.entrySet()) {
            Ev g = c.get(e.getKey(), Ev.class);
            if (!same(g, e.getValue())) fail("after the transaction at " + tt + ": " + e.getKey() + " is " + str(g)
                    + ", expected " + str(e.getValue()));
        }
        for (int i = 0; i < texts; i++) {
            String k = "/log/" + time18(tt) + "/t" + i + ".txt";
            if (!("text " + i).equals(c.get(k, String.class))) fail("text " + k + " missing");
        }
    }

    static boolean same(Ev a, Ev b) {
        if (a == null || b == null) return a == b;
        return Objects.equals(a.kind, b.kind) && a.n == b.n && Objects.equals(a.body, b.body);
    }

    static String str(Ev e) { return e == null ? "null" : "{" + e.kind + "," + e.n + "," + e.body + "}"; }

    // Long keys and long levels: the index entries' keys pass 56 KiB before 500 operations.
    static void longTx() {
        // by-kind's levels: the kind's bytes and one, then 8 for n: at most 111 (L6).
        int kindLen = r.nextBoolean() ? 70 : 100;
        int nameLen = r.nextBoolean() ? 50 : 75;
        boolean l6 = r.nextInt(6) == 0;
        if (l6) kindLen = 104 + r.nextInt(5);       // over L6: the whole transaction refused
        int m = 60 + r.nextInt(106);
        boolean rw = r.nextBoolean();
        String shape = "kind" + kindLen + "/name" + nameLen + (rw ? "/rw" : "/w");
        List<Planned> ps = new ArrayList<>();
        for (int i = 0; i < m; i++) {
            Planned p = new Planned();
            StringBuilder sb = new StringBuilder("L" + i + "-");
            while (sb.length() < nameLen) sb.append('x');
            p.name = sb.toString();
            p.ev = new Ev();
            p.ev.kind = kind(kindLen - 1);
            p.ev.n = r.nextInt(1000);
            p.ev.body = "long";
            ps.add(p);
        }
        Transaction t = null;
        boolean refused = false;
        String why = "";
        try {
            if (rw) {
                t = c.rw(env -> { for (Planned p : ps) env.put("/ev/${transactionTime}-" + p.name, p.ev); });
            } else {
                WBuilder w = c.w();
                for (Planned p : ps) w.put("/ev/${transactionTime}-" + p.name, p.ev);
                t = w.execute();
            }
        } catch (IllegalArgumentException e) {
            refused = true; why = "L6";
            if (!l6) fail("a transaction of levels of " + kindLen + " bytes refused with " + e);
            nRefusedL6++;
        } catch (DbException e) {
            refused = true; why = "keys";
            if (l6) fail("a transaction with a level over 111 bytes refused with DbException, not "
                    + "IllegalArgumentException: " + e);
            nRefusedKeyBytes++;
        }
        if (l6 && !refused) fail("a transaction with a level of " + kindLen + " bytes was taken");
        if (refused) {
            nRefused++;
            checkUnchanged();
            if (why.equals("keys")) {
                long[] s = shapes.computeIfAbsent(shape, k -> new long[] {0, Long.MAX_VALUE});
                s[1] = Math.min(s[1], m);
                if (s[0] >= s[1]) fail("shape " + shape + ": " + s[0] + " objects taken, " + s[1] + " refused");
            }
            return;
        }
        long[] s = shapes.computeIfAbsent(shape, k -> new long[] {0, Long.MAX_VALUE});
        s[0] = Math.max(s[0], m);
        if (s[0] >= s[1]) fail("shape " + shape + ": " + s[0] + " objects taken, " + s[1] + " refused");
        taken(t, ps, 0);
    }

    // Updates and deletes of earlier events, by plain keys.
    static void churn() {
        if (ev.isEmpty()) return;
        List<String> ks = new ArrayList<>(ev.keySet());
        int m = 1 + r.nextInt(Math.min(90, ks.size()));
        List<Planned> ps = new ArrayList<>();
        Set<String> used = new HashSet<>();
        for (int i = 0; i < m; i++) {
            String k = ks.get(r.nextInt(ks.size()));
            if (!used.add(k)) continue;
            Planned p = new Planned();
            p.name = k;
            if (r.nextInt(3) > 0) {
                p.ev = new Ev();
                p.ev.kind = r.nextInt(8) == 0 ? null : kind(2 + r.nextInt(10));
                p.ev.n = r.nextInt(1000);
                p.ev.body = "u" + r.nextInt();
            }
            ps.add(p);
        }
        WBuilder w = c.w();
        for (Planned p : ps) { if (p.ev == null) w.delete(p.name); else w.put(p.name, p.ev); }
        Transaction t = w.execute();
        taken(t, ps, 0);
    }

    // Two puts at one replaced key: the last counts.
    static void dupTx() {
        Ev a = new Ev(); a.kind = "dup"; a.n = 1; a.body = "first";
        Ev b = new Ev(); b.kind = "dup"; b.n = 2; b.body = "second";
        Transaction t = c.w().put("/ev/${transactionTime}-d", a).put("/ev/${transactionTime}-d", b).execute();
        Planned p = new Planned(); p.name = "d"; p.ev = b;
        taken(t, Collections.singletonList(p), 0);
        nDup++;
    }

    // "${transactionTime}" in an object key's directory: refused at once, the builder spoiled.
    static void badKey() {
        WBuilder w = c.w();
        Ev e = new Ev(); e.kind = "bad"; e.n = 0; e.body = "x";
        w.put("/log/ok${transactionTime}.txt", "ok");
        try {
            w.put("/ev/${transactionTime}/x", e);
            fail("an object key with the replace in its directory was taken");
        } catch (IllegalArgumentException ex) {
            nBadKey++;
        }
        try {
            w.execute();
            fail("a spoiled builder executed");
        } catch (IllegalStateException ex) {
            // expected
        }
        try {
            c.put("/ev/${transactionTime}/y", e);
            fail("put of an object key with the replace in its directory was taken");
        } catch (IllegalArgumentException ex) { }
        checkUnchanged();
    }

    // Without key replace, the text is the key.
    static void plainTx() {
        String v = "plain" + r.nextInt();
        plain.put("/log/${transactionTime}.txt", v);
        logs.put("/log/${transactionTime}.txt", v);
        if (!v.equals(c.get("/log/${transactionTime}.txt", String.class))) fail("the literal key");
    }

    static void checkUnchanged() {
        check(Long.MAX_VALUE, "after a refusal");
    }

    static Map<String, Ev> evAt(long t) {
        Map<String, Ev> m = new TreeMap<>(ReplaceLimits::cmpBytes);
        for (Map<String, Ev> ch : evHistory.headMap(t, true).values()) {
            for (Map.Entry<String, Ev> e : ch.entrySet()) {
                if (e.getValue() == null) m.remove(e.getKey()); else m.put(e.getKey(), e.getValue());
            }
        }
        return m;
    }

    static void check(long t, String what) {
        Connection cc = c;
        Map<String, Ev> m = ev;
        if (t != Long.MAX_VALUE) {
            cc = db.newConnection();
            cc.setLookupTime(Time.units(t));
            m = evAt(t);
            what = what + " at " + t;
        }
        // The listing.
        List<String> exp = new ArrayList<>(m.keySet());
        List<String> got = new ArrayList<>();
        for (Kv<Ev> kv : cc.usePrimary(Ev.class).dir("/ev/").kvs()) {
            got.add(kv.key());
            if (!same(kv.value(), m.get(kv.key()))) fail(what + ": " + kv.key() + " is " + str(kv.value()) + ", expected "
                    + str(m.get(kv.key())));
        }
        if (!got.equals(exp)) fail(what + ": /ev/ lists " + got.size() + " keys, expected " + exp.size());
        // by-n, forward and backward.
        final Map<String, Ev> mm = m;
        List<String> byN = new ArrayList<>(exp);
        byN.sort((a, b) -> mm.get(a).n != mm.get(b).n ? Long.compare(mm.get(a).n, mm.get(b).n) : cmpBytes(a, b));
        List<String> gn = new ArrayList<>();
        for (Kv<Ev> kv : cc.useIndex("by-n", Ev.class).kvs()) gn.add(kv.key());
        if (!gn.equals(byN)) fail(what + ": by-n lists " + gn.size() + ", expected " + byN.size());
        long lo = r.nextInt(1000), hi = lo + r.nextInt(300);
        List<String> rangeExp = new ArrayList<>();
        for (String k : byN) if (mm.get(k).n > lo && mm.get(k).n <= hi) rangeExp.add(k);
        Collections.reverse(rangeExp);
        List<String> rg = new ArrayList<>();
        for (Kv<Ev> kv : cc.useIndex("by-n", Ev.class).from(lo, false).to(hi, true).backward().kvs()) rg.add(kv.key());
        if (!rg.equals(rangeExp)) fail(what + ": by-n (" + lo + ", " + hi + "] backward lists " + rg.size() + ", expected "
                + rangeExp.size());
        // by-kind: eq(kind) with n from, and a prefix.
        List<String> withKind = new ArrayList<>();
        for (String k : exp) if (mm.get(k).kind != null) withKind.add(k);
        withKind.sort((a, b) -> {
            int x = mm.get(a).kind.compareTo(mm.get(b).kind);   // ASCII kinds: code points
            if (x != 0) return x;
            if (mm.get(a).n != mm.get(b).n) return Long.compare(mm.get(a).n, mm.get(b).n);
            return cmpBytes(a, b);
        });
        List<String> gk = new ArrayList<>();
        for (Kv<Ev> kv : cc.useIndex("by-kind", Ev.class).kvs()) gk.add(kv.key());
        if (!gk.equals(withKind)) fail(what + ": by-kind lists " + gk.size() + ", expected " + withKind.size());
        if (!withKind.isEmpty()) {
            String kd = mm.get(withKind.get(r.nextInt(withKind.size()))).kind;
            long from = r.nextInt(1000);
            List<String> e2 = new ArrayList<>();
            for (String k : withKind) if (mm.get(k).kind.equals(kd) && mm.get(k).n >= from) e2.add(k);
            List<String> g2 = new ArrayList<>();
            for (Kv<Ev> kv : cc.useIndex("by-kind", Ev.class).eq(kd).from(from, true).kvs()) g2.add(kv.key());
            if (!g2.equals(e2)) fail(what + ": by-kind eq " + kd + " from " + from + " lists " + g2.size() + ", expected " + e2.size());
            String pre = kd.substring(0, Math.min(kd.length(), 1 + r.nextInt(3)));
            List<String> e3 = new ArrayList<>();
            for (String k : withKind) if (mm.get(k).kind.startsWith(pre)) e3.add(k);
            Collections.reverse(e3);
            List<String> g3 = new ArrayList<>();
            for (Kv<Ev> kv : cc.useIndex("by-kind", Ev.class).prefix(pre).backward().kvs()) g3.add(kv.key());
            if (!g3.equals(e3)) fail(what + ": by-kind prefix " + pre + " backward lists " + g3.size() + ", expected " + e3.size());
        }
        if (t == Long.MAX_VALUE) {
            // The texts: each log directory listed.
            Map<String, List<String>> byDir = new TreeMap<>();
            for (String k : logs.keySet()) byDir.computeIfAbsent(k.substring(0, k.lastIndexOf('/') + 1), x -> new ArrayList<>()).add(k);
            int checked = 0;
            for (Map.Entry<String, List<String>> e : byDir.entrySet()) {
                if (checked++ > 30 && r.nextInt(10) > 0) continue;
                List<String> g = new ArrayList<>();
                for (Kv<String> kv : cc.usePrimary(String.class).dir(e.getKey()).kvs()) {
                    g.add(kv.key());
                    if (!kv.value().equals(logs.get(kv.key()))) fail(what + ": text " + kv.key());
                }
                List<String> ex = new ArrayList<>(e.getValue());
                ex.sort(ReplaceLimits::cmpBytes);
                if (!g.equals(ex)) fail(what + ": " + e.getKey() + " lists " + g + ", expected " + ex);
            }
        }
    }

    static void checkOld(String what) {
        if (evHistory.size() < 2) return;
        List<Long> ts = new ArrayList<>(evHistory.keySet());
        long t = ts.get(r.nextInt(ts.size()));
        if (r.nextBoolean()) t--;
        check(t, what);
    }
}
