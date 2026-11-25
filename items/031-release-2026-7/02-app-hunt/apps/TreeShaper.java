import bergdb.core.*;
import bergdb.dag.*;
import bergdb.stream.*;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.util.*;
import java.io.File;
import java.util.*;

/**
 * TreeShaper (031-02, e7). The Core API under overwrite and delete patterns that reshape the
 * index's trees: bulk puts in key order, in reverse and at random; every other key deleted,
 * ranges deleted, a prefix emptied and filled again; keys that share starts of 7, 14 and 21
 * bytes (deep segment trees), keys of exactly 7, 14, 21 bytes, the empty key, bytes 00 and
 * FF; values that grow and shrink, some of 100 kB; a cache budget of 4 MB and a startup
 * distance of 5 MB, a test clock that the app moves and, in some runs, a retain duration of
 * a few seconds with maintain(). The oracle keeps every version of every key. Checked after
 * each step: scans forward and backward from a start key (inclusive or not), forward ranges
 * with an end key, GetN, getOne of a sample, at the latest time and at older times from the
 * first available one; restarts now and then, with a check of everything after each.
 *
 * Usage: java TreeShaper DIR SEED STEPS RETAIN_SECONDS(0: forever)
 */
public class TreeShaper {
    static void fail(String m) {
        System.out.println("TREESHAPER FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    static final class BK implements Comparable<BK> {
        final byte[] b;
        BK(byte[] b) { this.b = b; }
        public int compareTo(BK o) { return Arrays.compareUnsigned(b, o.b); }
        public boolean equals(Object o) { return o instanceof BK && Arrays.equals(b, ((BK) o).b); }
        public int hashCode() { return Arrays.hashCode(b); }
        public String toString() { return Keys.toDisplayString(b); }
    }

    static final Map<BK, TreeMap<Long, byte[]>> versions = new HashMap<>();
    static final byte[] DEL = new byte[0];   // marker, compared by identity
    static TreeMap<BK, byte[]> latest = new TreeMap<>();
    static Db db;
    static String dir;
    static TestClock clock;
    static long now;
    static Random r;
    static long retainUnits;
    static long nTx, nScan, nOld, nMaintain;

    static byte[] key(int family, int i) {
        switch (family) {
        case 0: return String.format("seq%08d", i).getBytes();                 // 11 bytes
        case 1: { byte[] b = new byte[21]; Arrays.fill(b, (byte) 'p');     // exactly 21, deep
                  b[20] = (byte) i; b[19] = (byte) (i >> 8); b[13] = (byte) (i % 3); return b; }
        case 2: { byte[] b = new byte[7]; b[0] = (byte) 0xFF; b[6] = (byte) i; b[5] = (byte) (i >> 8); return b; }
        case 3: { byte[] b = new byte[1 + i % 40]; b[0] = 0; for (int j = 1; j < b.length; j++) b[j] = (byte) (i * 31 + j); return b; }
        case 4: return i == 0 ? new byte[0] : String.format("x/%d", i).getBytes();
        default: { byte[] b = new byte[14 + i % 2]; Arrays.fill(b, (byte) 'q'); b[13] = (byte) (i % 7); b[7] = (byte) (i / 7 % 200);
                   if (b.length > 14) b[14] = (byte) i; return b; }
        }
    }

    static byte[] value(int size) {
        byte[] v = new byte[size];
        r.nextBytes(v);
        if (size > 0) v[0] = (byte) nTx;
        return v;
    }

    static int size() {
        int x = r.nextInt(100);
        if (x < 2) return 50_000 + r.nextInt(60_000);
        if (x < 15) return 500 + r.nextInt(3000);
        return r.nextInt(30);
    }

    static void commit(Map<BK, byte[]> ops) {
        for (int start = 0; start < 1; start++) { }
        now += r.nextInt(2_000_000);
        clock.setTime(Time.units(now));
        Trans.Builder b = db.trans();
        for (Map.Entry<BK, byte[]> e : ops.entrySet()) {
            if (e.getValue() == DEL) b.delete(e.getKey().b); else b.put(e.getKey().b, e.getValue());
        }
        Trans t = b.build();
        db.execute(t);
        long tt = t.tt;
        for (Map.Entry<BK, byte[]> e : ops.entrySet()) {
            TreeMap<Long, byte[]> v = versions.computeIfAbsent(e.getKey(), k -> new TreeMap<>());
            if (!v.isEmpty() && v.lastKey() >= tt) fail("time not increasing");
            v.put(tt, e.getValue());
            if (e.getValue() == DEL) latest.remove(e.getKey()); else latest.put(e.getKey(), e.getValue());
        }
        nTx++;
        if (retainUnits > 0 && r.nextInt(30) == 0) {
            while (db.maintain()) nMaintain++;
            nMaintain++;
        }
    }

    // Puts or deletes ks in transactions of up to n.
    static void batch(List<BK> ks, boolean delete, int n) {
        for (int i = 0; i < ks.size(); i += n) {
            Map<BK, byte[]> ops = new LinkedHashMap<>();
            for (BK k : ks.subList(i, Math.min(ks.size(), i + n))) ops.put(k, delete ? DEL : value(size()));
            commit(ops);
        }
    }

    public static void main(String[] args) throws Exception {
        dir = args[0];
        long seed = Long.parseLong(args[1]);
        int steps = Integer.parseInt(args[2]);
        int retain = Integer.parseInt(args[3]);
        r = new Random(seed);
        System.out.println("TreeShaper seed " + seed + " steps " + steps + " retain " + retain);
        now = Time.utc("2026-06-01 00:00:00").units();
        clock = new TestClock();
        clock.setTime(Time.units(now));
        open();
        db.setStartupDistance(5);
        if (retain > 0) {
            retainUnits = retain * Clock.UNITS_PER_SEC;
            db.setRetainDuration(retainUnits);
        }
        for (int step = 0; step < steps; step++) {
            int fam = r.nextInt(6);
            int n = 200 + r.nextInt(r.nextInt(3) == 0 ? 8000 : 1500);
            List<BK> ks = new ArrayList<>();
            for (int i = 0; i < n; i++) ks.add(new BK(key(fam, i)));
            int pat = r.nextInt(9);
            String what;
            switch (pat) {
            case 0: batch(ks, false, 1 + r.nextInt(500)); what = "put in order"; break;
            case 1: { List<BK> rev = new ArrayList<>(ks); Collections.reverse(rev); batch(rev, false, 1 + r.nextInt(500)); what = "put in reverse"; break; }
            case 2: { List<BK> sh = new ArrayList<>(ks); Collections.shuffle(sh, r); batch(sh, false, 1 + r.nextInt(500)); what = "put at random"; break; }
            case 3: { List<BK> ev = new ArrayList<>(); for (int i = 0; i < ks.size(); i += 2) ev.add(ks.get(i)); batch(ev, true, 1 + r.nextInt(500)); what = "every other deleted"; break; }
            case 4: { int a = r.nextInt(n), b = Math.min(n, a + r.nextInt(n)); batch(ks.subList(a, b), true, 1 + r.nextInt(500)); what = "range deleted"; break; }
            case 5: { // a prefix emptied: every key of the family in the model
                List<BK> fk = new ArrayList<>();
                byte[] k0 = key(fam, 1);
                for (BK k : latest.keySet()) if (k.b.length > 0 && k0.length > 0 && k.b[0] == k0[0]) fk.add(k);
                batch(fk, true, 1 + r.nextInt(500)); what = "family emptied (" + fk.size() + ")"; break; }
            case 6: { // single overwrites with growing values
                for (int i = 0; i < 200; i++) {
                    Map<BK, byte[]> ops = new HashMap<>();
                    ops.put(ks.get(r.nextInt(ks.size())), value(r.nextInt(4000)));
                    commit(ops);
                }
                what = "single overwrites"; break; }
            case 7: { // mixed transactions: puts and deletes of one family, last op per key
                for (int i = 0; i < 20; i++) {
                    Map<BK, byte[]> ops = new LinkedHashMap<>();
                    int m = 1 + r.nextInt(450);
                    for (int j = 0; j < m; j++) ops.put(ks.get(r.nextInt(ks.size())), r.nextInt(3) == 0 ? DEL : value(size()));
                    commit(ops);
                }
                what = "mixed"; break; }
            default: { // everything deleted
                batch(new ArrayList<>(latest.keySet()), true, 400); what = "all deleted"; break; }
            }
            checkLatest("step " + step + " (" + what + ")");
            if (step % 3 == 0) checkOld("step " + step);
            if (step % 10 == 9) {
                db.close();
                open();
                checkLatest("step " + step + " restarted");
                checkOld("step " + step + " restarted");
            }
            if (step % 10 == 0) System.out.println("  step " + step + ": tx " + nTx + " keys " + latest.size() + " scans " + nScan
                    + " old " + nOld + " maintain " + nMaintain + " stream " + db.getStreamLength() / 1000 + " kB, first "
                    + (db.getFirstAvailableLookupTime() > 0 ? "moved" : "0"));
        }
        db.close();
        System.out.println("TREESHAPER OK");
    }

    static void open() throws Exception {
        clock = new TestClock();
        clock.setTime(Time.units(now));
        db = Db.builder().mainStream(new FileStream(new File(dir))).cacheSizeIndicator(4_000_000).clock(clock).start();
    }

    static byte[] at(BK k, long t) {
        TreeMap<Long, byte[]> v = versions.get(k);
        if (v == null) return null;
        Map.Entry<Long, byte[]> e = v.floorEntry(t);
        return e == null || e.getValue() == DEL ? null : e.getValue();
    }

    static TreeMap<BK, byte[]> stateAt(long t) {
        if (t == Long.MAX_VALUE) return latest;
        TreeMap<BK, byte[]> m = new TreeMap<>();
        for (BK k : versions.keySet()) { byte[] v = at(k, t); if (v != null) m.put(k, v); }
        return m;
    }

    static boolean own(byte[] kb) { return kb.length >= 2 && kb[0] == 1 && kb[1] == 0x25; }

    static List<Kvt> scan(GetMany g) {
        db.getMany(g);
        List<Kvt> l = new ArrayList<>();
        for (Kvt k : g.result) if (!own(Keys.toBytes(k.key))) l.add(k);
        return l;
    }

    static void compare(Collection<Map.Entry<BK, byte[]>> exp, List<Kvt> got, String what) {
        Iterator<Map.Entry<BK, byte[]>> it = exp.iterator();
        int i = 0;
        for (Kvt k : got) {
            if (!it.hasNext()) fail(what + ": more KVs than " + exp.size() + "; extra " + new BK(Keys.toBytes(k.key)));
            Map.Entry<BK, byte[]> e = it.next();
            byte[] kb = Keys.toBytes(k.key);
            if (!Arrays.equals(kb, e.getKey().b)) fail(what + ": KV " + i + " is " + new BK(kb) + ", expected " + e.getKey());
            if (!Arrays.equals(k.value, e.getValue())) fail(what + ": KV " + i + " " + e.getKey() + " has another value ("
                    + k.value.length + " bytes, expected " + e.getValue().length + ")");
            i++;
        }
        if (it.hasNext()) fail(what + ": " + got.size() + " KVs, expected " + exp.size());
        nScan++;
    }

    static void checkAt(long t, String what) {
        TreeMap<BK, byte[]> m = stateAt(t);
        GetMany g = db.newGetMany();
        g.lookupTime = t;
        compare(m.entrySet(), scan(g), what + " all forward");
        g = db.newGetMany();
        g.lookupTime = t;
        g.setBackward();
        List<Kvt> back = scan(g);
        compare(m.descendingMap().entrySet(), back, what + " all backward");
        if (m.isEmpty()) return;
        List<BK> keys = new ArrayList<>(m.keySet());
        for (int q = 0; q < 4; q++) {
            BK a = keys.get(r.nextInt(keys.size()));
            byte[] startB = a.b.clone();
            if (r.nextBoolean() && startB.length > 0) startB[startB.length - 1]++;   // a key that may not exist
            if (startB.length == 0) startB = new byte[] {0};
            BK s = new BK(startB);
            boolean incl = r.nextBoolean();
            g = db.newGetMany(); g.lookupTime = t; g.startKey = Keys.toSegments(s.b); g.inclusive = incl;
            compare(m.tailMap(s, incl).entrySet(), scan(g), what + " forward from " + s + " incl " + incl);
            g = db.newGetMany(); g.lookupTime = t; g.startKey = Keys.toSegments(s.b); g.inclusive = incl; g.setBackward();
            compare(m.headMap(s, incl).descendingMap().entrySet(), scan(g), what + " backward from " + s + " incl " + incl);
            BK z = keys.get(r.nextInt(keys.size()));
            if (z.compareTo(s) >= 0) {
                boolean ei = r.nextBoolean();
                g = db.newGetMany(); g.lookupTime = t; g.startKey = Keys.toSegments(s.b); g.inclusive = incl;
                g.endKey = Keys.toSegments(z.b); g.endInclusive = ei;
                compare(m.subMap(s, incl, z, ei).entrySet(), scan(g), what + " range " + s + " to " + z);
            }
            int nn = r.nextInt(20);
            g = db.newGetMany(); g.lookupTime = t; g.startKey = Keys.toSegments(s.b); g.stopCondition = new GetMany.GetN(nn);
            db.getMany(g);
            List<Map.Entry<BK, byte[]>> first = new ArrayList<>();
            // GetN counts BergDB's own keys too: compare only when none is in the range.
            boolean ownIn = false;
            for (Kvt k : g.result) if (own(Keys.toBytes(k.key))) ownIn = true;
            if (!ownIn) {
                for (Map.Entry<BK, byte[]> e : m.tailMap(s, true).entrySet()) { if (first.size() >= nn) break; first.add(e); }
                compare(first, g.result, what + " GetN(" + nn + ") from " + s);
            }
        }
        GetData gd = db.newGetData();
        for (int q = 0; q < 50; q++) {
            BK k = keys.get(r.nextInt(keys.size()));
            byte[] v = db.getOne(t, Keys.toSegments(k.b), gd);
            if (!Arrays.equals(v, m.get(k))) fail(what + ": getOne " + k);
        }
    }

    static void checkLatest(String what) { checkAt(Long.MAX_VALUE, what); }

    static void checkOld(String what) {
        long fa = db.getFirstAvailableLookupTime();
        long last = db.currentTime();
        if (last <= fa) return;
        for (int q = 0; q < 2; q++) {
            long t = fa + (long) (r.nextDouble() * (last - fa));
            try {
                checkAt(t, what + " at " + t);
                nOld++;
            } catch (LookupTimeNotAvailableException e) {
                if (t >= db.getFirstAvailableLookupTime()) fail(what + ": read at " + t + " refused, first available "
                        + db.getFirstAvailableLookupTime());
            }
        }
    }
}
