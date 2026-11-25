import bergdb.core.*;
import bergdb.dag.*;
import bergdb.stream.*;
import bergdb.pub.util.*;
import java.io.File;
import java.util.*;
import java.util.concurrent.atomic.*;

/**
 * CoreTransform (031-02, e2). The Core API's key and value transformations, near and over
 * the limits. Transactions of 1 to 520 KVs mix plain puts and deletes with key
 * transformations that lengthen a short key to 7 to 112 bytes with the transaction's time
 * and bytes of their own (500 of them of 111 bytes with distinct starts make the most index
 * nodes dirty), transformations that throw, that give a key of the Core's own, or that make
 * two keys one, and value transformations that add to a counter, delete, throw or pass 8 MiB.
 * Each transaction is either taken, and then the oracle, a map of the latest values with a
 * history, applies it with the time it got, or refused with a DbException: then nothing of
 * it is written, its KVs have their keys as written again, and a transaction refused by a
 * transformation that throws only once is executed again, the same Trans, and is taken. A
 * second thread increments counters by optimistic transactions (keyRead and RerunException)
 * while the main thread adds to the same counters by value transformations: each counter
 * ends at the sum of what was committed. Full scans forward and backward, ranges with an end
 * key, and scans at older times are compared with the oracle; the database restarts now and
 * then.
 *
 * Usage: java CoreTransform DIR SEED TRANSACTIONS
 */
public class CoreTransform {
    static void fail(String m) {
        System.out.println("CORETRANSFORM FAILED: " + m);
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

    static TreeMap<BK, byte[]> model = new TreeMap<>();
    // History: per commit time, the changes (value null = delete).
    static TreeMap<Long, Map<BK, byte[]>> history = new TreeMap<>();
    static final int COUNTERS = 8;
    static final AtomicLong[] counterAdds = new AtomicLong[COUNTERS];
    static volatile boolean stop = false;
    static Db db;
    static String dir;
    static long nTaken, nRefused, nRerun, nAgain, nOptimistic, nOptRerun;

    static byte[] counterKey(int i) { return ("ctr" + i).getBytes(); }

    static byte[] lng(long v) {
        byte[] b = new byte[8];
        for (int i = 0; i < 8; i++) b[i] = (byte) (v >>> (56 - 8 * i));
        return b;
    }

    static long lng(byte[] b) {
        long v = 0;
        for (int i = 0; i < Math.min(8, b.length); i++) v = (v << 8) | (b[i] & 0xff);
        return v;
    }

    // The key a lengthening transformation gives: the key as written, the time, then bytes
    // made from the key and the time, up to len bytes in all.
    static byte[] lengthen(byte[] written, long tt, int len) {
        byte[] out = new byte[len];
        int n = Math.min(len, written.length);
        System.arraycopy(written, 0, out, 0, n);
        long x = tt * 0x9E3779B97F4A7C15L + Arrays.hashCode(written);
        for (int i = n; i < len; i++) {
            int j = i - written.length;
            if (j < 8) out[i] = (byte) (tt >>> (56 - 8 * j));
            else { x ^= x << 13; x ^= x >>> 7; x ^= x << 17; out[i] = (byte) (x | 1); }
        }
        return out;
    }

    static final class Lengthen implements KeyTransformation {
        final byte[] written; final int len;
        Lengthen(byte[] w, int len) { this.written = w; this.len = len; }
        public void transform(Trans t, int index) {
            byte[] nk = lengthen(written, t.tt, len);
            long[] seg = Keys.toSegments(nk);
            t.kvs[index].setKey(seg);
            t.writeKeyHashes[index] = Keys.hash(seg);
        }
    }

    static final class Fixed implements KeyTransformation {
        final byte[] to;
        Fixed(byte[] to) { this.to = to; }
        public void transform(Trans t, int index) {
            long[] seg = Keys.toSegments(to);
            t.kvs[index].setKey(seg);
            t.writeKeyHashes[index] = Keys.hash(seg);
        }
    }

    static final class ThrowOnce implements KeyTransformation {
        boolean thrown;
        final KeyTransformation then;
        ThrowOnce(KeyTransformation then) { this.then = then; }
        public void transform(Trans t, int index) {
            if (!thrown) { thrown = true; throw new IllegalStateException("once"); }
            then.transform(t, index);
        }
    }

    static final class Add implements ValueTransformation {
        public byte[] transform(long tt, byte[] in, byte[] prev) {
            return lng((prev == null ? 0 : lng(prev)) + lng(in));
        }
    }

    static final class DeleteIfPresent implements ValueTransformation {
        public byte[] transform(long tt, byte[] in, byte[] prev) {
            return prev == null ? in : null;
        }
    }

    static final class ThrowV implements ValueTransformation {
        public byte[] transform(long tt, byte[] in, byte[] prev) { throw new RuntimeException("v"); }
    }

    static final class Huge implements ValueTransformation {
        public byte[] transform(long tt, byte[] in, byte[] prev) { return new byte[8 * 1024 * 1024 + 1]; }
    }

    // A planned KV: how the oracle applies it once the time is known.
    static final class Plan {
        byte[] written;
        int kind;       // 0 put, 1 delete, 2 lengthen-put, 3 add, 4 delete-if-present
        byte[] value;
        int len;
    }

    public static void main(String[] args) throws Exception {
        dir = args[0];
        long seed = Long.parseLong(args[1]);
        int total = Integer.parseInt(args[2]);
        System.out.println("CoreTransform seed " + seed + " transactions " + total);
        for (int i = 0; i < COUNTERS; i++) counterAdds[i] = new AtomicLong();
        open();
        Random r = new Random(seed);
        Thread opt = new Thread(() -> optimistic(seed + 1));
        opt.start();
        for (int n = 0; n < total; n++) {
            one(r, n);
            if (n % 97 == 0) checkScan(r, Long.MAX_VALUE, false);
            if (n % 211 == 0) checkOld(r);
            if (n % 1500 == 1499) {
                stop = true; opt.join(); stop = false;
                db.close();
                open();
                checkScan(r, Long.MAX_VALUE, true);
                checkOld(r);
                opt = new Thread(() -> optimistic(seed + 2 + System.nanoTime()));
                opt.start();
            }
            if (n % 1000 == 0) System.out.println("  " + n + ": taken " + nTaken + " refused " + nRefused
                    + " again " + nAgain + " keys " + model.size() + " optimistic " + nOptimistic
                    + " (reruns " + nOptRerun + ")");
        }
        stop = true;
        opt.join();
        checkScan(r, Long.MAX_VALUE, true);
        for (int i = 0; i < 10; i++) checkOld(r);
        db.close();
        open();
        checkScan(r, Long.MAX_VALUE, true);
        for (int i = 0; i < 10; i++) checkOld(r);
        db.close();
        System.out.println("taken " + nTaken + ", refused " + nRefused + ", executed again " + nAgain
                + ", optimistic increments " + nOptimistic + " (reruns " + nOptRerun + "), keys " + model.size());
        System.out.println("CORETRANSFORM OK");
    }

    static void open() throws Exception {
        db = Db.builder().mainStream(new FileStream(new File(dir))).cacheSizeIndicator(8_000_000).start();
    }

    // The counters: the model's value is checked against the sum of every committed add,
    // so the optimistic thread's writes do not go into the map's history.
    static boolean isCounter(BK k) {
        return k.b.length >= 3 && k.b[0] == 'c' && k.b[1] == 't' && k.b[2] == 'r';
    }

    static void optimistic(long seed) {
        Random r = new Random(seed);
        GetData gd = db.newGetData();
        while (!stop) {
            int i = r.nextInt(COUNTERS);
            long[] seg = Keys.toSegments(counterKey(i));
            while (true) {
                long t = db.currentTime();
                byte[] old = db.getOne(t, seg, gd);
                long v = old == null ? 0 : lng(old);
                Trans.Builder b = db.trans().lookupTime(t).keyRead(seg);
                b.put(counterKey(i), lng(v + 1));
                try {
                    db.execute(b.build());
                    counterAdds[i].incrementAndGet();
                    nOptimistic++;
                    break;
                } catch (RerunException e) {
                    nOptRerun++;
                }
            }
            try { Thread.sleep(r.nextInt(3)); } catch (InterruptedException e) { return; }
        }
    }

    static void one(Random r, int n) {
        int mode = r.nextInt(100);
        int size;
        if (mode < 8) size = 495 + r.nextInt(6);         // near the limit, taken
        else if (mode < 11) size = 501 + r.nextInt(20);  // over the limit, refused
        else if (mode < 40) size = 50 + r.nextInt(450);
        else size = 1 + r.nextInt(40);
        // What refuses it, if anything.
        int refuse = 0;      // 0 none, 1 too long a key, 2 two keys one, 3 throws, 4 core key,
                             // 5 value throws, 6 value over 8 MiB, 7 throw once then retry
        int rr = r.nextInt(100);
        if (rr < 3) refuse = 1;
        else if (rr < 5) refuse = 2;
        else if (rr < 7) refuse = 3;
        else if (rr < 8) refuse = 4;
        else if (rr < 10) refuse = 5;
        else if (rr < 11 && n % 7 == 0) refuse = 6;
        else if (rr < 14) refuse = 7;
        boolean allLong = r.nextInt(6) == 0;   // every KV lengthened to 111 bytes: the worst case
        Trans.Builder b = db.trans();
        List<Plan> plans = new ArrayList<>();
        Set<BK> writtenKeys = new HashSet<>();
        List<byte[]> writtenOrder = new ArrayList<>();
        ThrowOnce once = null;
        int special = size > 0 ? r.nextInt(size) : 0;
        for (int i = 0; i < size; i++) {
            Plan p = new Plan();
            int kind = r.nextInt(100);
            byte[] key;
            do {
                if (allLong || kind < 40) {
                    key = ("L" + Integer.toString(r.nextInt(1 << 30), 36)).getBytes();
                } else {
                    key = ("p/" + r.nextInt(3000) + "/" + r.nextInt(30)).getBytes();
                }
            } while (!writtenKeys.add(new BK(key)));
            p.written = key;
            writtenOrder.add(key);
            long[] seg = Keys.toSegments(key);
            if (i == special && refuse != 0 && refuse != 5 && refuse != 6) {
                switch (refuse) {
                case 1: p.kind = 2; p.len = 112 + r.nextInt(20); break;
                case 2: p.kind = 2; p.len = 0; break;    // set below to another KV's key
                case 3: p.kind = 2; p.len = 50; break;
                case 4: p.kind = 2; p.len = 0; break;
                case 7: p.kind = 2; p.len = 7 * (1 + r.nextInt(15)) + r.nextInt(2); if (p.len > 111) p.len = 111; break;
                }
                p.value = val(r);
                KeyTransformation kt;
                if (refuse == 1) kt = new Lengthen(key, p.len);
                else if (refuse == 2) {
                    kt = new Fixed("p/dup-target".getBytes());
                    b.put("p/dup-target".getBytes(), new byte[] {1});
                }
                else if (refuse == 3) kt = (t, idx) -> { throw new IllegalArgumentException("kt"); };
                else if (refuse == 4) kt = new Fixed(Keys.toBytes("/#i/-sd"));
                else { once = new ThrowOnce(new Lengthen(key, p.len)); kt = once; }
                b.put(seg, kt, p.value, null);
                plans.add(p);
                continue;
            }
            if (i == special && refuse == 5) {
                p.kind = 3; p.value = lng(1);
                b.put(seg, null, p.value, new ThrowV());
                plans.add(p);
                continue;
            }
            if (i == special && refuse == 6) {
                p.kind = 3; p.value = lng(1);
                b.put(seg, null, p.value, new Huge());
                plans.add(p);
                continue;
            }
            if (allLong || kind < 40) {
                p.kind = 2;
                p.len = allLong ? 111 : 7 * (1 + r.nextInt(15)) + (r.nextInt(3) - 1);
                if (p.len < key.length + 1) p.len = key.length + 1;
                if (p.len > 111) p.len = 111;
                p.value = val(r);
                b.put(seg, new Lengthen(key, p.len), p.value, null);
            } else if (kind < 70) {
                p.kind = 0; p.value = val(r);
                b.put(key, p.value);
            } else if (kind < 82) {
                p.kind = 1;
                b.delete(key);
            } else if (kind < 92) {
                p.kind = 3; p.value = lng(1 + r.nextInt(5));
                b.put(seg, null, p.value, new Add());
            } else {
                p.kind = 4; p.value = val(r);
                b.put(seg, null, p.value, new DeleteIfPresent());
            }
            plans.add(p);
        }
        // Counter adds by value transformations, on keys of their own.
        int ci = -1; long cdelta = 0;
        if (r.nextInt(4) == 0 && size < 500) {
            ci = r.nextInt(COUNTERS); cdelta = 1 + r.nextInt(9);
            b.put(Keys.toSegments(counterKey(ci)), null, lng(cdelta), new Add());
        }
        Trans t = b.build();
        long[][] keysBefore = new long[t.kvs.length][];
        for (int i = 0; i < t.kvs.length; i++) keysBefore[i] = t.kvs[i].getKey().clone();
        byte[][] valuesBefore = new byte[t.kvs.length][];
        for (int i = 0; i < t.kvs.length; i++) valuesBefore[i] = t.kvs[i].getValue();
        int ops = t.kvs.length;
        boolean expectRefused = ops > 500 || (refuse != 0);
        boolean taken;
        try {
            db.execute(t);
            taken = true;
        } catch (RerunException e) {
            fail("a transaction without reads got RerunException");
            return;
        } catch (DbException e) {
            taken = false;
            if (!expectRefused) fail("transaction " + n + " of " + ops + " KVs refused: " + e);
        }
        if (taken && expectRefused) fail("transaction " + n + " of " + ops + " KVs, refusal kind " + refuse
                + ", was taken");
        if (!taken) {
            nRefused++;
            for (int i = 0; i < t.kvs.length; i++) {
                if (!Arrays.equals(t.kvs[i].getKey(), keysBefore[i])) fail("refused transaction " + n
                        + " (kind " + refuse + "): KV " + i + " did not get its key as written back");
                if (!Arrays.equals(t.kvs[i].getValue(), valuesBefore[i])) fail("refused transaction " + n
                        + ": KV " + i + " did not get its value back");
            }
            // Nothing written: the keys as written are as the model has them.
            checkKeys(writtenOrder, "after refused transaction " + n + " (kind " + refuse + ")");
            if (refuse == 7 && ops <= 500) {
                // Run the same Trans again: the transformation goes on this time.
                try {
                    db.execute(t);
                } catch (DbException e) {
                    fail("the refused transaction " + n + " executed again was refused: " + e);
                }
                nAgain++;
                taken = true;
            }
        }
        if (!taken) return;
        nTaken++;
        long tt = t.tt;
        if (history.containsKey(tt) || (!history.isEmpty() && history.lastKey() >= tt)) {
            fail("time " + tt + " not after the last, " + history.lastKey());
        }
        Map<BK, byte[]> changes = new LinkedHashMap<>();
        for (Plan p : plans) {
            if (p == null) continue;
            BK wk = new BK(p.written);
            switch (p.kind) {
            case 0: changes.put(wk, p.value); break;
            case 1: changes.put(wk, null); break;
            case 2: {
                BK nk = new BK(lengthen(p.written, tt, p.len));
                changes.put(nk, p.value);
                break;
            }
            case 3: {
                byte[] prev = model.get(wk);
                changes.put(wk, lng((prev == null ? 0 : lng(prev)) + lng(p.value)));
                break;
            }
            case 4: {
                byte[] prev = model.get(wk);
                changes.put(wk, prev == null ? p.value : null);
                break;
            }
            }
        }
        if (ci >= 0) counterAdds[ci].addAndGet(cdelta);
        for (Map.Entry<BK, byte[]> e : changes.entrySet()) {
            if (e.getValue() == null) model.remove(e.getKey()); else model.put(e.getKey(), e.getValue());
        }
        history.put(tt, changes);
        // Each changed key at the latest time and just before.
        GetData gd = db.newGetData();
        for (Map.Entry<BK, byte[]> e : changes.entrySet()) {
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(e.getKey().b), gd);
            byte[] exp = model.get(e.getKey());
            if (!Arrays.equals(v, exp)) fail("after transaction " + n + " at " + tt + ": key " + e.getKey()
                    + " is " + Arrays.toString(v) + ", expected " + Arrays.toString(exp));
        }
    }

    static byte[] val(Random r) {
        int n = r.nextInt(10) == 0 ? r.nextInt(3000) : r.nextInt(40);
        byte[] v = new byte[n];
        r.nextBytes(v);
        return v;
    }

    static void checkKeys(List<byte[]> keys, String what) {
        GetData gd = db.newGetData();
        for (byte[] k : keys) {
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(k), gd);
            BK bk = new BK(k);
            if (isCounter(bk)) continue;
            if (!Arrays.equals(v, model.get(bk))) fail(what + ": key " + bk + " is " + Arrays.toString(v)
                    + ", expected " + Arrays.toString(model.get(bk)));
        }
        byte[] dup = db.getOne(Long.MAX_VALUE, Keys.toSegments("p/dup-target".getBytes()), gd);
        if (dup != null) fail(what + ": p/dup-target has a value");
    }

    // The map at time t: the model's state, rebuilt from the history.
    static TreeMap<BK, byte[]> at(long t) {
        TreeMap<BK, byte[]> m = new TreeMap<>();
        for (Map.Entry<Long, Map<BK, byte[]>> h : history.headMap(t, true).entrySet()) {
            for (Map.Entry<BK, byte[]> e : h.getValue().entrySet()) {
                if (e.getValue() == null) m.remove(e.getKey()); else m.put(e.getKey(), e.getValue());
            }
        }
        return m;
    }

    static List<Map.Entry<BK, byte[]>> userEntries(TreeMap<BK, byte[]> m) {
        List<Map.Entry<BK, byte[]>> l = new ArrayList<>();
        for (Map.Entry<BK, byte[]> e : m.entrySet()) if (!isCounter(e.getKey())) l.add(e);
        return l;
    }

    // Scans at time t (MAX: latest): every KV forward, then backward from a random key, then a
    // range with an end key; BergDB's own keys (01 25 ...) and the counters skipped.
    static void checkScan(Random r, long t, boolean counters) {
        TreeMap<BK, byte[]> m = t == Long.MAX_VALUE ? model : at(t);
        List<Map.Entry<BK, byte[]>> exp = userEntries(m);
        GetMany g = db.newGetMany();
        g.lookupTime = t;
        db.getMany(g);
        List<Kvt> got = new ArrayList<>();
        for (Kvt k : g.result) {
            byte[] kb = Keys.toBytes(k.key);
            if (kb.length >= 2 && kb[0] == 1 && kb[1] == 0x25) continue;
            if (isCounter(new BK(kb))) continue;
            got.add(k);
        }
        compare(exp, got, "forward scan at " + t);
        if (t == Long.MAX_VALUE && counters) {
            for (int i = 0; i < COUNTERS; i++) {
                byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(counterKey(i)), db.newGetData());
                long got2 = v == null ? 0 : lng(v);
                if (got2 != counterAdds[i].get()) fail("counter " + i + " is " + got2 + ", committed adds "
                        + counterAdds[i].get());
            }
        }
        if (exp.isEmpty()) return;
        // Backward from a random model key, exclusive.
        BK start = exp.get(r.nextInt(exp.size())).getKey();
        g = db.newGetMany();
        g.lookupTime = t;
        g.startKey = Keys.toSegments(start.b);
        g.inclusive = false;
        g.setBackward();
        db.getMany(g);
        List<Map.Entry<BK, byte[]>> expB = new ArrayList<>();
        for (Map.Entry<BK, byte[]> e : m.headMap(start, false).descendingMap().entrySet()) {
            if (!isCounter(e.getKey())) expB.add(e);
        }
        got = new ArrayList<>();
        for (Kvt k : g.result) {
            byte[] kb = Keys.toBytes(k.key);
            if (kb.length >= 2 && kb[0] == 1 && kb[1] == 0x25) continue;
            if (isCounter(new BK(kb))) continue;
            got.add(k);
        }
        compare(expB, got, "backward scan from " + start + " at " + t);
        // A range [a, b) with an end key.
        BK a = exp.get(r.nextInt(exp.size())).getKey();
        BK z = exp.get(r.nextInt(exp.size())).getKey();
        if (a.compareTo(z) > 0) { BK x = a; a = z; z = x; }
        g = db.newGetMany();
        g.lookupTime = t;
        g.startKey = Keys.toSegments(a.b);
        g.endKey = Keys.toSegments(z.b);
        g.endInclusive = false;
        db.getMany(g);
        List<Map.Entry<BK, byte[]>> expR = new ArrayList<>();
        for (Map.Entry<BK, byte[]> e : m.subMap(a, true, z, false).entrySet()) {
            if (!isCounter(e.getKey())) expR.add(e);
        }
        got = new ArrayList<>();
        for (Kvt k : g.result) {
            byte[] kb = Keys.toBytes(k.key);
            if (kb.length >= 2 && kb[0] == 1 && kb[1] == 0x25) continue;
            if (isCounter(new BK(kb))) continue;
            got.add(k);
        }
        compare(expR, got, "range scan [" + a + ", " + z + ") at " + t);
    }

    static void compare(List<Map.Entry<BK, byte[]>> exp, List<Kvt> got, String what) {
        int n = Math.min(exp.size(), got.size());
        for (int i = 0; i < n; i++) {
            byte[] gk = Keys.toBytes(got.get(i).key);
            if (!Arrays.equals(gk, exp.get(i).getKey().b)) fail(what + ": entry " + i + " is key "
                    + new BK(gk) + ", expected " + exp.get(i).getKey());
            if (!Arrays.equals(got.get(i).value, exp.get(i).getValue())) fail(what + ": entry " + i
                    + " key " + new BK(gk) + " has another value");
        }
        if (exp.size() != got.size()) fail(what + ": " + got.size() + " KVs, expected " + exp.size());
    }

    static void checkOld(Random r) {
        if (history.isEmpty()) return;
        List<Long> times = new ArrayList<>(history.keySet());
        long t = times.get(r.nextInt(times.size()));
        if (r.nextBoolean()) t = t - 1;    // just before a transaction
        checkScan(r, t, false);
    }
}
