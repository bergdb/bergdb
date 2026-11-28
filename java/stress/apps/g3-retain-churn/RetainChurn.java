import bergdb.pub.*;
import bergdb.pub.util.*;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * RetainChurn (031-02, e3). A file database with a test clock that the app moves, a short
 * retain duration and a small startup distance, in rounds: fill (thousands of keys in w()
 * batches), churn (overwrites, deletes, ranges deleted and put again in reverse order, keys
 * of many lengths around the 7-byte steps, names outside ASCII), empty (every key deleted),
 * then maintain() called as the clock moves until it has nothing more to do, and a restart,
 * some with a cache budget of 4 MB. The oracle keeps every version of every key with its
 * transaction's time. Checked: every listing of a directory forward and backward from a
 * name, inclusive or not, at the latest time and at older times from the first available
 * one; gets at older times; a read before the first available time refused with
 * LookupTimeNotAvailableException; the first available time never later than the clock less
 * the retain duration, and never moving back within a run; transactionInfo() of a value
 * whose version is within the available times; the stream kept after emptying (printed).
 *
 * With -DretainChanges=true the retain duration changes now and then between rounds; with
 * -Dprobe=true an emptied round goes on after its maintain() calls: more calls, a restart
 * and small writes, with the size of the stream kept printed (031-02, F2).
 *
 * Usage: java RetainChurn DIR SEED ROUNDS
 */
public class RetainChurn {
    static void fail(String m) {
        System.out.println("RETAINCHURN FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    static final String[] DIRS = {"/c/", "/c/sub/", "/z/", "/ö/"};
    static final Map<String, TreeMap<Long, String>> versions = new HashMap<>();
    static final TreeMap<String, String> latest = new TreeMap<>();
    static long now;
    static TestClock clock;
    static Database db;
    static Connection c;
    static String dir;
    static long retainUnits;
    static long checkRetain = Long.MAX_VALUE, checkRetainUntil = 0;

    static long retainForCheck() {
        return now > checkRetainUntil ? retainUnits : Math.min(checkRetain, retainUnits);
    }
    static long lastFirstAvailable = 0;
    static long nTx, nChecks, nOldChecks, nRefusedOld, nMaintain;
    static Random r;
    // The checks' own random numbers, so that the workload does not depend on what the
    // database does (when reclaim cuts, how long maintain() runs).
    static Random rc;

    static String dirOf(String key) { return key.substring(0, key.lastIndexOf('/') + 1); }
    static String nameOf(String key) { return key.substring(key.lastIndexOf('/') + 1); }

    // Names in the order the listing uses: by their UTF-8 bytes.
    static final Comparator<String> BYTES = (a, b) -> Arrays.compareUnsigned(
            a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));

    static String newName() {
        int shape = r.nextInt(6);
        int n = r.nextInt(4000);
        switch (shape) {
        case 0: return "k" + n + ".txt";
        case 1: return String.format("%05d", n) + ".txt";
        case 2: { // names that end the key near a 7-byte step
            int len = 3 + r.nextInt(30);
            StringBuilder sb = new StringBuilder("w" + n);
            while (sb.length() < len) sb.append((char) ('a' + r.nextInt(3)));
            return sb + ".txt";
        }
        case 3: return "å" + n + "é.txt";
        case 4: return "b" + n + ".bin";
        default: { // long names, near the key limit
            StringBuilder sb = new StringBuilder("long" + n + "-");
            while (sb.length() < 80 + r.nextInt(20)) sb.append((char) ('a' + r.nextInt(26)));
            return sb + ".txt";
        }
        }
    }

    static String newKey() {
        String k = DIRS[r.nextInt(DIRS.length)] + newName();
        if (Limits.keyBytes(k) > Limits.MAX_KEY_BYTES) return DIRS[0] + "x" + r.nextInt(1000) + ".txt";
        return k;
    }

    static String newValue() {
        int n = r.nextInt(8) == 0 ? 500 + r.nextInt(3000) : r.nextInt(60);
        StringBuilder sb = new StringBuilder();
        sb.append(nTx).append(':');
        while (sb.length() < n) sb.append((char) ('A' + r.nextInt(26)));
        return sb.toString();
    }

    static void tick(long maxUnits) {
        now += r.nextInt((int) Math.max(1, maxUnits));
        clock.setTime(Time.units(now));
    }

    static void record(Transaction t, Map<String, String> ops) {
        long tt = t.getTime().units();
        for (Map.Entry<String, String> e : ops.entrySet()) {
            TreeMap<Long, String> v = versions.computeIfAbsent(e.getKey(), k -> new TreeMap<>());
            if (!v.isEmpty() && v.lastKey() >= tt) fail("time " + tt + " not after " + v.lastKey());
            v.put(tt, e.getValue());
            if (e.getValue() == null) latest.remove(e.getKey()); else latest.put(e.getKey(), e.getValue());
        }
        nTx++;
        checkFirstAvailable();
    }

    static void checkFirstAvailable() {
        long fa = db.getFirstAvailableLookupTime().units();
        if (fa < lastFirstAvailable) fail("first available time moved back within a run: " + fa + " < "
                + lastFirstAvailable);
        if (fa > lastFirstAvailable && fa > now - retainForCheck()) fail("first available time " + fa
                + " is later than the clock less the retain duration, " + (now - retainForCheck()));
        lastFirstAvailable = fa;
    }

    static void execute(Map<String, String> ops) {
        WBuilder w = c.w();
        for (Map.Entry<String, String> e : ops.entrySet()) {
            if (e.getValue() == null) w.delete(e.getKey());
            else if (e.getKey().endsWith(".bin")) w.put(e.getKey(), e.getValue().getBytes(StandardCharsets.UTF_8));
            else w.put(e.getKey(), e.getValue());
        }
        record(w.execute(), ops);
    }

    static void single(String key, String value) {
        Transaction t;
        if (value == null) t = c.delete(key);
        else if (key.endsWith(".bin")) t = c.put(key, value.getBytes(StandardCharsets.UTF_8));
        else t = c.put(key, value);
        Map<String, String> m = new HashMap<>();
        m.put(key, value);
        record(t, m);
    }

    public static void main(String[] args) throws Exception {
        dir = args[0];
        long seed = Long.parseLong(args[1]);
        int rounds = Integer.parseInt(args[2]);
        r = new Random(seed);
        rc = new Random(seed + 1_000_000);
        System.out.println("RetainChurn seed " + seed + " rounds " + rounds);
        now = Time.utc("2026-01-01 00:00:00").units();
        clock = new TestClock();
        clock.setTime(Time.units(now));
        db = Factory.database().create(dir).clock(clock).start();
        db.setStartupDistanceInMb(5);
        long retainSec = 5 + r.nextInt(20);
        retainUnits = retainSec * Clock.UNITS_PER_SEC;
        db.setRetainDuration(Duration.seconds(retainSec));
        c = db.connection();
        db.sync();
        long freshSize = dirSize();
        for (int round = 0; round < rounds; round++) {
            int keys = 2000 + r.nextInt(r.nextInt(4) == 0 ? 60000 : 8000);
            // Fill.
            while (latest.size() < keys) {
                Map<String, String> ops = new LinkedHashMap<>();
                int n = 1 + r.nextInt(400);
                for (int i = 0; i < n; i++) ops.put(newKey(), newValue());
                tick(Clock.UNITS_PER_SEC / 20);
                execute(ops);
            }
            check("round " + round + " filled");
            // Churn.
            int churn = 2000 + r.nextInt(6000);
            for (int i = 0; i < churn; i++) {
                tick(Clock.UNITS_PER_SEC / 50);
                int op = r.nextInt(100);
                List<String> ks = new ArrayList<>(latest.keySet());
                if (ks.isEmpty()) break;
                if (op < 40) single(ks.get(r.nextInt(ks.size())), newValue());
                else if (op < 60) single(ks.get(r.nextInt(ks.size())), null);
                else if (op < 63) single(newKey(), null);       // a delete of a key without a value
                else if (op < 85) {
                    Map<String, String> ops = new LinkedHashMap<>();
                    int n = 1 + r.nextInt(300);
                    for (int j = 0; j < n; j++) {
                        String k = r.nextBoolean() ? ks.get(r.nextInt(ks.size())) : newKey();
                        ops.put(k, r.nextInt(3) == 0 ? null : newValue());
                    }
                    execute(ops);
                } else if (op < 95) {
                    // A range of a directory deleted, then put again in reverse order.
                    String d = DIRS[r.nextInt(DIRS.length)];
                    List<String> names = new ArrayList<>();
                    for (String k : latest.keySet()) if (dirOf(k).equals(d)) names.add(k);
                    if (names.isEmpty()) continue;
                    names.sort((a, b) -> BYTES.compare(nameOf(a), nameOf(b)));
                    int from = r.nextInt(names.size());
                    int to = Math.min(names.size(), from + 1 + r.nextInt(600));
                    List<String> range = names.subList(from, to);
                    for (int j = 0; j < range.size(); j += 450) {
                        Map<String, String> ops = new LinkedHashMap<>();
                        for (String k : range.subList(j, Math.min(range.size(), j + 450))) ops.put(k, null);
                        execute(ops);
                    }
                    if (r.nextBoolean()) {
                        List<String> rev = new ArrayList<>(range);
                        Collections.reverse(rev);
                        for (int j = 0; j < rev.size(); j += 1 + r.nextInt(100)) {
                            Map<String, String> ops = new LinkedHashMap<>();
                            for (String k : rev.subList(j, Math.min(rev.size(), j + 100))) ops.put(k, newValue());
                            execute(ops);
                        }
                    }
                } else {
                    checkOld("churn " + i);
                }
                if (i % 1000 == 999) check("round " + round + " churn " + i);
            }
            check("round " + round + " churned");
            if (r.nextInt(3) > 0) {
                // Empty.
                List<String> ks = new ArrayList<>(latest.keySet());
                Collections.shuffle(ks, r);
                for (int j = 0; j < ks.size(); j += 450) {
                    Map<String, String> ops = new LinkedHashMap<>();
                    for (String k : ks.subList(j, Math.min(ks.size(), j + 450))) ops.put(k, null);
                    tick(Clock.UNITS_PER_SEC / 10);
                    execute(ops);
                }
                check("round " + round + " emptied");
                // maintain() as the clock moves, until the stream kept no longer shrinks.
                StringBuilder traj = new StringBuilder();
                long best = Long.MAX_VALUE;
                int sinceBest = 0;
                for (int step = 0; step < 400 && sinceBest < 40; step++) {
                    int calls = 0;
                    while (db.maintain()) {
                        calls++; nMaintain++;
                        if (calls > 100000) fail("maintain() returns true 100,000 times");
                        if (calls % 50 == 0) checkFirstAvailableOnly();
                    }
                    nMaintain++;
                    checkFirstAvailableOnly();
                    now += retainUnits / 4 + rc.nextInt((int) Math.min(Integer.MAX_VALUE, retainUnits / 4));
                    clock.setTime(Time.units(now));
                    if (step % 20 == 19) checkOld("maintain step " + step);
                    long sz = dirSize();
                    if (sz < best) { best = sz; sinceBest = 0; } else sinceBest++;
                    if (step % 10 == 0) traj.append(' ').append(sz / 1000);
                }
                System.out.println("  maintain trajectory (kB every 10 steps of a quarter to half the retain"
                        + " duration):" + traj);
                if (Boolean.getBoolean("probe")) probe(freshSize);
                long size = dirSize();
                System.out.println("  round " + round + ": emptied and maintained, stream files "
                        + size / 1000 + " kB (fresh " + freshSize / 1000 + " kB), first available "
                        + db.getFirstAvailableLookupTime() + ", clock " + Time.units(now) + ", retain "
                        + retainUnits / Clock.UNITS_PER_SEC + " s, last commit " + c.currentTime());
                check("round " + round + " maintained");
            }
            // The retain duration changed now and then.
            if (Boolean.getBoolean("retainChanges") && r.nextInt(3) == 0) {
                long sec = 3 + r.nextInt(30);
                db.setRetainDuration(Duration.seconds(sec));
                long old = retainUnits;
                retainUnits = sec * Clock.UNITS_PER_SEC;
                // After an increase, a cut may still follow the shorter duration until the
                // longer one has passed: the checks use the shorter until then.
                checkRetain = Math.min(old, retainUnits);
                checkRetainUntil = now + retainUnits;
                System.out.println("  round " + round + ": retain duration now " + sec + " s");
            }
            // Restart.
            db.close();
            DatabaseBuilder b = Factory.database().open(dir);
            if (r.nextBoolean()) b.cacheSizeInMb(4);
            clock = new TestClock();
            clock.setTime(Time.units(now));
            db = b.clock(clock).start();
            c = db.connection();
            if (db.getRetainDuration().units() != retainUnits) fail("retain duration after a restart: "
                    + db.getRetainDuration());
            if (db.getStartupDistanceInMb() != 5) fail("startup distance after a restart");
            long fa = db.getFirstAvailableLookupTime().units();
            if (fa != lastFirstAvailable) fail("first available after a clean restart " + fa + ", before "
                    + lastFirstAvailable);
            check("round " + round + " restarted");
            for (int k = 0; k < 5; k++) checkOld("round " + round + " restarted");
            System.out.println("  round " + round + " done: tx " + nTx + " keys " + latest.size() + " checks "
                    + nChecks + " old " + nOldChecks + " refused-old " + nRefusedOld + " maintain calls "
                    + nMaintain);
        }
        db.close();
        System.out.println("RETAINCHURN OK");
    }

    // After the maintain loop: more calls, a restart, then small writes, with the size kept.
    static void probe(long fresh) throws Exception {
        StringBuilder sb = new StringBuilder();
        for (int step = 0; step < 200; step++) {
            while (db.maintain()) nMaintain++;
            now += retainUnits / 2;
            clock.setTime(Time.units(now));
            if (step % 50 == 0) sb.append(' ').append(dirSize() / 1000);
        }
        System.out.println("  probe: 200 more steps:" + sb + " kB; first available " + db.getFirstAvailableLookupTime()
                + ", clock " + Time.units(now) + ", retain " + retainUnits / Clock.UNITS_PER_SEC + " s");
        db.close();
        clock = new TestClock();
        clock.setTime(Time.units(now));
        db = Factory.database().open(dir).clock(clock).start();
        c = db.connection();
        sb.setLength(0);
        for (int step = 0; step < 100; step++) {
            while (db.maintain()) nMaintain++;
            now += retainUnits / 2;
            clock.setTime(Time.units(now));
            if (step % 25 == 0) sb.append(' ').append(dirSize() / 1000);
        }
        System.out.println("  probe: after a restart, 100 steps:" + sb + " kB");
        sb.setLength(0);
        // Small writes: a put and a delete of 1 kB, with the clock moving.
        String big = "x".repeat(1000);
        for (int i = 0; i < 30000; i++) {
            Transaction t = c.put("/probe/p.txt", big);
            Map<String, String> m = new HashMap<>(); m.put("/probe/p.txt", big); record(t, m);
            t = c.delete("/probe/p.txt");
            m.put("/probe/p.txt", null); record(t, m);
            now += retainUnits / 200;
            clock.setTime(Time.units(now));
            if (i % 3000 == 0) { while (db.maintain()) nMaintain++; sb.append(' ').append(dirSize() / 1000); }
        }
        System.out.println("  probe: 30,000 puts of 1 kB and deletes (about 30 MB):" + sb + " kB, then " + dirSize() / 1000 + " kB");
    }

    static long dirSize() {
        long s = 0;
        File[] fs = new File(dir).listFiles();
        if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) s += f.length();
        return s;
    }

    static void checkFirstAvailableOnly() {
        long fa = db.getFirstAvailableLookupTime().units();
        if (fa < lastFirstAvailable) fail("first available time moved back: " + fa);
        if (fa > lastFirstAvailable && fa > now - retainForCheck()) fail("first available time " + fa
                + " later than the clock less the retain duration " + (now - retainForCheck()) + " (maintain)");
        lastFirstAvailable = fa;
    }

    static String at(String key, long t) {
        TreeMap<Long, String> v = versions.get(key);
        if (v == null) return null;
        Map.Entry<Long, String> e = v.floorEntry(t);
        return e == null ? null : e.getValue();
    }

    static void check(String what) {
        listAll(c, Long.MAX_VALUE, what);
        // transactionInfo of some keys.
        List<String> ks = new ArrayList<>(latest.keySet());
        long fa = db.getFirstAvailableLookupTime().units();
        for (int i = 0; i < Math.min(30, ks.size()); i++) {
            String k = ks.get(rc.nextInt(ks.size()));
            byte[] v = c.get(k, byte[].class);
            long vt = versions.get(k).lastKey();
            if (vt >= fa) {
                long it = c.transactionInfo().time().units();
                if (it != vt) fail(what + ": transactionInfo of " + k + " gives " + it + ", the version's time "
                        + vt);
            }
        }
        nChecks++;
    }

    static void listAll(Connection cc, long t, String what) {
        for (String d : DIRS) {
            List<String> exp = new ArrayList<>();
            if (t == Long.MAX_VALUE) {
                for (String k : latest.keySet()) if (dirOf(k).equals(d)) exp.add(k);
            } else {
                for (String k : versions.keySet()) if (dirOf(k).equals(d) && at(k, t) != null) exp.add(k);
            }
            exp.sort((a, b) -> BYTES.compare(nameOf(a), nameOf(b)));
            List<Kv<byte[]>> got = new ArrayList<>();
            for (Kv<byte[]> kv : cc.usePrimary(byte[].class).dir(d).kvs()) got.add(kv);
            compareList(exp, got, t, what + ": " + d + " forward");
            if (exp.isEmpty()) continue;
            // Backward from a name, inclusive or not.
            String startKey = exp.get(rc.nextInt(exp.size()));
            boolean incl = rc.nextBoolean();
            List<String> expB = new ArrayList<>();
            for (String k : exp) {
                int cmp = BYTES.compare(nameOf(k), nameOf(startKey));
                if (cmp < 0 || (cmp == 0 && incl)) expB.add(k);
            }
            Collections.reverse(expB);
            got.clear();
            for (Kv<byte[]> kv : cc.usePrimary(byte[].class).dir(d).startAt(nameOf(startKey)).inclusive(incl)
                    .backward().kvs()) got.add(kv);
            compareList(expB, got, t, what + ": " + d + " backward from " + nameOf(startKey) + " incl " + incl);
            // Forward from a name that no key has.
            String probe = nameOf(startKey) + "~";
            List<String> expF = new ArrayList<>();
            for (String k : exp) if (BYTES.compare(nameOf(k), probe) >= 0) expF.add(k);
            got.clear();
            for (Kv<byte[]> kv : cc.usePrimary(byte[].class).dir(d).startAt(probe).kvs()) got.add(kv);
            compareList(expF, got, t, what + ": " + d + " forward from " + probe);
        }
    }

    static void compareList(List<String> exp, List<Kv<byte[]>> got, long t, String what) {
        for (int i = 0; i < Math.min(exp.size(), got.size()); i++) {
            String k = exp.get(i);
            if (!got.get(i).key().equals(k)) fail(what + " at " + t + ": entry " + i + " is " + got.get(i).key()
                    + ", expected " + k);
            String ev = t == Long.MAX_VALUE ? latest.get(k) : at(k, t);
            String gv = new String(got.get(i).value(), StandardCharsets.UTF_8);
            if (!gv.equals(ev)) fail(what + " at " + t + ": " + k + " = " + abbrev(gv) + ", expected " + abbrev(ev));
        }
        if (exp.size() != got.size()) fail(what + " at " + t + ": " + got.size() + " keys, expected " + exp.size());
    }

    static String abbrev(String s) { return s == null ? "null" : s.length() > 40 ? s.substring(0, 40) + "..." : s; }

    static void checkOld(String what) {
        long fa = db.getFirstAvailableLookupTime().units();
        long last = c.currentTime().units();
        if (last <= fa) return;
        Connection o = db.newConnection();
        long t = fa + (long) (rc.nextDouble() * (last - fa));
        o.setLookupTime(Time.units(t));
        try {
            listAll(o, t, what + " (old)");
        } catch (LookupTimeNotAvailableException e) {
            fail(what + ": a listing at " + t + ", after the first available time " + fa + ", refused");
        }
        nOldChecks++;
        if (fa > 0) {
            o.setLookupTime(Time.units(fa - 1 - rc.nextInt(1000)));
            String k = versions.keySet().iterator().next();
            try {
                o.get(k, byte[].class);
                fail(what + ": a get before the first available time was not refused");
            } catch (LookupTimeNotAvailableException e) {
                nRefusedOld++;
            }
        }
    }
}
