import bergdb.pub.*;
import bergdb.pub.util.LookupTimeNotAvailableException;

import java.io.File;
import java.util.*;

/**
 * App e1 of 031-08: Database.maintain(int budget) against what its Javadoc promises, with a
 * test clock that the application moves (Pub API).
 *
 * A database (a file one, or one in memory for some seeds) with the startup distance 5 MB:
 * maintain() with budgets from Integer.MIN_VALUE to Integer.MAX_VALUE while the retain
 * duration is forever (nothing to do: the stream size must not change), then a load, then a
 * finite retain duration R and rounds of churn (w() transactions of 1 to 500 puts and
 * deletes, values of 0 to 3,000 bytes and now and then up to 1 MB), maintain() calls by the
 * seed's style (never, every action, now and then, bursts) with budgets of the style, the
 * clock moved by 0 to R/2 an action, and restarts. After every action: reads at the latest
 * time, at the first available time, and at older times inside [now - R, now], against the
 * oracle (gets, both listings of each directory, transactionInfo's time); the promise
 * getFirstAvailableLookupTime() <= currentTime() - R; the first available time never moves
 * back within a run; a read at first - 1 refused. A restart keeps the stream size, the first
 * available time and the retain duration (a start appends nothing). Then everything but a
 * few keys deleted, and the idle phase: the clock moved by R/4 a call, maintain(budget) until
 * the stream size stays the same for 16 calls in a row (a hang guard of 200,000 calls); the
 * stream kept must then be within 1 MB of a fresh twin's that holds the same live data (the
 * twin's own maintain() quiet too): getStreamSize(), "in a database not written to for
 * longer than the retain duration, what it holds beyond the live data is what maintain()
 * can give back". Prints the calls the pass took against getStreamSize() / (budget kB).
 *
 * Usage: java E1MaintainBudget SEED DIR [KEYS] [ROUNDS]
 */
public class E1MaintainBudget {
    static final long T0 = Time.utc("2026-01-01").units();
    static final long SEC = 10_000_000L;
    static final String[] DIRS = {"/e1/a/", "/e1/b/", "/e1/c/d/", "/e1/"};

    final long seed;
    final Random rnd;
    final File dir;
    final boolean memory;
    final TestClock clock = new TestClock();
    final EOracle m = new EOracle();
    long retainUnits;
    long floorFirst;      // after an increase of the retain duration: the first available time then (setRetainDuration())
    long retainChanges;
    final int style;
    Database db;
    Connection c;
    long lastFirst, cuts, reads, maintains, restarts, txs, maxStream, maxDisk, txInfos;
    double maxDiskRatio;
    long maxOver = Long.MIN_VALUE;   // the most that a maintain() call wrote beyond its budget's bytes
    int maxOverBudget;
    long overCalls;                  // calls that wrote more than 472 kB beyond the budget's bytes
    /** A FAIL above it; 4 MB by default, -De1.maxOver=N for 031-08's UA-5. */
    static final long MAX_OVER = Long.getLong("e1.maxOver", 4_000_000L);

    E1MaintainBudget(long seed, File dir) {
        this.seed = seed;
        this.rnd = new Random(seed);
        this.dir = dir;
        this.memory = rnd.nextInt(5) == 0;
        long[] rs = {1 * SEC, 1 * SEC, 3 * SEC, 20 * SEC, 600 * SEC};
        this.retainUnits = rs[rnd.nextInt(rs.length)];
        this.style = rnd.nextInt(5);
    }

    int budget() {
        switch (style) {
            case 0: return 100;                                     // the least
            case 1: return 100_000;                                 // the most
            case 2: { int[] b = {Integer.MIN_VALUE, -1, 0, 1, 99, 100, 101, 1000, 99_999, 100_000, 100_001, Integer.MAX_VALUE};
                      return b[rnd.nextInt(b.length)]; }
            case 3: return 100 + rnd.nextInt(5000);
            default: return rnd.nextInt(3) == 0 ? 0 : 20_000;
        }
    }

    /** The bytes a budget allows, by the Javadoc: clamped to 100 .. 100,000 units of about 1 kB. */
    static long budgetBytes(int b) { return 1000L * Math.max(100, Math.min(100_000, b)); }

    void start(boolean create) {
        DatabaseBuilder b = Factory.database();
        if (memory) b.memory(); else if (create) b.create(dir.getPath()); else b.open(dir.getPath());
        db = b.clock(clock).cacheSizeInMb(64).start();
        c = db.connection();
    }

    long now() { return db.currentTime().units(); }

    void tick(long units) { clock.setTime(Time.units(clock.getTime() + units)); }

    String key(int i) {
        String d = DIRS[i % DIRS.length];
        if (i % 37 == 0) return EOracle.keyOfBytes(d, "long" + i + "-", 111);   // at the limit
        return d + "k" + i + ".bin";
    }

    byte[] val() {
        int x = rnd.nextInt(1000);
        int len = x < 600 ? rnd.nextInt(200) : x < 990 ? rnd.nextInt(3000) : x < 999 ? 10_000 + rnd.nextInt(200_000) : 1_000_000;
        return EOracle.value(rnd, len);
    }

    long tx(int nOps, int keySpace, int delPct) {
        LinkedHashMap<String, byte[]> ops = new LinkedHashMap<>();
        WBuilder w = c.w();
        long bytes = 0;
        for (int j = 0; j < nOps; j++) {
            String k = key(rnd.nextInt(keySpace));
            if (rnd.nextInt(100) < delPct) { w.delete(k); ops.put(k, null); }
            else {
                byte[] v = val();
                if (bytes + v.length > 30_000_000) v = new byte[0];
                bytes += v.length;
                w.put(k, v); ops.put(k, v);
            }
        }
        long t = w.execute().getTime().units();
        m.apply(ops, t);
        txs++;
        return t;
    }

    void maintainOnce(int b) {
        long before = db.getStreamSize();
        long firstBefore = db.getFirstAvailableLookupTime().units();
        db.maintain(b);
        maintains++;
        // what the call wrote, when it cut nothing: the budget (clamped, about 1 kB a unit) and "a small part's work"
        if (db.getFirstAvailableLookupTime().units() == firstBefore) {
            long over = db.getStreamSize() - before - budgetBytes(b);
            if (over > maxOver) { maxOver = over; maxOverBudget = b; }
            if (over > 472_000) overCalls++;   // past the Core's list: a step of 16 kB, a take of 256 kB, a table padded by 200 kB
            EOracle.check(over <= MAX_OVER, "maintain(" + b + ") wrote " + (db.getStreamSize() - before) + " bytes, " + over
                    + " more than the budget's (Database.maintain(): \"may go past it by a small part's work\"; 031-08, UA-5)");
        }
        if (db.getRetainDuration().equals(Duration.MAX))
            EOracle.check(db.getStreamSize() == before, "maintain(" + b + ") with the retain duration forever changed the stream size "
                    + before + " -> " + db.getStreamSize() + " (Database.maintain(): \"With the retain duration forever ... there is nothing to do\")");
    }

    /** The checks after an action. */
    void checks(String what) {
        long now = now();
        long first = db.getFirstAvailableLookupTime().units();
        EOracle.check(first >= lastFirst, what + ": the first available time moved back, " + lastFirst + " -> " + first);
        if (first > lastFirst) cuts++;
        lastFirst = first;
        if (!db.getRetainDuration().equals(Duration.MAX))
            EOracle.check(first <= Math.max(floorFirst, now - retainUnits), what + ": first available " + first + " is after now - R = " + (now - retainUnits)
                    + " (getFirstAvailableLookupTime(): lookups work for every time in [now - retain duration, now])");
        long ss = db.getStreamSize();
        maxStream = Math.max(maxStream, ss);
        if (!memory) {
            long disk = EOracle.dirBytes(dir);
            maxDisk = Math.max(maxDisk, disk);
            if (ss > 2_000_000 && disk / (double) ss > maxDiskRatio) {
                maxDiskRatio = disk / (double) ss;
                if (maxDiskRatio > 1.5) {
                    StringBuilder sb = new StringBuilder();
                    File[] fs = dir.listFiles();
                    Arrays.sort(fs);
                    for (File f : fs) if (f.getName().endsWith(".bergdb")) sb.append(' ').append(f.getName().replaceFirst("^0+", "")).append('=').append(f.length());
                    EOracle.log("  " + what + ": disk " + disk + " for a stream of " + ss + " (" + String.format("%.2f", maxDiskRatio) + "):" + sb);
                }
            }
        }
        reads += m.verify(c, Long.MAX_VALUE, rnd, 12, 400, what + " latest");
        reads += m.verify(c, Math.max(first, m.lastTime), rnd, 4, 0, what + " last");
        reads += m.verify(c, first, rnd, 6, rnd.nextInt(8) == 0 ? 400 : 0, what + " first available");
        long lo = Math.max(first, now - retainUnits);
        // older times inside the retain duration: transaction times and the unit before each
        int i = Collections.binarySearch(m.times, lo);
        int from = i >= 0 ? i : -i - 1;
        if (from < m.times.size()) {
            for (int n = 0; n < 2; n++) {
                long t = m.times.get(from + rnd.nextInt(m.times.size() - from));
                reads += m.verify(c, t, rnd, 4, n == 0 && rnd.nextInt(6) == 0 ? 400 : 0, what + " at a transaction's time");
                if (t - 1 >= lo) reads += m.verify(c, t - 1, rnd, 3, 0, what + " just before a transaction");
            }
        }
        // transactionInfo of a value written at or after first: its own transaction, not reclaim's
        List<String> ks = m.allKeys();
        for (int n = 0; n < 3 && !ks.isEmpty(); n++) {
            String k = ks.get(rnd.nextInt(ks.size()));
            long wt = m.writeTimeAt(k, Long.MAX_VALUE);
            if (wt < 0 || wt < first) continue;
            c.setLookupTime(Time.MAX);
            c.get(k, byte[].class);
            TransactionInfo ti = c.transactionInfo();
            EOracle.check(ti.time().units() == wt, what + ": transactionInfo of " + k + " gives " + ti.time().units() + ", the write was at " + wt);
            // its KVs: exactly the application's transaction, none of reclaim's copies that a commit's record carries
            Map<String, byte[]> want = m.txKvs.get(wt);
            int n2 = 0;
            for (Kv<byte[]> kv : ti.kvs()) {
                EOracle.check(want != null && want.containsKey(kv.key()) && Arrays.equals(kv.value(), want.get(kv.key())), what
                        + ": transactionInfo of " + k + " (time " + wt + ") lists " + kv.key() + " with " + (kv.value() == null ? "a delete"
                        : kv.value().length + " bytes") + ", which that transaction did not write" + (want == null ? " (no record of it)" : ""));
                n2++;
            }
            EOracle.check(want != null && n2 == want.size(), what + ": transactionInfo of " + k + " lists " + n2 + " KVs, the transaction had "
                    + (want == null ? "?" : want.size()));
            txInfos++;
            reads++;
        }
        EOracle.checkExpired(c, first, key(1), what);
        m.prune(Math.min(first, now - retainUnits));
    }

    void restart(String what) {
        if (memory) return;
        long ss = db.getStreamSize();
        long first = db.getFirstAvailableLookupTime().units();
        Duration r = db.getRetainDuration();
        if (rnd.nextBoolean()) db.close(); else { db.stop(); db.close(); }
        start(false);
        restarts++;
        EOracle.check(db.getStreamSize() == ss, what + ": the restart changed the stream size " + ss + " -> " + db.getStreamSize()
                + " (2026.7: nothing is appended at a start)");
        EOracle.check(db.getFirstAvailableLookupTime().units() == first, what + ": the restart changed the first available time "
                + first + " -> " + db.getFirstAvailableLookupTime().units() + " (\"A restart after stop() or close() keeps the time\")");
        EOracle.check(db.getRetainDuration().equals(r), what + ": the restart changed the retain duration");
        EOracle.check(db.getStartupDistanceInMb() == 5, what + ": the restart changed the startup distance");
        if (rnd.nextInt(3) == 0) {
            long before = db.getStreamSize();
            maintainOnce(budget());
            EOracle.log("  maintain right after a start: stream " + before + " -> " + db.getStreamSize());
        }
        checks(what + " after a restart");
    }

    void run(int keys, int rounds) throws Exception {
        EOracle.log("E1MaintainBudget seed " + seed + (memory ? " memory" : " file") + ", R " + retainUnits / SEC + " s, style " + style
                + ", keys " + keys + ", rounds " + rounds);
        clock.setTime(Time.units(T0));
        start(true);
        db.setStartupDistanceInMb(5);
        EOracle.check(db.getRetainDuration().equals(Duration.MAX), "a new database's retain duration is not forever");
        EOracle.check(db.getFirstAvailableLookupTime().units() == 0, "a new database's first available time is not 0");
        long s0 = db.getStreamSize();
        for (int b : new int[] {Integer.MIN_VALUE, -1, 0, 1, 99, 100, 100_000, Integer.MAX_VALUE}) maintainOnce(b);
        EOracle.check(db.getStreamSize() == s0, "maintain() on a new database changed the stream size");
        // the load, retain forever, with maintain() between
        for (int done = 0; done < keys; ) {
            int n = Math.min(keys - done, 1 + rnd.nextInt(500));
            LinkedHashMap<String, byte[]> ops = new LinkedHashMap<>();
            WBuilder w = c.w();
            for (int j = 0; j < n; j++) { String k = key(done + j); byte[] v = val(); if (v.length > 50_000) v = new byte[40]; w.put(k, v); ops.put(k, v); }
            m.apply(ops, w.execute().getTime().units());
            done += n;
            tick(rnd.nextInt(1000));
            if (rnd.nextInt(4) == 0) maintainOnce(budget());
        }
        checks("load");
        restart("load");
        // a finite retain duration
        long before = db.getStreamSize();
        db.setRetainDuration(Duration.units(retainUnits));
        EOracle.log("  setRetainDuration: stream " + before + " -> " + db.getStreamSize());
        checks("retain set");
        if (rnd.nextBoolean()) {
            before = db.getStreamSize();
            maintainOnce(budget());
            EOracle.log("  maintain right after setRetainDuration: stream " + before + " -> " + db.getStreamSize());
        }
        // churn
        for (int round = 0; round < rounds; round++) {
            tick(rnd.nextInt(10) == 0 ? retainUnits / 2 : (long) (rnd.nextDouble() * retainUnits / 50));
            int a = rnd.nextInt(100);
            if (a < 60) tx(1 + rnd.nextInt(rnd.nextInt(4) == 0 ? 500 : 20), keys + keys / 4, 25);
            else if (a < 70) tx(1, keys, 0);
            boolean doMaintain = style == 1 || style == 2 ? rnd.nextBoolean() : style == 0 ? rnd.nextInt(4) == 0 : style == 3 ? true : rnd.nextInt(20) == 0;
            if (doMaintain) {
                int burst = style == 4 ? 1 + rnd.nextInt(30) : 1;
                for (int k = 0; k < burst; k++) maintainOnce(budget());
            }
            if (round % 5 == 0 || a >= 70) checks("round " + round);
            if (rnd.nextInt(150) == 0) restart("round " + round);
            if (rnd.nextInt(400) == 0) {
                // another retain duration: after an increase the lookups' window grows to it ("If the retain duration
                // is increased, the actual duration available for lookups will increase until it equals or exceeds")
                long[] rs = {1 * SEC, 3 * SEC, 20 * SEC, 600 * SEC};
                long nr = rs[rnd.nextInt(rs.length)];
                if (nr > retainUnits) floorFirst = db.getFirstAvailableLookupTime().units();
                db.setRetainDuration(Duration.units(nr));
                EOracle.check(db.getRetainDuration().equals(Duration.units(nr)), "round " + round + ": the retain duration not in force");
                retainUnits = nr;
                retainChanges++;
                checks("round " + round + ", R set to " + nr / SEC + " s");
            }
            if (round % 500 == 0) EOracle.log("  round " + round + ": stream " + db.getStreamSize() + ", live " + m.live + " keys, "
                    + m.liveBytes + " bytes, cuts " + cuts + ", maintains " + maintains);
        }
        checks("churn end");
        // everything but a few keys deleted
        List<String> liveKeys = new ArrayList<>();
        for (String k : m.allKeys()) if (m.valueAt(k, Long.MAX_VALUE) != null) liveKeys.add(k);
        Collections.shuffle(liveKeys, rnd);
        int keep = rnd.nextInt(3) == 0 ? 0 : rnd.nextInt(30);
        for (int i = keep; i < liveKeys.size(); ) {
            int n = Math.min(liveKeys.size() - i, 1 + rnd.nextInt(500));
            LinkedHashMap<String, byte[]> ops = new LinkedHashMap<>();
            WBuilder w = c.w();
            for (int j = 0; j < n; j++) { w.delete(liveKeys.get(i + j)); ops.put(liveKeys.get(i + j), null); }
            m.apply(ops, w.execute().getTime().units());
            i += n;
            tick(rnd.nextInt(1000));
        }
        checks("deleted");
        if (rnd.nextBoolean()) restart("deleted");
        // idle: maintain() until quiet
        int b = budget();
        long ssStart = db.getStreamSize();
        int calls = 0, same = 0, writing = 0;
        long last = db.getStreamSize();
        while (same < 16) {
            EOracle.check(calls < 200_000, "maintain(" + b + ") did not go quiet in 200,000 calls: stream " + db.getStreamSize());
            tick(retainUnits / 4 + 1);
            maintainOnce(b);
            calls++;
            long ss = db.getStreamSize();
            if (ss == last) same++; else { same = 0; writing = calls; }
            last = ss;
            if (calls % 97 == 0) checks("idle " + calls);
        }
        checks("quiet");
        long kept = db.getStreamSize();
        // the twin: a fresh database with the same live data and settings
        long twin = twin();
        EOracle.log("  idle: budget " + b + ", stream " + ssStart + " -> " + kept + " in " + writing + " calls that wrote (a pass by the Javadoc: about "
                + (ssStart / budgetBytes(b) + 1) + "), live " + m.live + " keys " + m.liveBytes + " bytes, twin " + twin);
        EOracle.check(kept <= twin + 1_000_000, "the quiet database keeps " + kept + " bytes of stream, a fresh twin with the same live data "
                + twin + " (getStreamSize(): beyond the live data, what maintain() can give back)");
        if (!memory) {
            long disk = EOracle.dirBytes(dir);
            EOracle.log("  disk " + disk + " for a stream of " + kept);
        }
        restart("quiet");
        db.close();
        EOracle.log("OK E1MaintainBudget seed " + seed + ": " + txs + " transactions, " + maintains + " maintain calls, " + cuts + " cuts, "
                 + restarts + " restarts, " + retainChanges + " retain changes, " + reads + " reads checked (" + txInfos + " transactionInfo), a call's most beyond its budget " + maxOver
                + " bytes (budget " + maxOverBudget + "), " + overCalls + " calls more than 472 kB beyond, the most stream " + maxStream
                + (memory ? "" : ", the most disk " + maxDisk + " (" + String.format("%.2f", maxDiskRatio) + " of the stream at most)"));
    }

    long twin() {
        TestClock tc = new TestClock();
        tc.setTime(Time.units(T0));
        try (Database t = Factory.database().memory().clock(tc).start()) {
            t.setStartupDistanceInMb(5);
            t.setRetainDuration(Duration.units(retainUnits));
            Connection tcn = t.connection();
            WBuilder w = tcn.w();
            int n = 0;
            for (String k : m.allKeys()) {
                byte[] v = m.valueAt(k, Long.MAX_VALUE);
                if (v == null) continue;
                w.put(k, v);
                if (++n == 400) { w.execute(); w = tcn.w(); n = 0; }
            }
            if (n > 0) w.execute();
            long last = -1;
            int same = 0;
            for (int i = 0; i < 100_000 && same < 16; i++) {
                tc.setTime(Time.units(tc.getTime() + retainUnits / 4 + 1));
                t.maintain(100_000);
                long ss = t.getStreamSize();
                if (ss == last) same++; else same = 0;
                last = ss;
            }
            return t.getStreamSize();
        }
    }

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        File dir = new File(a[1]);
        int keys = a.length > 2 ? Integer.parseInt(a[2]) : 3000;
        int rounds = a.length > 3 ? Integer.parseInt(a[3]) : 3000;
        EOracle.rmrf(dir);
        E1MaintainBudget app = new E1MaintainBudget(seed, dir);
        try {
            app.run(keys, rounds);
        } catch (Throwable t) {
            System.out.println("FAIL E1MaintainBudget seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            try { if (app.db != null) app.db.close(); } catch (Throwable x) { }
            System.exit(1);
        }
        EOracle.rmrf(dir);
    }
}
