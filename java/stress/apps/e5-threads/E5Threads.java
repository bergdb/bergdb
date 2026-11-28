import bergdb.pub.*;
import bergdb.pub.util.LookupTimeNotAvailableException;

import java.io.File;
import java.nio.ByteBuffer;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

/**
 * App e5 of 031-08: many writers and readers, rw() transfers that conflict and run again,
 * iterators held over commits and over maintain(budget) calls from several threads (Pub API,
 * a file or a memory database, a test clock that a thread moves, a retain duration of 1 to
 * 3 s).
 *
 * Writer threads each own a directory and put, overwrite and delete there in w()
 * transactions of 1 to 60 KVs, each recording its transactions' times and KVs in its own
 * oracle after execute() returns, and its last recorded time. Transfer threads move amounts
 * between 40 accounts (byte[] balances) in rw() actions that read both balances, move the
 * amount only if the source has it and say so through an output; now and then an action
 * calls maintain(100) or reads a third account. maintain() threads call maintain(budget)
 * with budgets of 0 to 100,000 at random gaps. A clock thread moves the test clock by 0.2 to
 * 5 ms every millisecond, so that reclaim begins, steps and cuts during all this. Reader
 * threads, each round: take t = currentTime(), open a listing of a writer's directory at t
 * (and an index scan of the accounts' directory), read part of it, sleep while the others
 * commit and maintain, read the rest; then wait until the writer has recorded a transaction
 * after t, and compare the listing with the writer's oracle at t. A read may expire
 * (LookupTimeNotAvailableException) only when t is then before the first available time; a
 * listing that completes must be exact. Readers also read the accounts at a frozen time: the
 * sum is always the total. At the end every directory, every balance (the start plus the
 * committed transfers, from their outputs) and the sum are checked, again after a restart.
 *
 * Usage: java E5Threads SEED DIR SECONDS [WRITERS] [READERS]
 */
public class E5Threads {
    static final long T0 = Time.utc("2026-04-01").units();
    static final int ACCOUNTS = 40;
    static final long START_BALANCE = 1000;

    public static class Acc {
        public long balance;
        public long bucket;
        public Acc() {}
    }

    /** A writer's oracle: its keys' histories; its last recorded transaction time. */
    static final class W {
        final String dir;
        final ConcurrentHashMap<String, ConcurrentSkipListMap<Long, byte[]>> hist = new ConcurrentHashMap<>();
        final AtomicLong recorded = new AtomicLong(-1);
        volatile boolean done;
        long txs;
        W(String dir) { this.dir = dir; }
        static final byte[] DEL = new byte[0];
        /** Forgets each key's versions before the one in force at t (the reader's oldest time and the first available). */
        void prune(long t) {
            for (ConcurrentSkipListMap<Long, byte[]> h : hist.values()) {
                Long f = h.floorKey(t);
                if (f != null) h.headMap(f, false).clear();
            }
        }
        TreeMap<String, byte[]> stateAt(long t) {
            TreeMap<String, byte[]> m = new TreeMap<>(EOracle.ORDER);
            for (Map.Entry<String, ConcurrentSkipListMap<Long, byte[]>> e : hist.entrySet()) {
                Map.Entry<Long, byte[]> f = e.getValue().floorEntry(t);
                if (f != null && f.getValue() != DEL) m.put(e.getKey(), f.getValue());
            }
            return m;
        }
    }

    final long seed;
    final File dir;
    final boolean memory;
    final long retain;
    final TestClock clock = new TestClock();
    volatile Database db;
    final AtomicBoolean stop = new AtomicBoolean();
    final AtomicReference<String> failure = new AtomicReference<>();
    final AtomicLong transfers = new AtomicLong(), moved = new AtomicLong(), maintains = new AtomicLong(), listings = new AtomicLong(),
            expired = new AtomicLong(), rwExpired = new AtomicLong(), sums = new AtomicLong(), heldOverMaintain = new AtomicLong(), maintainInAction = new AtomicLong();
    final long[] balances = new long[ACCOUNTS];   // the oracle of the accounts, from the committed transfers' outputs
    final List<W> writers = new ArrayList<>();

    E5Threads(long seed, File dir) {
        this.seed = seed;
        this.dir = dir;
        Random r = new Random(seed);
        memory = r.nextInt(3) == 0;
        retain = (1 + r.nextInt(3)) * 10_000_000L;
    }

    void fail(String m) { failure.compareAndSet(null, m); stop.set(true); }

    static byte[] lng(long v) { return ByteBuffer.allocate(8).putLong(v).array(); }

    void start(boolean create) {
        DatabaseBuilder b = Factory.database();
        if (memory) b.memory(); else if (create) b.create(dir.getPath()); else b.open(dir.getPath());
        db = b.clock(clock).cacheSizeInMb(64).start();
    }

    void writer(W w, long s) {
        Random r = new Random(s);
        Connection c = db.connection();
        while (!stop.get()) {
            int n = 1 + r.nextInt(60);
            WBuilder b = c.w();
            LinkedHashMap<String, byte[]> ops = new LinkedHashMap<>();
            for (int j = 0; j < n; j++) {
                String k = w.dir + "k" + r.nextInt(300) + ".bin";
                if (r.nextInt(5) == 0) { b.delete(k); ops.put(k, W.DEL); }
                else { byte[] v = EOracle.value(r, r.nextInt(50) == 0 ? 20_000 : r.nextInt(400)); b.put(k, v); ops.put(k, v); }
            }
            long t = b.execute().getTime().units();
            for (Map.Entry<String, byte[]> e : ops.entrySet()) w.hist.computeIfAbsent(e.getKey(), x -> new ConcurrentSkipListMap<>()).put(t, e.getValue());
            if (t <= w.recorded.get()) fail("writer " + w.dir + ": a transaction time " + t + " not after its last, " + w.recorded.get());
            w.recorded.set(t);
            w.txs++;
            if (r.nextInt(20) == 0) sleep(r.nextInt(5));
        }
        w.done = true;
    }

    void transfer(long s) {
        Random r = new Random(s);
        Connection c = db.connection();
        while (!stop.get()) {
            int a = r.nextInt(ACCOUNTS), b = r.nextInt(ACCOUNTS - 1);
            if (b >= a) b++;
            final int from = a, to = b;
            final long amount = 1 + r.nextInt(300);
            final boolean maint = r.nextInt(30) == 0, third = r.nextInt(5) == 0;
            final int other = r.nextInt(ACCOUNTS);
            Transaction tr;
            try {
              tr = c.rw(env -> {
                Acc x = env.get("/e5/acc/" + from, Acc.class), y = env.get("/e5/acc/" + to, Acc.class);
                if (third) env.get("/e5/acc/" + other, Acc.class);
                if (maint) { db.maintain(100); maintainInAction.incrementAndGet(); }
                boolean ok = x.balance >= amount;
                if (ok) { x.balance -= amount; y.balance += amount; env.put("/e5/acc/" + from, x); env.put("/e5/acc/" + to, y); }
                env.setOutput("moved", ok);
              });
            } catch (LookupTimeNotAvailableException e) {
                // the action ran longer than the retain duration (031-08, UA-3): its read time expired; nothing
                // is written (the final check of the balances shows it), and the transfer is not counted
                rwExpired.incrementAndGet();
                continue;
            }
            boolean ok = tr.getOutput("moved", Boolean.class);
            synchronized (balances) { if (ok) { balances[from] -= amount; balances[to] += amount; moved.incrementAndGet(); } }
            transfers.incrementAndGet();
        }
    }

    void maintainer(long s) {
        Random r = new Random(s);
        while (!stop.get()) {
            db.maintain(new int[] {0, 100, 1000, 20_000, 100_000}[r.nextInt(5)]);
            maintains.incrementAndGet();
            sleep(r.nextInt(8));
        }
    }

    void clockThread(long s) {
        Random r = new Random(s);
        while (!stop.get()) {
            clock.setTime(Time.units(clock.getTime() + 2_000 + r.nextInt(48_000)));
            sleep(1);
        }
    }

    void reader(long s) {
        Random r = new Random(s);
        Connection c = db.newConnection();
        while (!stop.get()) {
            W w = writers.get(r.nextInt(writers.size()));
            long t = db.currentTime().units();
            Long reg = t * 64 + (s & 63);        // unique among the readers (each its own seed's low bits)
            readerTimes.add(reg);
            try { readOnce(w, t, c, r); } finally { readerTimes.remove(reg); }
        }
    }

    final ConcurrentSkipListSet<Long> readerTimes = new ConcurrentSkipListSet<>();   // the times that readers read at now

    void readOnce(W w, long t, Connection c, Random r) {
        {
            c.setLookupTime(Time.units(t));
            List<String> got = new ArrayList<>();
            List<byte[]> vals = new ArrayList<>();
            try {
                Iterator<Kv<byte[]>> it = c.usePrimary(byte[].class).dir(w.dir).kvs().iterator();
                int part = r.nextInt(200);
                long m0 = maintains.get();
                for (int i = 0; i < part && it.hasNext(); i++) { Kv<byte[]> kv = it.next(); got.add(kv.key()); vals.add(kv.value()); }
                sleep(r.nextInt(10) == 0 ? 300 + r.nextInt(1700) : r.nextInt(30));   // now and then past the retain duration
                if (maintains.get() > m0) heldOverMaintain.incrementAndGet();
                while (it.hasNext()) { Kv<byte[]> kv = it.next(); got.add(kv.key()); vals.add(kv.value()); }
            } catch (LookupTimeNotAvailableException e) {
                long first = db.getFirstAvailableLookupTime().units();
                if (t >= first) { fail("a listing at " + t + " expired, but the first available time is " + first + ": " + e); return; }
                expired.incrementAndGet();
                return;
            }
            // wait until the writer has recorded a transaction after t (or ended)
            long until = System.currentTimeMillis() + 120_000;
            while (w.recorded.get() <= t && !w.done && !stop.get()) {
                if (System.currentTimeMillis() > until) { fail("writer " + w.dir + " recorded nothing after " + t + " in 120 s"); return; }
                sleep(1);
            }
            if (stop.get() && w.recorded.get() <= t && !w.done) return;
            TreeMap<String, byte[]> want = w.stateAt(t);
            Iterator<Map.Entry<String, byte[]>> wi = want.entrySet().iterator();
            for (int i = 0; i < got.size(); i++) {
                if (!wi.hasNext()) { fail("listing of " + w.dir + " at " + t + ": an extra key " + got.get(i)); return; }
                Map.Entry<String, byte[]> e = wi.next();
                if (!e.getKey().equals(got.get(i)) || !Arrays.equals(e.getValue(), vals.get(i))) {
                    fail("listing of " + w.dir + " at " + t + ", index " + i + ": " + got.get(i) + ", expected " + e.getKey()
                            + (e.getKey().equals(got.get(i)) ? " (the value differs)" : "")); return;
                }
            }
            if (wi.hasNext()) { fail("listing of " + w.dir + " at " + t + " lacks " + wi.next().getKey()); return; }
            listings.incrementAndGet();
            // the accounts at a frozen time: the sum is the total
            Connection fc = db.newConnection();
            fc.freezeLookupTime();
            try {
                long sum = 0;
                int n = 0;
                for (Acc a : fc.usePrimary(Acc.class).dir("/e5/acc/").objects()) { sum += a.balance; n++; if (r.nextInt(20) == 0) sleep(1); }
                if (n != ACCOUNTS || sum != ACCOUNTS * START_BALANCE) { fail("accounts at a frozen time: " + n + " with the sum " + sum); return; }
                sums.incrementAndGet();
            } catch (LookupTimeNotAvailableException e) {
                expired.incrementAndGet();
            }
        }
    }

    static void sleep(long ms) {
        if (ms <= 0) return;
        try { Thread.sleep(ms); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
    }

    void finalCheck(String what) {
        Connection c = db.newConnection();
        for (W w : writers) {
            TreeMap<String, byte[]> want = w.stateAt(Long.MAX_VALUE);
            Iterator<Map.Entry<String, byte[]>> wi = want.entrySet().iterator();
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir(w.dir).kvs()) {
                EOracle.check(wi.hasNext(), what + ": " + w.dir + " has an extra key " + kv.key());
                Map.Entry<String, byte[]> e = wi.next();
                EOracle.check(e.getKey().equals(kv.key()) && Arrays.equals(e.getValue(), kv.value()), what + ": " + w.dir + ": " + kv.key()
                        + ", expected " + e.getKey());
            }
            EOracle.check(!wi.hasNext(), what + ": " + w.dir + " lacks keys");
        }
        long sum = 0;
        for (int i = 0; i < ACCOUNTS; i++) {
            Acc a = c.get("/e5/acc/" + i, Acc.class);
            EOracle.check(a.balance == balances[i], what + ": account " + i + " holds " + a.balance + ", the committed transfers give " + balances[i]);
            sum += a.balance;
        }
        EOracle.check(sum == ACCOUNTS * START_BALANCE, what + ": the sum is " + sum);
    }

    void run(int seconds, int nWriters, int nReaders) throws Exception {
        EOracle.log("E5Threads seed " + seed + (memory ? " memory" : " file") + ", R " + retain / 10_000_000 + " s, " + seconds + " s, "
                + nWriters + " writers, " + nReaders + " readers");
        EOracle.rmrf(dir);
        clock.setTime(Time.units(T0));
        start(true);
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.units(retain));
        Connection c = db.connection();
        db.indexBuilder("by-balance").dir("/e5/acc/").type("long").field("balance").start().join();
        WBuilder wb = c.w();
        for (int i = 0; i < ACCOUNTS; i++) { Acc a = new Acc(); a.balance = START_BALANCE; a.bucket = i % 4; wb.put("/e5/acc/" + i, a); balances[i] = START_BALANCE; }
        wb.execute();
        for (int i = 0; i < nWriters; i++) writers.add(new W("/e5/w" + i + "/"));
        List<Thread> ts = new ArrayList<>();
        Random r = new Random(seed);
        for (W w : writers) { long s = r.nextLong(); ts.add(new Thread(() -> guard(() -> writer(w, s)), "writer")); }
        for (int i = 0; i < 3; i++) { long s = r.nextLong(); ts.add(new Thread(() -> guard(() -> transfer(s)), "transfer")); }
        for (int i = 0; i < 2; i++) { long s = r.nextLong(); ts.add(new Thread(() -> guard(() -> maintainer(s)), "maintain")); }
        for (int i = 0; i < nReaders; i++) { long s = (r.nextLong() & ~63L) | i; ts.add(new Thread(() -> guard(() -> reader(s)), "reader")); }
        long cs = r.nextLong();
        ts.add(new Thread(() -> guard(() -> clockThread(cs)), "clock"));
        for (Thread t : ts) t.start();
        long end = System.currentTimeMillis() + seconds * 1000L;
        long firstSeen = 0, cuts = 0;
        while (System.currentTimeMillis() < end && !stop.get()) {
            sleep(200);
            long f = db.getFirstAvailableLookupTime().units();
            if (f < firstSeen) fail("the first available time moved back, " + firstSeen + " -> " + f);
            long horizon = f;
            Long oldest = readerTimes.isEmpty() ? null : readerTimes.first();
            if (oldest != null) horizon = Math.min(horizon, oldest / 64);
            // a reader that starts after this takes a currentTime() later than the first available time
            for (W w : writers) w.prune(horizon);
            if (f > firstSeen) cuts++;
            firstSeen = f;
        }
        stop.set(true);
        for (Thread t : ts) t.join(300_000);
        for (Thread t : ts) if (t.isAlive()) fail("thread " + t.getName() + " did not end in 300 s");
        if (failure.get() != null) throw new EOracle.Fail(failure.get());
        finalCheck("end");
        if (!memory) {
            db.close();
            start(false);
            finalCheck("restarted");
        }
        db.close();
        long wtx = 0;
        for (W w : writers) wtx += w.txs;
        EOracle.log("OK E5Threads seed " + seed + ": " + wtx + " writer transactions, " + transfers.get() + " transfers (" + moved.get()
                + " moved), " + maintains.get() + " maintain calls (" + maintainInAction.get() + " inside rw actions), " + cuts + " cuts seen, "
                + listings.get() + " listings checked (" + heldOverMaintain.get() + " held over a maintain call), " + sums.get()
                + " frozen sums, " + expired.get() + " reads expired, " + rwExpired.get() + " rw() expired");
        EOracle.rmrf(dir);
    }

    void guard(Runnable r) {
        try { r.run(); }
        catch (Throwable t) {
            java.io.StringWriter sw = new java.io.StringWriter();
            t.printStackTrace(new java.io.PrintWriter(sw));
            fail(Thread.currentThread().getName() + ": " + sw);
        }
    }

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        File dir = new File(a[1]);
        int seconds = Integer.parseInt(a[2]);
        int nw = a.length > 3 ? Integer.parseInt(a[3]) : 4;
        int nr = a.length > 4 ? Integer.parseInt(a[4]) : 3;
        E5Threads app = new E5Threads(seed, dir);
        try {
            app.run(seconds, nw, nr);
        } catch (Throwable t) {
            System.out.println("FAIL E5Threads seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            try { if (app.db != null) app.db.close(); } catch (Throwable x) { }
            System.exit(1);
        }
        System.exit(0);
    }
}
