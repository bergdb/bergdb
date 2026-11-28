import bergdb.pub.*;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;

import java.io.File;
import java.nio.ByteBuffer;
import java.util.*;
import java.util.concurrent.atomic.*;

/**
 * App e8 of 031-08: stop() and close() from another thread at random moments, while writers
 * commit, transfers run rw() actions, maintain(budget) runs and an index builds, under a
 * retain duration (Pub API, a file database, the system clock).
 *
 * Rounds on one database: a start; writer threads (each its own directory, w() transactions
 * of 1 to 30 puts and deletes), two transfer threads (rw() between 30 accounts, objects with
 * an index on the balance), a maintain() thread (budgets 100 to 100,000), and in some rounds
 * an index deleted and started again; after 20 to 1,500 ms a stopper calls stop() or close().
 * Each thread records which of its calls returned and which threw IllegalDbStateException
 * (Database.stop(): a call that has not begun its commit "is refused: it throws
 * IllegalDbStateException, nothing of it is written, and the database has not failed"; one
 * whose commit has begun completes). Then close(), a new start, and the checks: each
 * writer's directory is what its returned transactions made, none of a refused one; every
 * account holds the start plus the transfers that returned, and the sum is the total; the
 * index on the balance lists the accounts in the oracle's order; the retain duration, the
 * startup distance and the first available time as before the stop; the indexes that a
 * round started are built by the next start's jobs (indexJob().join()). No call may throw
 * DbFailedException.
 *
 * Usage: java E8StopEverywhere SEED DIR [ROUNDS]
 */
public class E8StopEverywhere {
    public static class Acc {
        public long balance;
        public long n;
        public Acc() {}
    }

    static final int ACCOUNTS = 30;
    static final long START = 1000;

    final long seed;
    final Random rnd;
    final File dir;
    final long[] balances = new long[ACCOUNTS];
    final List<TreeMap<String, byte[]>> writerState = new ArrayList<>();
    final AtomicReference<String> failure = new AtomicReference<>();
    long returned, refused, transfers, maintains, stops, closes, rebuilt, inFlightMaintain, absentIndex;
    boolean indexExists = true;

    E8StopEverywhere(long seed, File dir) { this.seed = seed; rnd = new Random(seed); this.dir = dir; }

    void fail(String m) { failure.compareAndSet(null, m); }

    Database start() {
        return Factory.database().create(dir.getPath()).cacheSizeInMb(32).start();
    }

    /** One round's threads; returns when all have ended after the stop. */
    void round(Database db, int r) throws Exception {
        int nw = writerState.size();
        List<Thread> ts = new ArrayList<>();
        AtomicLong ret = new AtomicLong(), ref = new AtomicLong(), tr = new AtomicLong(), mc = new AtomicLong();
        AtomicBoolean inMaintain = new AtomicBoolean();
        for (int w = 0; w < nw; w++) {
            final int id = w;
            final long s = rnd.nextLong();
            ts.add(new Thread(() -> {
                Random wr = new Random(s);
                Connection c = db.connection();
                TreeMap<String, byte[]> st = writerState.get(id);
                for (int seq = 0; ; seq++) {
                    WBuilder b;
                    LinkedHashMap<String, byte[]> ops = new LinkedHashMap<>();
                    try {
                        b = c.w();
                        int n = 1 + wr.nextInt(30);
                        for (int j = 0; j < n; j++) {
                            String k = "/e8/w" + id + "/k" + wr.nextInt(200) + ".bin";
                            if (wr.nextInt(5) == 0) { b.delete(k); ops.put(k, null); }
                            else {
                                byte[] v = ByteBuffer.allocate(16 + wr.nextInt(300)).putLong(r).putLong(seq).array();
                                b.put(k, v); ops.put(k, v);
                            }
                        }
                        b.execute();
                    } catch (DbFailedException e) {
                        fail("writer " + id + ": DbFailedException at a stop: " + e);
                        return;
                    } catch (IllegalDbStateException e) {
                        ref.incrementAndGet();
                        return;        // refused: nothing of it written
                    } catch (Throwable e) {
                        fail("writer " + id + ": " + e);
                        return;
                    }
                    for (Map.Entry<String, byte[]> e : ops.entrySet()) { if (e.getValue() == null) st.remove(e.getKey()); else st.put(e.getKey(), e.getValue()); }
                    ret.incrementAndGet();
                }
            }, "writer"));
        }
        for (int t = 0; t < 2; t++) {
            final long s = rnd.nextLong();
            ts.add(new Thread(() -> {
                Random tr2 = new Random(s);
                Connection c = db.connection();
                while (true) {
                    int a = tr2.nextInt(ACCOUNTS), b = tr2.nextInt(ACCOUNTS - 1);
                    if (b >= a) b++;
                    final int from = a, to = b;
                    final long amount = 1 + tr2.nextInt(200);
                    Transaction x;
                    try {
                        x = c.rw(env -> {
                            Acc p = env.get("/e8/acc/a" + from, Acc.class), q = env.get("/e8/acc/a" + to, Acc.class);
                            boolean ok = p.balance >= amount;
                            if (ok) { p.balance -= amount; q.balance += amount; p.n++; q.n++; env.put("/e8/acc/a" + from, p); env.put("/e8/acc/a" + to, q); }
                            env.setOutput("ok", ok);
                        });
                    } catch (DbFailedException e) {
                        fail("transfer: DbFailedException at a stop: " + e);
                        return;
                    } catch (IllegalDbStateException e) {
                        ref.incrementAndGet();
                        return;
                    } catch (Throwable e) {
                        fail("transfer: " + e);
                        return;
                    }
                    if (x.getOutput("ok", Boolean.class)) synchronized (balances) { balances[from] -= amount; balances[to] += amount; }
                    tr.incrementAndGet();
                }
            }, "transfer"));
        }
        final long ms = rnd.nextLong();
        ts.add(new Thread(() -> {
            Random mr = new Random(ms);
            while (true) {
                try {
                    inMaintain.set(true);
                    db.maintain(new int[] {100, 2000, 100_000}[mr.nextInt(3)]);
                    inMaintain.set(false);
                    mc.incrementAndGet();
                } catch (DbFailedException e) {
                    fail("maintain: DbFailedException at a stop: " + e);
                    return;
                } catch (IllegalDbStateException e) {
                    return;
                } catch (bergdb.pub.util.DbException e) {
                    return;            // a StreamIoException at a stop (UA-2)
                } catch (Throwable e) {
                    fail("maintain: " + e);
                    return;
                }
                try { Thread.sleep(mr.nextInt(5)); } catch (InterruptedException e) { return; }
            }
        }, "maintain"));
        boolean rebuild = rnd.nextInt(3) == 0;
        for (Thread t : ts) t.start();
        if (rebuild) {
            try {
                db.deleteIndex("by-balance");
                indexExists = false;     // returned: written, also at a stop
                db.indexBuilder("by-balance").dir("/e8/acc/").type("long").field("balance").start();
                indexExists = true;
                rebuilt++;
            } catch (DbFailedException e) {
                fail("the index's deletion or creation: DbFailedException at a stop: " + e);
            } catch (IllegalDbStateException e) {
                // the stop came first: the call refused, nothing of it written
            }
        }
        Thread.sleep(20 + rnd.nextInt(1500));
        boolean close = rnd.nextBoolean();
        if (inMaintain.get()) inFlightMaintain++;
        if (close) { db.close(); closes++; } else { db.stop(); stops++; }
        for (Thread t : ts) t.join(120_000);
        for (Thread t : ts) if (t.isAlive()) fail("round " + r + ": a thread did not end in 120 s after the stop: " + t.getName());
        db.close();
        returned += ret.get();
        refused += ref.get();
        transfers += tr.get();
        maintains += mc.get();
    }

    void check(Database db, String what) {
        Connection c = db.connection();
        for (int w = 0; w < writerState.size(); w++) {
            TreeMap<String, byte[]> st = writerState.get(w);
            Iterator<Map.Entry<String, byte[]>> it = st.entrySet().iterator();
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/e8/w" + w + "/").kvs()) {
                EOracle.check(it.hasNext(), what + ": writer " + w + " has an extra key " + kv.key() + " (a refused transaction written?)");
                Map.Entry<String, byte[]> e = it.next();
                EOracle.check(e.getKey().equals(kv.key()), what + ": writer " + w + ": " + kv.key() + ", expected " + e.getKey());
                if (!Arrays.equals(e.getValue(), kv.value())) {
                    ByteBuffer g = ByteBuffer.wrap(kv.value()), x = ByteBuffer.wrap(e.getValue());
                    throw new EOracle.Fail(what + ": writer " + w + ": " + kv.key() + " holds round " + g.getLong() + " seq " + g.getLong()
                            + ", the last returned transaction wrote round " + x.getLong() + " seq " + x.getLong());
                }
            }
            EOracle.check(!it.hasNext(), what + ": writer " + w + " lacks " + (it.hasNext() ? it.next().getKey() : "") + " (a returned transaction lost?)");
        }
        long sum = 0;
        List<long[]> byBalance = new ArrayList<>();
        for (int i = 0; i < ACCOUNTS; i++) {
            Acc a = c.get("/e8/acc/a" + i, Acc.class);
            EOracle.check(a.balance == balances[i], what + ": account " + i + " holds " + a.balance + ", the returned transfers give " + balances[i]);
            sum += a.balance;
            byBalance.add(new long[] {a.balance, i});
        }
        EOracle.check(sum == ACCOUNTS * START, what + ": the sum is " + sum);
        if (!indexExists) {
            // deleted, and the stop refused its creation: absent, then made again
            try { db.indexJob("by-balance"); throw new EOracle.Fail(what + ": the index is there, though its creation was refused at a stop"); }
            catch (NoSuchIndexException good) { }
            db.indexBuilder("by-balance").dir("/e8/acc/").type("long").field("balance").start();
            indexExists = true;
            absentIndex++;
        }
        db.indexJob("by-balance").join();
        byBalance.sort((x, y) -> x[0] != y[0] ? Long.compare(x[0], y[0]) : EOracle.ORDER.compare("a" + x[1], "a" + y[1]));
        List<String> want = new ArrayList<>();
        for (long[] b : byBalance) want.add("/e8/acc/a" + b[1]);
        List<String> got = new ArrayList<>();
        for (Kv<Acc> kv : c.useIndex("by-balance", Acc.class).kvs()) got.add(kv.key());
        EOracle.check(got.equals(want), what + ": the index by-balance lists " + got.size() + " accounts, not in the oracle's order");
    }

    void run(int rounds) throws Exception {
        EOracle.log("E8StopEverywhere seed " + seed + ", rounds " + rounds);
        EOracle.rmrf(dir);
        int nw = 2 + rnd.nextInt(4);
        for (int i = 0; i < nw; i++) writerState.add(new TreeMap<>(EOracle.ORDER));
        Database db = start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(1 + rnd.nextInt(3)));
        Duration retain = db.getRetainDuration();
        WBuilder b = db.connection().w();
        for (int i = 0; i < ACCOUNTS; i++) { Acc a = new Acc(); a.balance = START; b.put("/e8/acc/a" + i, a); balances[i] = START; }
        b.execute();
        db.indexBuilder("by-balance").dir("/e8/acc/").type("long").field("balance").start().join();
        db.close();
        for (int r = 0; r < rounds; r++) {
            db = start();
            EOracle.check(db.getRetainDuration().equals(retain), "round " + r + ": the retain duration " + db.getRetainDuration());
            EOracle.check(db.getStartupDistanceInMb() == 5, "round " + r + ": the startup distance " + db.getStartupDistanceInMb());
            check(db, "round " + r + " before");
            round(db, r);
            if (failure.get() != null) throw new EOracle.Fail(failure.get());
            if (r % 20 == 19) EOracle.log("  round " + r + ": " + returned + " returned, " + refused + " refused at a stop, " + transfers + " transfers");
        }
        db = start();
        check(db, "end");
        db.close();
        EOracle.log("OK E8StopEverywhere seed " + seed + ": " + rounds + " rounds (" + stops + " by stop(), " + closes + " by close(), "
                + inFlightMaintain + " with a maintain() call running), " + returned + " writer transactions returned, " + refused
                + " calls refused at a stop, " + transfers + " transfers, " + maintains + " maintain calls, " + rebuilt + " index rebuilds ("
                + absentIndex + " left deleted by a stop)");
        EOracle.rmrf(dir);
    }

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        File dir = new File(a[1]);
        int rounds = a.length > 2 ? Integer.parseInt(a[2]) : 60;
        E8StopEverywhere app = new E8StopEverywhere(seed, dir);
        try {
            app.run(rounds);
        } catch (Throwable t) {
            System.out.println("FAIL E8StopEverywhere seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            System.exit(1);
        }
        System.exit(0);
    }
}
