package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.*;

import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe of bergdb 031-06 (2026-11-27): readers while commits carry steps and cuts.
 * ACC accounts whose values hold a number and padding; two writer threads move amounts
 * between two accounts in one transaction each (the sum stays TOTAL), a thread calls
 * maintain(), and reader threads scan every account at currentTime() and at times back to
 * the first available lookup time: each scan must give ACC accounts whose sum is TOTAL, or
 * be refused because its time is no longer available. Eviction with -Dcache=BYTES.
 *
 * Usage: java -ea -cp OUT:JAR bergdb.core.RvRead SEED SECONDS [NODE]
 */
public class RvRead {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final int ACC = 300;
    static final long TOTAL = 1000L * ACC;

    public static void main(String[] args) throws Exception {
        final long seed = Long.parseLong(args[0]);
        final long seconds = Long.parseLong(args[1]);
        final int node = args.length > 2 ? Integer.parseInt(args[2]) : 0;
        final AtomicLong clock = new AtomicLong(SEC);
        DbBuilder b = Db.builder().testSetup(new CutStream()).clock(clock::get);
        if (node == 8) b.maxNodeSize8();
        if (Long.getLong("cache", 0) > 0) b.cacheSizeIndicator(Long.getLong("cache"));
        final Db db = b.start();
        db.setStartupDistance(3000);
        db.setRetainDuration(SEC);
        final long[] amount = new long[ACC];
        Random r0 = new Random(seed);
        for (int i = 0; i < ACC; i += 50) {
            Trans.Builder tb = db.trans();
            for (int j = i; j < i + 50; j++) { amount[j] = 1000; tb.put(key(j), value(1000, r0)); }
            clock.addAndGet(1000);
            db.execute(tb.build());
        }
        final long deadline = System.nanoTime() + seconds * 1000000000L;
        final AtomicLong commits = new AtomicLong(), scans = new AtomicLong(), old = new AtomicLong(),
                expired = new AtomicLong(), calls = new AtomicLong();
        final AtomicReference<Throwable> failure = new AtomicReference<>();
        final Object money = new Object();
        List<Thread> ts = new ArrayList<>();
        for (int w = 0; w < 2; w++) {
            final Random r = new Random(seed * 10 + w);
            ts.add(new Thread(() -> {
                try {
                    while (System.nanoTime() < deadline && failure.get() == null) {
                        synchronized (money) {
                            int a = r.nextInt(ACC), c = r.nextInt(ACC);
                            if (a == c) continue;
                            long x = r.nextInt(50);
                            clock.addAndGet(100000 + r.nextInt(300000));
                            db.execute(db.trans().put(key(a), value(amount[a] - x, r))
                                    .put(key(c), value(amount[c] + x, r)).build());
                            amount[a] -= x; amount[c] += x;
                        }
                        commits.incrementAndGet();
                        java.util.concurrent.locks.LockSupport.parkNanos(r.nextInt(200000));
                    }
                } catch (Throwable e) { failure.compareAndSet(null, e); }
            }));
        }
        ts.add(new Thread(() -> {
            try {
                Random r = new Random(seed + 77);
                while (System.nanoTime() < deadline && failure.get() == null) {
                    db.maintain(100 + r.nextInt(1500));
                    calls.incrementAndGet();
                    java.util.concurrent.locks.LockSupport.parkNanos(300000);
                }
            } catch (Throwable e) { failure.compareAndSet(null, e); }
        }));
        for (int rd = 0; rd < 3; rd++) {
            final Random r = new Random(seed * 100 + rd);
            ts.add(new Thread(() -> {
                try {
                    while (System.nanoTime() < deadline && failure.get() == null) {
                        long now = db.currentTime();
                        long first = db.getFirstAvailableLookupTime();
                        boolean past = r.nextInt(3) == 0;
                        long t = past ? first + (long) (r.nextDouble() * Math.max(0, now - first)) : now;
                        if (t < 2 * SEC) continue;      // before the accounts were all put
                        GetMany g = db.newGetMany();
                        g.startKey = Keys.toSegments("/a/");
                        g.inclusive = false;
                        g.lookupTime = t;
                        final long[] sum = new long[2];
                        g.stopCondition = new GetMany.StopCondition() {
                            public int handleKvt(Kvt kvt) {
                                if (!Keys.toString(kvt.key).startsWith("/a/")) return STOP;
                                sum[0] += java.nio.ByteBuffer.wrap(kvt.value).getLong();
                                sum[1]++;
                                return CONTINUE;
                            }
                            public void eod() {}
                        };
                        try {
                            db.getMany(g);
                        } catch (bergdb.pub.util.LookupTimeNotAvailableException e) {
                            expired.incrementAndGet();
                            continue;
                        }
                        if (sum[1] != ACC || sum[0] != TOTAL) throw new AssertionError("a scan at " + t
                                + " (now " + now + ", first " + first + "): " + sum[1] + " accounts, sum " + sum[0]);
                        scans.incrementAndGet();
                        if (past) old.incrementAndGet();
                    }
                } catch (Throwable e) { failure.compareAndSet(null, e); }
            }));
        }
        // transactionInfo()'s walk from a reader thread, while commits carry copies: the value
        // read, followed back through the copies (the copy mark) to the record that wrote it.
        final AtomicLong walks = new AtomicLong(), followed = new AtomicLong(), walkRefused = new AtomicLong();
        ts.add(new Thread(() -> {
            try {
                Random r = new Random(seed + 5);
                while (System.nanoTime() < deadline && failure.get() == null) {
                    final long[] key = key(r.nextInt(ACC));
                    bergdb.dag.GetData gd = db.newGetData();
                    final byte[] v;
                    try {
                        v = db.getOne(db.currentTime(), key, gd);
                    } catch (bergdb.pub.util.LookupTimeNotAvailableException e) { continue; }
                    if (v == null) throw new AssertionError("no value of an account");
                    if (gd.tpos <= 0) continue;         // its record still being stored
                    try {
                        StoredTrans st = db.getTrans(gd.tpos);
                        while (true) {
                            StoredValueNode vn = null;
                            for (StoredNode sn : st.nodes) {
                                if (sn instanceof StoredValueNode && Arrays.equals(key, ((StoredValueNode) sn).getKey())) vn = (StoredValueNode) sn;
                            }
                            if (vn == null) throw new AssertionError("no node of the key in the record at " + st.tpos);
                            if (!Arrays.equals(vn.getValueNode().value, v)) throw new AssertionError("another value in the walk");
                            if (!vn.isCopy()) break;
                            followed.incrementAndGet();
                            bergdb.dag.GetData before = db.newGetData();
                            byte[] copied = db.getOne(st.tt - 1, key, before);
                            if (!Arrays.equals(copied, v) || before.tpos >= st.tpos || before.tpos <= 0) throw new AssertionError(
                                    "a copy at " + st.tpos + " that is not the value before it (" + before.tpos + ")");
                            st = db.getTrans(before.tpos);
                        }
                        walks.incrementAndGet();
                    } catch (bergdb.pub.util.LookupTimeNotAvailableException e) {
                        walkRefused.incrementAndGet();
                    } catch (RuntimeException e) {
                        // A record below the first available position by now: expired.
                        if (gd.tpos >= db.getFirstAvailablePos() && !(e.getCause() instanceof bergdb.pub.util.LookupTimeNotAvailableException)
                                && !String.valueOf(e).contains("first")) throw e;
                        walkRefused.incrementAndGet();
                    }
                }
            } catch (Throwable e) { failure.compareAndSet(null, e); }
        }));
        for (Thread t : ts) t.start();
        for (Thread t : ts) t.join();
        if (failure.get() != null) { failure.get().printStackTrace(); System.exit(1); }
        long cut = db.getFirstAvailablePos();
        Reclaim.IterationInfo it = db.internal().reclaim().currentIteration();
        db.close();
        System.out.println("RvRead seed " + seed + " node " + node + " cache " + Long.getLong("cache", 0) + ": "
                + commits + " commits, " + calls + " maintain() calls, " + scans + " scans with the sum right ("
                + old + " at earlier times), " + expired + " refused as no longer available; " + walks + " walks to the writing record through " + followed
                + " copies, " + walkRefused + " refused; the first available position " + cut + ": OK");
    }

    static long[] key(int i) { return Keys.toSegments(String.format("/a/%04d", i)); }

    static byte[] value(long amount, Random r) {
        byte[] v = new byte[8 + r.nextInt(600)];
        java.nio.ByteBuffer.wrap(v).putLong(amount);
        return v;
    }
}
