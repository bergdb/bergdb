package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.dag.GetMany;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, after the review of 031-05 by Fable (its ConcProbe): several threads at
 * once, WRITERS committing puts and deletes, one calling maintain(B), one calling the
 * setters, two reading (gets and scans at currentTime(), which moves the times of the
 * records after them), on a clock that the threads move on together. Every record is
 * logged, in the order the write lock gave, with the action that wrote it and its time.
 * Then one thread replays the logged actions, each at its record's time (a part as
 * maintain(B) with Db.TestHooks.maintainMaxParts() 1: the call's first part that writes, which is the part due), on a new
 * database: the stream must be the same, byte for byte from the decided cut, its length and
 * its decided cut the same. So the stream is a function of the accepted actions, in the
 * write lock's order, with their times, whatever the threads did.
 *
 * Usage: java -ea -cp OUT:build/bergdb.jar bergdb.core.ConcProbe SEED SECONDS WRITERS [node]
 *   -Dpause=200000: each writer pauses up to this many ns after a commit (0: none).
 */
public class ConcProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final AtomicLong clock = new AtomicLong(SEC);
    static final ThreadLocal<Object[]> current = new ThreadLocal<>();
    static final List<Object[]> log = new ArrayList<>();       // {kind, tt, data...}, lock order
    static volatile boolean logging;
    static final int PAUSE = Integer.getInteger("pause", 200000);   // ns, at most, after a commit

    static Db start(CutStream s, int node) {
        DbBuilder b = Db.builder().testSetup(s).clock(clock::get);
        if (node == 8) b.maxNodeSize8();
        if (node == 30) b.maxNodeSize30();
        return b.start();
    }

    public static void main(String[] args) throws Exception {
        final long seed = Long.parseLong(args[0]);
        final long seconds = Long.parseLong(args[1]);
        final int writers = Integer.parseInt(args[2]);
        final int node = args.length > 3 ? Integer.parseInt(args[3]) : 0;
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (!logging) return;
                Object[] a = current.get();
                if (a == null) throw new IllegalStateException("a record of no action");
                char kind = (Character) a[0];
                if (x.trans.part) kind = 'm';
                else if (kind == 'm') throw new IllegalStateException("a call's record not a part's");
                Object[] e = a.clone();
                e[0] = kind;
                e[1] = x.trans.tt;
                log.add(e);     // under the write lock: the records' order
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
        CutStream s1 = new CutStream();
        final Db db = start(s1, node);
        db.setStartupDistance(2000);
        db.setRetainDuration(SEC);
        logging = true;
        final long deadline = System.nanoTime() + seconds * 1000000000L;
        final List<Thread> ts = new ArrayList<>();
        final long[] counts = new long[4];
        for (int w = 0; w < writers; w++) {
            final Random r = new Random(seed * 100 + w);
            ts.add(new Thread(() -> {
                while (System.nanoTime() < deadline) {
                    clock.addAndGet(r.nextInt(2000));
                    Trans.Builder b = db.trans();
                    int m = 1 + r.nextInt(3);
                    TreeMap<String, byte[]> kv = new TreeMap<>();
                    for (int j = 0; j < m; j++) {
                        String k = "/k" + r.nextInt(500);
                        byte[] v = r.nextInt(8) == 0 ? null : new byte[r.nextInt(2000)];
                        if (v != null) r.nextBytes(v);
                        kv.put(k, v);
                    }
                    for (Map.Entry<String, byte[]> e : kv.entrySet()) {
                        if (e.getValue() == null) b.delete(e.getKey()); else b.put(e.getKey(), e.getValue());
                    }
                    current.set(new Object[] {'c', 0L, kv});
                    db.execute(b.build());
                    synchronized (counts) { counts[0]++; }
                    // A pause, so that maintain(), which gives way to waiting commits
                    // (031-04, Q9), gets the lock between them.
                    if (PAUSE > 0) java.util.concurrent.locks.LockSupport.parkNanos(r.nextInt(PAUSE));
                }
            }));
        }
        final Random rm = new Random(seed * 100 + 50);
        ts.add(new Thread(() -> {
            while (System.nanoTime() < deadline) {
                clock.addAndGet(rm.nextInt(2000));
                int budget = 100 + rm.nextInt(2000);
                current.set(new Object[] {'m', 0L, budget});
                db.maintain(budget);
                synchronized (counts) { counts[1]++; }
                java.util.concurrent.locks.LockSupport.parkNanos(200000);
            }
        }));
        final Random rs = new Random(seed * 100 + 60);
        ts.add(new Thread(() -> {
            while (System.nanoTime() < deadline) {
                clock.addAndGet(rs.nextInt(2000));
                if (rs.nextBoolean()) {
                    long v = (1 + rs.nextInt(2)) * SEC;
                    current.set(new Object[] {'r', 0L, v});
                    db.setRetainDuration(v);
                } else {
                    int v = 1000 + rs.nextInt(3000);
                    current.set(new Object[] {'s', 0L, v});
                    db.setStartupDistance(v);
                }
                synchronized (counts) { counts[2]++; }
                java.util.concurrent.locks.LockSupport.parkNanos(20000000);
            }
        }));
        for (int q = 0; q < 2; q++) {
            final Random rr = new Random(seed * 100 + 70 + q);
            ts.add(new Thread(() -> {
                while (System.nanoTime() < deadline) {
                    long t = db.currentTime();
                    try {
                        db.getOne(t, bergdb.dag.Keys.toSegments("/k" + rr.nextInt(500)), db.newGetData());
                        GetMany g = db.newGetMany();
                        g.lookupTime = t;
                        g.stopCondition = new GetMany.GetN(20);
                        db.getMany(g);
                    } catch (bergdb.pub.util.LookupTimeNotAvailableException e) {
                        // expired: a cut overtook it
                    }
                    synchronized (counts) { counts[3]++; }
                }
            }));
        }
        for (Thread t : ts) t.start();
        for (Thread t : ts) t.join();
        logging = false;
        db.sync(SyncLevel.ORDINARY);
        final long decided1 = db.getFirstAvailablePos();
        db.close();
        P2CrashProbe.Image a = P2CrashProbe.image(s1, decided1);

        // The replay, one thread, each action at its record's time.
        Db.testHooks = null;
        clock.set(SEC);
        CutStream s2 = new CutStream();
        Db d2 = start(s2, node);
        d2.setStartupDistance(2000);
        d2.setRetainDuration(SEC);
        // A part as maintain(B) with at most one part that writes (Db.TestHooks.maintainMaxParts).
        Db.testHooks = new Db.TestHooks() {
            public int maintainMaxParts() { return 1; }
            public void transExecuted(Db.ExecuteData x) {}
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        int parts = 0, commits = 0, setters = 0;
        for (Object[] e : log) {
            char kind = (Character) e[0];
            clock.set((Long) e[1]);
            switch (kind) {
            case 'c': {
                @SuppressWarnings("unchecked")
                TreeMap<String, byte[]> kv = (TreeMap<String, byte[]>) e[2];
                Trans.Builder b = d2.trans();
                for (Map.Entry<String, byte[]> x : kv.entrySet()) {
                    if (x.getValue() == null) b.delete(x.getKey()); else b.put(x.getKey(), x.getValue());
                }
                d2.execute(b.build());
                commits++;
                break;
            }
            case 'm': d2.maintain((Integer) e[2]); parts++; break;
            case 'r': d2.setRetainDuration((Long) e[2]); setters++; break;
            case 's': d2.setStartupDistance((Integer) e[2]); setters++; break;
            default: throw new IllegalStateException();
            }
        }
        d2.sync(SyncLevel.ORDINARY);
        final long decided2 = d2.getFirstAvailablePos();
        d2.close();
        Db.testHooks = null;
        P2CrashProbe.Image b = P2CrashProbe.image(s2, decided2);
        String why = P2CrashProbe.compare(a, b);
        System.out.println("seed " + seed + ", " + seconds + " s, " + writers + " writers, node "
                + node + ": " + counts[0] + " commits, " + counts[1] + " maintain() calls, "
                + counts[2] + " setter calls, " + counts[3] + " reads; " + log.size()
                + " records (" + commits + " commits, " + parts + " parts, " + setters
                + " setters'), stream " + a.length + ", decided cut " + a.decided + "; replayed: "
                + (why == null ? "the same stream" : "DIFFERENT, " + why));
        if (why != null) System.exit(1);
    }
}
