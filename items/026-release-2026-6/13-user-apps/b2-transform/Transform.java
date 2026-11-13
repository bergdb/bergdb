import bergdb.core.*;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

import java.io.File;
import java.nio.ByteBuffer;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * B2 of 026-13: Core value and key transformations that throw or pass the limits, amid
 * concurrent writers and readers (bergdb 026-06), written from the Javadoc of
 * ValueTransformation, KeyTransformation, Trans.Builder and Db ("Limits", execute()) only.
 *
 * Writers of plain puts and deletes, each in a key range of its own; transformer threads,
 * each with a group of 5 keys that every transaction of it puts with one stamp, a counter
 * of its own and one of 4 shared counters incremented by value transformations, now and
 * then a log key that a key transformation ends with the transaction's time, and in about
 * a quarter of its transactions a KV that must refuse it: a value transformation that
 * throws, gives 8 MiB + 1, or takes the transaction over 32 MiB; a key transformation that
 * throws, gives 112+ bytes, or gives another key of the transaction; a value transformation
 * that throws once, after which the same Trans is run again and must commit. Oracle: after
 * a refusal the thread's keys are as before, the Trans's KVs as given; readers check that a
 * group is never seen with two stamps; at the end every range, counter and log key against
 * the threads' models, again after a restart; then probes: a value transformation that
 * returns null, and one that throws an Error (the database fails, the restart recovers
 * what was synced).
 *
 * Usage: java -cp bergdb-release.jar:out Transform SEED SECONDS DIR [NODESIZE] [PLAIN] [TRANSFORMERS] [READERS]
 */
public class Transform {
    static Db db;
    static File dir;
    static int nodeSize;
    static volatile boolean stop;
    static volatile String failure;
    static final AtomicLong[] shared = new AtomicLong[4];
    static final AtomicLong refusals = new AtomicLong(), commits = new AtomicLong(), reruns = new AtomicLong(),
            reads = new AtomicLong(), plainTx = new AtomicLong();
    static final ConcurrentHashMap<String, AtomicLong> byMode = new ConcurrentHashMap<>();
    static final byte[] SEVEN_MIB = new byte[7 * 1024 * 1024];

    // per-thread models
    static List<TreeMap<Common.K, byte[]>> plainModels = new ArrayList<>();
    static List<TModel> tModels = new ArrayList<>();

    static final class TModel {
        volatile long stamp = -1;
        long counter;
        final TreeMap<Common.K, byte[]> logs = new TreeMap<>();
    }

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        int seconds = Integer.parseInt(a[1]);
        dir = new File(a[2]);
        nodeSize = a.length > 3 ? Integer.parseInt(a[3]) : 30;
        if (nodeSize != 30) throw new IllegalArgumentException("node size 30 only");  // 026-08: every database a user makes has the node size 30, and no public method sets another
        int nPlain = a.length > 4 ? Integer.parseInt(a[4]) : 2;
        int nT = a.length > 5 ? Integer.parseInt(a[5]) : 3;
        int nR = a.length > 6 ? Integer.parseInt(a[6]) : 2;
        Common.rmrf(dir);
        for (int i = 0; i < 4; i++) shared[i] = new AtomicLong();
        long t0 = System.currentTimeMillis();
        try {
            start();
            db.setRetainDuration(10_000_000L);          // 1 s: reclaim runs beside the writers
            db.setStartupDistance(400_000);
            List<Thread> ts = new ArrayList<>();
            for (int p = 0; p < nPlain; p++) {
                plainModels.add(new TreeMap<>());
                final int pp = p;
                ts.add(new Thread(() -> guard(() -> plain(pp, new Random(seed * 31 + pp))), "plain" + p));
            }
            for (int t = 0; t < nT; t++) {
                tModels.add(new TModel());
                final int tt = t;
                ts.add(new Thread(() -> guard(() -> transformer(tt, new Random(seed * 37 + tt))), "trans" + t));
            }
            for (int r = 0; r < nR; r++) {
                final int rr = r;
                ts.add(new Thread(() -> guard(() -> reader(new Random(seed * 41 + rr), nT)), "reader" + r));
            }
            for (Thread t : ts) t.start();
            long end = System.currentTimeMillis() + seconds * 1000L;
            while (System.currentTimeMillis() < end && failure == null) {
                Thread.sleep(200);
                if ((System.currentTimeMillis() - t0) % 20_000 < 200) progress();
            }
            stop = true;
            for (Thread t : ts) t.join();
            if (failure != null) throw new Common.Fail(failure);
            progress();
            db.sync(SyncLevel.ORDINARY);
            verifyAll("end");
            db.close();
            start();
            verifyAll("after restart");
            probes();
            db.close();
            start();
            verifyAll("after the probes and a restart");
            db.close();
        } catch (Common.Fail f) {
            System.out.println("FAIL Transform seed " + seed + " node " + nodeSize + ": " + f.getMessage());
            try { db.close(); } catch (Throwable t) { }
            System.exit(1);
        } catch (Throwable t) {
            System.out.println("FAIL (exception) Transform seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            try { db.close(); } catch (Throwable x) { }
            System.exit(2);
        }
        Common.log("OK Transform seed " + seed + " node " + nodeSize + ": " + commits + " transformer commits, " + refusals
                + " refusals " + byMode + ", " + reruns + " reruns, " + plainTx + " plain transactions, " + reads + " group reads, "
                + (System.currentTimeMillis() - t0) + " ms");
    }

    static void start() throws Exception {
        DbBuilder b = Db.builder().mainStream(new FileStream(dir, false)).cacheSizeIndicator(30_000_000);
        db = b.start();
    }

    interface Body { void run() throws Exception; }

    static void guard(Body b) {
        try { b.run(); }
        catch (Common.Fail f) { if (failure == null) failure = f.getMessage(); stop = true; }
        catch (Throwable t) {
            java.io.StringWriter sw = new java.io.StringWriter();
            t.printStackTrace(new java.io.PrintWriter(sw));
            if (failure == null) failure = Thread.currentThread().getName() + ": " + sw;
            stop = true;
        }
    }

    static void progress() {
        Common.log("commits " + commits + ", refusals " + refusals + " " + byMode + ", reruns " + reruns + ", plain " + plainTx
                + ", reads " + reads + ", stream " + db.getStreamLength() + ", first available pos " + db.getFirstAvailablePos());
    }

    static byte[] lng(long x) { return ByteBuffer.allocate(8).putLong(x).array(); }
    static long lng(byte[] b) { return ByteBuffer.wrap(b).getLong(); }

    // ---- plain writers ----

    static void plain(int p, Random r) {
        TreeMap<Common.K, byte[]> m = plainModels.get(p);
        while (!stop) {
            int n = 1 + r.nextInt(r.nextInt(10) == 0 ? 400 : 40);
            Trans.Builder b = db.trans();
            Map<Common.K, byte[]> ops = new LinkedHashMap<>();
            for (int i = 0; i < n; i++) {
                int k = r.nextInt(3000);
                Common.K key = new Common.K(new byte[] {0x20, (byte) p, (byte) (k >>> 8), (byte) k});
                if (r.nextInt(3) == 0) { b.delete(key.b); ops.put(key, null); }
                else { byte[] v = Common.value(r, 200); b.put(key.b, v); ops.put(key, v); }
            }
            db.execute(b.build());
            for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
                if (e.getValue() == null) m.remove(e.getKey()); else m.put(e.getKey(), e.getValue());
            }
            plainTx.incrementAndGet();
        }
    }

    // ---- transformers ----

    static byte[] gkey(int t, int i) { return new byte[] {0x30, (byte) t, 0x00, (byte) i}; }
    static byte[] ckey(int t) { return new byte[] {0x30, (byte) t, 0x01}; }
    static byte[] skey(int j) { return new byte[] {0x50, (byte) j}; }

    static final ValueTransformation INCREMENT = (tt, in, prev) -> lng(prev == null ? 1 : lng(prev) + 1);

    /** Ends the key with the transaction's time, 8 bytes; the write hash with it (KeyTransformation). */
    static final class AppendTime implements KeyTransformation {
        final int extra;   // bytes of padding before the time: a long key when large
        AppendTime(int extra) { this.extra = extra; }
        @Override public void transform(Trans trans, int index) {
            byte[] k = Keys.toBytes(trans.kvs[index].getKey());
            byte[] nk = Arrays.copyOf(k, k.length + extra + 8);
            Arrays.fill(nk, k.length, k.length + extra, (byte) 0x77);
            ByteBuffer.wrap(nk, k.length + extra, 8).putLong(trans.tt);
            long[] seg = Keys.toSegments(nk);
            trans.kvs[index].setKey(seg);
            trans.writeKeyHashes[index] = Keys.hash(seg);
        }
    }

    static final String[] MODES = {"vt-throws", "vt-over-L4", "vt-over-L5", "kt-throws", "kt-over-L2", "kt-duplicate",
            "vt-throws-once"};

    static void transformer(int t, Random r) {
        TModel m = tModels.get(t);
        long seq = 0;
        GetData gd = db.newGetData();
        while (!stop) {
            long stamp = ((long) t << 40) | ++seq;
            int j = r.nextInt(4);
            boolean log = r.nextInt(3) == 0;
            String mode = r.nextInt(4) == 0 ? MODES[r.nextInt(MODES.length)] : null;
            final boolean[] thrown = {false};
            Trans.Builder b = db.trans();
            for (int i = 0; i < 5; i++) b.put(gkey(t, i), lng(stamp));
            b.put(Keys.toSegments(ckey(t)), null, new byte[0], INCREMENT);
            b.put(Keys.toSegments(skey(j)), null, new byte[0], INCREMENT);
            if (log) b.put(Keys.toSegments(new byte[] {0x30, (byte) t, 0x02}), new AppendTime(0), lng(stamp), null);
            if (mode != null) addMode(b, t, mode, stamp, thrown, r);
            Trans tr = b.build();
            long[][] keysBefore = new long[tr.kvs.length][];
            byte[][] valsBefore = new byte[tr.kvs.length][];
            for (int i = 0; i < tr.kvs.length; i++) { keysBefore[i] = tr.kvs[i].getKey().clone(); valsBefore[i] = tr.kvs[i].getValue(); }
            long counterBefore = m.counter;
            boolean committed;
            try {
                db.execute(tr);
                committed = true;
            } catch (DbFailedException e) {
                throw new Common.Fail("the database failed at a transaction of mode " + mode + ": " + e + " cause " + e.getCause());
            } catch (DbException e) {
                committed = false;
                if (mode == null) throw new Common.Fail("a plain transformer transaction refused: " + e);
                if ((mode.equals("vt-throws") || mode.equals("kt-throws") || mode.equals("vt-throws-once"))
                        && (e.getCause() == null || !String.valueOf(e.getCause().getMessage()).contains("" + stamp)))
                    throw new Common.Fail("mode " + mode + ": the DbException's cause is not the transformation's exception: " + e
                            + " cause " + e.getCause());
            }
            if (mode != null && committed && !mode.equals("vt-throws-once"))
                throw new Common.Fail("mode " + mode + " committed (stamp " + stamp + ")");
            if (mode != null && mode.equals("vt-throws-once") && committed)
                throw new Common.Fail("vt-throws-once committed at the first run");
            if (!committed) {
                refusals.incrementAndGet();
                byMode.computeIfAbsent(mode, x -> new AtomicLong()).incrementAndGet();
                // The Trans as it was: keys as written, values as given (ValueTransformation, KeyTransformation).
                for (int i = 0; i < tr.kvs.length; i++) {
                    if (!Arrays.equals(tr.kvs[i].getKey(), keysBefore[i]))
                        throw new Common.Fail("mode " + mode + ": KV " + i + "'s key not given back: " + Common.hex(Keys.toBytes(tr.kvs[i].getKey())));
                    if (tr.kvs[i].getValue() != valsBefore[i] && !Arrays.equals(tr.kvs[i].getValue(), valsBefore[i]))
                        throw new Common.Fail("mode " + mode + ": KV " + i + "'s value not given back");
                }
                // Nothing written: the group, the counter, the fail key.
                checkGroup(t, m.stamp, gd, "after a refusal of mode " + mode);
                byte[] cv = db.getOne(Long.MAX_VALUE, Keys.toSegments(ckey(t)), gd);
                long cnt = cv == null ? 0 : lng(cv);
                if (cnt != counterBefore) throw new Common.Fail("mode " + mode + ": own counter " + cnt + " after a refusal, expected " + counterBefore);
                if (db.getOne(Long.MAX_VALUE, Keys.toSegments(new byte[] {0x30, (byte) t, 0x03}), gd) != null)
                    throw new Common.Fail("mode " + mode + ": the refused KV is in the database");
                if (mode.equals("vt-throws-once")) {
                    db.execute(tr);                          // run again: it must commit now
                    committed = true;
                    reruns.incrementAndGet();
                    byte[] fv = db.getOne(Long.MAX_VALUE, Keys.toSegments(new byte[] {0x30, (byte) t, 0x03}), gd);
                    if (fv == null || fv.length != 1 || fv[0] != 8) throw new Common.Fail("the rerun's transformed value is "
                            + Common.hex(fv) + ", expected 08");
                    // delete it again so that the next refusal's check holds
                    db.execute(db.trans().delete(new byte[] {0x30, (byte) t, 0x03}).build());
                }
            }
            if (committed) {
                m.stamp = stamp;
                m.counter++;
                shared[j].incrementAndGet();
                if (log) {
                    byte[] lk = Arrays.copyOf(new byte[] {0x30, (byte) t, 0x02}, 11);
                    ByteBuffer.wrap(lk, 3, 8).putLong(tr.tt);
                    synchronized (m.logs) { m.logs.put(new Common.K(lk), lng(stamp)); }
                }
                commits.incrementAndGet();
                byte[] cv = db.getOne(Long.MAX_VALUE, Keys.toSegments(ckey(t)), gd);
                if (cv == null || lng(cv) != m.counter) throw new Common.Fail("own counter " + (cv == null ? "null" : lng(cv))
                        + ", expected " + m.counter + " after a commit");
                checkGroup(t, stamp, gd, "after a commit");
            }
        }
    }

    static void addMode(Trans.Builder b, int t, String mode, long stamp, boolean[] thrown, Random r) {
        long[] fk = Keys.toSegments(new byte[] {0x30, (byte) t, 0x03});
        switch (mode) {
            case "vt-throws":
                b.put(fk, null, new byte[1], (tt, in, prev) -> { throw new IllegalStateException("app throws " + stamp); });
                break;
            case "vt-over-L4":
                b.put(fk, null, new byte[1], (tt, in, prev) -> new byte[Db.MAX_VALUE_BYTES + 1]);
                break;
            case "vt-over-L5":
                for (int i = 0; i < 4; i++) b.put(new byte[] {0x30, (byte) t, 0x04, (byte) i}, SEVEN_MIB);
                b.put(fk, null, new byte[1], (tt, in, prev) -> new byte[5 * 1024 * 1024]);
                break;
            case "kt-throws":
                b.put(fk, (tr, ix) -> { throw new UnsupportedOperationException("kt throws " + stamp); }, new byte[1], null);
                break;
            case "kt-over-L2":
                b.put(Keys.toSegments(Arrays.copyOf(new byte[] {0x30, (byte) t, 0x05}, 96 + r.nextInt(8))),
                        new AppendTime(8), new byte[1], null);
                break;
            case "kt-duplicate":
                b.put(fk, (tr, ix) -> {
                    long[] seg = Keys.toSegments(gkey(t, 2));
                    tr.kvs[ix].setKey(seg);
                    tr.writeKeyHashes[ix] = Keys.hash(seg);
                }, new byte[1], null);
                break;
            case "vt-throws-once":
                b.put(fk, null, new byte[] {7}, (tt, in, prev) -> {
                    if (!thrown[0]) { thrown[0] = true; throw new IllegalStateException("once " + stamp); }
                    return new byte[] {(byte) (in[0] + 1)};
                });
                break;
            default: throw new Common.Fail("mode");
        }
    }

    static void checkGroup(int t, long stamp, GetData gd, String what) {
        for (int i = 0; i < 5; i++) {
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(gkey(t, i)), gd);
            long got = v == null ? -1 : lng(v);
            if (got != stamp) throw new Common.Fail("group " + t + " key " + i + " has stamp " + got + ", expected " + stamp + " " + what);
        }
    }

    // ---- readers ----

    static void reader(Random r, int nT) {
        while (!stop) {
            int t = r.nextInt(nT);
            long time = r.nextBoolean() ? Long.MAX_VALUE : db.currentTime();
            GetMany g = db.newGetMany();
            g.lookupTime = time;
            g.startKey = Keys.toSegments(new byte[] {0x30, (byte) t, 0x00});
            g.stopCondition = new GetMany.Prefix(Keys.toSegments(new byte[] {0x30, (byte) t, 0x00}));
            try {
                db.getMany(g);
            } catch (RuntimeException e) {
                if (Common.isNotAvailable(e)) continue;
                throw e;
            }
            long first = Long.MIN_VALUE;
            for (Kvt kvt : g.result) {
                long s = lng(kvt.value);
                if (first == Long.MIN_VALUE) first = s;
                else if (s != first) throw new Common.Fail("reader: group " + t + " has stamps " + first + " and " + s + " at "
                        + g.actualLookupTime);
            }
            if (g.result.size() != 0 && g.result.size() != 5) throw new Common.Fail("reader: group " + t + " has " + g.result.size() + " keys");
            if (first != Long.MIN_VALUE && (first >>> 40) != t) throw new Common.Fail("reader: a foreign stamp");
            reads.incrementAndGet();
        }
    }

    // ---- final checks ----

    static TreeMap<Common.K, byte[]> scanPrefix(byte[] prefix) {
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments(prefix);
        g.stopCondition = new GetMany.Prefix(Keys.toSegments(prefix));
        db.getMany(g);
        TreeMap<Common.K, byte[]> m = new TreeMap<>();
        for (Kvt kvt : g.result) m.put(new Common.K(Keys.toBytes(kvt.key)), kvt.value);
        return m;
    }

    static void sameMap(String what, TreeMap<Common.K, byte[]> exp, TreeMap<Common.K, byte[]> got) {
        if (exp.size() != got.size()) throw new Common.Fail(what + ": " + got.size() + " KVs, expected " + exp.size());
        Iterator<Map.Entry<Common.K, byte[]>> a = exp.entrySet().iterator(), b = got.entrySet().iterator();
        while (a.hasNext()) {
            Map.Entry<Common.K, byte[]> x = a.next(), y = b.next();
            if (!x.getKey().equals(y.getKey()) || !Arrays.equals(x.getValue(), y.getValue()))
                throw new Common.Fail(what + ": " + y.getKey() + "=" + Common.hex(y.getValue()) + ", expected " + x.getKey() + "="
                        + Common.hex(x.getValue()));
        }
    }

    static void verifyAll(String what) {
        for (int p = 0; p < plainModels.size(); p++) sameMap(what + ": plain " + p, plainModels.get(p), scanPrefix(new byte[] {0x20, (byte) p}));
        GetData gd = db.newGetData();
        for (int t = 0; t < tModels.size(); t++) {
            TModel m = tModels.get(t);
            checkGroup(t, m.stamp, gd, what);
            byte[] cv = db.getOne(Long.MAX_VALUE, Keys.toSegments(ckey(t)), gd);
            if ((cv == null ? 0 : lng(cv)) != m.counter) throw new Common.Fail(what + ": counter of " + t + " is "
                    + (cv == null ? 0 : lng(cv)) + ", expected " + m.counter);
            sameMap(what + ": logs of " + t, m.logs, scanPrefix(new byte[] {0x30, (byte) t, 0x02}));
            for (byte x : new byte[] {0x03, 0x04, 0x05})
                if (!scanPrefix(new byte[] {0x30, (byte) t, x}).isEmpty()) throw new Common.Fail(what + ": a refused KV is in the database, prefix " + x);
        }
        for (int j = 0; j < 4; j++) {
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(skey(j)), gd);
            long got = v == null ? 0 : lng(v);
            if (got != shared[j].get()) throw new Common.Fail(what + ": shared counter " + j + " is " + got + ", expected " + shared[j]);
        }
        Common.log(what + ": all ranges, counters and logs as the oracle");
    }

    static void probes() throws Exception {
        GetData gd = db.newGetData();
        // Alone: a refusal of each mode appends nothing and counts no transaction (Db.execute: nothing written).
        Random r = new Random(5);
        for (String mode : MODES) {
            if (mode.equals("vt-throws-once")) continue;
            Trans.Builder b = db.trans();
            for (int i = 0; i < 5; i++) b.put(gkey(0, i), lng(-5));
            addMode(b, 0, mode, -5, new boolean[1], r);
            long len = db.getStreamLength(), txc = db.getTransactionCount(), kvc = db.getKvCount();
            try { db.execute(b.build()); throw new Common.Fail("alone: mode " + mode + " committed"); }
            catch (DbFailedException e) { throw new Common.Fail("alone: mode " + mode + " failed the database: " + e); }
            catch (DbException e) { }
            if (db.getStreamLength() != len || db.getTransactionCount() != txc || db.getKvCount() != kvc)
                throw new Common.Fail("alone: a refusal of mode " + mode + " changed the stream length " + len + " -> "
                        + db.getStreamLength() + ", transactions " + txc + " -> " + db.getTransactionCount() + ", KVs " + kvc
                        + " -> " + db.getKvCount());
        }
        verifyAll("after the refusals alone");
        byte[] pk = {0x31, 0x01};
        // A value transformation that returns null over a value, then a restart: what is stored?
        db.execute(db.trans().put(pk, new byte[] {9}).build());
        Trans nt = db.trans().put(Keys.toSegments(pk), null, new byte[] {1}, (tt, in, prev) -> null).build();
        String overValue;
        try {
            db.execute(nt);
            overValue = "committed over a value; the key reads " + Common.hex(db.getOne(Long.MAX_VALUE, Keys.toSegments(pk), gd))
                    + ", at the transaction's time less one " + Common.hex(db.getOne(nt.tt - 1, Keys.toSegments(pk), gd));
            StoredTrans st = db.getTrans(nt.tpos);
            overValue += "; getTrans lists " + st.getValueNodes().size() + " value nodes";
        } catch (Throwable e) {
            overValue = "threw " + e;
        }
        Common.log("probe, a null result over a value: " + overValue);
        db.sync(SyncLevel.ORDINARY);
        db.close();
        start();
        gd = db.newGetData();
        Common.log("probe, after a restart the key reads " + Common.hex(db.getOne(Long.MAX_VALUE, Keys.toSegments(pk), gd)));
        db.execute(db.trans().delete(pk).build());
        // A value transformation that returns null: not said in the Javadoc. Recorded.
        String nullResult;
        try {
            db.execute(db.trans().put(Keys.toSegments(pk), null, new byte[] {1}, (tt, in, prev) -> null).build());
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(pk), gd);
            nullResult = "committed; the key reads " + Common.hex(v);
            db.execute(db.trans().delete(pk).build());
        } catch (DbFailedException e) {
            nullResult = "THE DATABASE FAILED: " + e + " cause " + e.getCause();
        } catch (Throwable e) {
            nullResult = "refused: " + e + " cause " + e.getCause();
        }
        Common.log("probe, a value transformation that returns null: " + nullResult);
        boolean failed = nullResult.startsWith("THE DATABASE FAILED");
        if (failed) {
            System.out.println("FINDING null-vt: " + nullResult);
            db.close();
            start();
            verifyAll("after the null probe failed the database");
        }
        // An Error from a value transformation fails the database (Db, "Errors"); a restart recovers.
        db.sync(SyncLevel.ORDINARY);
        String errResult;
        try {
            db.execute(db.trans().put(Keys.toSegments(pk), null, new byte[] {1}, (tt, in, prev) -> { throw new AssertionError("app error"); }).build());
            errResult = "committed";
        } catch (AssertionError e) {
            errResult = "the Error as it is";
        } catch (Throwable e) {
            errResult = "threw " + e;
        }
        String after;
        try { db.getOne(Long.MAX_VALUE, Keys.toSegments(pk), gd); after = "a read works"; }
        catch (DbFailedException e) { after = "a read throws DbFailedException"; }
        Common.log("probe, an Error from a value transformation: " + errResult + "; then " + after);
        if (!errResult.equals("the Error as it is") || !after.contains("DbFailed"))
            System.out.println("FINDING error-vt: " + errResult + "; " + after);
        db.close();
        start();
        if (db.getOne(Long.MAX_VALUE, Keys.toSegments(pk), gd = db.newGetData()) != null)
            throw new Common.Fail("the transaction whose transformation threw an Error is in the database after the restart");
    }
}
