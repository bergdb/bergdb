package bergdb.core;

import java.util.*;

import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06's probe of Codex's third test (2026-11-27): reclaim's safety and pace with
 * one record an action. Old live values (cold keys put once), overlapping puts and deletes
 * of hot keys, value transformations, key transformations onto cold keys (so that the copy
 * of a key that the action writes, by its key as transformed, is dropped), a small step
 * reserve (split steps), a lowered record limit with sustained large commits (values of
 * up to 0.8 of the transaction's value limit), maintain() calls and restarts.
 *
 * Checked, every CHECK actions, after every restart and after every new cut:
 *   latest: every key's value is the model's;
 *   historical: at sampled times from the first available lookup time on, every key's value
 *     is the model's at that time;
 *   provenance: for every live key, the walk of Connection.transactionInfo() (a value whose
 *     node has the copy mark is followed to the value before the record, equal and stored
 *     before it) ends at a record at the model's time of the key's last write, whose node of
 *     the key has no copy mark;
 *   the stream kept (the stream's length less the first available position) stays within
 *     the stated bound (bound()), BOUND = 2 x max(8 x LIVE, W / 6, 2 x SD) + 3 x W + 2 x
 *     META + 2 x CAP, LIVE the most node bytes of the live values so far, W the most bytes
 *     written in a window of 1.5 retain durations so far, SD the startup distance, META the
 *     meta block distance and CAP the record cap; and its largest value in the run's last
 *     third is at most 1.25 times its largest in the middle third (no growth without end).
 * And a run through the Pub API (DatabaseImp on a Core Db with a test clock), whose
 * transactionInfo() of every key is checked against the time its put returned, before and
 * after cuts and restarts.
 *
 * Usage, compiled with P2CrashProbe:
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.SafetyProbe SEED ACTIONS
 *   -Dlimit=200000 (the record limit, StoredTrans.recordLimit; 0: the release's)
 *   -Dreserve=2000 (the step reserve) -Dnode=8|30 -Dcold=300 -Dhot=60 -Dsd=2000
 */
public class SafetyProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final int COLD = Integer.getInteger("cold", 300), HOT = Integer.getInteger("hot", 60);
    static final int SD = Integer.getInteger("sd", 2000), CHECK = Integer.getInteger("check", 50);
    static final long LIMIT = Long.getLong("limit", 200000), RESERVE = Long.getLong("reserve", 2000);
    static final int NODE = Integer.getInteger("node", 0);
    static long time = SEC;
    static final CoreTestClock clock = new CoreTestClock();
    static final Map<String, TreeMap<Long, byte[]>> model = new TreeMap<>();
    static final List<long[]> written = new ArrayList<>();      // (time, stream length)
    static long maxLive, maxW;
    static long checks, histReads, walks, walksRefused, copiesFollowed, maxRatio1000, cutsSeen;

    static Db start(CutStream s) {
        DbBuilder b = Db.builder().testSetup(s).clock(clock).reclaimStepReserve(RESERVE);
        if (NODE == 8) b.maxNodeSize8();
        if (NODE == 30) b.maxNodeSize30();
        return b.start();
    }

    static void put(String k, long tt, byte[] v) {
        model.computeIfAbsent(k, x -> new TreeMap<>()).put(tt, v);
    }

    public static void main(String[] args) throws Exception {
        long seed = Long.parseLong(args[0]);
        int n = Integer.parseInt(args[1]);
        final long saved = StoredTrans.recordLimit;
        if (LIMIT > 0) StoredTrans.recordLimit = LIMIT;
        try {
            core(seed, n);
            PubInfoProbe.run(seed, n / 4, SD, RESERVE, NODE);
        } finally {
            StoredTrans.recordLimit = saved;
        }
    }

    static void core(long seed, int n) throws Exception {
        Random r = new Random(seed);
        clock.setTime(time);
        CutStream s = new CutStream();
        Db db = start(s);
        db.setStartupDistance(SD);
        db.setRetainDuration(SEC);
        final long valueLimit = StoredTrans.valueLimit();
        // Old live values: the cold keys, put once (some rewritten by key transformations).
        for (int i = 0; i < COLD; i += 10) {
            time += SEC / 50; clock.setTime(time);
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(COLD, i + 10); j++) b.put("/c/" + j, value(r, 1 + r.nextInt(300)));
            Trans t = b.build();
            db.execute(t);
            for (Kv kv : t.kvs) put(Keys.toString(kv.getKey()), t.tt, kv.getValue());
        }
        long maxKeptMid = 0, maxKeptEnd = 0, lastFirst = 0;
        int large = 0, kts = 0, vts = 0, deletes = 0, maint = 0, restarts = 0, refused = 0;
        for (int i = 0; i < n; i++) {
            time += 1 + r.nextInt((int) (SEC / 10)); clock.setTime(time);
            int c = r.nextInt(100);
            Trans t = null;
            try {
                if (c < 50) {
                    Trans.Builder b = db.trans();
                    int m = 1 + r.nextInt(4);
                    for (int j = 0; j < m; j++) b.put("/h/" + r.nextInt(HOT), value(r, r.nextInt(400)));
                    t = b.build();
                } else if (c < 60) {
                    deletes++;
                    t = db.trans().delete(r.nextBoolean() ? "/h/" + r.nextInt(HOT) : "/c/" + r.nextInt(COLD)).build();
                } else if (c < 70) {
                    // A value transformation: the previous value and one byte, or a delete.
                    vts++;
                    final byte add = (byte) r.nextInt(256);
                    final String k = r.nextBoolean() ? "/h/" + r.nextInt(HOT) : "/c/" + r.nextInt(COLD);
                    t = db.trans().put(Keys.toSegments(k), null, new byte[0], new ValueTransformation() {
                        public byte[] transform(long tt, byte[] in, byte[] prev) {
                            if (prev != null && prev.length > 600) return null;
                            byte[] v = prev == null ? new byte[0] : prev;
                            v = Arrays.copyOf(v, v.length + 1);
                            v[v.length - 1] = add;
                            return v;
                        }
                    }).build();
                } else if (c < 78) {
                    // A key transformation onto a cold key, which reclaim may be copying.
                    kts++;
                    final String target = "/c/" + r.nextInt(COLD);
                    t = db.trans().put(Keys.toSegments("/x/" + i), new KeyTransformation() {
                        public void transform(Trans tr, int index) {
                            tr.kvs[index].setKey(Keys.toSegments(target));
                        }
                    }, value(r, r.nextInt(200)), null).build();
                } else if (c < 84) {
                    // A sustained large commit: values up to 0.8 of the value limit.
                    large++;
                    Trans.Builder b = db.trans();
                    long left = (long) (valueLimit * (0.5 + 0.3 * r.nextDouble()));
                    for (int j = 0; j < 4 && left > 1000; j++) {
                        int len = (int) Math.min(left - 200, Math.min(Db.MAX_VALUE_BYTES, left / (4 - j)));
                        b.put("/L/" + j, value(r, Math.max(0, len)));
                        left -= len + 200;
                    }
                    t = b.build();
                } else if (c < 90) {
                    maint++;
                    db.maintain(100 + r.nextInt(2000));
                } else if (c < 93) {
                    t = db.trans().build();
                } else if (c < 94) {
                    restarts++;
                    db.sync(SyncLevel.ORDINARY);
                    db.close();
                    s = s.copy();
                    db = start(s);
                    check(db, s, r, "restart " + i);
                } else {
                    Trans.Builder b = db.trans();
                    b.put("/h/" + r.nextInt(HOT), value(r, r.nextInt(3000)));
                    t = b.build();
                }
                if (t != null) {
                    db.execute(t);
                    for (Kv kv : t.kvs) put(Keys.toString(kv.getKey()), t.tt, kv.getValue());
                }
            } catch (bergdb.pub.util.DbException e) {
                if (e instanceof bergdb.pub.util.DbFailedException) throw e;
                refused++;      // a transaction over the lowered limits: refused, nothing written
            }
            written.add(new long[] {time, db.getStreamLength()});
            long kept = db.getStreamLength() - db.getFirstAvailablePos();
            if (i >= n / 3 && i < 2 * n / 3) maxKeptMid = Math.max(maxKeptMid, kept);
            if (i >= 2 * n / 3) maxKeptEnd = Math.max(maxKeptEnd, kept);
            boolean cut = db.getFirstAvailablePos() != lastFirst;
            if (cut) { cutsSeen++; lastFirst = db.getFirstAvailablePos(); }
            if (cut || i % CHECK == CHECK - 1) check(db, s, r, "action " + i);
            bound(db);
        }
        check(db, s, r, "end");
        db.close();
        System.out.println("core: seed " + seed + ", " + n + " actions (" + large + " large, "
                + kts + " key transformations, " + vts + " value transformations, " + deletes
                + " deletes, " + maint + " maintain() calls, " + restarts + " restarts, " + refused
                + " refused), record limit " + StoredTrans.recordLimit + ", cap "
                + StoredTrans.recordCap() + ", reserve " + RESERVE + ", node " + NODE + ": "
                + checks + " checks, " + histReads + " historical reads, " + walks + " walks ("
                + copiesFollowed + " copies followed, " + walksRefused + " refused: the write before the first available time), " + cutsSeen + " cuts; the stream kept "
                + "at most " + maxRatio1000 / 10.0 + " % of the bound; its largest in the last "
                + "third " + maxKeptEnd + ", in the middle third " + maxKeptMid + ": OK");
        if (maxKeptEnd > maxKeptMid * 5 / 4) throw new AssertionError("the stream kept grows: "
                + maxKeptEnd + " after " + maxKeptMid);
    }

    static byte[] value(Random r, int len) {
        byte[] v = new byte[len];
        r.nextBytes(v);
        return v;
    }

    /** The stated bound of the stream kept (the class comment). */
    static void bound(Db db) {
        long live = 0;
        for (Map.Entry<String, TreeMap<Long, byte[]>> e : model.entrySet()) {
            byte[] v = e.getValue().lastEntry().getValue();
            if (v != null) live += StoredValueNode.getByteSizeLong(v, Keys.toSegments(e.getKey()));
        }
        long now = time, from = now - 3 * SEC / 2, w0 = -1;
        for (long[] tw : written) if (tw[0] >= from) { w0 = tw[1]; break; }
        long w = w0 == -1 ? 0 : db.getStreamLength() - w0;
        long cap = StoredTrans.recordCap();
        maxLive = Math.max(maxLive, live);
        maxW = Math.max(maxW, w);
        // A cut point is the iteration before's pStart: that iteration, the next one (each
        // rewrites the live values, with their index nodes about twice their bytes, at the
        // internal fraction, 1/4, of the growth, and begins after a quarter of R and two
        // startup distances), the retain duration after the second one's end, the startup
        // pos's lag and a meta block, each with a record of the largest size.
        long bound = 2 * Math.max(8 * maxLive, Math.max(maxW / 6, 2L * SD)) + 3 * maxW
                + 2 * bergdb.storage.RecoverableStream.META_BLOCK_DISTANCE + 2 * cap;
        long kept = db.getStreamLength() - db.getFirstAvailablePos();
        maxRatio1000 = Math.max(maxRatio1000, kept * 1000 / bound);
        if (kept > bound) throw new AssertionError("kept " + kept + " over the bound " + bound
                + " (live " + live + ", written in 1.5 R " + w + ", cap " + cap + ")");
    }

    static void check(Db db, CutStream s, Random r, String where) {
        checks++;
        final long first = db.getFirstAvailableLookupTime();
        for (Map.Entry<String, TreeMap<Long, byte[]>> e : model.entrySet()) {
            final long[] key = Keys.toSegments(e.getKey());
            final byte[] want = e.getValue().lastEntry().getValue();
            final GetData gd = db.newGetData();
            final byte[] got = db.getOne(Long.MAX_VALUE, key, gd);
            if (!Arrays.equals(want, got)) throw new AssertionError(where + ": latest " + e.getKey());
            if (got != null) walk(db, key, gd.tpos, e.getValue().lastKey(), where);
            for (int j = 0; j < 3; j++) {
                long t = first + (long) (r.nextDouble() * Math.max(1, time - first));
                Map.Entry<Long, byte[]> f = e.getValue().floorEntry(t);
                byte[] w = f == null ? null : f.getValue();
                histReads++;
                if (!Arrays.equals(w, db.getOne(t, key, db.newGetData()))) {
                    throw new AssertionError(where + ": " + e.getKey() + " at " + t + " (first " + first + ")");
                }
            }
        }
    }

    /** Connection.transactionInfo()'s walk: through the copies to the write (bergdb 031-06). */
    static void walk(Db db, long[] key, long tpos, long wantTime, String where) {
        walks++;
        StoredTrans st = db.getTrans(tpos);
        while (true) {
            StoredValueNode node = null;
            for (StoredNode sn : st.nodes) {
                if (sn instanceof StoredValueNode && Arrays.equals(key, ((StoredValueNode) sn).getKey())) {
                    node = (StoredValueNode) sn;
                }
            }
            if (node == null) throw new AssertionError(where + ": no node of the key in its record");
            if (!node.isCopy()) break;
            copiesFollowed++;
            GetData before = db.newGetData();
            if (st.tt - 1 < db.getFirstAvailableLookupTime()) {
                // transactionInfo() refuses: the write is before the first available time.
                walksRefused++;
                if (wantTime >= db.getFirstAvailableLookupTime()) throw new AssertionError(where
                        + ": a copy before the first available time of a write after it");
                return;
            }
            byte[] copied = db.getOne(st.tt - 1, key, before);
            if (!Arrays.equals(copied, node.getValueNode().value) || before.tpos >= st.tpos) {
                throw new AssertionError(where + ": a copy that is not the value before it");
            }
            st = db.getTrans(before.tpos);
        }
        if (st.tt != wantTime) throw new AssertionError(where + ": the walk ends at " + st.tt
                + ", the key was last written at " + wantTime);
    }

}
