package bergdb.core;

import java.util.*;

import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * Review probe of bergdb 031-06 (2026-11-27): actions aimed at the keys that the next step's
 * scan meets (the keys after the running iteration's lastKey), so that the copy of a key that
 * the action writes is dropped at nearly every step: a put of the same bytes, a value
 * transformation that returns the previous value (the same array), a delete, a value
 * transformation that deletes, a key transformation onto the key, a Trans executed twice, a
 * refused transaction before it, an empty commit, maintain() parts and restarts; each aimed
 * action also puts a value of 3 to 6 kB at a hot key, so that its own record may carry the
 * step. Checked
 * against a model after every cut and restart and every CHECK actions: the latest value of
 * every key, and its value at sampled times from the first available lookup time.
 *
 * Usage: java -ea -cp OUT:build/bergdb.jar bergdb.core.RvFront SEED ACTIONS [NODE]
 *   -Dcold=400 -Dlen=300 -Dsd=2000 -Dcache=BYTES (eviction with that budget; default none)
 *   -Dmaint=4 (the maintain() calls, a percentage of the actions; 0: the commits' steps only)
 */
public class RvFront {
    static final long SEC = Clock.UNITS_PER_SEC;
    static long time = SEC;
    static final CoreTestClock clock = new CoreTestClock();
    static final TreeMap<String, TreeMap<Long, byte[]>> model = new TreeMap<>();
    static long hist, cuts, aimed, dropped, restarts, refused;
    static int NODE;
    static long totD, totS;

    static Db start(CutStream s) {
        DbBuilder b = Db.builder().testSetup(s).clock(clock);
        if (NODE == 8) b.maxNodeSize8();
        if (NODE == 30) b.maxNodeSize30();
        if (Long.getLong("cache", 0) > 0) b.cacheSizeIndicator(Long.getLong("cache"));
        return b.start();
    }

    static void put(String k, long tt, byte[] v) {
        model.computeIfAbsent(k, x -> new TreeMap<>()).put(tt, v);
    }

    static byte[] value(Random r, int len) {
        byte[] v = new byte[len];
        r.nextBytes(v);
        return v;
    }

    /** A hot key for a value that makes the stream grow, so that the action's record may
     *  carry a step (the commit's allowance is a fraction of the growth). */
    static String grow(Random r) {
        return "/g/" + r.nextInt(30);        // never aimed at (the front leaves /g/ out)
    }

    static byte[] latest(String k) {
        TreeMap<Long, byte[]> m = model.get(k);
        return m == null ? null : m.lastEntry().getValue();
    }

    public static void main(String[] args) throws Exception {
        long seed = Long.parseLong(args[0]);
        int n = Integer.parseInt(args[1]);
        NODE = args.length > 2 ? Integer.parseInt(args[2]) : 0;
        int COLD = Integer.getInteger("cold", 400);
        Random r = new Random(seed);
        clock.setTime(time);
        CutStream s = new CutStream();
        Db db = start(s);
        db.setStartupDistance(Integer.getInteger("sd", 2000));
        db.setRetainDuration(SEC);
        for (int i = 0; i < COLD; i += 10) {
            time += SEC / 50; clock.setTime(time);
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(COLD, i + 10); j++) {
                b.put(String.format("/c/%05d", j), value(r, 1 + r.nextInt(Integer.getInteger("len", 300))));
            }
            Trans t = b.build();
            db.execute(t);
            for (Kv kv : t.kvs) put(Keys.toString(kv.getKey()), t.tt, kv.getValue());
        }
        Reclaim.Stats stats = db.internal().reclaim().enableStats();
        long lastFirst = 0;
        Trans again = null;
        for (int i = 0; i < n; i++) {
            time += 1 + r.nextInt((int) (SEC / 10)); clock.setTime(time);
            // The keys that the next step's scan meets first.
            Reclaim.IterationInfo it = db.internal().reclaim().currentIteration();
            String from = it == null || it.lastKey == null ? "" : Keys.toString(it.lastKey);
            List<String> front = new ArrayList<>();
            for (String k : model.tailMap(from, false).keySet()) {
                if (latest(k) != null && !k.startsWith("/g/")) front.add(k);
                if (front.size() >= 1 + r.nextInt(40)) break;
            }
            int c = r.nextInt(100);
            Trans t = null;
            final String k = front.isEmpty() || c >= 80 ? String.format("/c/%05d", r.nextInt(COLD))
                    : front.get(r.nextInt(front.size()));
            if (it != null && !front.isEmpty() && c < 80) aimed++;
            try {
                if (c < 12) {
                    byte[] v = latest(k);
                    t = db.trans().put(k, v == null ? value(r, 20) : v.clone()).put(grow(r), value(r, 3000 + r.nextInt(3000))).build();
                } else if (c < 24) {
                    t = db.trans().put(Keys.toSegments(k), null, new byte[0], new ValueTransformation() {
                        public byte[] transform(long tt, byte[] in, byte[] prev) {
                            return prev;        // the same array, or null: a delete of no value
                        }
                    }).put(grow(r), value(r, 3000 + r.nextInt(3000))).build();
                } else if (c < 34) {
                    t = db.trans().delete(k).put(grow(r), value(r, 3000 + r.nextInt(3000))).build();
                } else if (c < 42) {
                    t = db.trans().put(Keys.toSegments(k), null, new byte[0], new ValueTransformation() {
                        public byte[] transform(long tt, byte[] in, byte[] prev) {
                            return null;
                        }
                    }).put(grow(r), value(r, 3000 + r.nextInt(3000))).build();
                } else if (c < 54) {
                    final String target = k;
                    t = db.trans().put(Keys.toSegments("/x/" + i), new KeyTransformation() {
                        public void transform(Trans tr, int index) {
                            tr.kvs[index].setKey(Keys.toSegments(target));
                        }
                    }, value(r, r.nextInt(200)), null).put(grow(r), value(r, 3000 + r.nextInt(3000))).build();
                } else if (c < 60 && again != null) {
                    t = again;          // a Trans executed again
                } else if (c < 66) {
                    // A refused transaction (its value transformation throws), then a put.
                    try {
                        db.execute(db.trans().put(Keys.toSegments(k), null, new byte[0], new ValueTransformation() {
                            public byte[] transform(long tt, byte[] in, byte[] prev) {
                                throw new IllegalStateException("refuse");
                            }
                        }).build());
                        throw new AssertionError("not refused");
                    } catch (bergdb.pub.util.DbException e) {
                        if (e instanceof bergdb.pub.util.DbFailedException) throw e;
                        refused++;
                    }
                    t = db.trans().put(k, value(r, r.nextInt(100))).build();
                } else if (c < 72) {
                    // Several of the front's keys in one action, puts and deletes.
                    Trans.Builder b = db.trans();
                    for (String f : front) {
                        if (r.nextInt(3) == 0) b.delete(f); else if (r.nextBoolean()) b.put(f, latest(f).clone());
                    }
                    b.put(grow(r), value(r, 3000 + r.nextInt(3000)));
                    t = b.build();
                } else if (c < 76) {
                    t = db.trans().build();
                } else if (c < 76 + Integer.getInteger("maint", 4)) {
                    db.maintain(100 + r.nextInt(500));
                } else if (c < 82) {
                    restarts++;
                    for (Reclaim.Stats.Iteration st : stats.iterations) { totD += st.droppedCopies; totS += st.steps; }
                    db.sync(SyncLevel.ORDINARY);
                    db.close();
                    s = s.copy();
                    db = start(s);
                    stats = db.internal().reclaim().enableStats();
                    check(db, r, "restart " + i);
                } else {
                    // Growth: new values at hot keys, so that iterations begin and step.
                    Trans.Builder b = db.trans();
                    for (int j = 0; j < 3; j++) b.put("/h/" + r.nextInt(30), value(r, 500 + r.nextInt(3000)));
                    t = b.build();
                }
                if (t != null) {
                    final Kv[] own = t.kvs;
                    final String[] keysBefore = new String[own.length];
                    db.execute(t);
                    for (Kv kv : t.kvs) put(Keys.toString(kv.getKey()), t.tt, kv.getValue());
                    if (t.kvs.length == 1 && t.kvs[0].valueTransformation == null
                            && t.kvs[0].keyTransformation == null) again = t;
                }
            } catch (bergdb.pub.util.DbException e) {
                if (e instanceof bergdb.pub.util.DbFailedException) throw e;
                throw new AssertionError("refused at action " + i + " c " + c, e);
            }
            boolean cut = db.getFirstAvailablePos() != lastFirst;
            if (cut) { cuts++; lastFirst = db.getFirstAvailablePos(); }
            if (cut || i % 40 == 39) check(db, r, "action " + i);
        }
        check(db, r, "end");
        long d = totD, steps = totS;
        for (Reclaim.Stats.Iteration st : stats.iterations) { d += st.droppedCopies; steps += st.steps; }
        db.close();
        System.out.println("RvFront seed " + seed + " node " + NODE + ": " + n + " actions, " + aimed
                + " aimed at the scan's front, " + d + " copies dropped in " + steps
                + " steps " + cuts + " cuts, " + restarts + " restarts, "
                + refused + " refused, " + hist + " historical reads: OK");
    }

    static void check(Db db, Random r, String where) {
        final long first = db.getFirstAvailableLookupTime();
        for (Map.Entry<String, TreeMap<Long, byte[]>> e : model.entrySet()) {
            final long[] key = Keys.toSegments(e.getKey());
            final byte[] want = e.getValue().lastEntry().getValue();
            final byte[] got = db.getOne(Long.MAX_VALUE, key, db.newGetData());
            if (!Arrays.equals(want, got)) throw new AssertionError(where + ": latest " + e.getKey()
                    + " want " + (want == null ? -1 : want.length) + " got " + (got == null ? -1 : got.length));
            for (int j = 0; j < 4; j++) {
                long t = j == 0 ? first : first + (long) (r.nextDouble() * Math.max(1, time - first));
                Map.Entry<Long, byte[]> f = e.getValue().floorEntry(t);
                byte[] w = f == null ? null : f.getValue();
                hist++;
                if (!Arrays.equals(w, db.getOne(t, key, db.newGetData()))) {
                    throw new AssertionError(where + ": " + e.getKey() + " at " + t + " (first " + first + ")");
                }
            }
        }
    }
}
