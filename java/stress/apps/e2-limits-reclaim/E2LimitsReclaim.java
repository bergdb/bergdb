import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.TestNodeSize;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.util.DbException;
import bergdb.stream.FileStream;

import java.io.File;
import java.util.*;

/**
 * App e2 of 031-08: transactions at the limits while reclaim's work rides in the commits
 * (Core API, node sizes 8 to 62 through TestNodeSize, a file stream, a clock that the app
 * moves).
 *
 * A database with a startup distance of 100 kB to 1 MB and a retain duration of 1 s gets a
 * base of live data that reclaim must rewrite at every iteration: 3,000 to 12,000 keys of 111
 * bytes (Db, "Limits": a key has at most MAX_KEY_BYTES = 111 bytes), a few values of 8 MiB
 * (MAX_VALUE_BYTES) and many small ones. Then rounds of a random kind, the clock moved by 0.05
 * to 0.6 s a round so that iterations begin, step and cut in the commits:
 *  - 500 KVs (MAX_OPERATIONS) of new random 111-byte keys, the most index nodes dirty;
 *  - 500 overwrites of base keys;
 *  - one value of exactly 8 MiB, or of 8 MiB + 1 (refused by Trans.Builder.put() with
 *    IllegalArgumentException, which spoils the builder);
 *  - keys and values of exactly 32 MiB (MAX_TRANS_BYTES; four values and their keys), or one
 *    byte more (refused by execute() with a DbException);
 *  - 501 KVs (refused by execute(), DbException); a key of 112 bytes (refused by the
 *    builder);
 *  - a commit of one KV of 1 byte, of an empty value, a delete of a key without a value;
 *  - maintain(budget) calls, 100 to 100,000.
 * Every taken transaction must commit; every refusal must leave the stream's length, the
 * transaction count and the state unchanged, and the database must go on. After each round
 * a check: gets of what the round wrote and of 100 random keys, against the oracle; the
 * promise getFirstAvailableLookupTime() <= currentTime() - R; every 10 rounds a full scan, and
 * a full scan at an older time inside the retain duration; restarts now and then, the state
 * checked after each.
 *
 * Usage: java -Xmx2g E2LimitsReclaim SEED DIR [NODESIZE] [ROUNDS]
 */
public class E2LimitsReclaim {
    static final long T0 = 17_700_000_000_000_000L;
    static final long SEC = 10_000_000L;
    static final int MIB = 1024 * 1024;

    final long seed;
    final Random rnd;
    final File dir;
    final int nodeSize;
    final int sd;
    final Common.Model m = new Common.Model();
    final Common.ManualClock clock = new Common.ManualClock(T0);
    final List<Common.K> base = new ArrayList<>();
    final List<byte[]> bigKeys = new ArrayList<>();   // the keys of the large values: 8 of 111 bytes, overwritten
    Db db;
    long taken, refused, maintains, restarts, scans, lastFirst, cuts, bigBytes;

    E2LimitsReclaim(long seed, File dir, int nodeSize) {
        this.seed = seed;
        this.rnd = new Random(seed);
        this.dir = dir;
        this.nodeSize = nodeSize;
        this.sd = new int[] {100_000, 300_000, 1_000_000}[rnd.nextInt(3)];
    }

    void start() throws Exception {
        DbBuilder b = TestNodeSize.builder(nodeSize).mainStream(new FileStream(dir, false)).clock(clock);
        b.cacheSizeIndicator(64_000_000);
        db = b.start();
    }

    byte[] key111() {
        byte[] k = new byte[Db.MAX_KEY_BYTES];
        rnd.nextBytes(k);
        k[0] = (byte) (0x10 + rnd.nextInt(0xe0));
        return k;
    }

    long exec(LinkedHashMap<Common.K, byte[]> ops) {
        Trans.Builder tb = db.trans();
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
            if (e.getValue() == Common.DELETED) tb.delete(e.getKey().b);
            else tb.put(e.getKey().b, e.getValue());
        }
        Trans t = tb.build();
        db.execute(t);
        m.apply(ops, t.tt);
        taken++;
        return t.tt;
    }

    /** A transaction that execute() must refuse with a DbException, changing nothing. */
    void refusedAtExecute(LinkedHashMap<Common.K, byte[]> ops, String what) {
        long len = db.getStreamLength(), txs = db.getTransactionCount();
        Trans.Builder tb = db.trans();
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) tb.put(e.getKey().b, e.getValue());
        Trans t = tb.build();
        try {
            db.execute(t);
            throw new Common.Fail(what + " was taken (Db, \"Limits\": execute() refuses one over them with a DbException)");
        } catch (DbException e) {
            if (e instanceof bergdb.pub.util.DbFailedException) throw new Common.Fail(what + ": the database failed: " + e);
        }
        Common.check(db.getStreamLength() == len, what + ": the refusal changed the stream's length " + len + " -> " + db.getStreamLength());
        Common.check(db.getTransactionCount() == txs, what + ": the refusal changed the transaction count");
        for (Common.K k : ops.keySet()) {
            byte[] got = db.getOne(Long.MAX_VALUE, Keys.toSegments(k.b), db.newGetData());
            Common.check(Arrays.equals(got, m.valueAt(k, Long.MAX_VALUE)), what + ": the refusal changed " + k);
            break;
        }
        refused++;
    }

    /** A builder call that must throw IllegalArgumentException. */
    void refusedAtBuilder(byte[] k, byte[] v, String what) {
        long len = db.getStreamLength();
        Trans.Builder tb = db.trans();
        tb.put(new byte[] {0x7f, 1}, new byte[] {1});
        try {
            tb.put(k, v);
            throw new Common.Fail(what + " was taken by Trans.Builder.put()");
        } catch (IllegalArgumentException e) {
        }
        try {
            db.execute(tb.build());
            throw new Common.Fail(what + ": the spoiled builder's transaction was executed");
        } catch (IllegalStateException | IllegalArgumentException | DbException e) {
            if (e instanceof bergdb.pub.util.DbFailedException) throw new Common.Fail(what + ": the database failed: " + e);
        }
        Common.check(db.getStreamLength() == len, what + ": the refusal changed the stream's length");
        refused++;
    }

    void maintain(int b) {
        clock.t.addAndGet(10_000L);
        db.maintain(b);
        maintains++;
    }

    void checks(Collection<Common.K> written, String what) {
        long now = db.currentTime();
        long first = db.getFirstAvailableLookupTime();
        Common.check(first >= lastFirst, what + ": the first available time moved back");
        if (first > lastFirst) cuts++;
        lastFirst = first;
        Common.check(first <= now - SEC, what + ": first available " + first + " after now - R " + (now - SEC));
        GetData gd = db.newGetData();
        for (Common.K k : written) {
            byte[] got = db.getOne(Long.MAX_VALUE, Keys.toSegments(k.b), gd);
            Common.check(Arrays.equals(got, m.valueAt(k, Long.MAX_VALUE)), what + ": get " + k + " gave " + Common.hex(got) + ", expected "
                    + Common.hex(m.valueAt(k, Long.MAX_VALUE)));
        }
        Common.verifyGets(db, m, Long.MAX_VALUE, rnd, 100, what);
    }

    void fullChecks(String what) {
        long first = db.getFirstAvailableLookupTime();
        Common.verifyFull(db, m, Long.MAX_VALUE, what + " full");
        // an older time inside the retain duration: a transaction's time and the unit before it
        Long t = m.times.ceilingKey(Math.max(first, db.currentTime() - SEC));
        if (t != null) {
            Common.verifyFull(db, m, t, what + " at an older time");
            if (t - 1 >= first) Common.verifyGets(db, m, t - 1, rnd, 100, what + " just before it");
        }
        Common.verifyRange(db, m, Long.MAX_VALUE, rnd, what);
        scans++;
        m.prune(first);
    }

    void run(int rounds) throws Exception {
        Common.log("E2LimitsReclaim seed " + seed + ", node " + nodeSize + ", sd " + sd + ", rounds " + rounds);
        Common.rmrf(dir);
        dir.mkdirs();
        start();
        db.setStartupDistance(sd);
        db.setRetainDuration(SEC);
        // the base
        int nBase = 3000 + rnd.nextInt(9000);
        for (int done = 0; done < nBase; ) {
            LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
            for (int j = 0; j < 450 && done < nBase; j++, done++) {
                Common.K k = new Common.K(key111());
                base.add(k);
                ops.put(k, Common.value(rnd, rnd.nextInt(10) == 0 ? 2000 : 40));
            }
            clock.t.addAndGet(rnd.nextInt(2_000_000));
            exec(ops);
        }
        for (int i = 0; i < 2 + rnd.nextInt(3); i++) {
            LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
            Common.K k = new Common.K(new byte[] {0x08, (byte) i});
            ops.put(k, fill(Db.MAX_VALUE_BYTES));
            clock.t.addAndGet(2_000_000);
            exec(ops);
        }
        for (int i = 0; i < 8; i++) bigKeys.add(key111());
        fullChecks("base");
        for (int round = 0; round < rounds; round++) {
            clock.t.addAndGet(500_000 + rnd.nextInt(5_500_000));
            List<Common.K> written = new ArrayList<>();
            int kind = rnd.nextInt(14);
            LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
            switch (kind) {
                case 0: case 1: {   // 500 new keys of 111 bytes
                    for (int j = 0; j < Db.MAX_OPERATIONS; j++) ops.put(new Common.K(key111()), Common.value(rnd, 30));
                    exec(ops);
                    break;
                }
                case 2: case 3: {   // 500 overwrites and deletes of base keys
                    while (ops.size() < Db.MAX_OPERATIONS) {
                        Common.K k = base.get(rnd.nextInt(base.size()));
                        ops.put(k, rnd.nextInt(5) == 0 ? Common.DELETED : Common.value(rnd, 60));
                    }
                    exec(ops);
                    break;
                }
                case 4: {           // a value of exactly 8 MiB at a long key
                    ops.put(new Common.K(bigKeys.get(rnd.nextInt(8))), fill(Db.MAX_VALUE_BYTES));
                    exec(ops);
                    bigBytes += Db.MAX_VALUE_BYTES;
                    break;
                }
                case 5: {           // exactly 32 MiB of keys and values
                    ops = exactly(Db.MAX_TRANS_BYTES);
                    exec(ops);
                    bigBytes += Db.MAX_TRANS_BYTES;
                    break;
                }
                case 6: {           // 32 MiB + 1: refused
                    refusedAtExecute(exactly(Db.MAX_TRANS_BYTES + 1), "keys and values of 32 MiB + 1");
                    break;
                }
                case 7: {           // 501 KVs: refused
                    for (int j = 0; j <= Db.MAX_OPERATIONS; j++) ops.put(new Common.K(key111()), Common.value(rnd, 10));
                    refusedAtExecute(ops, "501 KVs");
                    ops.clear();
                    break;
                }
                case 8: {           // builder refusals
                    if (rnd.nextBoolean()) refusedAtBuilder(new byte[Db.MAX_KEY_BYTES + 1], new byte[1], "a key of 112 bytes");
                    else refusedAtBuilder(key111(), new byte[Db.MAX_VALUE_BYTES + 1], "a value of 8 MiB + 1");
                    break;
                }
                case 9: {           // the smallest commits
                    int x = rnd.nextInt(3);
                    if (x == 0) ops.put(new Common.K(new byte[] {0x09, (byte) rnd.nextInt(4)}), new byte[] {(byte) round});
                    else if (x == 1) ops.put(new Common.K(new byte[] {0x09, (byte) rnd.nextInt(4)}), new byte[0]);
                    else ops.put(new Common.K(new byte[] {0x0a, (byte) rnd.nextInt(250)}), Common.DELETED);
                    exec(ops);
                    break;
                }
                case 10: case 11: { // maintain calls
                    int n = 1 + rnd.nextInt(6);
                    for (int j = 0; j < n; j++) maintain(new int[] {100, 1000, 20_000, 100_000}[rnd.nextInt(4)]);
                    break;
                }
                default: {          // a mix: some 111-byte keys and a large value
                    int n = 1 + rnd.nextInt(Db.MAX_OPERATIONS - 1);
                    for (int j = 0; j < n - 1; j++) ops.put(new Common.K(key111()), Common.value(rnd, 200));
                    ops.put(new Common.K(bigKeys.get(rnd.nextInt(8))), fill(1 + rnd.nextInt(Db.MAX_VALUE_BYTES)));
                    exec(ops);
                }
            }
            written.addAll(ops.keySet());
            if (written.size() > 200) written = written.subList(0, 200);
            checks(written, "round " + round + " (kind " + kind + ")");
            if (round % 10 == 9) fullChecks("round " + round);
            if (rnd.nextInt(25) == 0) {
                if (rnd.nextBoolean()) db.close(); else { db.stop(); db.close(); }
                start();
                restarts++;
                Common.check(db.getFirstAvailableLookupTime() == lastFirst, "the restart changed the first available time");
                fullChecks("restart after round " + round);
            }
            if (round % 50 == 49) Common.log("  round " + round + ": stream kept " + (db.getStreamLength() - db.getFirstAvailablePos())
                    + ", disk " + Common.dirBytes(dir) + ", cuts " + cuts);
        }
        fullChecks("end");
        db.close();
        start();
        fullChecks("end, restarted");
        db.close();
        Common.log("OK E2LimitsReclaim seed " + seed + " node " + nodeSize + ": " + taken + " transactions taken (" + bigBytes / 1_000_000
                + " MB in transactions of 8 to 32 MiB), " + refused + " refused, " + maintains + " maintain calls, " + cuts + " cuts, "
                + restarts + " restarts, " + scans + " full checks");
        Common.rmrf(dir);
    }

    byte[] fill(int n) {
        byte[] v = new byte[n];
        rnd.nextBytes(v);
        return v;
    }

    /** Four KVs whose keys and values are exactly 'total' bytes (Db, "Limits", L5). */
    LinkedHashMap<Common.K, byte[]> exactly(long total) {
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        long left = total;
        List<byte[]> ks = new ArrayList<>(bigKeys);
        Collections.shuffle(ks, rnd);
        for (int j = 0; j < 4; j++) {
            byte[] k = ks.get(j);
            int v = (int) (j < 3 ? (total / 4 - k.length) : left - k.length);
            if (v > Db.MAX_VALUE_BYTES) {   // the last value over 8 MiB: move a byte to the key's side is not possible, so add a fifth KV
                v = Db.MAX_VALUE_BYTES;
            }
            ops.put(new Common.K(k), fill(v));
            left -= k.length + v;
        }
        if (left > 0) {
            byte[] k = new byte[] {0x0b, (byte) rnd.nextInt(256)};
            ops.put(new Common.K(k), fill((int) (left - k.length)));
        }
        long sum = 0;
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) sum += e.getKey().b.length + e.getValue().length;
        Common.check(sum == total, "exactly(" + total + "): " + sum);
        return ops;
    }

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        File dir = new File(a[1]);
        Random r = new Random(seed);
        int ns = a.length > 2 ? Integer.parseInt(a[2]) : new int[] {8, 14, 30, 62}[r.nextInt(4)];
        int rounds = a.length > 3 ? Integer.parseInt(a[3]) : 300;
        E2LimitsReclaim app = new E2LimitsReclaim(seed, dir, ns);
        try {
            app.run(rounds);
        } catch (Throwable t) {
            System.out.println("FAIL E2LimitsReclaim seed " + seed + " node " + ns + ": " + t);
            t.printStackTrace(System.out);
            try { if (app.db != null) app.db.close(); } catch (Throwable x) { }
            System.exit(1);
        }
    }
}
