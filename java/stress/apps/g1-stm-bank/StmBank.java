import bergdb.pub.*;
import bergdb.pub.util.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

/**
 * StmBank (031-02, e1). Accounts as objects with an index on the balance, hot counters,
 * transfers whose amount depends on what they read, transfers over many accounts, slow
 * transfers that sleep inside their action, blind puts, and noise writers that put hundreds
 * of thousands of fresh keys so that the record of recent writes wraps. Every committed rw()
 * records what it read, through its outputs, with its time. The oracle replays all
 * transactions in time order: each must have read exactly the state that the replay has
 * just before it (serializability in commit order), the final state and the states at
 * sampled older times must equal the replay's, and the index scans must list the replay's
 * balances in order. Readers that freeze their lookup time record what they saw, checked
 * against the replay at their frozen time.
 *
 * Usage: java StmBank DIR|mem SEED SECONDS THREADS ACCOUNTS
 */
public class StmBank {
    public static class Acc {
        public long bal;
        public long n;
        public Acc() {}
    }

    static void fail(String msg) {
        System.out.println("STMBANK FAILED: " + msg);
        System.out.flush();
        System.exit(1);
    }

    // A committed transaction: its time and what it read and wrote.
    static final class Rec {
        long time;
        char type;          // T transfer, M multi, H hot, B blind, N noise
        int[] ids;          // accounts read (T: from,to; M: all; B: one)
        long[] read;        // balances read, aligned with ids (H: one value)
        int hot;
        long blindValue;
        int from, to;       // M: the max and min accounts
        long amount;        // T, M: amount moved, computed from the reads
        String noiseKey; int noiseCount; int noiseThread; long noiseBatch;
    }

    static final class Snap {
        long time; long hash; long sum;
    }

    static final ConcurrentLinkedQueue<Rec> recs = new ConcurrentLinkedQueue<>();
    static final ConcurrentLinkedQueue<Snap> snaps = new ConcurrentLinkedQueue<>();
    static volatile boolean stop = false;
    static final AtomicLong nExpired = new AtomicLong();
    static final AtomicLong nT = new AtomicLong(), nM = new AtomicLong(), nH = new AtomicLong(),
            nB = new AtomicLong(), nN = new AtomicLong(), nS = new AtomicLong(), nR = new AtomicLong();
    static int ACCOUNTS;
    static final int HOT = 4;
    static final int NOISE_SLEEP = Integer.getInteger("noiseSleep", 8);
    // Noise keys wrap at this many, so that the noise overwrites (0: never).
    static final int NOISE_SPACE = Integer.getInteger("noiseSpace", 0);
    // A finite retain duration in seconds (0: forever), with a startup distance of 5 MB.
    static final int RETAIN = Integer.getInteger("retain", 0);

    static String acc(int i) { return String.format("/acc/a%05d", i); }

    public static void main(String[] args) throws Exception {
        String dir = args[0];
        long seed = Long.parseLong(args[1]);
        int seconds = Integer.parseInt(args[2]);
        int threads = Integer.parseInt(args[3]);
        ACCOUNTS = Integer.parseInt(args[4]);
        System.out.println("StmBank seed " + seed + " seconds " + seconds + " threads " + threads
                + " accounts " + ACCOUNTS + " db " + dir);
        DatabaseBuilder b = dir.equals("mem") ? Factory.database().memory()
                : Factory.database().create(dir);
        final Database db0 = b.start();
        Database db = db0;
        Connection c = db.connection();
        if (RETAIN > 0) {
            db.setStartupDistanceInMb(5);
            db.setRetainDuration(Duration.seconds(RETAIN));
        }
        // Initial state, in transactions of 100 accounts.
        long[] init = new long[ACCOUNTS];
        Random r0 = new Random(seed);
        for (int i = 0; i < ACCOUNTS; i += 100) {
            WBuilder w = c.w();
            for (int j = i; j < Math.min(ACCOUNTS, i + 100); j++) {
                Acc a = new Acc(); a.bal = 1000 + r0.nextInt(100000); init[j] = a.bal;
                w.put(acc(j), a);
            }
            w.execute();
        }
        for (int h = 0; h < HOT; h++) c.put("/hot/h" + h + ".txt", "0");
        // The index is built over the data, while the threads start writing.
        Job job = db.indexBuilder("by-bal").dir("/acc/").type("long").field("bal").start();
        Time tInit = c.currentTime();

        ExecutorService ex = Executors.newFixedThreadPool(threads + 3);
        List<Future<?>> fs = new ArrayList<>();
        for (int t = 0; t < threads; t++) {
            final int tid = t;
            final long ts = seed * 1000 + t;
            fs.add(ex.submit(() -> { worker(db0, tid, ts); return null; }));
        }
        fs.add(ex.submit(() -> { noise(db0, 100, seed + 77); return null; }));
        fs.add(ex.submit(() -> { reader(db0, seed + 99); return null; }));
        if (RETAIN > 0) fs.add(ex.submit(() -> { maintainer(db0); return null; }));
        long end = System.currentTimeMillis() + seconds * 1000L;
        long lastPrint = System.currentTimeMillis();
        while (System.currentTimeMillis() < end) {
            Thread.sleep(200);
            for (Future<?> f : fs) if (f.isDone()) { stop = true; f.get(); }
            if (System.currentTimeMillis() - lastPrint > 30000) {
                lastPrint = System.currentTimeMillis();
                System.out.println("  T " + nT + " M " + nM + " H " + nH + " B " + nB + " S " + nS
                        + " noise keys " + nN + " reader snaps " + nR);
            }
        }
        stop = true;
        for (Future<?> f : fs) f.get(10, TimeUnit.MINUTES);
        ex.shutdown();
        JobStatus js = job.join();
        System.out.println("index build: " + js.state());
        System.out.println("actions whose read time was cut while they ran: " + nExpired + "; maintain() calls " + nMaintain);
        System.out.println("committed: T " + nT + " M " + nM + " H " + nH + " B " + nB + " S " + nS
                + " noise keys " + nN + " reader snaps " + nR);

        // ---- Replay in time order ----
        List<Rec> all = new ArrayList<>(recs);
        all.sort(Comparator.comparingLong(x -> x.time));
        for (int i = 1; i < all.size(); i++) {
            if (all.get(i).time == all.get(i - 1).time) fail("two transactions with time " + all.get(i).time);
        }
        long[] bal = init.clone();
        long[] hot = new long[HOT];
        List<Rec> noiseBatches = new ArrayList<>();
        List<Snap> snapList = new ArrayList<>(snaps);
        snapList.sort(Comparator.comparingLong(x -> x.time));
        int si = 0;
        Random rs = new Random(seed + 5);
        // Sampled times: the state just after these records.
        TreeMap<Long, long[]> samples = new TreeMap<>();
        int sampleEvery = Math.max(1, all.size() / 150);
        for (int i = 0; i < all.size(); i++) {
            Rec x = all.get(i);
            while (si < snapList.size() && snapList.get(si).time < x.time) {
                checkSnap(snapList.get(si), bal); si++;
            }
            switch (x.type) {
            case 'T': case 'S': {
                if (bal[x.ids[0]] != x.read[0] || bal[x.ids[1]] != x.read[1]) {
                    fail("transfer at " + x.time + " read " + x.read[0] + "," + x.read[1]
                            + " but the state before it has " + bal[x.ids[0]] + "," + bal[x.ids[1]]
                            + " (accounts " + x.ids[0] + "," + x.ids[1] + ")");
                }
                long amt = x.read[0] / 3;
                if (amt != x.amount) fail("amount");
                bal[x.ids[0]] -= amt; bal[x.ids[1]] += amt;
                break;
            }
            case 'M': {
                for (int k = 0; k < x.ids.length; k++) {
                    if (bal[x.ids[k]] != x.read[k]) {
                        fail("multi-read transfer at " + x.time + " of " + x.ids.length
                                + " accounts read " + x.read[k] + " at account " + x.ids[k]
                                + " but the state before it has " + bal[x.ids[k]]);
                    }
                }
                bal[x.from] -= x.amount; bal[x.to] += x.amount;
                break;
            }
            case 'H':
                if (hot[x.hot] != x.read[0]) fail("hot counter " + x.hot + " at " + x.time + " read "
                        + x.read[0] + ", the state before has " + hot[x.hot]);
                hot[x.hot]++;
                break;
            case 'B':
                bal[x.ids[0]] = x.blindValue;
                break;
            case 'N':
                noiseBatches.add(x);
                break;
            }
            if (i % sampleEvery == 0) samples.put(x.time, bal.clone());
        }
        while (si < snapList.size()) { checkSnap(snapList.get(si), bal); si++; }
        System.out.println("replay: every read of " + all.size() + " transactions matches the "
                + "state before it; " + snapList.size() + " reader snapshots match");

        // ---- The final state ----
        c.setLookupTime(Time.MAX);
        checkState(c, bal, "final");
        for (int h = 0; h < HOT; h++) {
            String v = c.get("/hot/h" + h + ".txt", String.class);
            if (Long.parseLong(v) != hot[h]) fail("hot " + h + " is " + v + ", replay " + hot[h]);
        }
        int nk = 0;
        Map<String, Long> lastBatch = new HashMap<>();
        if (NOISE_SPACE > 0) {
            for (Rec x : noiseBatches) for (int k = 0; k < x.noiseCount; k++) lastBatch.put(noiseKey(x.noiseThread, x.noiseBatch, k), x.noiseBatch);
            for (Map.Entry<String, Long> e : lastBatch.entrySet()) {
                String v = c.get(e.getKey(), String.class);
                if (v == null || Long.parseLong(v) != e.getValue()) fail("noise key " + e.getKey() + " is " + v + ", expected " + e.getValue());
                nk++;
            }
        } else for (Rec x : noiseBatches) {
            for (int k : new int[] {0, x.noiseCount - 1, rs.nextInt(x.noiseCount), rs.nextInt(x.noiseCount)}) {
                String key = noiseKey(x.noiseThread, x.noiseBatch, k);
                String v = c.get(key, String.class);
                if (v == null || Long.parseLong(v) != x.noiseBatch) fail("noise key " + key + " is " + v);
                nk++;
            }
            if (c.exists("/noise/t" + x.noiseThread + "/k" + (x.noiseBatch * 1000 + x.noiseCount) + ".txt")) {
                fail("noise key past its batch exists");
            }
        }
        System.out.println("final state equals the replay; " + nk + " noise keys checked");
        // ---- Older times ----
        Connection old = db.newConnection();
        int ns = 0;
        int nCut = 0;
        for (Map.Entry<Long, long[]> e : samples.entrySet()) {
            if (e.getKey() < db.getFirstAvailableLookupTime().units()) { nCut++; continue; }
            old.setLookupTime(Time.units(e.getKey()));
            try {
                checkState(old, e.getValue(), "at " + e.getKey());
                ns++;
            } catch (LookupTimeNotAvailableException lex) {
                nCut++;
            }
        }
        if (RETAIN == 0) {
            old.setLookupTime(tInit);
            checkState(old, init, "initial");
        }
        if (nCut > 0) System.out.println(nCut + " sampled times no longer available (reclaim)");
        System.out.println(ns + " older states equal the replay (accounts, index forward and backward)");
        if (!dir.equals("mem")) {
            db.close();
            db = Factory.database().open(dir).start();
            checkState(db.connection(), bal, "after restart");
            Connection o2 = db.newConnection();
            int k = 0;
            for (Map.Entry<Long, long[]> e : samples.entrySet()) {
                if (k++ % 5 != 0 || e.getKey() < db.getFirstAvailableLookupTime().units()) continue;
                o2.setLookupTime(Time.units(e.getKey()));
                checkState(o2, e.getValue(), "after restart at " + e.getKey());
            }
            System.out.println("after a restart: final and older states equal the replay");
        }
        db.close();
        System.out.println("STMBANK OK");
    }

    static long hash(long[] bal) {
        long h = 17;
        for (long v : bal) h = h * 1000003 + v;
        return h;
    }

    static void checkSnap(Snap s, long[] bal) {
        long sum = 0;
        for (long v : bal) sum += v;
        if (s.hash != hash(bal)) fail("reader snapshot at " + s.time + " (sum " + s.sum + ") differs from "
                + "the replay's state (sum " + sum + ")");
    }

    static void checkState(Connection c, long[] bal, String what) {
        long[] seen = new long[bal.length];
        Arrays.fill(seen, Long.MIN_VALUE);
        int n = 0;
        for (Kv<Acc> kv : c.usePrimary(Acc.class).dir("/acc/").kvs()) {
            int i = Integer.parseInt(kv.key().substring(6));
            seen[i] = kv.value().bal;
            n++;
        }
        if (n != bal.length) fail(what + ": " + n + " accounts listed, expected " + bal.length);
        for (int i = 0; i < bal.length; i++) {
            if (seen[i] != bal[i]) fail(what + ": account " + i + " is " + seen[i] + ", replay " + bal[i]);
        }
        // Index order: (bal, key).
        Integer[] order = new Integer[bal.length];
        for (int i = 0; i < order.length; i++) order[i] = i;
        Arrays.sort(order, (a, b2) -> bal[a] != bal[b2] ? Long.compare(bal[a], bal[b2]) : Integer.compare(a, b2));
        try {
            int k = 0;
            for (Kv<Acc> kv : c.useIndex("by-bal", Acc.class).kvs()) {
                if (k >= order.length) fail(what + ": index lists more than " + order.length);
                if (!kv.key().equals(acc(order[k])) || kv.value().bal != bal[order[k]]) {
                    fail(what + ": index entry " + k + " is " + kv.key() + "=" + kv.value().bal
                            + ", expected " + acc(order[k]) + "=" + bal[order[k]]);
                }
                k++;
            }
            if (k != order.length) fail(what + ": index lists " + k + ", expected " + order.length);
            k = order.length - 1;
            for (Kv<Acc> kv : c.useIndex("by-bal", Acc.class).backward().kvs()) {
                if (!kv.key().equals(acc(order[k]))) fail(what + ": backward index entry differs at " + k);
                k--;
            }
            if (k != -1) fail(what + ": backward index count");
            // A range: from the median balance up, exclusive.
            long mid = bal[order[order.length / 2]];
            int first = 0;
            while (first < order.length && bal[order[first]] <= mid) first++;
            k = first;
            for (Kv<Acc> kv : c.useIndex("by-bal", Acc.class).from(mid, false).kvs()) {
                if (k >= order.length || !kv.key().equals(acc(order[k]))) fail(what + ": range scan differs at " + k);
                k++;
            }
            if (k != order.length) fail(what + ": range scan count");
        } catch (NoSuchIndexException e) {
            // Before the build's end the index is not active: no scan.
        }
    }

    static void worker(Database db, int tid, long seed) throws Exception {
        Connection c = db.connection();
        Random r = new Random(seed);
        while (!stop) {
            int op = r.nextInt(100);
            if (op < 45) transfer(c, r, false);
            else if (op < 55) transfer(c, r, true);
            else if (op < 70) multi(c, r);
            else if (op < 92) hot(c, r);
            else blind(c, r);
        }
    }

    static void transfer(Connection c, Random r, boolean slow) throws Exception {
        int from = r.nextInt(ACCOUNTS), to = r.nextInt(ACCOUNTS - 1);
        if (to >= from) to++;
        final int f = from, t = to;
        final long sleep = slow ? 5 + r.nextInt(120) : 0;
        final boolean verySlow = slow && r.nextInt(40) == 0;
        Transaction tr = null;
        while (tr == null) try { tr = c.rw(env -> {
            Acc a = env.get(acc(f), Acc.class);
            long sl = verySlow ? 500 + ThreadLocalRandom.current().nextInt(14000) : sleep;
            if (sl > 0) { try { Thread.sleep(sl); } catch (InterruptedException ie) { throw new RuntimeException(ie); } }
            Acc bb = env.get(acc(t), Acc.class);
            long amt = a.bal / 3;
            env.setOutput("ra", a.bal);
            env.setOutput("rb", bb.bal);
            a.bal -= amt; a.n++;
            bb.bal += amt; bb.n++;
            env.put(acc(f), a);
            env.put(acc(t), bb);
            env.setOutput("amt", amt);
        }); } catch (LookupTimeNotAvailableException e) {
            // The action ran longer than the retain duration: its read time was cut, and
            // rw() throws what the action's read threw (RwEnvironment.get()). Again.
            nExpired.incrementAndGet();
        }
        Rec x = new Rec();
        x.time = tr.getTime().units();
        x.type = slow ? 'S' : 'T';
        x.ids = new int[] {f, t};
        x.read = new long[] {tr.getOutput("ra", Long.class), tr.getOutput("rb", Long.class)};
        x.amount = tr.getOutput("amt", Long.class);
        recs.add(x);
        (slow ? nS : nT).incrementAndGet();
    }

    static void multi(Connection c, Random r) {
        int k = 20 + r.nextInt(280);
        LinkedHashSet<Integer> set = new LinkedHashSet<>();
        while (set.size() < k) set.add(r.nextInt(ACCOUNTS));
        int[] ids = set.stream().mapToInt(Integer::intValue).toArray();
        Transaction tr = c.rw(env -> {
            long[] read = new long[ids.length];
            int mx = 0, mn = 0;
            for (int i = 0; i < ids.length; i++) {
                read[i] = env.get(acc(ids[i]), Acc.class).bal;
                if (read[i] > read[mx]) mx = i;
                if (read[i] < read[mn]) mn = i;
            }
            long amt = (read[mx] - read[mn]) / 4;
            if (mx != mn && amt > 0) {
                Acc a = env.get(acc(ids[mx]), Acc.class);
                Acc bb = env.get(acc(ids[mn]), Acc.class);
                a.bal -= amt; bb.bal += amt;
                env.put(acc(ids[mx]), a);
                env.put(acc(ids[mn]), bb);
            } else {
                amt = 0;
            }
            env.setOutput("read", read);
            env.setOutput("mx", ids[mx]);
            env.setOutput("mn", ids[mn]);
            env.setOutput("amt", amt);
        });
        Rec x = new Rec();
        x.time = tr.getTime().units();
        x.type = 'M';
        x.ids = ids;
        x.read = tr.getOutput("read", long[].class);
        x.from = tr.getOutput("mx", Integer.class);
        x.to = tr.getOutput("mn", Integer.class);
        x.amount = tr.getOutput("amt", Long.class);
        recs.add(x);
        nM.incrementAndGet();
    }

    static void hot(Connection c, Random r) {
        int h = r.nextInt(HOT);
        Transaction tr = c.rw(env -> {
            long v = Long.parseLong(env.get("/hot/h" + h + ".txt", String.class));
            env.put("/hot/h" + h + ".txt", Long.toString(v + 1));
            env.setOutput("v", v);
        });
        Rec x = new Rec();
        x.time = tr.getTime().units();
        x.type = 'H';
        x.hot = h;
        x.read = new long[] {tr.getOutput("v", Long.class)};
        recs.add(x);
        nH.incrementAndGet();
    }

    static void blind(Connection c, Random r) {
        int i = r.nextInt(ACCOUNTS);
        Acc a = new Acc();
        a.bal = r.nextInt(200000);
        Transaction tr = c.put(acc(i), a);
        Rec x = new Rec();
        x.time = tr.getTime().units();
        x.type = 'B';
        x.ids = new int[] {i};
        x.blindValue = a.bal;
        recs.add(x);
        nB.incrementAndGet();
    }

    // Noise: fresh keys in batches of 300 to 450, each value its batch's number, to push
    // the record of recent writes past its reach while the transfers run.
    static void noise(Database db, int tid, long seed) {
        Connection c = db.connection();
        Random r = new Random(seed);
        long batch = 0;
        while (!stop) {
            int n = 300 + r.nextInt(150);
            WBuilder w = c.w();
            for (int k = 0; k < n; k++) w.put(noiseKey(tid, batch, k), Long.toString(batch));
            Transaction tr = w.execute();
            Rec x = new Rec();
            x.time = tr.getTime().units();
            x.type = 'N';
            x.noiseThread = tid;
            x.noiseBatch = batch;
            x.noiseCount = n;
            recs.add(x);
            nN.addAndGet(n);
            batch++;
            try { Thread.sleep(NOISE_SLEEP + r.nextInt(8)); } catch (InterruptedException e) { return; }
        }
    }

    // maintain() called again and again beside the commits.
    static final AtomicLong nMaintain = new AtomicLong();
    static void maintainer(Database db) throws Exception {
        while (!stop) {
            // One bounded part a call, as maintain() did before 031-06: the smallest budget.
            db.maintain(100);
            nMaintain.incrementAndGet();
            Thread.sleep(2);
        }
    }

    static String noiseKey(int tid, long batch, int k) {
        long i = batch * 1000 + k;
        if (NOISE_SPACE > 0) i %= NOISE_SPACE;
        return "/noise/t" + tid + "/k" + i + ".txt";
    }

    static void reader(Database db, long seed) throws Exception {
        Connection c = db.newConnection();
        Random r = new Random(seed);
        while (!stop) {
            c.freezeLookupTime();
            long[] bal = new long[ACCOUNTS];
            int n = 0;
            for (Kv<Acc> kv : c.usePrimary(Acc.class).dir("/acc/").kvs()) {
                bal[Integer.parseInt(kv.key().substring(6))] = kv.value().bal;
                n++;
            }
            if (n != ACCOUNTS) fail("reader listed " + n + " accounts");
            Snap s = new Snap();
            s.time = c.getLookupTime().units();
            s.hash = hash(bal);
            for (long v : bal) s.sum += v;
            snaps.add(s);
            nR.incrementAndGet();
            Thread.sleep(r.nextInt(300));
        }
    }
}
