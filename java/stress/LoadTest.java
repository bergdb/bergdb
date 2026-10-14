package bergdb.core;

import java.io.File;
import java.util.*;

import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.stream.FileStream;

/**
 * Level 2 under load, written 2026-10-13: write and read speed, commit
 * latency, the length of the startup section, the dirty set D, the bytes
 * appended per user byte, and the startup time, on a FileStream on disk.
 * See docs/levels.md, level 2, and problem.md, R3, R4 and R6.
 *
 * Phases:
 *   1. Load: n keys in random order, `batch` keys per transaction.
 *   2. Update: `updates` transactions of `tsize` puts each, keys chosen
 *      uniformly, or with hot=P, P percent of the puts on 1% of the keys.
 *      The versions of all keys are saved at the middle of the phase, for
 *      historical lookups.
 *   3. Restart: sync, stop, and start from the stream; startup time.
 *   4. Reads: random gets, the first ones after the restart (cold) and
 *      then warm; latest and at the middle of phase 2. Every value read is
 *      checked.
 *
 * In package bergdb.core to reach Db internals.
 *
 * Usage: java -Xmx24g [-Dprop=value ...] -cp bergdb.jar:. bergdb.core.LoadTest
 *
 * Properties:
 *   n=N        Number of keys (default 1000000). Keys are 4-byte binary ints.
 *   valsize=N  Value size in bytes, at least 8 (default 100).
 *   batch=N    Keys per transaction in phase 1 (default 100).
 *   updates=N  Transactions in phase 2 (default 1000000).
 *   tsize=N    Puts per transaction in phase 2 (default 1).
 *   hot=P      P percent of the puts in phase 2 on 1% of the keys (default 0).
 *   sd=N       Startup distance in bytes (default 0: Db default, 50 MB;
 *              -1: 2e9, so that startup replays the whole stream, level 1).
 *   maxnode=N  Max node size: 8, 14, 30 or 62 (default: Db default).
 *   sync=1     Sync (ORDINARY) after every transaction in phase 2.
 *   dir=D      Directory for the stream (default build/load); emptied first.
 *   gets=N     Gets per read measurement (default 1000000).
 *   retain=S   Reclaim on (level 3), retain duration S seconds; transactions are then
 *              10 us apart (0.1 us otherwise), and the historical reads are 20,000
 *              transactions before the end. Reports the stream kept after the cut.
 *   tstep=N    Time units (0.1 us) between transactions, instead of the default above.
 *   cutcheck=1 After every transaction that moves the cut (reclaim): restart, and
 *              check every key at the latest time (reads the stream after the cut).
 *   mem=1      The stream is a CutStream in memory, which refuses reads below the cut,
 *              instead of a FileStream on disk (which cuts whole files only).
 *   sample=N   Sample D and the startup section every N transactions
 *              (default 10000).
 */
public class LoadTest {
    final int n = Integer.getInteger("n", 1000000);
    final int valsize = Math.max(8, Integer.getInteger("valsize", 100));
    final int batch = Integer.getInteger("batch", 100);
    final int updates = Integer.getInteger("updates", 1000000);
    final int tsize = Integer.getInteger("tsize", 1);
    final int hot = Integer.getInteger("hot", 0);
    final int sdProp = Integer.getInteger("sd", 0);
    final int maxNode = Integer.getInteger("maxnode", 0);
    final boolean syncEach = "1".equals(System.getProperty("sync"));
    final File dir = new File(System.getProperty("dir", "build/load"));
    final int gets = Integer.getInteger("gets", 1000000);
    final int sample = Integer.getInteger("sample", 10000);
    final int retain = Integer.getInteger("retain", 0);
    final int tstep = Integer.getInteger("tstep", retain > 0 ? 100 : 1);
    final boolean mem = "1".equals(System.getProperty("mem"));
    final boolean cutCheck = "1".equals(System.getProperty("cutcheck"));
    int cutChecks;
    bergdb.stream.CutStream cutStream;

    final Random rnd = new Random(1);
    final CoreTestClock clock = new CoreTestClock();
    long time = 1000;

    final int[] version;      // current version of each key
    int[] midVersion;         // versions at the middle of phase 2
    long midTime;

    Db db;
    bergdb.stream.AppendOnlyStream fileStream;
    final Stats stats = new Stats();
    long keptMax;

    LoadTest() {
        version = new int[n];
    }

    /** Per-transaction measurements, taken in the transaction listener. */
    class Stats implements Trans.Listener {
        long trans, kvBytes, indexNodes, maxIndexNodes;
        long maxSection, sumSection;
        long firstPos = -1, lastPos;

        public void transExecuted(Db.ExecuteData x) {
            TransNodes tn = x.transNodes;
            int index = tn.topCount + tn.keyCount;
            trans++;
            kvBytes += tn.kvSize;
            indexNodes += index;
            if (index > maxIndexNodes) maxIndexNodes = index;
            if (firstPos < 0) firstPos = x.trans.tpos;
            lastPos = x.trans.lastPos;
            long section = x.trans.lastPos - x.trans.startupPos;
            sumSection += section;
            if (section > maxSection) maxSection = section;
            lastIndex = index;
        }

        public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}

        int lastIndex;

        void reset() {
            trans = kvBytes = indexNodes = maxIndexNodes = maxSection = sumSection = 0;
            firstPos = -1;
        }
    }

    Db start(boolean create) throws Exception {
        if (create) {
            dir.mkdirs();
            for (File f : dir.listFiles()) f.delete();
        }
        if (mem) {
            cutStream = cutStream == null ? new bergdb.stream.CutStream() : cutStream.copy();
            fileStream = cutStream;
        } else {
            fileStream = new FileStream(dir);
        }
        DbBuilder b = Db.builder().stream("main", fileStream)
                .clock(clock).noEvict().retainForever().testId();
        if (sdProp > 0) b.startupDistance(sdProp);
        if (sdProp < 0) b.startupDistance(2000 * 1000 * 1000);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        if (retain > 0) b.retainDuration(retain * bergdb.pub.util.Clock.UNITS_PER_SEC);
        return b.build();
    }

    byte[] key(int i) {
        return KeyFactory.binaryIntKey(i);
    }

    byte[] value(int k, int v) {
        byte[] b = new byte[valsize];
        b[0] = (byte) (k >>> 24); b[1] = (byte) (k >>> 16); b[2] = (byte) (k >>> 8); b[3] = (byte) k;
        b[4] = (byte) (v >>> 24); b[5] = (byte) (v >>> 16); b[6] = (byte) (v >>> 8); b[7] = (byte) v;
        for (int i = 8; i < valsize; i++) b[i] = (byte) (k + v + i);
        return b;
    }

    void check(int k, int v, byte[] got, String what) {
        byte[] want = value(k, v);
        if (!Arrays.equals(want, got)) {
            throw new AssertionError(what + ": wrong value for key " + k + ", version " + v
                    + (got == null ? ", got null" : ""));
        }
    }

    void execute(Trans.Builder b) {
        time += tstep;
        clock.setTime(time);
        Trans t = b.build();
        t.listener = stats;
        db.execute(t);
    }

    int pick() {
        if (hot > 0 && rnd.nextInt(100) < hot) {
            return rnd.nextInt(Math.max(1, n / 100));
        }
        return rnd.nextInt(n);
    }

    void run() throws Exception {
        System.out.println("LoadTest n=" + n + " valsize=" + valsize + " batch=" + batch
                + " updates=" + updates + " tsize=" + tsize + " hot=" + hot
                + " sd=" + sdProp + " maxnode=" + maxNode + " sync=" + syncEach);
        db = start(true);
        db.start();
        int sd = db.getStartupDistance();
        System.out.println("startupDistance " + sd);

        // Phase 1: load.
        int[] perm = new int[n];
        for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        stats.reset();
        long t0 = System.nanoTime();
        for (int i = 0; i < n; i += batch) {
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(n, i + batch); j++) {
                int k = perm[j];
                version[k] = 1;
                b.put(key(k), value(k, 1));
            }
            execute(b);
        }
        db.sync(SyncLevel.ORDINARY);
        double loadSec = 1e-9 * (System.nanoTime() - t0);
        perm = null;
        System.out.printf("LOAD %d keys in %.2f s: %.0f puts/s, stream %.1f MB, "
                + "%.2f bytes appended per user byte, %.2f index nodes per transaction, "
                + "max section %.1f MB%n",
                n, loadSec, n / loadSec, db.getStreamLength() / 1e6,
                (double) (stats.lastPos - stats.firstPos) / stats.kvBytes,
                (double) stats.indexNodes / stats.trans, stats.maxSection / 1e6);
        System.out.printf("HEAP after load %.0f MB%n", heapMB());

        // Phase 2: updates.
        stats.reset();
        long[] lat = new long[updates];
        int maxLatAt = -1;
        int maxLatIndex = 0;
        long dirtyMax = 0, transSeqMax = 0;
        keptMax = 0;
        long sectionSampleMax = 0;
        int[] slowIndex = new int[updates];
        t0 = System.nanoTime();
        for (int i = 0; i < updates; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < tsize; j++) {
                int k = pick();
                version[k]++;
                b.put(key(k), value(k, version[k]));
            }
            long s = System.nanoTime();
            long cutBefore = cutCheck ? db.getFirstAvailablePos() : 0;
            execute(b);
            if (syncEach) db.sync(SyncLevel.ORDINARY);
            if (cutCheck && db.getFirstAvailablePos() != cutBefore) {
                restartAndCheck("after the cut at " + db.getFirstAvailablePos());
            }
            lat[i] = System.nanoTime() - s;
            slowIndex[i] = stats.lastIndex;
            if (maxLatAt < 0 || lat[i] > lat[maxLatAt]) { maxLatAt = i; maxLatIndex = stats.lastIndex; }

            if (i == (retain > 0 ? Math.max(0, updates - 20000) : updates / 2)) {
                midVersion = version.clone();
                midTime = time;
            }
            if ((i + 1) % sample == 0) {
                long[] d = dirtyCount();
                dirtyMax = Math.max(dirtyMax, d[0]);
                transSeqMax = Math.max(transSeqMax, d[1]);
                long len = stats.lastPos;
                long sp = db.internal().getStartupPosForEvict();
                sectionSampleMax = Math.max(sectionSampleMax, len - sp);
                long kept = len - db.getFirstAvailablePos();
                keptMax = Math.max(keptMax, kept);
                if ((i + 1) % (sample * 10) == 0 || i + 1 == updates) {
                    System.out.printf("  update %d: stream %.1f MB, section %.2f MB (%.2f x sd), "
                            + "D %d nodes in %d transactions%s%n",
                            i + 1, len / 1e6, (len - sp) / 1e6, (double) (len - sp) / sd, d[0], d[1],
                            retain == 0 ? "" : String.format(", kept after the cut %.1f MB, "
                                    + "on disk %.1f MB", kept / 1e6,
                                    (len - fileStream.getFirstPos()) / 1e6));
                }
            }
        }
        db.sync(SyncLevel.ORDINARY);
        double updSec = 1e-9 * (System.nanoTime() - t0);
        long appended = stats.lastPos - stats.firstPos;
        System.out.printf("UPDATE %d transactions of %d puts in %.2f s: %.0f transactions/s, "
                + "stream %.1f MB%n", updates, tsize, updSec, updates / updSec,
                db.getStreamLength() / 1e6);
        System.out.printf("  bytes appended per user byte %.2f, index nodes per transaction %.2f "
                + "(max %d)%n", (double) appended / stats.kvBytes,
                (double) stats.indexNodes / stats.trans, stats.maxIndexNodes);
        System.out.printf("  startup section: mean %.2f MB, max %.2f MB (%.2f x sd)%n",
                stats.sumSection / 1e6 / stats.trans, stats.maxSection / 1e6,
                (double) stats.maxSection / sd);
        System.out.printf("  D: max %d nodes, max %d transactions (sampled)%n", dirtyMax, transSeqMax);
        if (cutCheck) {
            System.out.println("  restarts with a full check after a cut: " + cutChecks);
        }
        if (retain > 0) {
            long live = (long) n * (4 + valsize);
            System.out.printf("  reclaim: kept after the cut max %.1f MB, at the end %.1f MB; "
                    + "live data %.1f MB; %d iterations in this run%n", keptMax / 1e6,
                    (db.getStreamLength() - db.getFirstAvailablePos()) / 1e6, live / 1e6,
                    db.getReclaimIterationCount());
        }
        System.out.println("  commit latency (execute" + (syncEach ? " + sync" : "") + "): "
                + latencies(lat));
        System.out.printf("  slowest commit: transaction %d, %.2f ms, %d index nodes written%n",
                maxLatAt, lat[maxLatAt] / 1e6, maxLatIndex);
        System.out.println("  commits that wrote more than 100 index nodes: "
                + countOver(slowIndex, 100) + ", more than 1000: " + countOver(slowIndex, 1000));
        lat = null;
        slowIndex = null;
        System.out.printf("HEAP after updates %.0f MB%n", heapMB());

        long streamLength = db.getStreamLength();
        long sp = db.internal().getStartupPosForEvict();
        System.out.printf("Before stop: stream %.1f MB, startup pos %.1f MB, section %.2f MB%n",
                streamLength / 1e6, sp / 1e6, (streamLength - sp) / 1e6);

        // Phase 3: restart.
        db.sync(SyncLevel.STRONG);
        db.close();
        db = null;
        heapMB();
        db = start(false);
        t0 = System.nanoTime();
        StartInfo info = db.start();
        double startSec = 1e-9 * (System.nanoTime() - t0);
        System.out.printf("STARTUP %.3f s: %d transactions rerun, read from %.1f MB, "
                + "section %.2f MB%n", startSec, info.transCount, info.startPos / 1e6,
                (streamLength - info.startPos) / 1e6);
        System.out.printf("HEAP after startup %.0f MB%n", heapMB());

        // Phase 4: reads.
        reads("cold latest", Long.MAX_VALUE, version);
        reads("warm latest", Long.MAX_VALUE, version);
        reads("historical", midTime, midVersion);
        reads("historical warm", midTime, midVersion);

        // A few more transactions after the restart, then a full check.
        for (int i = 0; i < 1000; i++) {
            int k = pick();
            version[k]++;
            execute(db.trans().put(key(k), value(k, version[k])));
        }
        GetData gd = db.newGetData();
        for (int k = 0; k < n; k++) {
            check(k, version[k], db.getOne(Long.MAX_VALUE, Keys.toSegments(key(k)), gd), "full check");
        }
        System.out.println("Full check of " + n + " keys after restart: ok");
        db.close();
        System.out.println("LOADTEST OK");
    }

    void restartAndCheck(String what) throws Exception {
        db.sync(SyncLevel.STRONG);
        db.close();
        db = start(false);
        db.start();
        GetData gd = db.newGetData();
        for (int k = 0; k < n; k++) {
            check(k, version[k], db.getOne(Long.MAX_VALUE, Keys.toSegments(key(k)), gd), what);
        }
        cutChecks++;
    }

    void reads(String what, long lookupTime, int[] versions) {
        GetData gd = db.newGetData();
        Random r = new Random(2);
        int count = Math.min(gets, 10 * n);
        int[] ks = new int[count];
        long[][] segs = new long[count][];
        for (int i = 0; i < count; i++) {
            ks[i] = r.nextInt(n);
            segs[i] = Keys.toSegments(key(ks[i]));
        }
        long t0 = System.nanoTime();
        byte[][] got = new byte[Math.min(count, 1000)][];
        for (int i = 0; i < count; i++) {
            byte[] v = db.getOne(lookupTime, segs[i], gd);
            if (i < got.length) got[i] = v;
            else if (v == null) throw new AssertionError(what + ": null for key " + ks[i]);
        }
        double sec = 1e-9 * (System.nanoTime() - t0);
        for (int i = 0; i < got.length; i++) check(ks[i], versions[ks[i]], got[i], what);
        System.out.printf("READ %s: %d gets, %.0f ns per get%n", what, count, 1e9 * sec / count);
    }

    /** Returns {number of nodes in D, number of transactions in the TransSeq}. */
    long[] dirtyCount() {
        final long[] c = new long[2];
        synchronized (db.internal().getWriteLock()) {
            TransSeq seq = db.internal().transSeq();
            seq.visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                public void node(Node node, long tpos, long lastTpos) { c[0]++; }
            });
            c[1] = seq.getSize();
        }
        return c;
    }

    static String latencies(long[] lat) {
        long[] s = lat.clone();
        Arrays.sort(s);
        return String.format("p50 %.1f us, p99 %.1f us, p99.9 %.1f us, p99.99 %.1f us, max %.2f ms",
                s[s.length / 2] / 1e3, s[(int) (s.length * 0.99)] / 1e3,
                s[(int) (s.length * 0.999)] / 1e3, s[(int) (s.length * 0.9999)] / 1e3,
                s[s.length - 1] / 1e6);
    }

    static int countOver(int[] a, int limit) {
        int c = 0;
        for (int x : a) if (x > limit) c++;
        return c;
    }

    static double heapMB() {
        Runtime rt = Runtime.getRuntime();
        for (int i = 0; i < 3; i++) {
            System.gc();
            try { Thread.sleep(50); } catch (InterruptedException e) {}
        }
        return (rt.totalMemory() - rt.freeMemory()) / 1e6;
    }

    public static void main(String[] args) throws Exception {
        new LoadTest().run();
    }
}
