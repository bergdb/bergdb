package bergdb.core;

import java.io.*;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Long, count-driven functional test on a real file stream (bergdb 028-43).
 * Run with stress/large.sh. No throughput, latency or wall-clock deadline decides a pass.
 * The clock advances 10,000 units per user transaction, leaving room for reclaim's
 * internal transactions. Values and the entire historical oracle are computed from a
 * seeded permutation and a transaction number, without a map of past values.
 *
 * Each epoch visits every key once, four keys per atomic transaction, in a permutation
 * of key order. Version zero is the initial fill; some subsequent versions are deletes,
 * followed by reinsertion. A marker in the same transaction names the committed prefix.
 * The independent crash journal records PREPARE before execute and SYNC after sync.
 * A recovered marker must be between the last SYNC and PREPARE; a full scan must match
 * that exact prefix, detecting a partial batch, lost synced data or an extra write.
 *
 * The space envelope is 6 L0 + H_R for the logical kept bytes (G3, bergdb 024-30),
 * plus at most 2 GB for whole-file rounding. L0 is the fresh filled stream; H_R is an
 * upper bound on retained user records: ALL stream growth over the last R plus one
 * user transactions. A second check caps H_R at 2 L0, so the absolute envelope is
 * 8 L0 + 2 GB. It is measured with a bounded ring, not estimated from throughput.
 * This is a workload acceptance envelope, not a proof of BergDB's general space bound.
 *
 * L0 depends on the seed's key order: at 10 million keys a fill in a random order writes
 * about 6 GB, while an order that puts neighbouring keys within a few dozen transactions
 * of each other writes about 2 GB (bergdb 028-63). So the data cap scales with the fill:
 * 8 L0 + 3 GB, one GB above the absolute envelope, so that the envelope's checks fail
 * first; after the fill the free disk must hold the rest of it. A fill of more than 1,000
 * bytes a key fails: at 10 million keys the orders measured wrote 211 to 724 bytes a key.
 */
public final class LargeReclaimRun {
    static final long DT = 10_000;
    static final long GB = 1_000_000_000L;
    /** The most bytes a key that the fresh fill may write (bergdb 028-63). */
    static final long FILL_BYTES_PER_KEY = 1_000;
    static final int BATCH = 4, VALUE_BYTES = 64, BLOCK = 16_384;
    static final byte[] MARKER = "/large-run/prefix".getBytes(StandardCharsets.US_ASCII);
    static final long[] MARKER_KEY = Keys.toSegments(MARKER);
    static final long KEY_TAG = 0x4000000000000000L;
    static final AtomicLong GETS = new AtomicLong(), SCANS = new AtomicLong();
    static final AtomicLong OLD = new AtomicLong(), EXPIRED = new AtomicLong();
    static final long START_NS = System.nanoTime();

    final Path out, data;
    final long seed;
    final int n, epochs, perEpoch, retainTx, minCuts;
    final long multiplier, inverse, offset, baseTime;
    final long cacheBudget;
    final long[] lengths;
    final Random random;
    CoreTestClock clock;
    FileStream stream;
    Db db;
    Reclaim.Stats stats;
    long seq, fresh, cuts, lastPhysical, maxLogical, maxPhysical, maxOldBytes, ringStart;
    long epochMaxLogical, epochMaxPhysical, observedAppended, originalLength;
    int cleanRestarts;
    int straddledScans;

    static void require(boolean ok, String message) {
        if (!ok) throw new AssertionError(message);
    }

    static void log(String message) {
        System.out.printf(Locale.ROOT, "[%.3fs] %s%n", (System.nanoTime() - START_NS) / 1e9, message);
        System.out.flush();
    }

    LargeReclaimRun(Path out, long seed, int n, int epochs) {
        require(n >= 100 && n % 100 == 0 && epochs >= 12, "n must be a multiple of 100; epochs >= 12");
        this.out = out;
        this.data = out.resolve("data");
        this.seed = seed;
        this.n = n;
        this.epochs = epochs;
        perEpoch = n / BATCH;
        cacheBudget = 300L * n;
        retainTx = Math.max(1_000, perEpoch / 10);
        minCuts = Math.max(6, epochs / 2);
        lengths = new long[retainTx + 2];
        long a = 1_000_003 + Math.floorMod(seed, 100_000);
        while (!BigInteger.valueOf(a).gcd(BigInteger.valueOf(n)).equals(BigInteger.ONE)) a++;
        multiplier = a;
        inverse = BigInteger.valueOf(a).modInverse(BigInteger.valueOf(n)).longValueExact();
        offset = Math.floorMod(seed, n);
        // Load: n/100 transactions; marker and settings: three reserved clock ticks.
        baseTime = 100_000_000L + (n / 100L + 3) * DT;
        random = new Random(seed);
    }

    int keyAt(long slot) { return (int) ((multiplier * (slot % n) + offset) % n); }
    int slotOf(int key) { return (int) (Math.floorMod(key - offset, n) * inverse % n); }

    int version(int key, long prefix) {
        long updates = prefix * BATCH;
        return (int) (updates / n + (slotOf(key) < updates % n ? 1 : 0));
    }

    boolean deleted(int key, int version) {
        return version > 0 && Math.floorMod(key * 31L + version, 17) == 0;
    }

    static byte[] keyBytes(int key) { return ByteBuffer.allocate(8).putLong(KEY_TAG + key).array(); }
    static long[] key(int key) { return Keys.toSegments(keyBytes(key)); }

    int keyNumber(long[] segments) {
        byte[] b = Keys.toBytes(segments);
        require(b.length == 8, "unexpected scan key length " + b.length);
        long k = ByteBuffer.wrap(b).getLong() - KEY_TAG;
        require(k >= 0 && k < n, "unexpected scan key " + k);
        return (int) k;
    }

    static long mix(long x) {
        x = (x ^ (x >>> 30)) * 0xbf58476d1ce4e5b9L;
        x = (x ^ (x >>> 27)) * 0x94d049bb133111ebL;
        return x ^ (x >>> 31);
    }

    byte[] value(int key, int version) {
        byte[] v = new byte[VALUE_BYTES];
        ByteBuffer b = ByteBuffer.wrap(v);
        b.putInt(key).putInt(version);
        for (int i = 8; i < v.length; i += 8) b.putLong(mix(seed ^ ((long) key << 32) ^ version ^ i));
        return v;
    }

    byte[] marker(long prefix) {
        return ByteBuffer.allocate(16).putLong(prefix).putLong(mix(prefix ^ seed)).array();
    }

    long time(long prefix) { return baseTime + prefix * DT; }
    long prefixAt(long time) { return Math.max(0, (time - baseTime) / DT); }

    long checkedPrefix(long requested, long actual) {
        // Every explicit request is at or before a published, completed transaction.
        // A history read must use that time; accepting a silently substituted latest
        // snapshot would make a value check against the database's own output vacuous.
        if (requested != Long.MAX_VALUE && actual != requested)
            throw new AssertionError("snapshot time: requested=" + requested + " actual=" + actual);
        return prefixAt(actual);
    }

    void checkValue(int key, long prefix, byte[] actual, String where) {
        int version = version(key, prefix);
        byte[] expected = deleted(key, version) ? null : value(key, version);
        if (!Arrays.equals(expected, actual)) throw new AssertionError(where + ": key=" + key
                + " prefix=" + prefix + " version=" + version + " expected=" + Arrays.toString(expected)
                + " actual=" + Arrays.toString(actual));
    }

    void open(long prefix, boolean create) throws Exception {
        long t = System.nanoTime();
        clock = new CoreTestClock();
        clock.setTime(create ? 100_000_000L : time(prefix) + DT / 2);
        stream = new FileStream(data.toFile());
        stream.setMax2G(true); // Explicit whole-file slack in the physical envelope.
        db = builder().start();
        stats = db.internal().reclaim().enableStats();
        stats.countTouch = false;
        if (!create) {
            require(db.getRetainDuration() == retainTx * DT, "retention changed across restart");
            long recovered = readMarker();
            require(recovered == prefix, "restart prefix=" + recovered + ", expected=" + prefix);
        }
        log("OPEN create=" + create + " prefix=" + prefix + " seconds=" + (System.nanoTime() - t) / 1e9
                + " length=" + db.getStreamLength() + " physicalFirst=" + stream.getFirstPos());
    }

    DbBuilder builder() {
        return Db.builder().mainStream(stream).clock(clock).testId().cacheSizeIndicator(cacheBudget)
                .evictionSchedule(Eviction.Schedule.BUDGET, seed);
    }

    long readMarker() {
        byte[] v = db.getOne(Long.MAX_VALUE, MARKER_KEY, db.newGetData());
        require(v != null && v.length == 16, "missing or malformed prefix marker");
        long p = ByteBuffer.wrap(v).getLong();
        require(Arrays.equals(v, marker(p)), "prefix marker checksum");
        return p;
    }

    void checkMarkerAt(long lookupTime, long prefix) {
        byte[] actual = db.getOne(lookupTime, MARKER_KEY, db.newGetData());
        if (!Arrays.equals(actual, marker(prefix))) throw new AssertionError("historical prefix marker: time="
                + lookupTime + " expected=" + prefix + " actual=" + Arrays.toString(actual));
    }

    void fill() throws Exception {
        Files.createDirectory(data);
        open(0, true);
        for (int start = 0; start < n; start += 100) {
            clock.setTime(100_000_000L + (start / 100L + 1) * DT);
            Trans.Builder b = db.trans();
            for (int j = 0; j < 100; j++) {
                int k = keyAt(start + j);
                b.put(key(k), value(k, 0));
            }
            db.execute(b.build());
            if ((start + 100) % 1_000_000 == 0) log("LOAD keys=" + (start + 100)
                    + " length=" + db.getStreamLength());
        }
        clock.setTime(baseTime - DT);
        db.execute(db.trans().put(MARKER_KEY, marker(0)).build());
        clock.setTime(baseTime);
        db.setRetainDuration(retainTx * DT);
        db.sync(SyncLevel.ORDINARY);
        fresh = db.getStreamLength();
        require(fresh <= FILL_BYTES_PER_KEY * n, "fresh fill wrote " + fresh + " bytes, more than "
                + FILL_BYTES_PER_KEY + " a key");
        long need = diskCap() - fresh + 2 * GB, usable = Files.getFileStore(data).getUsableSpace();
        require(usable >= need, "free disk " + usable + " is below the " + need
                + " bytes that this fill's data cap 8 L0 + 3 GB and a 2 GB reserve need");
        originalLength = fresh;
        Arrays.fill(lengths, fresh);
        lastPhysical = stream.getFirstPos();
        Files.writeString(out.resolve("fresh.txt"), Long.toString(fresh) + "\n");
        log("FILL keys=" + n + " fresh=" + fresh + " retentionTransactions=" + retainTx
                + " retentionUnits=" + retainTx * DT + " oracleBytes=" + lengths.length * 8L
                + " dataCap=" + diskCap());
        fullScan("filled", 0);
        diskCheck();
    }

    void write(long next) {
        clock.setTime(time(next));
        Trans.Builder b = db.trans();
        for (int j = 0; j < BATCH; j++) {
            long slot = (next - 1) * BATCH + j;
            int k = keyAt(slot), ver = (int) (slot / n) + 1;
            if (deleted(k, ver)) b.delete(key(k));
            else b.put(key(k), value(k, ver));
        }
        b.put(MARKER_KEY, marker(next));
        Trans t = b.build();
        db.execute(t);
        require(t.tt == time(next), "clock schedule changed: " + t.tt + " != " + time(next));
        seq = next;
    }

    /** Checked after EVERY user transaction, not just progress samples. */
    void observe() {
        long length = db.getStreamLength(), first = db.getFirstAvailablePos();
        lengths[(int) (seq % lengths.length)] = length;
        long oldSeq = Math.max(0, seq - retainTx - 1L);
        long h = length - lengths[(int) (oldSeq % lengths.length)];
        long logical = length - first, physical = length - stream.getFirstPos();
        maxLogical = Math.max(maxLogical, logical);
        maxPhysical = Math.max(maxPhysical, physical);
        epochMaxLogical = Math.max(epochMaxLogical, logical);
        epochMaxPhysical = Math.max(epochMaxPhysical, physical);
        if (first > 0) {
            maxOldBytes = Math.max(maxOldBytes, logical - h);
            if (seq - ringStart > retainTx && h > 2 * fresh)
                throw new AssertionError("retained growth exceeded 2 L0 at prefix=" + seq + ": " + h);
            if (logical > 6 * fresh + h) throw new AssertionError("space envelope: prefix=" + seq
                    + " logical=" + logical + " H_R=" + h + " 6L0=" + 6 * fresh);
            if (physical > 6 * fresh + h + 2 * GB) throw new AssertionError("physical space envelope at " + seq);
            if (logical > 8 * fresh || physical > 8 * fresh + 2 * GB)
                throw new AssertionError("fixed space envelope exceeded at prefix=" + seq);
        }
        if (physical >= diskCap() - 16_000_000)
            throw new AssertionError("data near the cap 8 L0 + 3 GB at prefix=" + seq);
        long p = stream.getFirstPos();
        require(p >= lastPhysical, "physical first position moved backwards");
        if (p > lastPhysical) {
            cuts++;
            log("CUT number=" + cuts + " prefix=" + seq + " length=" + length
                    + " physicalFirst=" + p + " logicalKept=" + logical + " physicalKept=" + physical);
            lastPhysical = p;
        }
        if (db.getFirstAvailableLookupTime() > Math.max(0, time(seq) - retainTx * DT))
            throw new AssertionError("retention frontier entered retained interval at " + seq);
    }

    void get(long requested, int k, boolean mayExpire) {
        GetData gd = db.newGetData();
        try {
            byte[] actual = db.getOne(requested, key(k), gd);
            checkValue(k, checkedPrefix(requested, gd.actualLookupTime), actual, "get time=" + gd.actualLookupTime);
            GETS.incrementAndGet();
            if (requested != Long.MAX_VALUE) OLD.incrementAndGet();
        } catch (LookupTimeNotAvailableException e) {
            long actual = requested == Long.MAX_VALUE ? gd.actualLookupTime : requested;
            require(mayExpire && actual < db.getFirstAvailableLookupTime(),
                    "unexpected expiry of time " + actual);
            EXPIRED.incrementAndGet();
        }
    }

    /** Also detects omitted or extra scan rows, in either direction. */
    void scan(long requested, int start, boolean forward, int count, boolean mayExpire) {
        scan(requested, start, forward, count, mayExpire, null, null);
    }

    void scan(long requested, int start, boolean forward, int count, boolean mayExpire,
            CountDownLatch entered, CountDownLatch release) {
        GetMany g = db.newGetMany();
        g.lookupTime = requested;
        g.startKey = key(start);
        g.forward = forward;
        if (forward) g.endKey = key(n - 1);
        g.stopCondition = new GetMany.StopCondition() {
            int rows;
            public int handleKvt(Kvt kv) {
                if (!forward && Keys.compareKeys(kv.key, key(0)) < 0) return STOP;
                if (rows == 0 && entered != null) {
                    checkValue(keyNumber(kv.key), checkedPrefix(requested, g.actualLookupTime),
                            kv.value, "held scan first row");
                    entered.countDown();
                    try { require(release.await(30, TimeUnit.MINUTES), "held scan release hang guard"); }
                    catch (InterruptedException e) { Thread.currentThread().interrupt(); throw new RuntimeException(e); }
                }
                return ++rows == count ? ADD_AND_STOP : ADD;
            }
            public void eod() { }
        };
        try {
            db.getMany(g);
            long p = checkedPrefix(requested, g.actualLookupTime);
            int expectedKey = start, direction = forward ? 1 : -1;
            for (Kvt kv : g.result) {
                while (expectedKey >= 0 && expectedKey < n && deleted(expectedKey, version(expectedKey, p)))
                    expectedKey += direction;
                int k = keyNumber(kv.key);
                require(k == expectedKey, "scan gap/order: time=" + g.actualLookupTime
                        + " expected=" + expectedKey + " actual=" + k);
                checkValue(k, p, kv.value, "scan");
                expectedKey += direction;
            }
            while (expectedKey >= 0 && expectedKey < n && deleted(expectedKey, version(expectedKey, p)))
                expectedKey += direction;
            require(g.result.size() == count || expectedKey < 0 || expectedKey >= n,
                    "scan ended before expected key " + expectedKey);
            SCANS.incrementAndGet();
        } catch (LookupTimeNotAvailableException e) {
            long actual = requested == Long.MAX_VALUE ? g.actualLookupTime : requested;
            require(mayExpire && actual < db.getFirstAvailableLookupTime(), "unexpected scan expiry");
            EXPIRED.incrementAndGet();
        }
    }

    void fullScan(String phase, long prefix) {
        long t = System.nanoTime();
        GetMany g = db.newGetMany();
        g.startKey = key(0);
        g.endKey = key(n - 1);
        final int[] expected = {0}, live = {0};
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kv) {
                while (expected[0] < n && deleted(expected[0], version(expected[0], prefix))) expected[0]++;
                int k = keyNumber(kv.key);
                require(k == expected[0], phase + ": full scan missing/extra key, expected=" + expected[0]
                        + " actual=" + k + " prefix=" + prefix);
                checkValue(k, prefix, kv.value, phase);
                expected[0]++;
                live[0]++;
                return CONTINUE; // Stream the check; do not retain ten million result rows.
            }
            public void eod() { }
        };
        db.getMany(g);
        while (expected[0] < n && deleted(expected[0], version(expected[0], prefix))) expected[0]++;
        require(expected[0] == n, phase + ": full scan ended at " + expected[0]);
        require(readMarker() == prefix, phase + ": wrong marker");
        log("FULL_SCAN phase=" + phase + " keys=" + n + " live=" + live[0] + " prefix=" + prefix
                + " seconds=" + (System.nanoTime() - t) / 1e9);
    }

    void checkpoint() throws Exception {
        db.sync(SyncLevel.ORDINARY);
        long now = time(seq), first = db.getFirstAvailableLookupTime();
        for (int i = 0; i < 32; i++) {
            int k = i < BATCH ? keyAt((seq - 1) * BATCH + i) : random.nextInt(n);
            get(Long.MAX_VALUE, k, false);
            get(now - retainTx * DT, k, false);
            get(now - retainTx * DT / 2, k, false);
            if (first > baseTime) get(first, k, false);
        }
        scan(now - retainTx * DT, random.nextInt(n), true, 64, false);
        scan(now - retainTx * DT / 2, random.nextInt(n), false, 64, false);
        if (first > 0) {
            boolean refused = false;
            try { db.getOne(first - 1, key(0), db.newGetData()); }
            catch (LookupTimeNotAvailableException expected) { refused = true; }
            require(refused, "get admitted first available time minus one");
            GetMany g = db.newGetMany();
            g.lookupTime = first - 1;
            g.stopCondition = new GetMany.GetN(1);
            refused = false;
            try { db.getMany(g); }
            catch (LookupTimeNotAvailableException expected) { refused = true; }
            require(refused, "scan admitted first available time minus one");
            get(Long.MAX_VALUE, 0, false); // Refusal must not fail the database.
        }
        diskCheck();
    }

    /** The data cap, 8 L0 + 3 GB: above the absolute envelope 8 L0 + 2 GB (bergdb 028-63). */
    long diskCap() { return 8 * fresh + 3 * GB; }

    void diskCheck() throws IOException {
        long bytes = 0;
        try (DirectoryStream<Path> files = Files.newDirectoryStream(data)) {
            for (Path f : files) if (Files.isRegularFile(f)) bytes += Files.size(f);
        }
        require(bytes < diskCap(), "actual data files exceeded the cap 8 L0 + 3 GB: " + bytes);
        require(Files.getFileStore(data).getUsableSpace() >= 2 * GB, "less than 2 GB free disk");
    }

    void restart() throws Exception {
        checkpoint();
        long fa = db.getFirstAvailableLookupTime(), fp = db.getFirstAvailablePos();
        db.close();
        db = null;
        open(seq, false);
        require(db.getFirstAvailableLookupTime() >= fa && db.getFirstAvailablePos() >= fp,
                "reclaim frontier moved backwards across restart");
        fullScan("clean-restart", seq);
        checkpoint();
        cleanRestarts++;
        log("CLEAN_RESTART_OK prefix=" + seq);
    }

    void history() throws Exception {
        ExecutorService readers = Executors.newFixedThreadPool(2);
        try {
            for (int epoch = 1; epoch <= epochs; epoch++) {
                long end = (long) epoch * perEpoch;
                epochMaxLogical = epochMaxPhysical = 0;
                CountDownLatch entered = new CountDownLatch(1), release = new CountDownLatch(1);
                Future<?> held = null;
                long heldFirst = stream.getFirstPos(), heldTime = time(Math.max(0, seq - retainTx / 2));
                if (epoch == 2 || epoch == epochs / 3 + 2 || epoch == 2 * epochs / 3 + 2) {
                    held = readers.submit(() -> scan(heldTime, 0, true, 256, true, entered, release));
                    require(entered.await(5, TimeUnit.MINUTES), "held scan admission hang guard");
                }
                while (seq < end) {
                    final long from = seq;
                    final long blockEnd = Math.min(end, seq + BLOCK);
                    Future<?> reading = readers.submit(() -> {
                        Random r = new Random(seed ^ from);
                        for (int i = 0; i < 512; i++) {
                            long old = Math.max(0, from - r.nextInt(retainTx + 1));
                            // Half the probes target keys whose versions changed in the retained window.
                            int k = (i & 1) == 0 ? keyAt(Math.max(0, old - 1) * BATCH + i % BATCH)
                                    : r.nextInt(n);
                            get((i & 3) == 0 ? Long.MAX_VALUE : time(old), k, true);
                            if (i % 64 == 0) scan(time(old), k, (i & 64) == 0, 32, true);
                        }
                    });
                    while (seq < blockEnd) {
                        write(seq + 1);
                        observe();
                    }
                    // A generous hang guard, not a read-rate requirement.
                    reading.get(30, TimeUnit.MINUTES);
                }
                if (held != null) {
                    db.sync(SyncLevel.ORDINARY);
                    long after = stream.getFirstPos();
                    release.countDown();
                    held.get(30, TimeUnit.MINUTES);
                    require(after > heldFirst, "no physical cut while historical scan held open");
                    require(db.getFirstAvailableLookupTime() > heldTime, "held snapshot was not overtaken by a cut");
                    straddledScans++;
                    log("SCAN_STRADDLED_CUT time=" + heldTime + " physicalBefore=" + heldFirst
                            + " physicalAfter=" + after + " firstTimeAfter=" + db.getFirstAvailableLookupTime());
                }
                checkpoint();
                log("EPOCH number=" + epoch + " prefix=" + seq + " length=" + db.getStreamLength()
                        + " logicalKept=" + (db.getStreamLength() - db.getFirstAvailablePos())
                        + " physicalKept=" + (db.getStreamLength() - stream.getFirstPos())
                        + " epochMaxLogical=" + epochMaxLogical + " epochMaxPhysical=" + epochMaxPhysical
                        + " cuts=" + cuts + " firstTime=" + db.getFirstAvailableLookupTime()
                        + " resident=" + db.internal().cache().residents().bytes()
                        + " heapUsed=" + (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()));
                if (epoch == epochs / 3 || epoch == 2 * epochs / 3) restart();
            }
        } finally {
            readers.shutdownNow();
            readers.awaitTermination(1, TimeUnit.MINUTES);
        }
        observedAppended = db.getStreamLength() - originalLength;
        require(cuts >= minCuts, "only " + cuts + " physical cuts, expected at least " + minCuts);
        require(observedAppended >= 12 * fresh, "history too short to test a stationary space envelope");
        fullScan("history-end", seq);
        log("STEADY_OK appended=" + observedAppended + " fresh=" + fresh
                + " maxOldBytes=" + maxOldBytes + " oldBound=" + 6 * fresh
                + " maxLogical=" + maxLogical + " maxPhysical=" + maxPhysical + " cuts=" + cuts);
    }

    /** SIGKILL child: journal is separate from BergDB and never read to construct expected values. */
    void crash() throws Exception {
        checkpoint();
        db.close();
        db = null;
        long start = seq;
        List<String> command = new ArrayList<>();
        command.add(Path.of(System.getProperty("java.home"), "bin", "java").toString());
        command.add("-Xms256m");
        command.add("-Xmx" + System.getProperty("large.childheap", "10g"));
        command.add("-XX:+UseG1GC");
        command.add("-cp");
        command.add(System.getProperty("java.class.path"));
        command.add(LargeReclaimRun.class.getName());
        Collections.addAll(command, "child", out.toString(), Long.toString(seed), Integer.toString(n),
                Integer.toString(epochs), Long.toString(start));
        Process child = new ProcessBuilder(command).redirectErrorStream(true)
                .redirectOutput(out.resolve("child.txt").toFile()).start();
        try {
            long guard = System.nanoTime() + TimeUnit.MINUTES.toNanos(30);
            Path ready = out.resolve("child-ready");
            while (!Files.exists(ready)) {
                require(child.isAlive(), "child exited before kill; see child.txt");
                require(System.nanoTime() < guard, "child ready hang guard; see child.txt");
                Thread.sleep(100);
            }
            // Randomizes the physical append boundary. The readiness condition is a count of
            // writes and completed syncs; this delay is not a throughput condition.
            Thread.sleep(25 + random.nextInt(175));
            require(child.isAlive(), "child exited before SIGKILL");
            child.destroyForcibly();
            require(child.waitFor(5, TimeUnit.MINUTES), "killed child did not exit");
            require(child.exitValue() != 0, "child was not abruptly stopped");
            long offered = start, synced = start;
            List<Long> syncs = new ArrayList<>();
            syncs.add(start); // The parent synced this state before handing the database over.
            String journal = Files.readString(out.resolve("journal.txt"));
            // A kill can interrupt the last journal write, before execute (P), or before
            // acknowledging a completed sync (S). Only newline-terminated records count.
            for (String line : journal.substring(0, journal.lastIndexOf('\n') + 1).split("\n")) {
                String[] fields = line.split(" ");
                require(fields.length == 2, "bad journal line: " + line);
                long p = Long.parseLong(fields[1]);
                if (fields[0].equals("P")) {
                    require(p == offered + 1, "journal prepare order");
                    offered = p;
                } else {
                    require(fields[0].equals("S") && p <= offered && p >= synced, "journal sync order");
                    synced = p;
                    syncs.add(p);
                }
            }
            // The recovered marker is unknown: open first, then bound it by the journal.
            clock = new CoreTestClock();
            clock.setTime(time(offered) + DT / 2);
            stream = new FileStream(data.toFile());
            stream.setMax2G(true);
            long t = System.nanoTime();
            db = builder().start();
            seq = readMarker();
            require(seq >= synced && seq <= offered, "recovery prefix=" + seq
                    + " outside synced=" + synced + " offered=" + offered);
            require(db.getRetainDuration() == retainTx * DT, "crash lost retention setting");
            log("CRASH_RECOVERY start=" + start + " synced=" + synced + " offered=" + offered
                    + " recovered=" + seq + " exit=" + child.exitValue()
                    + " openSeconds=" + (System.nanoTime() - t) / 1e9);
            fullScan("crash-recovery", seq);
            long available = db.getFirstAvailableLookupTime(), checked = 0, checkedSyncs = 0;
            // Check EACH retained transaction at its own snapshot, not only its effect on
            // the recovered latest state. Also look just before its atomic four-key batch.
            for (long p = start; p <= seq; p++) {
                if (time(p) < available) continue;
                checkMarkerAt(time(p), p);
                for (int j = 0; j < BATCH; j++) {
                    int k = keyAt((p - 1) * BATCH + j);
                    get(time(p), k, false);
                    if (time(p) - 1 >= available) get(time(p) - 1, k, false);
                }
                checked++;
            }
            for (long p : syncs) {
                if (time(p) < available) continue; // Legitimately reclaimed, as the frontier says.
                checkMarkerAt(time(p), p);
                checkedSyncs++;
            }
            log("CRASH_HISTORY_OK transactions=" + checked + " syncedSnapshots=" + checkedSyncs
                    + " syncRecords=" + syncs.size() + " firstTime=" + available);
            checkpoint();
            // Continue writing after recovery. The logical time is above even an offered,
            // incomplete record, while the oracle still uses the fixed user-time grid.
            // Reopen with the recovered prefix's clock, rather than the upper offered bound.
            db.close();
            db = null;
            open(seq, false);
            Arrays.fill(lengths, stream.getFirstPos()); // Conservative H_R until the ring fills.
            lengths[(int) (seq % lengths.length)] = db.getStreamLength();
            ringStart = seq;
            lastPhysical = stream.getFirstPos();
            for (int i = 0; i < BLOCK; i++) { write(seq + 1); observe(); }
            checkpoint();
            fullScan("final", seq);
            log("CRASH_RESTART_OK resumedTransactions=" + BLOCK);
        } finally {
            if (child.isAlive()) { child.destroyForcibly(); child.waitFor(5, TimeUnit.MINUTES); }
        }
    }

    void child(long start) throws Exception {
        seq = start;
        fresh = Long.parseLong(Files.readString(out.resolve("fresh.txt")).trim());
        open(start, false);
        Arrays.fill(lengths, stream.getFirstPos()); // Conservative H_R during the short child run.
        lengths[(int) (seq % lengths.length)] = db.getStreamLength();
        ringStart = start;
        lastPhysical = stream.getFirstPos();
        long readyAfter = Math.max(4_096, Math.min(65_536, perEpoch / 4));
        try (FileOutputStream journal = new FileOutputStream(out.resolve("journal.txt").toFile())) {
            for (long next = start + 1; ; next++) {
                journal.write(("P " + next + "\n").getBytes(StandardCharsets.US_ASCII));
                write(next);
                observe();
                if ((next - start) % 1_024 == 0) {
                    db.sync(SyncLevel.ORDINARY);
                    journal.write(("S " + next + "\n").getBytes(StandardCharsets.US_ASCII));
                    journal.getChannel().force(true);
                    diskCheck();
                    log("CHILD_SYNC prefix=" + next + " physicalKept="
                            + (db.getStreamLength() - stream.getFirstPos()) + " maxPhysical=" + maxPhysical);
                    if (next - start >= readyAfter && !Files.exists(out.resolve("child-ready"))) {
                        Files.writeString(out.resolve("child-ready"), "writing after synced prefix " + next + "\n");
                        log("CHILD_WRITING prefix=" + next);
                    }
                }
            }
        }
    }

    /** Independent small array model, plus planted wrong values and missing values. */
    void oracleSelfCheck() {
        int small = Math.min(n, 200);
        int[] versions = new int[n];
        for (int p = 1; p <= 2 * perEpoch; p++) {
            for (int j = 0; j < BATCH; j++) versions[keyAt((p - 1L) * BATCH + j)]++;
            if (p % Math.max(1, perEpoch / small) == 0) {
                for (int k = 0; k < n; k += Math.max(1, n / small))
                    require(versions[k] == version(k, p), "oracle self-check at " + p + " key=" + k);
            }
        }
        byte[] wrong = value(0, 0);
        wrong[wrong.length - 1] ^= 1;
        int detected = 0;
        try { checkValue(0, 0, wrong, "planted wrong byte"); } catch (AssertionError expected) { detected++; }
        try { checkValue(0, 0, null, "planted missing value"); } catch (AssertionError expected) { detected++; }
        try { checkedPrefix(time(1), time(2)); } catch (AssertionError expected) { detected++; }
        require(detected == 3, "oracle accepted planted faults");
        log("ORACLE_SELF_CHECK_OK plantedFaults=" + detected);
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 5) throw new IllegalArgumentException("run|child|verify OUT SEED KEYS EPOCHS [PREFIX]");
        LargeReclaimRun run = new LargeReclaimRun(Path.of(args[1]), Long.parseLong(args[2]),
                Integer.parseInt(args[3]), Integer.parseInt(args[4]));
        log("CONFIG kind=functional seed=" + run.seed + " keys=" + run.n + " epochs=" + run.epochs
                + " batch=" + BATCH + " valueBytes=" + VALUE_BYTES + " minCuts=" + run.minCuts
                + " multiplier=" + run.multiplier + " offset=" + run.offset + " cacheBudget=" + run.cacheBudget);
        Thread guard = new Thread(() -> {
            try { Thread.sleep(TimeUnit.HOURS.toMillis(12)); }
            catch (InterruptedException ignored) { return; }
            log("LARGE RECLAIM FAILED: 12-hour hang guard, seed=" + run.seed);
            ProcessHandle.current().children().forEach(ProcessHandle::destroyForcibly);
            Runtime.getRuntime().halt(1);
        }, "large-run-hang-guard");
        guard.setDaemon(true);
        guard.start();
        try {
            if (args[0].equals("child")) { run.child(Long.parseLong(args[5])); return; }
            if (args[0].equals("verify")) {
                run.seq = Long.parseLong(args[5]);
                run.fresh = Long.parseLong(Files.readString(run.out.resolve("fresh.txt")).trim());
                run.open(run.seq, false);
                run.fullScan("existing-recovery", run.seq);
                run.checkpoint();
                log("EXISTING RECOVERY OK prefix=" + run.seq);
                return;
            }
            require(args[0].equals("run"), "unknown mode " + args[0]);
            run.oracleSelfCheck();
            run.fill();
            run.history();
            run.crash();
            log("LARGE RECLAIM OK seed=" + run.seed + " keys=" + run.n + " epochs=" + run.epochs
                    + " transactions=" + run.seq + " cuts=" + run.cuts + " cleanRestarts=" + run.cleanRestarts
                    + " abruptRestarts=1 scansAcrossCuts=" + run.straddledScans
                    + " gets=" + GETS.get() + " oldGets=" + OLD.get()
                    + " scans=" + SCANS.get() + " validExpiries=" + EXPIRED.get()
                    + " maxLogical=" + run.maxLogical + " maxPhysical=" + run.maxPhysical
                    + " finalLogical=" + (run.db.getStreamLength() - run.db.getFirstAvailablePos())
                    + " finalPhysical=" + (run.db.getStreamLength() - run.stream.getFirstPos()));
        } catch (Throwable failure) {
            log("LARGE RECLAIM FAILED seed=" + run.seed + " prefix=" + run.seq + " " + failure);
            throw failure;
        } finally {
            if (run.db != null) run.db.close();
        }
    }
}
