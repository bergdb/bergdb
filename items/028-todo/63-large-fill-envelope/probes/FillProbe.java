package bergdb.core;

import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.Comparator;
import java.util.stream.Stream;

import bergdb.dag.Keys;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * The fresh fill of LargeReclaimRun (bergdb 028-43) alone, for 028-63: the same keys,
 * values, key order (keyAt), clock, settings and cache budget as LargeReclaimRun.fill(),
 * at the harness source of 2026-11-21 (SHA-256 e1dd086d...). Prints the stream length
 * after every STEP keys and the fresh length; deletes its data at the end.
 *
 * Usage: java -cp PROBE_CLASSES:bergdb.jar bergdb.core.FillProbe OUT SEED KEYS [STEP [MAXKEYS
 *     [HISTORY [ORDER]]]]
 * OUT must not exist. MAXKEYS stops the fill early (the order stays that of KEYS). HISTORY
 * user transactions of LargeReclaimRun.write() follow a complete fill, without its reads,
 * syncs and checks; the length is printed every 250,000. ORDER: affine (keyAt, the
 * default) or shuffle (a permutation of the keys by java.util.Random(seed), for the fill
 * only; the history keeps keyAt).
 */
public final class FillProbe {
    static final long DT = 10_000;
    static final int VALUE_BYTES = 64;
    static final byte[] MARKER = "/large-run/prefix".getBytes(StandardCharsets.US_ASCII);
    static final long[] MARKER_KEY = Keys.toSegments(MARKER);
    static final long KEY_TAG = 0x4000000000000000L;

    final long seed, multiplier, offset, baseTime, cacheBudget;
    final int n, retainTx;

    FillProbe(long seed, int n) {
        this.seed = seed;
        this.n = n;
        cacheBudget = 300L * n;
        retainTx = Math.max(1_000, n / 4 / 10);
        long a = 1_000_003 + Math.floorMod(seed, 100_000);
        while (!BigInteger.valueOf(a).gcd(BigInteger.valueOf(n)).equals(BigInteger.ONE)) a++;
        multiplier = a;
        offset = Math.floorMod(seed, n);
        baseTime = 100_000_000L + (n / 100L + 3) * DT;
    }

    int[] shuffled;

    int keyAt(long slot) { return (int) ((multiplier * (slot % n) + offset) % n); }
    int fillKeyAt(long slot) { return shuffled == null ? keyAt(slot) : shuffled[(int) slot]; }

    boolean deleted(int key, int version) {
        return version > 0 && Math.floorMod(key * 31L + version, 17) == 0;
    }

    long time(long prefix) { return baseTime + prefix * DT; }

    static long[] key(int key) {
        return Keys.toSegments(ByteBuffer.allocate(8).putLong(KEY_TAG + key).array());
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

    public static void main(String[] args) throws Exception {
        Path out = Path.of(args[0]);
        long seed = Long.parseLong(args[1]);
        int n = Integer.parseInt(args[2]);
        int step = args.length > 3 ? Integer.parseInt(args[3]) : 1_000_000;
        int max = args.length > 4 ? Integer.parseInt(args[4]) : n;
        long history = args.length > 5 ? Long.parseLong(args[5]) : 0;
        String order = args.length > 6 ? args[6] : "affine";
        FillProbe p = new FillProbe(seed, n);
        if (order.equals("shuffle")) {
            p.shuffled = new int[n];
            for (int i = 0; i < n; i++) p.shuffled[i] = i;
            java.util.Random r = new java.util.Random(seed);
            for (int i = n - 1; i > 0; i--) {
                int j = r.nextInt(i + 1), t = p.shuffled[i];
                p.shuffled[i] = p.shuffled[j];
                p.shuffled[j] = t;
            }
        } else if (!order.equals("affine")) {
            throw new IllegalArgumentException("ORDER is affine or shuffle");
        }
        System.out.println("CONFIG seed=" + seed + " keys=" + n + " maxKeys=" + max + " order=" + order
                + " multiplier=" + p.multiplier + " offset=" + p.offset + " cacheBudget=" + p.cacheBudget);
        Files.createDirectories(out);
        Path data = out.resolve("data");
        Files.createDirectory(data);
        long t0 = System.nanoTime();
        try {
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(100_000_000L);
            FileStream stream = new FileStream(data.toFile());
            stream.setMax2G(true);
            Db db = Db.builder().mainStream(stream).clock(clock).testId().cacheSizeIndicator(p.cacheBudget)
                    .evictionSchedule(Eviction.Schedule.BUDGET, seed).start();
            try {
                for (int start = 0; start < max; start += 100) {
                    clock.setTime(100_000_000L + (start / 100L + 1) * DT);
                    Trans.Builder b = db.trans();
                    for (int j = 0; j < 100; j++) {
                        int k = p.fillKeyAt(start + j);
                        b.put(key(k), p.value(k, 0));
                    }
                    db.execute(b.build());
                    if ((start + 100) % step == 0) System.out.println("LOAD keys=" + (start + 100)
                            + " length=" + db.getStreamLength());
                }
                if (max == n) {
                    clock.setTime(p.baseTime - DT);
                    db.execute(db.trans().put(MARKER_KEY, p.marker(0)).build());
                    clock.setTime(p.baseTime);
                    db.setRetainDuration(p.retainTx * DT);
                    db.sync(SyncLevel.ORDINARY);
                    long fresh = db.getStreamLength();
                    System.out.println("FILL keys=" + n + " fresh=" + fresh);
                    for (long next = 1; next <= history; next++) {
                        clock.setTime(p.time(next));
                        Trans.Builder b = db.trans();
                        for (int j = 0; j < 4; j++) {
                            long slot = (next - 1) * 4 + j;
                            int k = p.keyAt(slot), ver = (int) (slot / n) + 1;
                            if (p.deleted(k, ver)) b.delete(key(k));
                            else b.put(key(k), p.value(k, ver));
                        }
                        b.put(MARKER_KEY, p.marker(next));
                        db.execute(b.build());
                        if (next % 250_000 == 0) System.out.println("HISTORY transactions=" + next
                                + " appended=" + (db.getStreamLength() - fresh)
                                + " logicalKept=" + (db.getStreamLength() - db.getFirstAvailablePos()));
                    }
                }
            } finally {
                db.close();
            }
        } finally {
            try (Stream<Path> s = Files.walk(out)) {
                s.sorted(Comparator.reverseOrder()).forEach(f -> f.toFile().delete());
            }
        }
        System.out.printf("SECONDS %.1f%n", (System.nanoTime() - t0) / 1e9);
    }
}
