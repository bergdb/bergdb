package bergdb.core;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import bergdb.pub.util.DbException;
import bergdb.storage.RecoverableStream;

/**
 * Probe of 031-07 (2026-11-27), not part of BergDB: CorruptStreamTester's damage, and stale
 * tails as 035-02 made them, each copy started; which check refuses it, by the refusal's
 * message, tallied by the damaged region. Run with -Dprobe.nochecksum=true and the shadow
 * NodeStream first on the class path for the variant without the node checksum.
 */
public class CstChecks {

    static final class Tally {
        final Map<String, Map<String, Integer>> byRegion = new TreeMap<>();
        int copies;

        synchronized void add(String region, String outcome) {
            copies++;
            byRegion.computeIfAbsent(region, k -> new TreeMap<>()).merge(outcome, 1, Integer::sum);
        }

        void print(PrintStream out, String title) {
            out.println("== " + title + ": " + copies + " copies");
            for (Map.Entry<String, Map<String, Integer>> e : byRegion.entrySet()) {
                int sum = 0;
                for (int n : e.getValue().values()) sum += n;
                out.println(e.getKey() + "  (" + sum + ")");
                for (Map.Entry<String, Integer> o : e.getValue().entrySet()) {
                    out.println("    " + o.getValue() + "\t" + o.getKey());
                }
            }
        }
    }

    static String norm(Throwable e) {
        Throwable t = e;
        while (t.getCause() != null && t.getCause() != t) {
            t = t.getCause();
        }
        String m = t.getClass().getSimpleName() + ": " + String.valueOf(t.getMessage());
        m = m.replaceAll("0x[0-9a-fA-F]+", "X").replaceAll("-?\\d+", "N");
        return m.length() > 80 ? m.substring(0, 80) : m;
    }

    static String regionClass(CorruptStreamTester.Original o, int p) {
        String r = CorruptStreamTester.region(o, p);
        if (r.equals("meta block") || r.equals("no record")) return r;
        int colon = r.indexOf(": ");
        String rest = r.substring(colon + 2);
        if (rest.startsWith("node at offset")) {
            // "node at offset X of size Y, its byte b ..."
            String[] w = rest.split("[ ,]+");
            int off = Integer.parseInt(w[3]);
            int b = Integer.parseInt(w[9]);
            CorruptStreamTester.Record rec = o.recordAt(p);
            int type = rec.bytes[off + 4];
            String cls = b < 4 ? "size" : b == 4 ? "type" : b == 5 ? "format"
                    : b < 8 ? "bytes 6-7" : b < 12 ? "checksum" : "body";
            String tn = type == 10 ? "top" : type == 20 ? "key" : type == 30 ? "value"
                    : type == 40 ? "delete" : "?" + type;
            return "node " + tn + ": " + cls;
        }
        return "record: " + rest;
    }

    /** The outcome of one copy, with the refusal's or the read failure's message. */
    static String outcome(CorruptStreamTester.Original o, CorruptStreamTester.Copy c, int realK) {
        byte[] bytes = c.bytes.get();
        CorruptStreamTester.CopyStream stream = new CorruptStreamTester.CopyStream(bytes,
                c.length < 0 ? bytes.length : c.length);
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(CorruptStreamTester.TIME_STEP * (o.n + 5));
        Db db;
        try {
            db = Db.builder().testSetup(stream).clock(clock).audit(0).start();
        } catch (DbException e) {
            if (stream.tooMuch()) return "zero fill > 1 MB (014-01)";
            return "refused" + (stream.appended() > 0 ? " after a fill" : "") + ": " + norm(e);
        } catch (Throwable e) {
            if (stream.tooMuch()) return "zero fill > 1 MB (014-01)";
            return "START THREW: " + norm(e);
        }
        String result;
        try {
            CorruptStreamTester.Outcome out = CorruptStreamTester.read(o, c, db);
            if (out.failure != null) {
                result = "UNDETECTED (wrong values): " + out.failure.replaceAll("\\d+", "N");
                if (result.length() > 90) result = result.substring(0, 90);
            } else if (out.kind.startsWith("read failed")) {
                String why = "?";
                try {
                    DbUtil.get(db, Long.MAX_VALUE, CorruptStreamTester.COUNTER);
                } catch (Throwable t) {
                    why = norm(t);
                }
                result = "read failed: " + why;
            } else if (out.kind.startsWith("known")) {
                result = out.kind.replaceAll("\\d{4,}", "N");
            } else {
                result = out.kind;
                if (realK >= 0) {
                    byte[] v = DbUtil.get(db, Long.MAX_VALUE, CorruptStreamTester.COUNTER);
                    int k = v == null ? 0 : Integer.parseInt(new String(v));
                    result += k > realK ? " MORE THAN THE REAL RECORDS" : " (real records only)";
                }
            }
        } catch (Throwable e) {
            result = "READ THREW: " + norm(e);
        }
        try {
            db.close();
        } catch (Throwable e) {
            // a failed database
        }
        if (stream.tooMuch() && !result.startsWith("refused")) {
            return "zero fill > 1 MB (014-01)";
        }
        return result;
    }

    static void runAll(CorruptStreamTester.Original o, List<CorruptStreamTester.Copy> copies,
            List<String> regions, List<Integer> realKs, Tally tally, int threads) throws Exception {
        ExecutorService pool = Executors.newFixedThreadPool(threads, r -> {
            Thread t = new Thread(r, "CstChecks");
            t.setDaemon(true);
            return t;
        });
        try {
            List<Future<String>> fs = new ArrayList<>();
            for (int i = 0; i < copies.size(); i++) {
                final int j = i;
                fs.add(pool.submit(() -> outcome(o, copies.get(j), realKs.get(j))));
            }
            for (int i = 0; i < copies.size(); i++) {
                String out;
                try {
                    out = fs.get(i).get(60, TimeUnit.SECONDS);
                } catch (Exception e) {
                    out = "TIMEOUT OR " + e;
                }
                tally.add(regions.get(i), out);
                if (out.startsWith("UNDETECTED") || out.contains("MORE THAN") || out.contains("THREW")
                        || out.startsWith("TIMEOUT")) {
                    System.out.println("  case: " + o.config + ", " + copies.get(i).what + ": " + out);
                }
            }
        } finally {
            pool.shutdownNow();
        }
    }

    /** The stream's bytes to Z, then 'stale' from Z to the end. */
    static CorruptStreamTester.Copy staleCopy(CorruptStreamTester.Original o, int z,
            byte[] stale, String what) {
        return new CorruptStreamTester.Copy("stale", what, () -> {
            byte[] b = o.bytes.clone();
            for (int i = z; i < b.length; i++) {
                b[i] = stale[i];
            }
            return b;
        }, -1, -1, null);
    }

    public static void main(String[] args) throws Exception {
        final long seed = Long.parseLong(args[0]);
        final String what = args[1];        // "damage" or "stale"
        final int threads = Integer.parseInt(args[2]);
        final boolean noSum = Boolean.getBoolean("probe.nochecksum");
        PrintStream out = System.out;
        out.println("CstChecks: seed " + seed + ", " + what + ", node checksum "
                + (noSum ? "NOT checked" : "checked") + ", NodeStream.NO_CHECKSUM="
                + NodeStream.NO_CHECKSUM);
        Tally tally = new Tally();
        long t0 = System.nanoTime();
        for (CorruptStreamTester.Config cfg : CorruptStreamTester.FULL_CONFIGS) {
            CorruptStreamTester.Original o = CorruptStreamTester.write(cfg,
                    seed * 31 + cfg.name.hashCode());
            out.println(cfg.name + ": " + o.bytes.length + " bytes, " + o.records.size()
                    + " records");
            List<CorruptStreamTester.Copy> copies = new ArrayList<>();
            List<String> regions = new ArrayList<>();
            List<Integer> realKs = new ArrayList<>();
            if (what.equals("damage")) {
                // Every byte flipped by 0x01 and 0xff where the stream is small; a sample else.
                Random r = new Random(seed);
                List<Integer> positions = new ArrayList<>();
                if (o.bytes.length < 100000) {
                    for (int p = 0; p < o.bytes.length; p++) positions.add(p);
                } else {
                    for (int i = 0; i < 20000; i++) positions.add(r.nextInt(o.bytes.length));
                }
                for (int p : positions) {
                    for (int mask : new int[] {0x01, 0xff}) {
                        final int pp = p, mm = mask;
                        copies.add(new CorruptStreamTester.Copy("flip", "xor " + mask + " at " + p,
                                () -> {
                                    byte[] b = o.bytes.clone();
                                    b[pp] ^= (byte) mm;
                                    return b;
                                }, -1, -1, CorruptStreamTester.flipKnown(
                                        CorruptStreamTester.region(o, p), mask)));
                        regions.add("flip " + regionClass(o, p));
                        realKs.add(-1);
                    }
                }
                List<CorruptStreamTester.Copy> h = new ArrayList<>();
                for (CorruptStreamTester.Record rec : o.records) {
                    CorruptStreamTester.headerFields(o, rec, h);
                }
                for (CorruptStreamTester.Copy c : h) {
                    copies.add(c);
                    String w = c.what.split(" ")[0];
                    if (w.equals("got-dirty")) w = "got-dirty " + c.what.split(" ")[1];
                    regions.add("set " + w);
                    realKs.add(-1);
                }
                List<CorruptStreamTester.Copy> cuts = new ArrayList<>();
                CorruptStreamTester.cuts(o, r, 400, 400, cuts);
                for (CorruptStreamTester.Copy c : cuts) {
                    copies.add(c);
                    regions.add("cut out");
                    realKs.add(-1);
                }
            } else {
                // Stale tails (035-02): from Z, a multiple of 512, to the end, other bytes.
                CorruptStreamTester.Original other = CorruptStreamTester.write(cfg,
                        seed * 31 + cfg.name.hashCode() + 7777);
                byte[] otherDb = new byte[o.bytes.length];
                for (int i = 0; i < otherDb.length; i++) {
                    otherDb[i] = other.bytes[i % other.bytes.length];
                }
                List<Object[]> sources = new ArrayList<>();
                sources.add(new Object[] {"another database, the same positions", otherDb});
                for (int d : new int[] {4096, 3 * 4096, 200000}) {
                    if (d >= o.bytes.length) continue;
                    byte[] own = new byte[o.bytes.length];
                    for (int i = 0; i < own.length; i++) {
                        own[i] = i >= d ? o.bytes[i - d] : 0;
                    }
                    sources.add(new Object[] {"its own bytes from " + d + " before", own});
                    byte[] oth = new byte[o.bytes.length];
                    for (int i = 0; i < oth.length; i++) {
                        oth[i] = other.bytes[(i + d) % other.bytes.length];
                    }
                    sources.add(new Object[] {"another database, " + d + " after", oth});
                }
                for (Object[] s : sources) {
                    for (int z = 512; z < o.bytes.length; z += 512) {
                        // Where Z falls: in a record's header, its nodes or its end.
                        String at;
                        if (z % RecoverableStream.META_BLOCK_DISTANCE
                                < RecoverableStream.META_BLOCK_SIZE) {
                            at = "in a meta block";
                        } else {
                            CorruptStreamTester.Record rec = o.recordAt(z);
                            int off = (int) (z - rec.tpos);   // no meta block inside: approximate
                            at = off < 32 ? "Z in a header" : off < rec.endMarker
                                    ? "Z in the nodes" : "Z in the record's end";
                        }
                        copies.add(staleCopy(o, z, (byte[]) s[1], s[0] + ", Z " + z));
                        regions.add("stale: " + s[0] + "; " + at);
                        realKs.add(o.committed(z));
                    }
                }
            }
            runAll(o, copies, regions, realKs, tally, threads);
            out.println(cfg.name + " done, " + (System.nanoTime() - t0) / 1000000 + " ms");
        }
        tally.print(out, what + (noSum ? ", without the node checksum" : ", with it"));
    }
}
