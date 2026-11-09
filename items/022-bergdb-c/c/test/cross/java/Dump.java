package bergdb.cross;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.TreeSet;

import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.StartInfo;
import bergdb.core.StoredTrans;
import bergdb.core.StoredValueNode;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.FileStream;

/**
 * Java's dumper of a database directory (bergdb 012-05, section 3, which defines its text,
 * "bergdb-dump 1"). It starts the database in DIR, through Db's public API only, and
 * prints its status, its latest state through getMany forward and backward, the state at
 * sampled times, ranges and prefixes from sampled keys, getOne of sampled keys at sampled
 * times, and getTrans of every committed record at or after the first available position.
 * Values as length and SHA-256. C's bergdb-dump prints the same text.
 *
 * The samples come from a scan of the database (StreamScan's text, "streamscan 1"): its
 * committed records give the positions and times, its value and delete nodes the keys.
 * Both sides of a comparison are given the same scan (side A's), so that they sample alike.
 *
 * A start may write (the zero fill of a torn record, bergdb 012-02): give it a copy.
 *
 * <pre>
 * Usage: java -ea -cp CLASSES bergdb.cross.Dump [-maxnode N] [-audit N] [-large] DIR SCAN
 *   -maxnode N  the database's node size, 8, 14, 30 (default) or 62; a start with
 *               another is refused (bergdb 005-50)
 *   -audit N    DbBuilder.audit(N), Java's audit (C to Java, 012-01, 1)
 *   -large      for large databases: the latest state as its digest only (no kv lines),
 *               the states at latest and at the middle time only, and getTrans of at
 *               most 1,000 records, sampled
 * Exit: 0, 1 if the start failed (a line "start error=NAME"), 2 on bad usage. A failed
 * start's exception, its name and its message, also goes to standard error, as C's
 * bergdb-dump writes its error there ("Dump: the start failed: NAME, MESSAGE"), for
 * test/stress/corruptset.sh, which compares the messages (bergdb 022-01, "Texts").
 * </pre>
 */
public final class Dump {
    /** How many keys and times the samples take at most. */
    static final int KEYS = 48, TIMES = 12, RANGES = 12, TRANS_LARGE = 1000;

    private final PrintStream out;
    private Db db;

    Dump(PrintStream out) {
        this.out = out;
    }

    public static void main(String[] args) throws Exception {
        PrintStream out = new PrintStream(new java.io.BufferedOutputStream(System.out, 1 << 16),
                false, "UTF-8");
        int status = main(args, out);
        out.flush();
        System.exit(status);
    }

    public static int main(String[] args, PrintStream out) throws IOException {
        return main(args, out, System.err);
    }

    /** As main(args, out), with standard error's lines to 'err'. */
    public static int main(String[] args, PrintStream out, PrintStream err) throws IOException {
        int maxNode = 30, audit = 0;
        boolean large = false;
        int i = 0;
        try {
            for (; i < args.length && args[i].startsWith("-"); i++) {
                if (args[i].equals("-maxnode")) {
                    maxNode = Integer.parseInt(args[++i]);
                } else if (args[i].equals("-audit")) {
                    audit = Integer.parseInt(args[++i]);
                } else if (args[i].equals("-large")) {
                    large = true;
                } else {
                    throw new IllegalArgumentException("unknown option " + args[i]);
                }
            }
            if (args.length - i != 2) {
                throw new IllegalArgumentException("DIR SCAN expected");
            }
        } catch (RuntimeException e) {
            err.println("Dump: " + e.getMessage());
            err.println("Usage: Dump [-maxnode N] [-audit N] [-large] DIR SCAN");
            return 2;
        }
        return new Dump(out).dump(new File(args[i]), new File(args[i + 1]), maxNode, audit,
                large, err);
    }

    int dump(File dir, File scanFile, int maxNode, int audit, boolean large, PrintStream err)
            throws IOException {
        out.println("bergdb-dump 1");
        Scan scan = Scan.read(scanFile);
        try {
            start(dir, maxNode, audit);
        } catch (RuntimeException e) {
            out.println("start error=" + e.getClass().getSimpleName());
            err.println("Dump: the start failed: " + e.getClass().getSimpleName() + ", "
                    + e.getMessage());
            return 1;
        }
        try {
            final long firstPos = db.getFirstAvailablePos();
            final long firstTime = db.getFirstAvailableLookupTime();
            out.println("status length=" + db.getStreamLength() + " firstAvailablePos=" + firstPos
                    + " firstAvailableTime=" + firstTime
                    + " startupDistance=" + db.getStartupDistance());

            // The latest state, forward and backward.
            List<Kvt> latest = many(Long.MAX_VALUE, null, true, true, null).result;
            MessageDigest md = Run.sha256();
            for (Kvt kvt : latest) {
                String s = Run.kvLine(kvt);
                digest(md, s);
                if (!large) out.println(s);
            }
            out.println("latest count=" + latest.size() + " sha256=" + Run.hex(md.digest()));
            List<Kvt> back = many(Long.MAX_VALUE, null, true, false, null).result;
            md = Run.sha256();
            for (Kvt kvt : back) {
                digest(md, Run.kvLine(kvt));
            }
            out.println("backward count=" + back.size() + " sha256=" + Run.hex(md.digest()));

            // The samples.
            List<byte[]> keys = sample(scan.keys(), KEYS);
            LinkedHashSet<Long> timeSet = new LinkedHashSet<Long>();
            for (long t : sample(scan.times(firstPos), TIMES)) {
                timeSet.add(t - 1);
                timeSet.add(t);
            }
            timeSet.add(Long.MAX_VALUE);
            if (firstTime > 0) {
                timeSet.add(firstTime - 1);     // before the first available time
            }
            List<Long> times = new ArrayList<Long>(timeSet);

            // The state at the sampled times (-large: at latest and at the middle time).
            long middle = times.size() > 2 ? times.get(times.size() / 2) : Long.MAX_VALUE;
            for (long t : large ? Arrays.asList(Long.MAX_VALUE, middle) : times) {
                state(t);
            }

            // Ranges, at latest and at the middle time, from each range key k: from k and from
            // k followed by '!' (0x23), inclusive or not, forward or backward, at most 5 pairs;
            // from k forward to k2 inclusive and from k2 backward to k exclusive, k2 being the
            // last key of the first of these ranges (if it has 2 pairs or more); and with the
            // prefix of k's first half, at most 10 pairs. All bounded, also for large ones.
            List<byte[]> rangeKeys = sample(keys, RANGES);
            for (long t : new long[] {Long.MAX_VALUE, middle}) {
                for (byte[] key : rangeKeys) {
                    byte[] after = Arrays.copyOf(key, key.length + 1);
                    after[key.length] = 0x23;           // the ikey character '!'
                    byte[] k2 = null;
                    for (byte[] start : new byte[][] {key, after}) {
                        for (int incl = 1; incl >= 0; incl--) {
                            for (int fwd = 1; fwd >= 0; fwd--) {
                                List<Kvt> r = range(t, start, incl == 1, fwd == 1,
                                        new GetMany.GetN(5), "get5");
                                if (k2 == null && r != null && r.size() >= 2) {
                                    k2 = Keys.toBytes(r.get(r.size() - 1).key);
                                }
                                if (k2 == null) k2 = new byte[0];
                            }
                        }
                    }
                    if (k2.length > 0) {
                        range(t, key, true, true, new GetMany.Endpoint(Keys.toSegments(k2),
                                true), "to=" + Workload.keyText(k2) + " endIncl=1");
                        range(t, k2, true, false, new GetMany.Endpoint(Keys.toSegments(key),
                                false, true), "to=" + Workload.keyText(key) + " endIncl=0");
                    }
                    byte[] prefix = Arrays.copyOf(key, (key.length + 1) / 2);
                    range(t, prefix, true, true,
                            new GetMany.PrefixN(Keys.toSegments(prefix), 10), "prefix10");
                }
            }

            // getOne of the sampled keys at the sampled times.
            GetData gd = db.newGetData();
            for (byte[] key : keys) {
                long[] segs = Keys.toSegments(key);
                for (long t : times) {
                    String s = "one at=" + time(t) + " key=" + Workload.keyText(key) + " ";
                    try {
                        byte[] v = db.getOne(t, segs, gd);
                        s += v == null ? "none" : Run.value(v) + " time=" + gd.kvTime
                                + " tpos=" + gd.tpos;
                    } catch (LookupTimeNotAvailableException e) {
                        s += "unavailable";
                    }
                    out.println(s);
                }
            }

            // getTrans of every committed record at or after the first available position.
            List<Long> positions = new ArrayList<Long>();
            for (long pos : scan.positions) {
                if (pos >= firstPos) {
                    positions.add(pos);
                }
            }
            for (long pos : large ? sample(positions, TRANS_LARGE) : positions) {
                trans(pos);
            }
        } finally {
            db.close();
        }
        out.println("end");
        return 0;
    }

    private void start(File dir, int maxNode, int audit) throws IOException {
        DbBuilder b = Db.builder().mainStream(new FileStream(dir));
        b.testSetupExceptStream();
        b.clock(new CoreTestClock());
        switch (maxNode) {
        case 8: b.maxNodeSize8(); break;
        case 14: b.maxNodeSize14(); break;
        case 30: b.maxNodeSize30(); break;
        case 62: b.maxNodeSize62(); break;
        default: throw new IllegalArgumentException("maxnode " + maxNode);
        }
        if (audit > 0) b.audit(audit);
        db = b.build();
        StartInfo si = db.start();
        out.println("start startPos=" + si.startPos + " startupDistance=" + si.startupDistance
                + " startTime=" + si.startTime + " transCount=" + si.transCount
                + " lastPos=" + si.lastPos);
    }

    static String time(long t) {
        return t == Long.MAX_VALUE ? "latest" : Long.toString(t);
    }

    private static void digest(MessageDigest md, String s) {
        md.update(s.getBytes(StandardCharsets.UTF_8));
        md.update((byte) '\n');
    }

    private GetMany many(long time, byte[] start, boolean incl, boolean fwd,
            GetMany.StopCondition stop) {
        GetMany g = db.newGetMany();
        g.lookupTime = time;
        g.startKey = start == null ? null : Keys.toSegments(start);
        g.inclusive = incl;
        g.forward = fwd;
        if (stop != null) g.stopCondition = stop;
        db.getMany(g);
        return g;
    }

    private void state(long t) {
        try {
            GetMany g = many(t, null, true, true, null);
            MessageDigest md = Run.sha256();
            for (Kvt kvt : g.result) {
                digest(md, Run.kvLine(kvt));
            }
            out.println("state at=" + time(t) + " actual=" + g.actualLookupTime + " count="
                    + g.result.size() + " sha256=" + Run.hex(md.digest()));
        } catch (LookupTimeNotAvailableException e) {
            out.println("state at=" + time(t) + " unavailable");
        }
    }

    /** A range; returns its pairs, or null if the time is not available. */
    private List<Kvt> range(long t, byte[] start, boolean incl, boolean fwd,
            GetMany.StopCondition stop, String stopText) {
        String head = "range at=" + time(t) + " start=" + Workload.keyText(start) + " incl="
                + (incl ? 1 : 0) + " fwd=" + (fwd ? 1 : 0) + " stop=" + stopText;
        try {
            GetMany g = many(t, start, incl, fwd, stop);
            out.println(head + " count=" + g.result.size());
            for (Kvt kvt : g.result) {
                out.println("  " + Run.kvLine(kvt));
            }
            return g.result;
        } catch (LookupTimeNotAvailableException e) {
            out.println(head + " unavailable");
            return null;
        }
    }

    private void trans(long pos) {
        StoredTrans st;
        try {
            st = db.getTrans(pos);
        } catch (LookupTimeNotAvailableException e) {
            out.println("trans pos=" + pos + " unavailable");
            return;
        } catch (RuntimeException e) {
            out.println("trans pos=" + pos + " error=" + e.getClass().getSimpleName());
            return;
        }
        List<StoredValueNode> values = st.getValueNodes();
        out.println("trans pos=" + st.tpos + " tt=" + st.tt + " lastPos=" + st.lastPos
                + " startupPos=" + st.startupPos + " topPos=" + st.topPos
                + " values=" + values.size());
        for (StoredValueNode v : values) {
            String key = Workload.keyText(Keys.toBytes(v.getKey()));
            if (v.getNode().getType() == Node.TYPE_DELETE) {
                out.println("  delete key=" + key);
            } else {
                out.println("  value key=" + key + " " + Run.value(v.getNode().value));
            }
        }
    }

    /** At most n elements of a list, evenly spread: those at i * size / n. */
    static <T> List<T> sample(List<T> all, int n) {
        if (all.size() <= n) {
            return all;
        }
        List<T> result = new ArrayList<T>(n);
        for (int i = 0; i < n; i++) {
            result.add(all.get((int) ((long) i * all.size() / n)));
        }
        return result;
    }

    /** What the dump takes from a scan: committed records and the keys of value nodes. */
    static final class Scan {
        final List<Long> positions = new ArrayList<Long>();
        final List<Long> recordTimes = new ArrayList<Long>();
        final TreeSet<String> keyHex = new TreeSet<String>();

        static Scan read(File file) throws IOException {
            Scan s = new Scan();
            BufferedReader r = new BufferedReader(new InputStreamReader(new FileInputStream(file),
                    StandardCharsets.UTF_8), 1 << 16);
            try {
                for (String line; (line = r.readLine()) != null; ) {
                    if (line.startsWith("record ") && line.contains(" time=")) {
                        s.positions.add(Long.parseLong(field(line, "pos")));
                        s.recordTimes.add(Long.parseLong(field(line, "time")));
                    } else if (line.startsWith("value ") || line.startsWith("delete ")) {
                        String k = field(line, "key");
                        if (k != null) s.keyHex.add(k);
                    }
                }
            } finally {
                r.close();
            }
            return s;
        }

        /** The keys, sorted by their bytes, unsigned (the order of their hex). */
        List<byte[]> keys() {
            List<byte[]> result = new ArrayList<byte[]>();
            for (String h : keyHex) {
                if (h.isEmpty()) continue;
                byte[] b = new byte[h.length() / 2];
                for (int i = 0; i < b.length; i++) {
                    b[i] = (byte) Integer.parseInt(h.substring(2 * i, 2 * i + 2), 16);
                }
                result.add(b);
            }
            return result;
        }

        /** The times of the records at or after a position, in stream order. */
        List<Long> times(long from) {
            List<Long> result = new ArrayList<Long>();
            for (int i = 0; i < positions.size(); i++) {
                if (positions.get(i) >= from) result.add(recordTimes.get(i));
            }
            return result;
        }

        /** The value of field "name=" in a scan line, or null. */
        static String field(String line, String name) {
            String key = " " + name + "=";
            int i = line.indexOf(key);
            if (i < 0) return null;
            int from = i + key.length();
            int to = line.indexOf(' ', from);
            return line.substring(from, to < 0 ? line.length() : to);
        }
    }
}
