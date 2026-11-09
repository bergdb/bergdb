package bergdb.cross;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.nio.charset.StandardCharsets;

import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.StartInfo;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Java's runner of a cross workload (bergdb 012-05, section 3, which defines the workload
 * format and this program's output, "bergdb-run 1"). It runs the workload on a database
 * directory through Db's public API only (and the public CoreTestClock, FileStream,
 * Trans.Builder, GetData, GetMany), so that it keeps working while Java's internals change.
 * C's bergdb-run prints the same text for the same workload.
 *
 * <pre>
 * Usage: java -ea -cp CLASSES bergdb.cross.Run [-v] [-segments A[-B]] [-audit N] WORKLOAD DIR
 *   -v           also print each get's and each check's key-value pairs
 *   -segments    run only segments A to B (0-based; the segments are separated by restart
 *                lines); DIR holds the database that segment A-1 left
 *   -audit N     DbBuilder.audit(N): Java's audit every N transactions and at every start
 * Exit: 0, or 1 if a transaction or a call was refused, or 2 on a bad workload or usage.
 * </pre>
 */
public final class Run {
    private final Workload w;
    private final File dir;
    private final PrintStream out;
    private final boolean verbose;
    private final int audit;

    private final CoreTestClock clock = new CoreTestClock();
    private Db db;
    private int refusals = 0;
    private MessageDigest reads;        // the gets of the segment
    private long readCount;

    Run(Workload w, File dir, PrintStream out, boolean verbose, int audit) {
        this.w = w;
        this.dir = dir;
        this.out = out;
        this.verbose = verbose;
        this.audit = audit;
    }

    public static void main(String[] args) throws Exception {
        PrintStream out = new PrintStream(new java.io.BufferedOutputStream(System.out, 1 << 16),
                false, "UTF-8");
        int status = main(args, out);
        out.flush();
        System.exit(status);
    }

    /** Runs one job; returns the exit status. */
    public static int main(String[] args, PrintStream out) throws IOException {
        boolean verbose = false;
        int from = 0, to = Integer.MAX_VALUE, audit = 0;
        int i = 0;
        try {
            for (; i < args.length && args[i].startsWith("-"); i++) {
                if (args[i].equals("-v")) {
                    verbose = true;
                } else if (args[i].equals("-segments")) {
                    String s = args[++i];
                    int dash = s.indexOf('-');
                    from = Integer.parseInt(dash < 0 ? s : s.substring(0, dash));
                    to = dash < 0 ? from : Integer.parseInt(s.substring(dash + 1));
                } else if (args[i].equals("-audit")) {
                    audit = Integer.parseInt(args[++i]);
                } else {
                    throw new IllegalArgumentException("unknown option " + args[i]);
                }
            }
            if (args.length - i != 2) {
                throw new IllegalArgumentException("WORKLOAD DIR expected");
            }
        } catch (RuntimeException e) {
            System.err.println("Run: " + e.getMessage());
            System.err.println("Usage: Run [-v] [-segments A[-B]] [-audit N] WORKLOAD DIR");
            return 2;
        }
        Workload w;
        try {
            w = Workload.read(new File(args[i]));
        } catch (IllegalArgumentException e) {
            System.err.println("Run: " + args[i] + ": " + e.getMessage());
            return 2;
        }
        Run run = new Run(w, new File(args[i + 1]), out, verbose, audit);
        try {
            return run.run(from, to);
        } catch (Workload.BadWorkload e) {
            out.flush();
            System.err.println("Run: " + args[i] + ": " + e.getMessage());
            return 2;
        }
    }

    int run(int from, int to) throws IOException {
        out.println("bergdb-run 1");
        to = Math.min(to, w.segments - 1);
        int li = 0;
        for (; li < w.lines.size() && w.lines.get(li).segment < from; li++) {
            // Earlier segments: only the clock, which is kept across restarts.
            Workload.Line line = w.lines.get(li);
            String c = line.cmd();
            if (c.equals("clock") || (c.equals("t") && !line.words[1].equals("-"))) {
                clock.setTime(Long.parseLong(line.words[1]));
            }
        }
        for (int segment = from; segment <= to; segment++) {
            out.println("segment i=" + segment);
            reads = sha256();
            readCount = 0;
            for (; li < w.lines.size() && w.lines.get(li).segment == segment; li++) {
                Workload.Line line = w.lines.get(li);
                if (!line.cmd().equals("clock") && db == null && !start()) {
                    return 1;
                }
                try {
                    execute(line);
                } catch (Workload.BadWorkload e) {
                    throw e;
                } catch (RuntimeException e) {
                    refused(line, e);
                }
            }
            if (segment == w.segments - 1) {
                // The last segment ends at the end of the workload, not at a restart line.
                if (db == null && !start()) return 1;
                endSegment(segment);
            }
        }
        return refusals == 0 ? 0 : 1;
    }

    private void refused(Workload.Line line, RuntimeException e) {
        refusals++;
        String what = line.cmd().equals("t") ? "trans i=" + line.trans : "line=" + line.number;
        out.println("refused " + what + " cmd=" + line.cmd() + " error="
                + e.getClass().getSimpleName());
    }

    /**
     * Starts the database for a segment; false, after a line "start error=NAME", if the
     * start throws (a cut copy whose creation is not complete, for example).
     */
    private boolean start() {
        try {
            startOrThrow();
            return true;
        } catch (RuntimeException e) {
            out.println("start error=" + e.getClass().getSimpleName());
            db = null;
            return false;
        }
    }

    private void startOrThrow() {
        boolean create = !hasStream(dir);
        DbBuilder b = Db.builder();
        try {
            b.mainStream(new FileStream(dir));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        b.testSetupExceptStream();      // test clock, no eviction, retain forever, test id
        b.clock(clock);
        switch (w.maxNode) {
        case 8: b.maxNodeSize8(); break;
        case 14: b.maxNodeSize14(); break;
        case 30: b.maxNodeSize30(); break;
        case 62: b.maxNodeSize62(); break;
        default: throw new IllegalArgumentException("maxnode " + w.maxNode);
        }
        if (w.startupDistance >= 0) b.startupDistance(w.startupDistance);
        if (w.budget >= 0) b.cacheSizeIndicator(w.budget);
        if (audit > 0) b.audit(audit);
        Db d = b.build();
        StartInfo si = d.start();
        db = d;
        if (create) {
            // The header's retain duration and fraction once, after the creation's start
            // (bergdb 022-01, D3): the stream keeps them (015-87), as in StreamDigest's
            // restarts-once; a later start takes the stream's. Each setter commits reclaim's
            // settings if its value is not the one in force.
            if (w.retain >= 0) db.setRetainDuration(w.retain);
            if (w.fraction != null) db.setReclaimInternalFraction(Double.parseDouble(w.fraction));
        }
        out.println("start create=" + (create ? 1 : 0) + " startPos=" + si.startPos
                + " startupDistance=" + si.startupDistance + " startTime=" + si.startTime
                + " transCount=" + si.transCount + " lastPos=" + si.lastPos);
    }

    static boolean hasStream(File dir) {
        String[] names = dir.list();
        if (names == null) return false;
        for (String n : names) {
            if (n.endsWith(".bergdb")) return true;
        }
        return false;
    }

    private void endSegment(int segment) {
        if (readCount > 0) {
            out.println("reads n=" + readCount + " sha256=" + hex(reads.digest()));
            reads = sha256();
            readCount = 0;
        }
        status();
        db.close();
        db = null;
        out.println("end segment=" + segment);
    }

    private void status() {
        out.println("status length=" + db.getStreamLength()
                + " firstAvailablePos=" + db.getFirstAvailablePos()
                + " firstAvailableTime=" + db.getFirstAvailableLookupTime()
                + " startupDistance=" + db.getStartupDistance());
    }

    private void execute(Workload.Line line) {
        String[] x = line.words;
        switch (line.cmd()) {
        case "clock":
            setClock(line, Long.parseLong(x[1]));
            break;
        case "t":
            trans(line);
            break;
        case "now":
            out.println("now time=" + db.currentTime());
            break;
        case "sync":
            db.sync(SyncLevel.ORDINARY);
            status();
            break;
        case "restart":
            endSegment(line.segment);
            break;
        case "setsd":
            db.setStartupDistance(Integer.parseInt(x[1]));
            break;
        case "setretain":
            db.setRetainDuration(Workload.retain(line.number, x[1]));
            break;
        case "setfraction":
            db.setReclaimInternalFraction(Double.parseDouble(x[1]));
            break;
        case "setbudget":
            db.setCacheSizeIndicator(Long.parseLong(x[1]));
            break;
        case "check":
            check(Workload.lookupTime(line.number, x[1]), x[1]);
            break;
        case "get":
            get(line);
            break;
        default:
            throw line.error("unknown command");
        }
    }

    private void trans(Workload.Line line) {
        String[] x = line.words;
        if (!x[1].equals("-")) {
            setClock(line, Long.parseLong(x[1]));
        }
        Trans.Builder b = db.trans();
        for (int i = 2; i < x.length; ) {
            if (x[i].equals("p")) {
                b.put(Workload.key(x[i + 1]), Workload.value(x[i + 2]));
                i += 3;
            } else {
                b.delete(Workload.key(x[i + 1]));
                i += 2;
            }
        }
        Trans t = b.build();
        db.execute(t);
        out.println("trans i=" + line.trans + " tt=" + t.tt + " tpos=" + t.tpos
                + " lastPos=" + t.lastPos);
    }

    private void setClock(Workload.Line line, long t) {
        if (t <= clock.getTime()) {
            throw line.error("time " + t + " not after the clock's " + clock.getTime());
        }
        clock.setTime(t);
    }

    /** The whole state at a time, as getMany forward from the first key. */
    private void check(long time, String word) {
        GetMany g = db.newGetMany();
        g.lookupTime = time;
        try {
            db.getMany(g);
        } catch (LookupTimeNotAvailableException e) {
            out.println("check at=" + word + " unavailable");
            return;
        }
        MessageDigest md = sha256();
        for (Kvt kvt : g.result) {
            String s = kvLine(kvt);
            md.update(s.getBytes(StandardCharsets.UTF_8));
            md.update((byte) '\n');
            if (verbose) out.println("  " + s);
        }
        out.println("check at=" + word + " actual=" + g.actualLookupTime + " count="
                + g.result.size() + " sha256=" + hex(md.digest()));
    }

    /** The text of a key-value pair of a getMany, as Run's checks and Dump print it. */
    static String kvLine(Kvt kvt) {
        return "kv key=" + Workload.keyText(Keys.toBytes(kvt.key)) + " " + value(kvt.value)
                + " time=" + kvt.time + " pos=" + kvt.spos;
    }

    /** "len=L sha256=H" of a value, "none" for null. */
    static String value(byte[] v) {
        if (v == null) return "none";
        MessageDigest md = sha256();
        return "len=" + v.length + " sha256=" + hex(md.digest(v));
    }

    private void get(Workload.Line line) {
        String[] x = line.words;
        long time = Workload.lookupTime(line.number, x[1]);
        GetData gd = db.newGetData();
        for (int i = 2; i < x.length; i++) {
            byte[] key = Workload.key(x[i]);
            String s = "get at=" + x[1] + " key=" + Workload.keyText(key) + " ";
            try {
                byte[] v = db.getOne(time, Keys.toSegments(key), gd);
                s += v == null ? "none" : value(v) + " time=" + gd.kvTime + " tpos=" + gd.tpos;
            } catch (LookupTimeNotAvailableException e) {
                s += "unavailable";
            }
            reads.update(s.getBytes(StandardCharsets.UTF_8));
            reads.update((byte) '\n');
            readCount++;
            if (verbose) out.println("  " + s);
        }
    }

    static MessageDigest sha256() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    static String hex(byte[] bytes) {
        StringBuilder b = new StringBuilder(bytes.length * 2);
        for (byte x : bytes) {
            b.append(Character.forDigit((x >> 4) & 15, 16)).append(Character.forDigit(x & 15, 16));
        }
        return b.toString();
    }
}
