package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Review probe (bergdb 033, review of the start, 2026-11-28): chains of faults on one file
 * database, each start checked. A chain is a seed. Each step starts the database on what the
 * step before left (a start must not refuse it, and every key must read as the model says),
 * then either stops it, or writes commits (values of random bytes, of zeros, of both; some
 * records over a meta block or over several files; reclaim cuts as the clock moves), and
 * then makes a fault by changing the files:
 *
 * - kill: the stream cut at a position c at or after the end of the record that decided the
 *   last cut that took files off (what a kill at the moment the stream ended at c leaves; a
 *   cut is made only when the stream is durable to there): right after that record, in the last
 *   record's header, in it, at, in and after a meta block, at a file's start (the file then
 *   absent, empty or zeros); optionally zeros after c within the file (028-60);
 * - kill during the start's own writes: after a start and a stop with no commit, the stream
 *   cut inside what the start's recovery appended;
 * - power loss in the cut's batch: the cut's thread is held at its deletes from the open on,
 *   so every file that the step's cuts (the start's too) took off is still there; the image
 *   is the files without any subset of them, with or without a kill's cut of the tail;
 * - kill with other bytes (STALE_PERCENT of the kills): after the cut at c, the file holds
 *   other bytes where the cut write's bytes should be (035-02): random bytes, an older stream
 *   file's bytes of this chain at the same offsets, or the file's own bytes of 4,096 or 8,192
 *   bytes before. The start must then take the stream as cut at c, or refuse it with a
 *   BadTailException and the files unchanged; the probe then cuts the stream at the P of the
 *   exception, as its message says, and the next start must hold what the stream held at c
 *   (or also the record that the kill cut in its padding or at its last byte, if the other
 *   bytes end it with the byte 10: all the record's content is the database's own).
 *   Any other refusal of such a tail is counted by its message and the tail removed. A later
 *   start of the chain that refuses the first block of the stream or of a file before a
 *   gap is counted as the review's F2 (other bytes that a start took, at a meta block's
 *   position), not as a failure; the chain ends, or goes on without the files before the gap.
 *
 * The forces are no-ops (the faults are made by hand). A refusal for a file before a gap
 * whose first block is recovery's fill is 028-76's decided case (a): counted, the file
 * moved out as the message says, and the chain goes on. Every other refusal, a wrong value
 * or a start that changed the files before it refused is printed with the chain's steps,
 * and the image kept in OUT/fail-SEED. After each commit the files must begin at or before
 * reclaim's cut. A chain does not repeat exactly: when a cut is made depends on when the
 * buffer's thread has written its record.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/StartChain.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.StartChain OUT FIRST_SEED LAST_SEED STEPS
 *       [RETAIN_SECONDS [STOP_PERCENT [SCALE [STALE_PERCENT]]]]
 * RETAIN_SECONDS (2): reclaim's retain duration in seconds of the test clock, which moves
 * 0.1 s a commit; with 250, SCALE 5 and 70 steps the stream kept passes 10 MB and 50 MB, and
 * the files are of 1 MB and 5 MB, with several meta blocks each. STOP_PERCENT (15): the share
 * of steps that stop with no commit. SCALE (1): the factor of the ordinary values' sizes,
 * 300 to 3,000 bytes. STALE_PERCENT (0): the share of kills with other bytes. With
 * -Dstopfile=FILE the run ends before the next chain when FILE is there.
 */
public class StartChain {
    static final long SEC = FileStreamPowerLossTester.SEC;
    static final int KEYS = 12;
    static final long MD = 200000;

    static class Io extends FileStreamIo {
        final Object gate = new Object();
        boolean held;
        protected void forceFile(File file, RandomAccessFile handle) { }
        protected void forceDirectory(File directory) { }
        void release() { synchronized (gate) { held = false; gate.notifyAll(); } }
        protected boolean delete(File file) throws IOException {
            synchronized (gate) {
                while (held) {
                    try { gate.wait(); } catch (InterruptedException e) { throw new IOException(e); }
                }
            }
            return super.delete(file);
        }
    }

    static class Entry {
        long lastPos; String key; byte[] value;
        Entry(long lastPos, String key, byte[] value) { this.lastPos = lastPos; this.key = key; this.value = value; }
    }

    static int starts, knownA, failures, faults;
    static long retain = 2;
    static int stopPercent = 15;
    static int scale = 1;
    static int stalePercent = 0;
    static TreeMap<String, Integer> staleOther = new TreeMap<String, Integer>();
    static TreeMap<String, Integer> laterRefused = new TreeMap<String, Integer>();
    static TreeMap<String, Integer> kinds = new TreeMap<String, Integer>();

    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        long first = Long.parseLong(args[1]), last = Long.parseLong(args[2]);
        int steps = Integer.parseInt(args[3]);
        if (args.length > 4) retain = Long.parseLong(args[4]);
        if (args.length > 5) stopPercent = Integer.parseInt(args[5]);
        if (args.length > 6) scale = Integer.parseInt(args[6]);
        if (args.length > 7) stalePercent = Integer.parseInt(args[7]);
        base.mkdirs();
        for (long seed = first; seed <= last; seed++) {
            String stop = System.getProperty("stopfile");     // ends the run when the file is there
            if (stop != null && new File(stop).exists()) break;
            try {
                chain(base, seed, steps);
            } catch (Throwable e) {
                failures++;
                System.out.println("FAIL seed " + seed + ": the probe threw " + e);
                e.printStackTrace(System.out);
            }
            if (seed % 20 == 0) System.out.println("at seed " + seed + ": starts " + starts
                    + ", faults " + kinds + ", known (a) " + knownA + ", failures " + failures);
        }
        System.out.println("STARTCHAIN DONE seeds " + first + ".." + last + ": starts " + starts
                + ", faults " + kinds + ", known (a) " + knownA + ", failures " + failures);
        for (Map.Entry<String, Integer> e : laterRefused.entrySet()) {
            System.out.println("a later start refused after other bytes were taken, " + e.getValue() + ": " + e.getKey());
        }
        for (Map.Entry<String, Integer> e : staleOther.entrySet()) {
            System.out.println("other refusal of a tail of other bytes, " + e.getValue() + ": " + e.getKey());
        }
    }

    static String key(int i) { return "/chain/key-" + i; }

    static void count(String kind) { kinds.merge(kind, 1, Integer::sum); }

    static void chain(File base, long seed, int steps) throws Exception {
        File dir = new File(base, "s" + seed);
        rm(dir);
        dir.mkdirs();
        Random r = new Random(seed);
        TreeMap<String, byte[]> model = new TreeMap<String, byte[]>();
        List<String> ops = new ArrayList<String>();
        long time = SEC;
        CoreTestClock clock = new CoreTestClock();
        Map<String, byte[]> graveyard = new TreeMap<String, byte[]>();   // files seen before
        Map<String, byte[]> clean = null;       // the image without the other bytes, if it has some
        long staleEnd = -1;
        boolean tookOther = false;      // the chain has had a tail of other bytes
        Entry lastByteCut = null;       // the record whose padding or last byte only the kill cut
        for (int step = 0; step < steps; step++) {
            Map<String, byte[]> image = files(dir);
            ops.add("      the files before step " + step + ":" + layout(image));
            while (ops.size() > 60) ops.remove(0);
            // < 0 stop; < 55 run, kill; else run, power loss
            int action = step == 0 ? 1 : r.nextInt(100 + stopPercent) - stopPercent;
            boolean power = action >= 55 || (action < 0 && r.nextInt(3) == 0);
            Io io = new Io();
            io.held = power;
            FileStream stream = null;
            Db db = null;
            long before = -1;
            time += SEC;
            clock.setTime(time);
            boolean retried = false;
            String suspect = null;
            while (true) {
                try {
                    stream = new FileStream(dir, io, true);
                    before = stream.getLength();
                    db = Db.builder().testSetup(stream).clock(clock).start();
                    db.setStartupDistance(20000);
                    db.setRetainDuration(retain * SEC);    // writes at the first start only
                    break;
                } catch (Throwable e) {
                    io.release();
                    if (stream != null) { try { stream.close(); } catch (Throwable x) { } }
                    String m = messages(e);
                    boolean changed = !FileStreamPowerLossTester.sameFiles(image, files(dir));
                    if (!retried && !changed && m.contains("BadDirStateException")
                            && m.contains("is not valid, its last byte 0") && leftoverIsFill(image)) {
                        knownA++;
                        ops.add("refused, 028-76 (a); the files before the gap moved out");
                        removeLeftovers(dir);
                        image = files(dir);
                        io = new Io();
                        io.held = power;
                        retried = true;
                        continue;
                    }
                    if (clean != null && !changed && badTail(e) != null) {
                        long p = badTail(e).getCutPos();
                        count("stale-refused-with-P");
                        if (p > staleEnd) {
                            fail(base, seed, step, ops, image, "P " + p + " after the stream's end: " + m);
                            return;
                        }
                        ops.add("refused, BadTailException; the stream cut at its P, " + p);
                        cutAt(dir, p);
                        image = files(dir);
                        clean = null;
                        io = new Io();
                        io.held = power;
                        continue;
                    }
                    // Other bytes that an earlier start took, at a meta block's position, as the
                    // first block of a file before a gap or of the stream (the review's F2).
                    String later = !tookOther || changed ? null
                            : m.contains("BadDirStateException") && m.contains("before a gap") ? "a file before a gap"
                            : m.contains("BadMagicBytes") ? "the stream's first block: other bytes"
                            : m.contains("Could not find *any* valid meta block") ? "the stream's first block: not its own position"
                            : m.contains("before the stream's first position") ? "the stream's first block: another ID"
                            : null;
                    if (later != null && clean != null) {
                        // If this step's tail of other bytes is not what the start refused,
                        // the start below, without it, is refused the same way and counted;
                        // if that start is taken, the tail was refused otherwise.
                        suspect = (changed ? "FILES CHANGED; " : "") + m;
                        restore(dir, clean);
                        image = files(dir);
                        clean = null;
                        io = new Io();
                        io.held = power;
                        continue;
                    }
                    if (later != null) {
                        suspect = null;
                        if (laterRefused.merge(later, 1, Integer::sum) == 1) {
                            System.out.println("seed " + seed + ", step " + step + ": refused after other bytes"
                                    + " were taken, " + later + ": " + m.substring(0, Math.min(m.length(), 300)));
                            for (String op : ops) if (!op.startsWith("      ")) System.out.println("    " + op);
                        }
                        if (!later.equals("a file before a gap") || retried) {
                            rm(dir);
                            return;         // the chain ends
                        }
                        ops.add("refused, a file before a gap with other bytes; the files before the gap moved out");
                        removeLeftovers(dir);
                        image = files(dir);
                        io = new Io();
                        io.held = power;
                        retried = true;
                        continue;
                    }
                    if (clean != null) {
                        String kind = (changed ? "FILES CHANGED; " : "") + m.replaceAll("[0-9]+", "N");
                        kind = kind.substring(0, Math.min(kind.length(), 160));
                        if (staleOther.merge(kind, 1, Integer::sum) == 1) {
                            System.out.println("seed " + seed + ", step " + step + ": a tail of other bytes"
                                    + " refused otherwise" + (changed ? ", THE FILES CHANGED" : "") + ": " + m);
                        }
                        ops.add("refused otherwise; the other bytes removed");
                        restore(dir, clean);
                        image = files(dir);
                        clean = null;
                        io = new Io();
                        io.held = power;
                        continue;
                    }
                    fail(base, seed, step, ops, image, "start refused" + (changed
                            ? " AND CHANGED THE FILES" : "") + ": " + m);
                    return;
                }
            }
            starts++;
            if (suspect != null) {
                String kind = suspect.replaceAll("[0-9]+", "N");
                kind = kind.substring(0, Math.min(kind.length(), 160));
                if (staleOther.merge(kind, 1, Integer::sum) == 1) {
                    System.out.println("seed " + seed + ", step " + step + ": a tail of other bytes"
                            + " refused otherwise: " + suspect);
                    for (String op : ops) if (!op.startsWith("      ")) System.out.println("    " + op);
                }
            }
            if (clean != null) count("stale-started");
            clean = null;
            long after = db.getStreamLength();   // with what the start appended, written or not
            String wrong = null;
            try {
                if (lastByteCut != null && !Arrays.equals(DbUtil.get(db, Long.MAX_VALUE, lastByteCut.key),
                        model.get(lastByteCut.key))) {
                    // Other bytes after a kill in a record's padding or at its last byte: if
                    // the last of them is 10, the record is whole and committed, with every
                    // byte of its header and nodes the database's own. Taken as such.
                    if (lastByteCut.value == null) model.remove(lastByteCut.key);
                    else model.put(lastByteCut.key, lastByteCut.value);
                    count("stale-last-byte-10");
                }
                lastByteCut = null;
                for (int i = 0; i < KEYS; i++) {
                    byte[] got = DbUtil.get(db, Long.MAX_VALUE, key(i));
                    if (!Arrays.equals(got, model.get(key(i)))) {
                        wrong = key(i) + ": " + (got == null ? "none" : got.length + " bytes") + ", the model "
                                + (model.get(key(i)) == null ? "none" : model.get(key(i)).length + " bytes");
                        break;
                    }
                }
                if (wrong == null && step % 4 == 3) db.checkNodes();
            } catch (Throwable e) {
                wrong = "read threw " + messages(e);
            }
            if (wrong != null) {
                io.release();
                db.close();
                fail(base, seed, step, ops, image, "wrong after start: " + wrong);
                return;
            }

            List<Entry> entries = new ArrayList<Entry>();
            long floor = after;
            long lastFirst = stream.getFirstPos();
            ops.add("      step " + step + ": started, the stream " + lastFirst + " to " + after
                    + " (" + before + " at the open), reclaim's cut " + db.getFirstAvailablePos());
            if (lastFirst > db.getFirstAvailablePos()) {
                io.release();
                db.close();
                fail(base, seed, step, ops, image, "THE FILES BEGIN AFTER RECLAIM'S CUT at the start: the"
                        + " first position " + lastFirst + ", the cut " + db.getFirstAvailablePos());
                return;
            }
            String op;
            if (action < 0) {
                op = "stop";
            } else {
                int n = 20 + r.nextInt(300);
                boolean straddle = r.nextInt(3) == 0;
                for (int i = 0; i < n || (straddle && i < n + 400); i++) {
                    long len = db.getStreamLength();
                    boolean big = false;
                    int size = (300 + r.nextInt(2700)) * scale;
                    if (i >= n) {
                        if (len % MD > 180000) { size = 25000 + r.nextInt(20000); big = true; }
                    } else if (r.nextInt(100) < 2) {
                        size = 210000 + r.nextInt(500000);
                    }
                    time += SEC / 10;
                    clock.setTime(time);
                    String key = key(r.nextInt(KEYS));
                    byte[] value = r.nextInt(100) < 5 ? null : value(r, size);
                    Trans t = value == null ? db.trans().delete(key).build() : db.trans().put(key, value).build();
                    // The length that was durable before the pending cut was made: the end of
                    // the record of its decision (Reclaim.pendingCutDurableAt()).
                    long pending = db.internal().reclaim().pendingCutDurableAt();
                    long cutBefore = db.getFirstAvailablePos();
                    db.execute(t);
                    entries.add(new Entry(t.lastPos, key, value));
                    long cutNow = db.getFirstAvailablePos();
                    if (stream.getFirstPos() != lastFirst) {
                        ops.add("      step " + step + ": the first position " + lastFirst + " to "
                                + stream.getFirstPos() + " in the record at " + t.tpos + " to " + t.nextPos
                                + ", the cut pending since " + pending + ", reclaim's cut " + cutBefore
                                + " to " + cutNow);
                        lastFirst = stream.getFirstPos();
                        // A cut decided in this record can be made in it too, after the one
                        // that was pending: then the record is the floor.
                        floor = Math.max(floor, pending != -1 && cutNow == cutBefore ? pending : t.nextPos);
                    }
                    if (stream.getFirstPos() > cutNow) {
                        io.release();
                        db.close();
                        fail(base, seed, step, ops, image, "THE FILES BEGIN AFTER RECLAIM'S CUT: the first"
                                + " position " + stream.getFirstPos() + ", the cut " + cutNow
                                + ", after the record at " + t.tpos);
                        return;
                    }
                    if (big) break;
                }
                op = "run " + entries.size();
            }
            db.sync(SyncLevel.ORDINARY);
            long end = db.getStreamLength();
            if (stream.getFirstPos() != lastFirst) floor = end;
            long firstPos = stream.getFirstPos();
            Map<String, byte[]> snapshot = power ? files(dir) : null;
            io.release();
            db.close();
            if (!power && FileStreamPowerLossTester.hasGap(dir)) {
                fail(base, seed, step, ops, image, "the start and the run left a gap in the files");
                return;
            }
            if (!power) snapshot = files(dir);

            // The fault.
            long c = end;
            if (action < 0) {
                if (after > before && before > 0 && r.nextInt(5) != 0) {
                    c = pick(r, before, after, before);
                    op += ", kill in the recovery's writes [" + before + ", " + after + ") at " + c;
                    count("kill-in-recovery");
                }
            } else if (r.nextInt(8) != 0 && floor < end) {
                long lastRecord = entries.isEmpty() ? floor : Math.max(floor, entries.size() > 1
                        ? entries.get(entries.size() - 2).lastPos + 1 : floor);
                c = pick(r, floor, end, lastRecord);
                op += ", kill at " + c + " of " + end;
                count("kill");
            }
            Map<String, byte[]> whole = c < end && !power && action >= 0 && r.nextInt(100) < stalePercent
                    ? new TreeMap<String, byte[]>(snapshot) : null;
            if (c < end) {
                faults++;
                op += cut(r, snapshot, c);
            }
            for (Map.Entry<String, byte[]> e : snapshot.entrySet()) {
                if (graveyard.size() < 40 || graveyard.containsKey(e.getKey())) graveyard.put(e.getKey(), e.getValue());
            }
            Map<String, byte[]> withStale = null;
            if (whole != null) {
                withStale = new TreeMap<String, byte[]>(snapshot);
                String did = stale(r, withStale, whole, graveyard, c);
                if (did == null) {
                    withStale = null;
                } else {
                    op += did;
                    count("stale");
                    tookOther = true;       // if the start takes it, or by the cut at P
                    staleEnd = 0;
                    for (Map.Entry<String, byte[]> e : withStale.entrySet()) {
                        staleEnd = Long.parseLong(e.getKey().substring(0, 14)) * 100000 + e.getValue().length;
                    }
                }
            }
            if (power) {
                List<String> taken = new ArrayList<String>();
                for (String name : snapshot.keySet()) {
                    if (Long.parseLong(name.substring(0, 14)) * 100000 < firstPos) taken.add(name);
                }
                if (!taken.isEmpty()) {
                    List<String> gone = new ArrayList<String>();
                    for (String name : taken) {
                        if (r.nextBoolean()) { gone.add(name); snapshot.remove(name); }
                    }
                    op += ", power loss in the batch: taken off " + taken + ", deleted " + gone;
                    count("power");
                    faults++;
                }
            }
            lastByteCut = null;
            for (Entry e : entries) {
                if (e.lastPos < c) {
                    if (e.value == null) model.remove(e.key); else model.put(e.key, e.value);
                } else if (withStale != null && lastByteCut == null && c > e.lastPos - 8) {
                    lastByteCut = e;    // records are multiples of 8 bytes: at most 7 of padding
                }
            }
            restore(dir, withStale != null ? withStale : snapshot);
            clean = withStale != null ? snapshot : null;
            ops.add(step + ": " + op);
        }
        rm(dir);
    }

    /** A position in [from, to): near 'record', the last record's start, or a meta block. */
    static long pick(Random r, long from, long to, long record) {
        for (int i = 0; i < 50; i++) {
            long c;
            long block = (from / MD + 1 + r.nextInt((int) ((to - from) / MD + 1))) * MD;
            switch (r.nextInt(11)) {
            case 0: case 1: c = record + 1 + r.nextInt(40); break;
            case 2: c = record + r.nextInt((int) Math.min(Integer.MAX_VALUE, Math.max(1, to - record))); break;
            case 3: c = to - 1 - r.nextInt(3); break;
            case 4: c = block; break;
            case 5: c = block + 1 + r.nextInt(127); break;
            case 6: c = block + 128 + r.nextInt(40); break;
            case 7: c = block - 1 - r.nextInt(40); break;
            case 8: c = record; break;
            case 9: c = from + r.nextInt(60); break;
            default: c = from + r.nextInt((int) Math.min(Integer.MAX_VALUE, to - from)); break;
            }
            if (c >= from && c < to) return c;
        }
        return from + r.nextInt((int) Math.min(Integer.MAX_VALUE, to - from));
    }

    /** Cuts the image at stream position c, as a kill leaves it; returns what it did. */
    static String cut(Random r, Map<String, byte[]> files, long c) {
        String did = "";
        for (String name : new ArrayList<String>(files.keySet())) {
            long start = Long.parseLong(name.substring(0, 14)) * 100000;
            byte[] bytes = files.get(name);
            if (start > c) {
                files.remove(name);
            } else if (start == c) {
                int how = r.nextInt(4);
                if (how < 2) { files.remove(name); did += ", the file at " + c + " absent"; }
                else if (how == 2) { files.put(name, new byte[0]); did += ", the file at " + c + " empty"; }
                else {
                    int z = 1 + r.nextInt(Math.max(1, Math.min(bytes.length, 20000)));
                    files.put(name, new byte[z]); did += ", the file at " + c + " " + z + " zeros";
                }
            } else if (start + bytes.length > c) {
                int keep = (int) (c - start);
                int room = bytes.length - keep;
                int z = 0;
                switch (r.nextInt(5)) {
                case 0: z = 1 + r.nextInt(Math.min(room, 5000)); break;
                case 1: z = Math.min(room, (4096 - keep % 4096) % 4096 + 4096 * r.nextInt(4)); break;
                default: break;
                }
                files.put(name, Arrays.copyOf(Arrays.copyOf(bytes, keep), keep + z));
                if (z > 0) did += ", " + z + " zeros after it";
            }
        }
        return did;
    }

    static bergdb.storage.BadTailException badTail(Throwable e) {
        for (Throwable t = e; t != null; t = t.getCause()) {
            if (t instanceof bergdb.storage.BadTailException) return (bergdb.storage.BadTailException) t;
        }
        return null;
    }

    /** Cuts the stream in 'dir' at 'p', as a BadTailException's message says. */
    static void cutAt(File dir, long p) throws IOException {
        Map<String, byte[]> files = files(dir);
        for (String name : new ArrayList<String>(files.keySet())) {
            long start = Long.parseLong(name.substring(0, 14)) * 100000;
            if (start >= p) files.remove(name);
            else if (start + files.get(name).length > p) files.put(name, Arrays.copyOf(files.get(name), (int) (p - start)));
        }
        restore(dir, files);
    }

    /**
     * Puts other bytes after the cut at c, within the bytes that the file at c held before
     * the cut ('whole'); returns what it did, or null if there is no room.
     */
    static String stale(Random r, Map<String, byte[]> files, Map<String, byte[]> whole,
            Map<String, byte[]> graveyard, long c) {
        String name = null;
        for (String n : whole.keySet()) {
            if (Long.parseLong(n.substring(0, 14)) * 100000 <= c) name = n;
        }
        long start = Long.parseLong(name.substring(0, 14)) * 100000;
        byte[] was = whole.get(name);
        int keep = (int) (c - start);
        if (was.length - keep < 1) return null;
        int g = r.nextBoolean() ? was.length - keep : 1 + r.nextInt(was.length - keep);
        byte[] now = Arrays.copyOf(Arrays.copyOf(was, keep), keep + g);
        String what;
        switch (r.nextInt(3)) {
        case 0: {
            byte[] random = new byte[g];
            r.nextBytes(random);
            System.arraycopy(random, 0, now, keep, g);
            what = "random bytes";
            break;
        }
        case 1: {
            List<String> names = new ArrayList<String>(graveyard.keySet());
            names.remove(name);
            if (names.isEmpty()) return null;
            String other = names.get(r.nextInt(names.size()));
            byte[] b = graveyard.get(other);
            for (int i = keep; i < keep + g && i < b.length; i++) now[i] = b[i];
            what = "the bytes of " + other + " at the same offsets";
            break;
        }
        default: {
            int shift = 4096 * (1 + r.nextInt(2));
            for (int i = keep; i < keep + g; i++) now[i] = i - shift >= 0 ? was[i - shift] : 0;
            what = "the file's own bytes of " + shift + " before";
            break;
        }
        }
        files.put(name, now);
        return ", then " + g + " other bytes: " + what;
    }

    static byte[] value(Random r, int size) {
        byte[] v = new byte[size];
        switch (r.nextInt(4)) {
        case 2: break;
        case 3: byte[] half = new byte[size / 2]; r.nextBytes(half); System.arraycopy(half, 0, v, 0, half.length); break;
        default: r.nextBytes(v); break;
        }
        return v;
    }

    /**
     * Whether the image's files before its last gap include one whose first block is recovery's
     * fill: the magic bytes and a last byte of 0.
     */
    static boolean leftoverIsFill(Map<String, byte[]> image) {
        long end = -1;
        List<String> beforeGap = new ArrayList<String>(), seen = new ArrayList<String>();
        for (Map.Entry<String, byte[]> e : image.entrySet()) {
            long start = Long.parseLong(e.getKey().substring(0, 14)) * 100000;
            if (end != -1 && start > end) beforeGap = new ArrayList<String>(seen);
            seen.add(e.getKey());
            end = start + e.getValue().length;
        }
        for (String name : beforeGap) {
            byte[] b = image.get(name);
            // The fill of a block not begun, or the completion of one that the kill cut.
            if (b.length >= 128 && b[0] == 'b' && b[1] == 'e' && b[2] == 'r' && b[3] == 'g'
                    && b[127] == 0) return true;
        }
        return false;
    }

    static void removeLeftovers(File dir) throws IOException {
        Map<String, byte[]> image = files(dir);
        long end = -1;
        List<String> beforeGap = new ArrayList<String>(), seen = new ArrayList<String>();
        for (Map.Entry<String, byte[]> e : image.entrySet()) {
            long start = Long.parseLong(e.getKey().substring(0, 14)) * 100000;
            if (end != -1 && start > end) beforeGap = new ArrayList<String>(seen);
            seen.add(e.getKey());
            end = start + e.getValue().length;
        }
        for (String name : beforeGap) new File(dir, name).delete();
    }

    static void fail(File base, long seed, int step, List<String> ops, Map<String, byte[]> image,
            String what) throws IOException {
        failures++;
        System.out.println("FAIL seed " + seed + ", step " + step + ": " + what);
        for (String op : ops) System.out.println("    " + op);
        System.out.println("    the image:" + layout(image));
        File keep = new File(base, "fail-" + seed);
        rm(keep);
        keep.mkdirs();
        restore(keep, image);
        rm(new File(base, "s" + seed));
    }

    /** The files of an image: the first's and each one's after a change of size or a gap, with its length. */
    static String layout(Map<String, byte[]> image) {
        StringBuilder b = new StringBuilder();
        long end = -1;
        int lastLength = -1;
        String lastName = null;
        for (Map.Entry<String, byte[]> e : image.entrySet()) {
            long start = Long.parseLong(e.getKey().substring(0, 14)) * 100000;
            boolean gap = end != -1 && start != end;
            if (gap || e.getValue().length != lastLength) {
                b.append(gap ? " GAP " : " ").append(start / 100000).append(":").append(e.getValue().length);
            }
            end = start + e.getValue().length;
            lastLength = e.getValue().length;
            lastName = e.getKey();
        }
        return b + " (to " + end + ", " + image.size() + " files)";
    }

    static String messages(Throwable e) {
        StringBuilder b = new StringBuilder();
        for (Throwable t = e; t != null; t = t.getCause()) {
            String m = String.valueOf(t.getMessage());
            b.append(t.getClass().getSimpleName()).append(": ").append(m, 0, Math.min(m.length(), 400)).append(" | ");
        }
        return b.toString();
    }

    static Map<String, byte[]> files(File dir) throws IOException {
        return new TreeMap<String, byte[]>(FileStreamPowerLossTester.streamFiles(dir));
    }

    static void restore(File dir, Map<String, byte[]> files) throws IOException {
        for (File f : dir.listFiles((d, name) -> name.endsWith(".bergdb"))) f.delete();
        for (Map.Entry<String, byte[]> e : files.entrySet()) {
            Files.write(new File(dir, e.getKey()).toPath(), e.getValue());
        }
    }

    static void rm(File f) {
        File[] c = f.listFiles();
        if (c != null) for (File x : c) rm(x);
        f.delete();
    }
}
