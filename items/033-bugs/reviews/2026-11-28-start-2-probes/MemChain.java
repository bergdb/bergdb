package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Review probe (bergdb 033, the second review of the start, 2026-11-28): StartChain's chains
 * of faults on a MemoryStream, through the Core API (no created.txt, no files). MemoryStream
 * keeps every byte that it is given: zeros after a kill stay in the stream (FileStream's open
 * leaves a run of them at the end of the last file out), and its cut takes off whole arrays
 * of 1 MB, so the stream's first block after a cut is at a multiple of 1,000,000.
 *
 * A chain is a seed. Each step starts the database on a copy of what the step before left
 * (a start must not refuse it, and every key must read as the model says), then stops it, or
 * writes commits (reclaim cuts as the clock moves), and then makes a fault on a copy:
 *
 * - kill: the stream cut at a position c at or after the end of the record that decided the
 *   last cut made (StartChain's rule), near the last record's start, in it, at, in and after
 *   a meta block;
 * - kill during the start's own writes: after a start and a stop with no commit, the stream
 *   cut inside what the start's recovery appended;
 * - ZERO_PERCENT of the kills: zeros after c, within the bytes that the stream held;
 * - STALE_PERCENT of the kills: other bytes after c, within the bytes that the stream held
 *   (random bytes, or the stream's own bytes of 4,096 or 8,192 before), a third of them
 *   after a run of zeros.
 *
 * After zeros or other bytes the start must take the stream as cut at c, or refuse it with a
 * BadTailException and the stream unchanged; the probe then cuts the stream at the P of the
 * exception, as its message says, and the next start must hold what the stream held at c
 * (or also the record that the kill cut in its padding or at its last byte, if the other
 * bytes end it with the byte 10). Every other refusal, a wrong value, and a refused start
 * that changed the stream is a failure, printed with the chain's steps; a refusal in a
 * later step of a chain that has taken zeros or other bytes is printed and counted apart
 * ("later").
 *
 * It uses StartChain2's choice of a kill's position (with -Dshapes=on more kills come 1 to 8
 * bytes into a meta block), its values and its reading of a refusal.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/StartChain2.java PROBES/MemChain.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.MemChain FIRST_SEED LAST_SEED STEPS
 *       [STALE_PERCENT [ZERO_PERCENT]]
 */
public class MemChain {
    static final long SEC = FileStreamPowerLossTester.SEC;
    static final int KEYS = 12;
    static final long MD = 200000;

    static class Entry {
        long lastPos; String key; byte[] value;
        Entry(long lastPos, String key, byte[] value) { this.lastPos = lastPos; this.key = key; this.value = value; }
    }

    static int starts, failures, later;
    static int stalePercent = 0, zeroPercent = 0;
    static TreeMap<String, Integer> kinds = new TreeMap<String, Integer>();

    public static void main(String[] args) throws Exception {
        long first = Long.parseLong(args[0]), last = Long.parseLong(args[1]);
        int steps = Integer.parseInt(args[2]);
        if (args.length > 3) stalePercent = Integer.parseInt(args[3]);
        if (args.length > 4) zeroPercent = Integer.parseInt(args[4]);
        for (long seed = first; seed <= last; seed++) {
            try {
                chain(seed, steps);
            } catch (Throwable e) {
                failures++;
                System.out.println("FAIL seed " + seed + ": the probe threw " + e);
                e.printStackTrace(System.out);
            }
            if (seed % 20 == 0) System.out.println("at seed " + seed + ": starts " + starts + ", " + kinds
                    + ", later " + later + ", failures " + failures);
        }
        System.out.println("MEMCHAIN DONE seeds " + first + ".." + last + ": starts " + starts + ", " + kinds
                + ", later " + later + ", failures " + failures);
    }

    static String key(int i) { return "/chain/key-" + i; }

    static void count(String kind) { kinds.merge(kind, 1, Integer::sum); }

    static byte[] dump(MemoryStream s) throws IOException {
        long first = s.getFirstPos(), length = s.getLength();
        byte[] b = new byte[(int) (length - first) + 16];
        bergdb.common.Bytes.longToBytesLE(first, b, 0);
        bergdb.common.Bytes.longToBytesLE(length, b, 8);
        if (length > first) s.read(first, b, 16, (int) (length - first));
        return b;
    }

    static void chain(long seed, int steps) throws Exception {
        Random r = new Random(seed);
        TreeMap<String, byte[]> model = new TreeMap<String, byte[]>();
        List<String> ops = new ArrayList<String>();
        long time = SEC;
        CoreTestClock clock = new CoreTestClock();
        MemoryStream image = new MemoryStream();
        boolean tainted = false;        // this step's image has zeros or other bytes after its kill
        boolean tookOther = false;      // the chain has had such an image
        long taintEnd = -1;
        Entry lastByteCut = null;
        for (int step = 0; step < steps; step++) {
            while (ops.size() > 50) ops.remove(0);
            int action = step == 0 ? 1 : r.nextInt(115) - 15;       // < 0 stop; else run, kill
            MemoryStream s = null;
            Db db = null;
            long before = -1;
            time += SEC;
            clock.setTime(time);
            while (true) {
                byte[] was = dump(image);
                s = image.copy();
                before = s.getLength();
                try {
                    db = Db.builder().testSetup(s).clock(clock).start();
                    db.setStartupDistance(20000);
                    db.setRetainDuration(2 * SEC);
                    break;
                } catch (Throwable e) {
                    String m = StartChain2.messages(e);
                    boolean changed = !Arrays.equals(was, dump(s));
                    bergdb.storage.BadTailException tail = StartChain2.badTail(e);
                    if (tainted && !changed && tail != null) {
                        long p = tail.getCutPos();
                        count("refused-with-P");
                        if (p > taintEnd || p < image.getFirstPos()) {
                            fail(seed, step, ops, "P " + p + " outside the stream: " + m);
                            return;
                        }
                        ops.add("refused, BadTailException; the stream cut at its P, " + p + ": "
                                + m.substring(0, Math.min(m.length(), 200)));
                        image = image.copy();
                        image.truncate(p);
                        tainted = false;
                        continue;
                    }
                    if (tookOther && !tainted && !changed) {
                        later++;
                        System.out.println("LATER seed " + seed + ", step " + step + ": refused after zeros or"
                                + " other bytes were taken: " + m);
                        for (String op : ops) System.out.println("    " + op);
                        return;
                    }
                    fail(seed, step, ops, "start refused" + (changed ? " AND CHANGED THE STREAM" : "") + ": " + m);
                    return;
                }
            }
            starts++;
            if (tainted) count("taken");
            tainted = false;
            long after = db.getStreamLength();
            String wrong = null;
            try {
                if (lastByteCut != null && !Arrays.equals(DbUtil.get(db, Long.MAX_VALUE, lastByteCut.key),
                        model.get(lastByteCut.key))) {
                    if (lastByteCut.value == null) model.remove(lastByteCut.key);
                    else model.put(lastByteCut.key, lastByteCut.value);
                    count("last-byte-10");
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
                wrong = "read threw " + StartChain2.messages(e);
            }
            if (wrong != null) {
                db.close();
                fail(seed, step, ops, "wrong after start: " + wrong);
                return;
            }

            List<Entry> entries = new ArrayList<Entry>();
            long floor = after;
            long lastFirst = s.getFirstPos();
            ops.add("      step " + step + ": started, the stream " + lastFirst + " to " + after + " (" + before
                    + " at the open), reclaim's cut " + db.getFirstAvailablePos());
            String op;
            if (action < 0) {
                op = "stop";
            } else {
                int n = 20 + r.nextInt(300);
                boolean straddle = r.nextInt(3) == 0;
                for (int i = 0; i < n || (straddle && i < n + 400); i++) {
                    long len = db.getStreamLength();
                    boolean big = false;
                    int size = 300 + r.nextInt(2700);
                    if (i >= n) {
                        if (len % MD > 180000) { size = 25000 + r.nextInt(20000); big = true; }
                    } else if (r.nextInt(100) < 2) {
                        size = 210000 + r.nextInt(500000);
                    }
                    time += SEC / 10;
                    clock.setTime(time);
                    String key = key(r.nextInt(KEYS));
                    byte[] value = r.nextInt(100) < 5 ? null : StartChain2.value(r, size);
                    Trans t = value == null ? db.trans().delete(key).build() : db.trans().put(key, value).build();
                    long pending = db.internal().reclaim().pendingCutDurableAt();
                    long cutBefore = db.getFirstAvailablePos();
                    db.execute(t);
                    entries.add(new Entry(t.lastPos, key, value));
                    long cutNow = db.getFirstAvailablePos();
                    if (s.getFirstPos() != lastFirst) {
                        lastFirst = s.getFirstPos();
                        floor = Math.max(floor, pending != -1 && cutNow == cutBefore ? pending : t.nextPos);
                    }
                    if (s.getFirstPos() > cutNow) {
                        db.close();
                        fail(seed, step, ops, "THE STREAM BEGINS AFTER RECLAIM'S CUT: " + s.getFirstPos() + ", " + cutNow);
                        return;
                    }
                    if (big) break;
                }
                op = "run " + entries.size();
            }
            db.sync(SyncLevel.ORDINARY);
            long end = db.getStreamLength();
            if (s.getFirstPos() != lastFirst) floor = end;
            db.close();

            // The fault.
            long c = end;
            if (action < 0) {
                if (after > before && before > 0 && r.nextInt(5) != 0) {
                    c = StartChain2.pick(r, before, after, before);
                    op += ", kill in the recovery's writes [" + before + ", " + after + ") at " + c;
                    count("kill-in-recovery");
                }
            } else if (r.nextInt(8) != 0 && floor < end) {
                long lastRecord = entries.isEmpty() ? floor : Math.max(floor, entries.size() > 1
                        ? entries.get(entries.size() - 2).lastPos + 1 : floor);
                c = StartChain2.pick(r, floor, end, lastRecord);
                op += ", kill at " + c + " of " + end;
                count("kill");
            }
            image = s.copy();
            boolean other = false;
            if (c < end) {
                image.truncate(c);
                int room = (int) Math.min(end - c, 2000000);
                int roll = r.nextInt(100);
                if (roll < stalePercent) {
                    int g = r.nextBoolean() ? room : 1 + r.nextInt(room);
                    byte[] bytes = new byte[g];
                    String what;
                    if (r.nextBoolean()) {
                        r.nextBytes(bytes);
                        what = "random bytes";
                    } else {
                        int shift = 4096 * (1 + r.nextInt(2));
                        long from = Math.max(s.getFirstPos(), c - shift);
                        int n = (int) Math.min(g, end - from);
                        s.read(from, bytes, 0, n);
                        what = "the stream's own bytes of " + shift + " before";
                    }
                    if (g > 1 && r.nextInt(3) == 0) {
                        int z = r.nextBoolean() ? 1 + r.nextInt(g - 1)
                                : (int) Math.min(g - 1, (4096 - c % 4096) % 4096 + 4096 * r.nextInt(60));
                        Arrays.fill(bytes, 0, z, (byte) 0);
                        what = z + " zeros first, then " + what;
                    }
                    image.append(bytes, 0, g);
                    op += ", then " + g + " other bytes: " + what;
                    count("stale");
                    other = true;
                    tainted = true;
                } else if (roll < stalePercent + zeroPercent) {
                    int z = r.nextInt(3) == 0 ? room : r.nextBoolean() ? 1 + r.nextInt(Math.min(room, 5000))
                            : (int) Math.min(room, (4096 - c % 4096) % 4096 + 4096 * r.nextInt(80));
                    if (z > 0) {
                        image.append(new byte[z], 0, z);
                        op += ", " + z + " zeros after it";
                        count("zeros");
                        tainted = true;
                    }
                }
            }
            if (tainted) {
                tookOther = true;
                taintEnd = image.getLength();
            }
            lastByteCut = null;
            for (Entry e : entries) {
                if (e.lastPos < c) {
                    if (e.value == null) model.remove(e.key); else model.put(e.key, e.value);
                } else if (other && lastByteCut == null && c > e.lastPos - 8) {
                    lastByteCut = e;
                }
            }
            ops.add(step + ": " + op);
        }
    }

    static void fail(long seed, int step, List<String> ops, String what) {
        failures++;
        System.out.println("FAIL seed " + seed + ", step " + step + ": " + what);
        for (String op : ops) System.out.println("    " + op);
    }
}
