package bergdb.core;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.ArrayList;
import java.util.Random;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * bergdb 031-03's review probe, run through the shim M by 031-04's review (Codex): a
 * stream written with main's or 2026.6's jar ("write"), then opened with the prototype's
 * ("open"). "write FILE SEED N SD": N random operations (puts, deletes, empty
 * transactions, setters, maintain() calls), the stream and the clock saved to FILE. "open
 * FILE SEED N": loads it, then N random operations with, after each, a start from the stream
 * cut after each of its records (its w against the run's); then 6 R of calls alone, every key
 * deleted, 8 R of calls alone; prints the stream kept.
 *   java -ea -cp out:main.jar bergdb.core.UpgradeProbe write F 314 250 10000
 *   java -ea -cp out:bergdb.jar bergdb.core.UpgradeProbe open F 2718 250
 */
public class UpgradeProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static CutStream stream;
    static final CoreTestClock clock = new CoreTestClock();
    static long time;
    static Db db;
    static Random rnd;
    static final ArrayList<long[]> made = new ArrayList<long[]>();
    static long starts, wrong, skipped;

    static final Db.TestHooks HOOKS = new Db.TestHooks() {
        public void transExecuted(Db.ExecuteData x) {
            made.add(new long[] {x.trans.nextPos, M.appW(db)});
        }
        public void valueNodeCreated(ValueNode n, long[] k) {}
        public void nodeTouched(Node n) {}
        public void nodeReplaced(Node n) {}
    };

    static void tick(long dt) { time += dt; clock.setTime(time); }

    static void check(boolean on) {
        if (!on) { made.clear(); return; }
        db.sync(SyncLevel.ORDINARY);
        for (long[] m : made) {
            CutStream c = stream.copy();
            try { c.truncate(m[0]); } catch (IllegalArgumentException e) { skipped++; continue; }
            Db d = Db.builder().testSetup(c).clock(clock).start();
            if (M.appW(d) != m[1]) {
                wrong++;
                if (wrong < 10) System.out.println("  WRONG w at " + m[0] + ": run " + m[1]
                        + " start " + M.appW(d));
            }
            starts++;
            d.close();
        }
        made.clear();
    }

    static void op(boolean checks) {
        int x = rnd.nextInt(100);
        Db.testHooks = HOOKS;
        if (x < 40) { tick(MS); M.call(db); }
        else if (x < 43) { tick(SEC / 4); M.call(db); }
        else if (x < 46) { tick(MS); db.execute(db.trans().build()); }
        else if (x < 48) { tick(MS); db.setRetainDuration(rnd.nextBoolean() ? SEC : SEC + 1); }
        else {
            tick(MS);
            Trans.Builder b = db.trans();
            int from = rnd.nextInt(2000), n = 1 + rnd.nextInt(60);
            boolean del = x % 4 == 0;
            for (int i = from; i < from + n; i++) {
                if (del) b.delete("/k/" + i); else b.put("/k/" + i, new byte[100 + rnd.nextInt(400)]);
            }
            db.execute(b.build());
        }
        Db.testHooks = null;
        check(checks);
    }

    static long idle(String name, int calls) {
        long len = db.getStreamLength(), last = -1;
        for (int i = 0; i < calls; i++) {
            long l = db.getStreamLength();
            Db.testHooks = HOOKS;
            tick(MS);
            boolean more = M.call(db);
            Db.testHooks = null;
            check(true);
            if (more || db.getStreamLength() != l) last = i;
        }
        System.out.println(name + ": wrote " + (db.getStreamLength() - len) + ", last work " + last
                + ", kept " + (db.getStreamLength() - db.getFirstAvailablePos()) + ", w "
                + M.appW(db) + ", fp " + db.getFirstAvailablePos());
        return db.getStreamLength() - db.getFirstAvailablePos();
    }

    public static void main(String[] a) throws Exception {
        File f = new File(a[1]);
        rnd = new Random(Long.parseLong(a[2]));
        int n = Integer.parseInt(a[3]);
        if (a[0].equals("writefill")) {
            // main's mode: R = 1 s, sd 10, some puts, then calls; stopped right after the first
            // filler put, so that -fill.txt stays live.
            time = SEC;
            clock.setTime(time);
            stream = new CutStream();
            db = Db.builder().testSetup(stream).clock(clock).start();
            db.setStartupDistance(Integer.parseInt(a[4]));
            db.setRetainDuration(SEC);
            final long[] fillKey = bergdb.dag.Keys.toSegments("/#i/dreclaim/-fill.txt");
            Db.testHooks = new Db.TestHooks() {
                public void transExecuted(Db.ExecuteData x) {
                    for (int i = 0; i < x.transNodes.valueCount; i++) {
                        if (java.util.Arrays.equals(fillKey, x.transNodes.keys[i])
                                && x.transNodes.valueNodes[i].getValue() != null
                                && x.transNodes.valueNodes[i].getValue().length > 0) {
                            System.out.println("stop after the filler put at " + x.trans.tpos);
                            db.stop();
                        }
                    }
                }
                public void valueNodeCreated(ValueNode n, long[] k) {}
                public void nodeTouched(Node n) {}
                public void nodeReplaced(Node n) {}
            };
            try {
                for (int i = 0; i < n; i++) { tick(MS); db.execute(db.trans().put("/k/" + i, new byte[200]).build()); }
                for (int i = 0; i < 5000; i++) { tick(MS); M.call(db); }
            } catch (RuntimeException e) {
                System.out.println("stopped: " + e.getClass().getSimpleName());
            }
            Db.testHooks = null;
            db.close();
            a[0] = "dump";
        }
        if (a[0].equals("dump") || a[0].equals("write")) {
          if (a[0].equals("write")) {
            time = SEC;
            clock.setTime(time);
            stream = new CutStream();
            db = Db.builder().testSetup(stream).clock(clock).start();
            db.setStartupDistance(Integer.parseInt(a[4]));
            db.setRetainDuration(SEC);
            for (int i = 0; i < n; i++) op(false);
            db.close();
          }
            long first = stream.getFirstPos(), len = stream.getLength();
            byte[] b = new byte[(int) (len - first)];
            stream.read(first, b, 0, b.length);
            try (DataOutputStream out = new DataOutputStream(new FileOutputStream(f))) {
                out.writeLong(time);
                out.writeLong(first);
                out.writeInt(b.length);
                out.write(b);
            }
            System.out.println("written (mode " + M.MAIN + "): first " + first + ", length " + len);
            return;
        }
        long first;
        byte[] b;
        try (DataInputStream in = new DataInputStream(new FileInputStream(f))) {
            time = in.readLong();
            first = in.readLong();
            b = new byte[in.readInt()];
            in.readFully(b);
        }
        clock.setTime(time);
        stream = new CutStream();
        stream.append(new byte[(int) first], 0, (int) first);
        stream.append(b, 0, b.length);
        if (first > 0) stream.pretruncate(first);
        db = Db.builder().testSetup(stream).clock(clock).start();
        final long[] fk = bergdb.dag.Keys.toSegments("/#i/dreclaim/-fill.txt");
        System.out.println("fill live at the open: " + (db.getOne(Long.MAX_VALUE, fk, db.newGetData()) != null));
        System.out.println("opened (mode " + M.MAIN + "): w " + M.appW(db)
                + ", length " + db.getStreamLength() + ", fp " + db.getFirstAvailablePos());
        for (int i = 0; i < n; i++) op(true);
        idle("idle", 6000);
        for (int i = 0; i < 2060; i += 60) {
            Trans.Builder t = db.trans();
            for (int k = i; k < i + 60; k++) t.delete("/k/" + k);
            Db.testHooks = HOOKS;
            tick(MS);
            db.execute(t.build());
            Db.testHooks = null;
            check(true);
        }
        idle("emptied", 8000);
        System.out.println("fill live at the end: " + (db.getOne(Long.MAX_VALUE, fk, db.newGetData()) != null));
        System.out.println("starts " + starts + ", wrong w " + wrong + ", skipped " + skipped);
        db.close();
    }
}
