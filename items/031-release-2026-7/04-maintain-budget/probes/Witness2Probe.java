package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Random;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * Adapted for bergdb 031-04: maintain() calls through M (maintain(B) on the
 * prototype, maintain() on main), w through M.appW.
 *
 * bergdb 031-03's review probe: WitnessProbe with more kinds of operations. a without restarts, b restarted
 * every EVERY operations; after every record of a, a start from a's stream cut there must
 * have a's w. Operations: puts of small, tiny, large (300 kB to 1.2 MB) values, deletes, empty
 * transactions, setRetainDuration (1 s, 1 s + 1, forever), setStartupDistance (10, 10 kB,
 * 200 kB, 5 MB), maintain() calls, time jumps (R/4, R).
 *   java -ea -cp out:bergdb.jar bergdb.core.Witness2Probe SD EVERY SEED OPS
 */
public class Witness2Probe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final long[] RS = {SEC, SEC + 1, Long.MAX_VALUE, SEC};
    static final int[] SDS = {10, 10000, 200000, 5000000};

    static final class Run {
        CutStream stream = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        Db db;
        int restarts;

        Run(int sd) {
            clock.setTime(time);
            db = Db.builder().testSetup(stream).clock(clock).start();
            db.setStartupDistance(sd);
            db.setRetainDuration(SEC);
        }

        void restart() {
            db.close();
            stream = stream.copy();
            db = Db.builder().testSetup(stream).clock(clock).start();
            restarts++;
        }

        byte[] bytes() throws IOException {
            long first = stream.getFirstPos();
            byte[] b = new byte[(int) (stream.getLength() - first)];
            stream.read(first, b, 0, b.length);
            return b;
        }
    }

    final Run a, b;
    final int every;
    final Random rnd;
    long ops, records, crashes, skipped, wrongW, wrongKind, ownRecords;
    int ri, si;
    boolean inSetter;
    final ArrayList<long[]> made = new ArrayList<long[]>();

    final Db.TestHooks hooks = new Db.TestHooks() {
        public void transExecuted(Db.ExecuteData x) {
            records++;
            final boolean own = Reclaim.isOwnRecord(x.transNodes);
            if (own) ownRecords++;
            if (own != (x.trans.isInternal() && !inSetter)) {
                wrongKind++;
                if (wrongKind < 10) System.out.println("  KIND op " + ops + " own " + own + " internal "
                        + x.trans.isInternal() + " inSetter " + inSetter + " values " + x.transNodes.valueCount
                        + " keys " + keysOf(x.transNodes) + " tpos " + x.trans.tpos);
            }
            inSetter = false;   // only a setter call's first record is the setter's
            made.add(new long[] {x.trans.nextPos, M.appW(a.db), own ? 1 : 0});
        }
        public void valueNodeCreated(ValueNode node, long[] key) {}
        public void nodeTouched(Node node) {}
        public void nodeReplaced(Node node) {}
    };

    static String keysOf(TransNodes n) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < n.valueCount; i++) b.append(Arrays.toString(n.keys[i])).append(' ');
        return b.toString();
    }

    Witness2Probe(int sd, int every, long seed) {
        a = new Run(sd);
        b = new Run(sd);
        this.every = every;
        rnd = new Random(seed);
    }

    void crashStarts(String what) {
        if (made.isEmpty()) return;
        a.db.sync(SyncLevel.ORDINARY);
        for (long[] m : made) {
            CutStream copy = a.stream.copy();
            try {
                copy.truncate(m[0]);
            } catch (IllegalArgumentException e) {
                skipped++;
                continue;
            }
            Db d = Db.builder().testSetup(copy).clock(a.clock).start();
            if (M.appW(d) != m[1]) {
                wrongW++;
                if (wrongW < 10) System.out.println("  WRONG w after " + what + " op " + ops
                        + ", record ending at " + m[0] + " (own " + m[2] + "): the run's " + m[1]
                        + ", the start's " + M.appW(d));
            }
            d.close();
            crashes++;
        }
        made.clear();
    }

    void before(long dt) {
        ops++;
        if (ops % every == 0) b.restart();
        for (Run r : new Run[] {a, b}) {
            r.time += dt;
            r.clock.setTime(r.time);
        }
    }

    void check(String what) {
        crashStarts(what);
        if (a.db.getStreamLength() != b.db.getStreamLength()) {
            throw new AssertionError(what + " " + ops + ": length " + a.db.getStreamLength() + " "
                    + b.db.getStreamLength());
        }
        long wa = M.appW(a.db), wb = M.appW(b.db);
        if (wa != wb) throw new AssertionError(what + " " + ops + ": w " + wa + " " + wb);
    }

    void trans(int from, int n, boolean delete, int size) {
        before(MS);
        for (Run r : new Run[] {a, b}) {
            Trans.Builder t = r.db.trans();
            for (int i = from; i < from + n; i++) {
                if (delete) t.delete("/k/" + i);
                else t.put("/k/" + i, new byte[size]);
            }
            Db.testHooks = r == a ? hooks : null;
            r.db.execute(t.build());
            Db.testHooks = null;
        }
        check(n == 0 ? "empty" : delete ? "delete" : "put");
    }

    void big(boolean delete) {
        int key = rnd.nextInt(3);
        int size = 300000 + rnd.nextInt(900000);
        before(MS);
        for (Run r : new Run[] {a, b}) {
            Db.testHooks = r == a ? hooks : null;
            if (delete) r.db.execute(r.db.trans().delete("/big/" + key).build());
            else r.db.execute(r.db.trans().put("/big/" + key, new byte[size]).build());
            Db.testHooks = null;
        }
        check(delete ? "big delete" : "big put");
    }

    void retain() {
        before(MS);
        ri = (ri + 1) % RS.length;
        for (Run r : new Run[] {a, b}) {
            inSetter = true;
            Db.testHooks = r == a ? hooks : null;
            r.db.setRetainDuration(RS[ri]);
            Db.testHooks = null;
            inSetter = false;
        }
        check("retain " + RS[ri]);
    }

    void sd() {
        before(MS);
        si = (si + 1) % SDS.length;
        for (Run r : new Run[] {a, b}) {
            inSetter = true;
            Db.testHooks = r == a ? hooks : null;
            r.db.setStartupDistance(SDS[si]);
            Db.testHooks = null;
            inSetter = false;
        }
        check("sd " + SDS[si]);
    }

    boolean maintain(long dt) {
        before(dt);
        Db.testHooks = hooks;
        boolean x = M.call(a.db);
        Db.testHooks = null;
        boolean y = M.call(b.db);
        if (x != y) throw new AssertionError("maintain " + ops + ": " + x + " " + y);
        check("maintain");
        return x;
    }

    void mixed(int n, int keys) {
        for (int i = 0; i < n; i++) {
            int x = rnd.nextInt(100);
            if (x < 35) maintain(MS);
            else if (x < 38) maintain(SEC / 4);
            else if (x < 40) maintain(SEC + MS);
            else if (x < 43) trans(0, 0, false, 0);
            else if (x < 45) retain();
            else if (x < 47) sd();
            else if (x < 49) big(false);
            else if (x < 51) big(true);
            else if (x < 55) trans(rnd.nextInt(keys), 1 + rnd.nextInt(30), false, rnd.nextInt(2));
            else if (x % 4 == 0) trans(rnd.nextInt(keys), 1 + rnd.nextInt(60), true, 0);
            else trans(rnd.nextInt(keys), 1 + rnd.nextInt(60), false, 100 + rnd.nextInt(400));
        }
    }

    void idle(String name, int calls) {
        long len = a.db.getStreamLength(), last = -1;
        for (int i = 0; i < calls; i++) {
            long l = a.db.getStreamLength();
            if (maintain(MS) || a.db.getStreamLength() != l) last = i;
        }
        System.out.println(name + ": " + calls + " calls wrote " + (a.db.getStreamLength() - len)
                + ", the last with work " + last + "; kept "
                + (a.db.getStreamLength() - a.db.getFirstAvailablePos()) + " w "
                + M.appW(a.db) + " fp " + a.db.getFirstAvailablePos());
    }

    void run(int n) throws IOException {
        mixed(n, 2000);
        // Finite R for the idle phases.
        while (RS[ri] == Long.MAX_VALUE) retain();
        idle("idle", 6000);
        idle("idle b", 2000);
        for (int i = 0; i < 2000; i += 60) trans(i, 60, true, 0);
        for (int k = 0; k < 3; k++) {
            before(MS);
            for (Run r : new Run[] {a, b}) {
                Db.testHooks = r == a ? hooks : null;
                r.db.execute(r.db.trans().delete("/big/" + k).build());
                Db.testHooks = null;
            }
            check("big delete");
        }
        idle("emptied", 8000);
        idle("emptied b", 2000);
        if (!Arrays.equals(a.bytes(), b.bytes())) throw new AssertionError("bytes differ");
        System.out.println("SAME STREAM: ops " + ops + ", restarts " + b.restarts + ", records "
                + records + " (" + ownRecords + " own), wrongKind " + wrongKind + "; " + crashes
                + " starts, " + wrongW + " with another w, " + skipped + " skipped");
        a.db.close();
        b.db.close();
        if (wrongW != 0 || wrongKind != 0) throw new AssertionError("WITNESS2 FAILED");
    }

    public static void main(String[] args) throws Exception {
        new Witness2Probe(Integer.parseInt(args[0]), Integer.parseInt(args[1]),
                Long.parseLong(args[2])).run(Integer.parseInt(args[3]));
        System.out.println("WITNESS2 OK");
    }
}
