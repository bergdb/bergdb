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
 * bergdb 031-03's probe of its prototype (the branch 031-03-proto): w is a function of the
 * stream at every record. Two runs of one random workload (seed SEED), a without restarts
 * and b with a restart every EVERY operations, R = 1 s (or R + 1 unit, a setter toggles it),
 * startup distance SD, CutStream and a test clock. An operation: a transaction of puts or of
 * deletes, an empty transaction, a setter's record (the retain duration) or a maintain()
 * call; phases of writes with calls between, of calls alone, of an emptied database.
 *
 * Checked:
 *   1. after every operation, a and b: the same stream length, return of maintain() and w;
 *      at the end the same bytes (P2 over restarts between calls);
 *   2. for every CRASH-th record that a writes, whatever its kind (the application's, a
 *      step, a table, a take's, a filler's): a database started from the stream cut after
 *      that record has the w that a had after it (a crash or a stop anywhere); a record
 *      before the stream's length at a cut made in the same operation is skipped, as a
 *      cut waits for the stream to be durable to there;
 *   3. every record that a writes is reclaim's own by its keys (Reclaim.isOwnRecord) exactly
 *      when reclaim's maintenance wrote it (an internal transaction outside a setter).
 * Prints the bytes written in each idle phase, and the stream kept at the end.
 *
 * In package bergdb.core; on the class path before the jar (from java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT WitnessProbe.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.WitnessProbe SD EVERY CRASH SEED
 */
public class WitnessProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;

    static final class Run {
        CutStream stream = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        final int sd;
        Db db;
        int restarts;
        boolean longR;

        Run(int sd) {
            this.sd = sd;
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
    final int every, crash;
    final Random rnd;
    long ops, records, crashes, skipped, wrongW, wrongKind, ownRecords;
    boolean inSetter;
    final ArrayList<long[]> made = new ArrayList<long[]>();    // of an operation: {end, w}

    final Db.TestHooks hooks = new Db.TestHooks() {
        public void transExecuted(Db.ExecuteData x) {
            records++;
            final boolean own = Reclaim.isOwnRecord(x.transNodes);
            if (own) ownRecords++;
            if (own != (x.trans.isInternal() && !inSetter)) wrongKind++;
            if (records % crash == 0) {
                made.add(new long[] {x.trans.nextPos, a.db.internal().reclaim().appW});
            }
        }
        public void valueNodeCreated(ValueNode node, long[] key) {}
        public void nodeTouched(Node node) {}
        public void nodeReplaced(Node node) {}
    };

    WitnessProbe(int sd, int every, int crash, long seed) {
        a = new Run(sd);
        b = new Run(sd);
        this.every = every;
        this.crash = crash;
        rnd = new Random(seed);
    }

    /** The starts from a's stream cut after each record noted in the last operation. */
    void crashStarts() {
        if (made.isEmpty()) return;
        a.db.sync(SyncLevel.ORDINARY);
        for (long[] m : made) {
            CutStream copy = a.stream.copy();
            try {
                copy.truncate(m[0]);
            } catch (IllegalArgumentException e) {
                // Before the stream's length when the operation's cut was made: not a state
                // that a crash leaves, as a cut waits for the stream to be durable to there.
                skipped++;
                continue;
            }
            Db d = Db.builder().testSetup(copy).clock(a.clock).start();
            if (d.internal().reclaim().appW != m[1]) {
                wrongW++;
                if (wrongW < 5) System.out.println("  WRONG w after the record ending at " + m[0]
                        + ": the run's " + m[1] + ", the start's " + d.internal().reclaim().appW);
            }
            d.close();
            crashes++;
        }
        made.clear();
    }

    void before() {
        ops++;
        if (ops % every == 0) b.restart();
        for (Run r : new Run[] {a, b}) {
            r.time += MS;
            r.clock.setTime(r.time);
        }
    }

    void check(String what) {
        crashStarts();
        if (a.db.getStreamLength() != b.db.getStreamLength()) {
            throw new AssertionError(what + " " + ops + ": length " + a.db.getStreamLength() + " "
                    + b.db.getStreamLength());
        }
        long wa = a.db.internal().reclaim().appW, wb = b.db.internal().reclaim().appW;
        if (wa != wb) throw new AssertionError(what + " " + ops + ": w " + wa + " " + wb);
    }

    void trans(int from, int n, boolean delete, int round) {
        before();
        for (Run r : new Run[] {a, b}) {
            Trans.Builder t = r.db.trans();
            for (int i = from; i < from + n; i++) {
                if (delete) t.delete("/k/" + i);
                else { byte[] v = new byte[100]; v[0] = (byte) round; t.put("/k/" + i, v); }
            }
            Db.testHooks = r == a ? hooks : null;
            r.db.execute(t.build());
            Db.testHooks = null;
        }
        check(n == 0 ? "empty" : delete ? "delete" : "put");
    }

    void setter() {
        before();
        for (Run r : new Run[] {a, b}) {
            r.longR = !r.longR;
            inSetter = true;
            Db.testHooks = r == a ? hooks : null;
            r.db.setRetainDuration(r.longR ? SEC + 1 : SEC);
            Db.testHooks = null;
            inSetter = false;
        }
        check("setter");
    }

    boolean maintain() {
        before();
        Db.testHooks = hooks;
        boolean x = a.db.maintain();
        Db.testHooks = null;
        boolean y = b.db.maintain();
        if (x != y) throw new AssertionError("maintain " + ops + ": " + x + " " + y);
        check("maintain");
        return x;
    }

    /** n random operations: p percent of them maintain() calls. */
    void mixed(int n, int p, int keys, int round) {
        for (int i = 0; i < n; i++) {
            int x = rnd.nextInt(100);
            if (x < p) maintain();
            else if (x < p + 2) trans(0, 0, false, 0);
            else if (x < p + 3) setter();
            else if (x % 4 == 0) trans(rnd.nextInt(keys), 1 + rnd.nextInt(60), true, round);
            else trans(rnd.nextInt(keys), 1 + rnd.nextInt(60), false, round);
        }
    }

    long idle(String name, int calls) {
        long len = a.db.getStreamLength(), last = -1;
        for (int i = 0; i < calls; i++) {
            long l = a.db.getStreamLength();
            if (maintain() || a.db.getStreamLength() != l) last = i;
        }
        System.out.println(name + ": " + calls + " calls wrote " + (a.db.getStreamLength() - len)
                + ", the last with work " + last + "; kept "
                + (a.db.getStreamLength() - a.db.getFirstAvailablePos()));
        return a.db.getStreamLength() - len;
    }

    void run() throws IOException {
        mixed(1500, 30, 3000, 1);
        idle("idle 1", 4000);
        long q = idle("idle 1b", 2000);
        // One empty transaction, then one setter's record, each followed by calls alone.
        trans(0, 0, false, 0);
        idle("after an empty transaction", 3000);
        setter();
        idle("after a setter", 3000);
        // Writes with few calls (iterations wait), then calls alone.
        mixed(600, 5, 3000, 2);
        idle("idle 2", 5000);
        long q2 = idle("idle 2b", 2000);
        // Emptied: every key deleted, with calls between; then calls alone.
        for (int i = 0; i < 3060; i += 60) { trans(i, 60, true, 0); if (i % 300 == 0) maintain(); }
        idle("emptied", 6000);
        long q3 = idle("emptied b", 2000);
        if (!Arrays.equals(a.bytes(), b.bytes())) throw new AssertionError("bytes differ");
        System.out.println("SAME STREAM: ops " + ops + ", restarts " + b.restarts + ", length "
                + a.db.getStreamLength() + ", fp " + a.db.getFirstAvailablePos() + ", w "
                + a.db.internal().reclaim().appW + "; records " + records + " (" + ownRecords
                + " reclaim's own), " + wrongKind + " of another kind than their keys say; "
                + crashes + " starts after a record, " + wrongW + " with another w, " + skipped
                + " records before a cut's durable length skipped");
        a.db.close();
        b.db.close();
        if (wrongW != 0 || wrongKind != 0 || q != 0 || q2 != 0 || q3 != 0) {
            throw new AssertionError("WITNESS FAILED");
        }
    }

    public static void main(String[] args) throws Exception {
        new WitnessProbe(Integer.parseInt(args[0]), Integer.parseInt(args[1]),
                Integer.parseInt(args[2]), Long.parseLong(args[3])).run();
        System.out.println("WITNESS OK");
    }
}
