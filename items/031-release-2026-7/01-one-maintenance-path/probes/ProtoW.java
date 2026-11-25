package bergdb.core;

import java.io.IOException;
import java.util.Arrays;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-01's probe of its prototype (the branch 031-01-proto), from 028-53's ProtoA:
 * the same stream over restarts. Two runs of one workload, a without restarts and b with a restart every EVERY
 * operations (a transaction or a maintain() call), R = 1 s, startup distance SD, CutStream
 * and a test clock: 3,000 values of 100 bytes overwritten in 7 rounds with calls between,
 * 3 R of calls, 5,000 keys put and deleted with calls between, 9 R of calls, the 3,000
 * deleted, 8 R of calls. After every operation the same stream length, the same return of
 * maintain() and the same w in memory and as stored (Reclaim.appW, appWStored); at the end
 * the same bytes. Needs the prototype's fields: it does not compile against main.
 *
 * In package bergdb.core; on the class path before the jar (from java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT ProtoW.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.ProtoW SD EVERY
 * 031-01 ran SD 5000, 50000, 200000 and 1000000 with EVERY 7, 23 and 101.
 */
public class ProtoW {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;

    static final class Run {
        CutStream stream = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        final int sd;
        Db db;
        Reclaim.Stats stats;
        int restarts;

        Run(int sd) {
            this.sd = sd;
            clock.setTime(time);
            start();
            db.setRetainDuration(SEC);
        }

        void start() {
            db = Db.builder().testSetup(stream).clock(clock).start();
            db.setStartupDistance(sd);
            synchronized (db.internal().getWriteLock()) {
                stats = db.internal().reclaim().enableStats();
            }
        }

        void restart() {
            db.close();
            stream = stream.copy();
            start();
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
    final int k;
    long ops, protoStores;

    ProtoW(int sd, int k) {
        a = new Run(sd);
        b = new Run(sd);
        this.k = k;
    }

    void check(String what) {
        if (a.db.getStreamLength() != b.db.getStreamLength()) {
            throw new AssertionError(what + ": length " + a.db.getStreamLength() + " " + b.db.getStreamLength());
        }
        Reclaim ra = a.db.internal().reclaim(), rb = b.db.internal().reclaim();
        if (ra.appW != rb.appW || ra.appWStored != rb.appWStored) {
            throw new AssertionError(what + ": w " + ra.appW + " " + rb.appW + ", stored "
                    + ra.appWStored + " " + rb.appWStored);
        }
    }

    void before() {
        ops++;
        if (ops % k == 0) b.restart();
        for (Run r : new Run[] {a, b}) {
            r.time += MS;
            r.clock.setTime(r.time);
        }
    }

    void trans(int from, int to, boolean delete, int round) {
        before();
        for (Run r : new Run[] {a, b}) {
            Trans.Builder t = r.db.trans();
            for (int i = from; i < to; i++) {
                if (delete) t.delete("/k/" + i);
                else { byte[] v = new byte[100]; v[0] = (byte) round; t.put("/k/" + i, v); }
            }
            r.db.execute(t.build());
        }
        check("trans " + ops);
    }

    boolean maintain() {
        before();
        boolean x = a.db.maintain(), y = b.db.maintain();
        if (x != y) throw new AssertionError("maintain " + ops + ": " + x + " " + y);
        check("maintain " + ops);
        return x;
    }

    void run() throws IOException {
        // Live values, overwritten in rounds, with calls between the commits.
        for (int round = 0; round < 7; round++) {
            for (int i = 0; i < 3000; i += 100) {
                trans(i, i + 100, false, round);
                if (i % 700 == 0) maintain();
            }
        }
        // Idle: the calls alone.
        long len = a.db.getStreamLength();
        for (int i = 0; i < 3000; i++) maintain();
        System.out.println("idle 1: wrote " + (a.db.getStreamLength() - len));
        // Writes while iterations run or wait (RB-007's kind), then idle again.
        for (int i = 10000; i < 15000; i += 100) trans(i, i + 100, false, 0);
        for (int i = 0; i < 50; i++) maintain();
        for (int i = 10000; i < 15000; i += 100) { trans(i, i + 100, true, 0); if (i % 500 == 0) maintain(); }
        len = a.db.getStreamLength();
        for (int i = 0; i < 6000; i++) maintain();
        System.out.println("idle 2: wrote " + (a.db.getStreamLength() - len));
        len = a.db.getStreamLength();
        for (int i = 0; i < 3000; i++) maintain();
        System.out.println("idle 3: wrote " + (a.db.getStreamLength() - len));
        // Emptied, then idle.
        for (int i = 0; i < 3000; i += 100) trans(i, i + 100, true, 0);
        for (int i = 0; i < 8000; i++) maintain();
        System.out.println("emptied: kept " + (a.db.getStreamLength() - a.db.getFirstAvailablePos()));
        if (!Arrays.equals(a.bytes(), b.bytes())) throw new AssertionError("bytes differ");
        System.out.println("SAME STREAM: ops " + ops + ", restarts " + b.restarts + ", length "
                + a.db.getStreamLength() + ", fp " + a.db.getFirstAvailablePos()
                + ", w " + a.db.internal().reclaim().appW);
        a.db.close();
        b.db.close();
    }

    public static void main(String[] args) throws Exception {
        new ProtoW(Integer.parseInt(args[0]), Integer.parseInt(args[1])).run();
    }
}
