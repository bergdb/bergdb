package bergdb.core;

import java.lang.reflect.Field;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 028-53's probe: 028-51's IdleLiveProbe (LIVE keys put, ROUNDS rounds of
 * overwrites, then RS R of maintain() calls, one a millisecond; R = 1 s, MemoryStream, a
 * test clock), printing reclaim's table whenever a row begins, ends, becomes safe or is cut:
 * the call, the stream length and fp in kB, and per row its pStart (S), pCut (C), rewritten
 * (rw, kB), kvCount, done (D) and cut (X). It shows the rows of a database not written to
 * rewriting the live values in two alternating halves.
 *
 * As IdleLiveProbe, on the class path before the jar (from java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT RowsProbe.java
 *   java -cp OUT:build/bergdb.jar bergdb.core.RowsProbe LIVE SD RS [ROUNDS]
 * 028-53 ran 30000 1000000 20 10.
 */
public class RowsProbe {
    static Field tableF, rowsF;
    static String last = "";

    static void show(Db db, String phase, long i) throws Exception {
        @SuppressWarnings("unchecked")
        List<Reclaim.IterationInfo> rows =
                (List<Reclaim.IterationInfo>) rowsF.get(tableF.get(db.internal().reclaim()));
        StringBuilder sb = new StringBuilder();
        StringBuilder sig = new StringBuilder();
        for (Reclaim.IterationInfo row : rows) {
            sig.append(row.pStart).append(row.done).append(row.cut).append(row.pSafe).append(',');
            sb.append(String.format(" [S %d C %d rw %d kv %d %s%s]", row.pStart / 1000,
                    row.pCut / 1000, row.rewritten / 1000, row.kvCount, row.done ? "D" : "-",
                    row.cut ? "X" : "-"));
        }
        if (!sig.toString().equals(last)) {
            last = sig.toString();
            System.out.println(String.format("%s %d L %d fp %d:%s", phase, i,
                    db.getStreamLength() / 1000, db.getFirstAvailablePos() / 1000, sb));
        }
    }

    static void put(Db db, AtomicLong clock, int live, long dt) {
        for (int i = 0; i < live; i += 100) {
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 100 && k < live; k++) {
                b.put(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k}, new byte[100]);
            }
            clock.addAndGet(dt);
            db.execute(b.build());
        }
    }

    public static void main(String[] a) throws Exception {
        tableF = Reclaim.class.getDeclaredField("table");
        tableF.setAccessible(true);
        rowsF = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
        rowsF.setAccessible(true);
        final int live = Integer.parseInt(a[0]);
        final int sd = Integer.parseInt(a[1]);
        final int rs = Integer.parseInt(a[2]);
        final int rounds = a.length > 3 ? Integer.parseInt(a[3]) : 0;
        final AtomicLong clock = new AtomicLong(1_778_000_000_000L * 10_000L);
        final Clock c = clock::get;
        Db db = Db.builder().mainStream(new MemoryStream()).clock(c).start();
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        db.setStartupDistance(sd);
        put(db, clock, live, 10_000);
        for (int r = 0; r < rounds; r++) {
            put(db, clock, live, 100_000);
        }
        show(db, "calls", -1);
        final long len0 = db.getStreamLength();
        long lenHalf = 0;
        for (int i = 0; i < rs * 1000; i++) {
            clock.addAndGet(10_000);
            db.maintain();
            show(db, "calls", i);
            if (i == rs * 500) lenHalf = db.getStreamLength();
        }
        final long len = db.getStreamLength();
        System.out.println(String.format("live %d: wrote %d kB in %d R, %d kB in the last %d R; "
                + "kept %d kB", live, (len - len0) / 1000, rs, (len - lenHalf) / 1000, rs / 2,
                (len - db.getFirstAvailablePos()) / 1000));
        db.close();
    }
}
