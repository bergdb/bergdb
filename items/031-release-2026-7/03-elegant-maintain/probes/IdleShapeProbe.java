package bergdb.core;

import java.lang.reflect.Field;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 031-03's review probe (claim (b)): IdleLiveProbe with keys of SEGS segments and values of VAL bytes,
 * N keys, ROUNDS overwrites, then 40 R of calls (1 ms apart, R = 1 s). Prints what the calls
 * wrote in the last 20 R, the last call with work, and each row's rewritten at the end.
 *   java -cp out:bergdb.jar bergdb.core.IdleShapeProbe N SEGS VAL SD ROUNDS [CALLS]
 * Also prints the stream of a twin with the same keys and values put once, and the stream
 * kept over it.
 */
public class IdleShapeProbe {
    static Field tableF, rowsF;

    @SuppressWarnings("unchecked")
    static List<Reclaim.IterationInfo> rows(Db d) throws Exception {
        return (List<Reclaim.IterationInfo>) rowsF.get(tableF.get(d.internal().reclaim()));
    }

    static String key(int k, int segs) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < segs - 1; i++) b.append("/s").append((k * 7 + i) % 13);
        b.append("/k").append(k);
        return b.toString();
    }

    public static void main(String[] a) throws Exception {
        tableF = Reclaim.class.getDeclaredField("table");
        tableF.setAccessible(true);
        rowsF = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
        rowsF.setAccessible(true);
        int n = Integer.parseInt(a[0]), segs = Integer.parseInt(a[1]), val = Integer.parseInt(a[2]);
        int sd = Integer.parseInt(a[3]), rounds = Integer.parseInt(a[4]);
        AtomicLong clock = new AtomicLong(1_778_000_000_000L * 10_000L);
        Clock c = clock::get;
        String ns = System.getProperty("ns", "");
        DbBuilder bb = Db.builder().mainStream(new MemoryStream()).clock(c);
        if (ns.equals("8")) bb.maxNodeSize8();
        if (ns.equals("14")) bb.maxNodeSize14();
        Db db = bb.start();
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        db.setStartupDistance(sd);
        for (int r = 0; r <= rounds; r++) {
            for (int i = 0; i < n; i += 50) {
                Trans.Builder b = db.trans();
                for (int k = i; k < i + 50 && k < n; k++) b.put(key(k, segs), new byte[val]);
                clock.addAndGet(r == 0 ? 10_000 : 100_000);
                db.execute(b.build());
            }
        }
        final int CALLS = a.length > 5 ? Integer.parseInt(a[5]) : 40000;
        long len0 = db.getStreamLength(), lenHalf = 0, lastWork = -1;
        int iters0 = rows(db).size();
        for (int i = 0; i < CALLS; i++) {
            clock.addAndGet(10_000);
            long l = db.getStreamLength();
            if (db.maintain() || db.getStreamLength() != l) lastWork = i;
            if (i == CALLS / 2) lenHalf = db.getStreamLength();
        }
        long len = db.getStreamLength();
        StringBuilder rs = new StringBuilder();
        for (Reclaim.IterationInfo r : rows(db)) rs.append(" [pStart " + r.pStart + " rewritten " + r.rewritten + "]");
        System.out.println(String.format("n %d segs %d val %d sd %d rounds %d: stream %d kB; calls wrote %d kB, %d kB in the last 20 R; last work %d; kept %d kB; w %d fp %d; iterations %d%s",
                n, segs, val, sd, rounds, len0 / 1000, (len - len0) / 1000, (len - lenHalf) / 1000, lastWork,
                (len - db.getFirstAvailablePos()) / 1000, db.internal().reclaim().appW, db.getFirstAvailablePos(),
                db.internal().reclaim().getIterationCount(), rs));
        // A twin: the same keys and values put once, retain forever: a fresh database's stream.
        Db twin = Db.builder().mainStream(new MemoryStream()).clock(c).start();
        twin.setStartupDistance(sd);
        for (int i = 0; i < n; i += 50) {
            Trans.Builder b = twin.trans();
            for (int k = i; k < i + 50 && k < n; k++) b.put(key(k, segs), new byte[val]);
            clock.addAndGet(10_000);
            twin.execute(b.build());
        }
        System.out.println("  twin (put once) stream " + twin.getStreamLength() / 1000 + " kB; kept/twin "
                + String.format("%.2f", (len - db.getFirstAvailablePos()) / (double) twin.getStreamLength()));
        twin.close();
        db.close();
    }
}
