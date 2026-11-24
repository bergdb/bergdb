package bergdb.core;

import java.lang.reflect.Field;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 028-53's probe of RB-007: writes made while an iteration waits for its cut, then
 * maintain() alone. Two databases, R = 1 s, startup distance 5 MB, MemoryStream and a test
 * clock: N1 keys of 100 bytes put and deleted in both; maintain() until false, a call a
 * millisecond, until the first iteration is done; then, in the first database only, N2 keys
 * put and deleted (before that iteration's cut); then 10 R of calls in both. Prints the
 * stream kept by each, the twin being the one without the second writes, and the last call
 * that wrote or returned true: on main the first keeps the second writes' stream for good.
 *
 * In package bergdb.core, as 028-51's IdleLiveProbe; on the class path before the jar (from
 * java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT HoleProbe.java
 *   java -cp OUT:build/bergdb.jar bergdb.core.HoleProbe N1 N2
 * 028-53 ran N1 4000 and 20000 with N2 20000.
 */
public class HoleProbe {
    static Field tableF, rowsF;
    static final AtomicLong clock = new AtomicLong(1_778_000_000_000L * 10_000L);

    @SuppressWarnings("unchecked")
    static List<Reclaim.IterationInfo> rows(Db db) throws Exception {
        return (List<Reclaim.IterationInfo>) rowsF.get(tableF.get(db.internal().reclaim()));
    }

    static void exec(Db db, Trans.Builder b) {
        clock.addAndGet(10_000);
        db.execute(b.build());
    }

    static void fill(Db db, int n, String p) {
        for (int i = 0; i < n; i += 100) {
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 100 && k < n; k++) b.put(p + k, new byte[100]);
            exec(db, b);
        }
    }

    static void delete(Db db, int n, String p) {
        for (int i = 0; i < n; i += 100) {
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 100 && k < n; k++) b.delete(p + k);
            exec(db, b);
        }
    }

    static void untilFalse(Db db) {
        for (int k = 0; k < 100 && db.maintain(); k++) { }
    }

    public static void main(String[] a) throws Exception {
        tableF = Reclaim.class.getDeclaredField("table");
        tableF.setAccessible(true);
        rowsF = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
        rowsF.setAccessible(true);
        final int n1 = Integer.parseInt(a[0]), n2 = Integer.parseInt(a[1]);
        final Clock c = clock::get;
        Db db = Db.builder().mainStream(new MemoryStream()).clock(c).start();
        Db twin = Db.builder().mainStream(new MemoryStream()).clock(c).start();
        for (Db d : new Db[] {db, twin}) {
            d.setRetainDuration(Clock.UNITS_PER_SEC);
            d.setStartupDistance(5000000);
            fill(d, n1, "/k/");
            delete(d, n1, "/k/");
        }
        for (int i = 0; i < 5000; i++) {
            clock.addAndGet(10_000);
            untilFalse(db);
            untilFalse(twin);
            List<Reclaim.IterationInfo> r = rows(db);
            if (!r.isEmpty() && r.get(r.size() - 1).done) break;
        }
        System.out.println("before the second writes: fp " + db.getFirstAvailablePos()
                + ", length " + db.getStreamLength() + ", rows " + rows(db).size());
        fill(db, n2, "/m/");
        delete(db, n2, "/m/");
        System.out.println("after them: fp " + db.getFirstAvailablePos() + ", length "
                + db.getStreamLength());
        long lastWork = -1;
        for (int j = 0; j < 10000; j++) {
            clock.addAndGet(10_000);
            final long length = db.getStreamLength();
            final boolean more = db.maintain();
            twin.maintain();
            if (more || db.getStreamLength() != length) lastWork = j;
        }
        System.out.println(String.format("after 10 R of calls: kept %d, the twin's %d; last call "
                + "with work %d of 10000; fp %d", db.getStreamLength() - db.getFirstAvailablePos(),
                twin.getStreamLength() - twin.getFirstAvailablePos(), lastWork,
                db.getFirstAvailablePos()));
        db.close();
        twin.close();
    }
}
