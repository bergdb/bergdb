package bergdb.core;

import java.util.List;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 028-47's probe of reclaim's state: C2's workload (026-13; 30,000 keys put and deleted,
 * then overwrites of one key of 900 bytes every DT ms, R = 1 s; MemoryStream) on one
 * database, or with "twin" the drive alone, and with "maintain" maintain() until false after
 * each commit. Printed every R/4: the stream written since the drive began (end), kept, the
 * startup pos's and the last valid meta block's distances from the end, the first available
 * position, and reclaim's table, a row as [pStart pCut run|done pEnd pSafe CUT] in kB from the
 * drive's start (-1: unknown); at the end the drive's bytes by writer (Reclaim.Stats).
 *
 * In package bergdb.core for the table; on the class path before the jar (from java/, after
 * build.sh):
 *   javac -cp build/bergdb.jar -d OUT SlowDriveProbe.java
 *   java -cp OUT:build/bergdb.jar bergdb.core.SlowDriveProbe SD DT RS [twin] [maintain]
 * RS: the drive in R. 028-47 ran SD 1000000, DT 5, RS 12 and 40; SD 50000000, DT 1.
 */
public class SlowDriveProbe {
    public static void main(String[] a) throws Exception {
        int sd = Integer.parseInt(a[0]);
        int dt = Integer.parseInt(a[1]);
        int rs = Integer.parseInt(a[2]);
        boolean twin = false, maintain = false;
        for (int k = 3; k < a.length; k++) {
            if (a[k].equals("twin")) twin = true;
            if (a[k].equals("maintain")) maintain = true;
        }
        AtomicLong clock = new AtomicLong(1_778_000_000_000L * 10_000L);
        Clock c = clock::get;
        Db db = Db.builder().mainStream(new MemoryStream()).clock(c).start();
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        db.setStartupDistance(sd);
        Reclaim.Stats st;
        synchronized (db.internal().getWriteLock()) {
            st = db.internal().reclaim().enableStats();
        }
        if (!twin) {
            for (int i = 0; i < 30_000; i += 300) {
                Trans.Builder b = db.trans();
                for (int k = i; k < i + 300; k++) b.put(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k}, new byte[60]);
                clock.addAndGet(50_000);
                db.execute(b.build());
            }
            for (int i = 0; i < 30_000; i += 300) {
                Trans.Builder b = db.trans();
                for (int k = i; k < i + 300; k++) b.delete(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k});
                clock.addAndGet(50_000);
                db.execute(b.build());
            }
        }
        int r = 1000 / dt;
        Random rnd = new Random(1);
        long s0 = db.getStreamLength();
        System.out.println("SD " + sd + " DT " + dt + " R " + r + (twin ? " twin" : " emptied")
                + (maintain ? " maintain" : "") + " s0 " + s0 + " kept " + kept(db));
        print(db, 0, r, s0);
        Reclaim.Stats.Record u0 = st.user.copy(), s0r = st.step.copy(), t0 = st.table.copy();
        for (int i = 1; i <= rs * r; i++) {
            byte[] v = new byte[900];
            rnd.nextBytes(v);
            clock.addAndGet(dt * 10_000L);
            db.execute(db.trans().put(new byte[] {0x06, 0x01}, v).build());
            if (maintain) for (int n = 0; n < 50 && db.maintain(); n++) { }
            if (i % (r / 4) == 0) print(db, i, r, s0);
        }
        Reclaim.Stats.Record u = st.user.minus(u0), sr = st.step.minus(s0r), tr = st.table.minus(t0);
        long all = db.getStreamLength() - s0;
        System.out.println(String.format("DRIVE bytes %d: user records %d bytes %d (values %d, index %d), steps %d bytes %d, table %d bytes %d, other %d",
                all, u.records, u.bytes, u.valueBytes, u.indexBytes, sr.records, sr.bytes, tr.records, tr.bytes,
                all - u.bytes - sr.bytes - tr.bytes));
        db.close();
    }

    static long kept(Db db) {
        return db.getStreamLength() - db.getFirstAvailablePos();
    }

    static void print(Db db, int i, int r, long s0) throws Exception {
        long len = db.getStreamLength();
        long sp = db.internal().getStartupPosForEvict();
        long fp = db.getFirstAvailablePos();
        long mp = db.getLastTransPosOfLastValidMetaBlock();
        StringBuilder sb = new StringBuilder();
        synchronized (db.internal().getWriteLock()) {
            Reclaim rc = db.internal().reclaim();
            java.lang.reflect.Field f = Reclaim.class.getDeclaredField("table");
            f.setAccessible(true);
            Object table = f.get(rc);
            java.lang.reflect.Field fr = table.getClass().getDeclaredField("rows");
            fr.setAccessible(true);
            for (Object o : (List<?>) fr.get(table)) {
                Reclaim.IterationInfo row = (Reclaim.IterationInfo) o;
                sb.append(String.format(" [ps%d pc%d %s pe%d psafe%d%s]", (row.pStart - s0) / 1000,
                        (row.pCut - s0) / 1000, row.done ? "done" : "run",
                        row.pEnd < 0 ? -1 : (row.pEnd - s0) / 1000,
                        row.pSafe < 0 ? -1 : (row.pSafe - s0) / 1000, row.cut ? " CUT" : ""));
            }
        }
        System.out.println(String.format("%6.2f R end %d kB kept %d kB  end-sp %d kB  end-mp %d kB  fp %d kB  rows%s",
                (double) i / r, (len - s0) / 1000, (len - fp) / 1000, (len - sp) / 1000, (len - mp) / 1000,
                (fp - s0) / 1000, sb));
    }
}
