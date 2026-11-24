package bergdb.core;

import java.io.File;

/**
 * bergdb 028-47's probe of G4's databases (CountGates.Run with a startup distance: FileStream,
 * the builder's cache, eviction on): put "/a.txt", with N the emptied database's fill and
 * deletes (N keys in key order, 100 a transaction), then a drive of overwrites of "/a.txt"
 * (1,000 bytes), one every DT time units, R = 1 s. Printed every P drive transactions, for
 * those P: the stream written, kept, the startup pos's distance from the end, and
 * Reclaim.Stats's bytes by writer (user records, reclaim's other internal records: tables,
 * rows, maintain()'s and 028-47's takes; steps), with their index nodes.
 *
 * In package bergdb.core, beside CountGates (from java/, after build.sh):
 *   javac -cp build/bergdb.jar:build/stress -d OUT TwinDriveProbe.java
 *   java -Xmx4g -cp OUT:build/bergdb.jar:build/stress bergdb.core.TwinDriveProbe SD DT DRIVE P DIR [N]
 * 028-47 ran SD 50000000, DT 10000, DRIVE 300000, P 10000.
 */
public class TwinDriveProbe {
    public static void main(String[] a) throws Exception {
        CountGates x = new CountGates();
        x.p.put("g4sd", a[0]);
        x.dt = Long.parseLong(a[1]);
        x.retain = CountGates.SEC;
        int drive = Integer.parseInt(a[2]), every = Integer.parseInt(a[3]);
        x.base = new File(a[4]);
        int nn = a.length > 5 ? Integer.parseInt(a[5]) : 0;
        CountGates.Run r = x.new Run("twin", Integer.parseInt(a[0]));
        r.db.setRetainDuration(x.retain);
        r.exec(r.db.trans().put("/a.txt", CountGates.HELLO), "create");
        if (nn > 0) {
            for (int k = 0; k < nn; ) {
                Trans.Builder b = r.db.trans();
                for (int j = 0; j < 100 && k < nn; j++, k++) b.put(CountGates.key(k), CountGates.value(100, k));
                r.exec(b, "fill");
            }
            for (int k = 0; k < nn; ) {
                Trans.Builder b = r.db.trans();
                for (int j = 0; j < 100 && k < nn; j++, k++) b.delete(CountGates.key(k));
                r.exec(b, "delete");
            }
        }
        long s0 = r.db.getStreamLength();
        Reclaim.Stats.Record u0 = r.stats.user.copy(), t0 = r.stats.table.copy(), st0 = r.stats.step.copy();
        for (int k = 1; k <= drive; k++) {
            r.exec(r.db.trans().put("/a.txt", CountGates.value(1000, k)), "drive");
            if (k % every == 0) {
                long len = r.db.getStreamLength();
                long sp = r.db.internal().getStartupPosForEvict();
                Reclaim.Stats.Record u = r.stats.user.minus(u0), t = r.stats.table.minus(t0), st = r.stats.step.minus(st0);
                System.out.println(String.format("%7d tx: wrote %d kB kept %d kB end-sp %d kB; user %d kB (index %d kB), table %d rec %d kB (index %d kB), steps %d rec %d kB; cuts %d",
                        k, (len - s0) / 1000, r.kept() / 1000, (len - sp) / 1000, u.bytes / 1000, u.indexBytes / 1000,
                        t.records, t.bytes / 1000, t.indexBytes / 1000, st.records, st.bytes / 1000, r.stats.cuts.size()));
                u0 = r.stats.user.copy(); t0 = r.stats.table.copy(); st0 = r.stats.step.copy(); s0 = len;
            }
        }
        r.close();
    }
}
