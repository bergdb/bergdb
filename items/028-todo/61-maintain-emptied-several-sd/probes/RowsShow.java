package bergdb.core;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.List;
import bergdb.pub.Database;
import bergdb.pubimp.DatabaseImp;

/**
 * bergdb 028-61's probe: reclaim's table and maintain()'s M1, printed by RetainChurnRows
 * (031-02's RetainChurn with calls to this class) whenever they change. Times in seconds
 * from the app's clock start (2026-01-01 00:00:00), positions in kB. Per row: pStart (S),
 * tStart (ts), pCut (C), rewritten (rw, kB), done (D), tEnd (te), pEnd (E), pSafe (P), cut
 * (X). M1's parts: whether R/4 has passed since the last tStart (q), whether a done row
 * waits for its cut (wait), M1's two stretches (own: fp to the last pStart; next: L to the
 * table's last store, main only) and the result (begin). With the 031-03 prototype
 * also w. On the class path before the jar; works with main, 2026.6 and 031-03-proto.
 */
public class RowsShow {
    /** The app's clock start, in units; set by the app. */
    public static long t0;
    static Field tableF, rowsF, appWF;
    static Method beginDueM, tablePosM;
    static String lastRows = "", lastM1 = "";

    static void init() throws Exception {
        if (tableF != null) return;
        tableF = Reclaim.class.getDeclaredField("table");
        tableF.setAccessible(true);
        rowsF = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
        rowsF.setAccessible(true);
        beginDueM = Reclaim.class.getDeclaredMethod("maintainBeginDue", long.class);
        beginDueM.setAccessible(true);
        try {
            tablePosM = Reclaim.class.getDeclaredMethod("tablePos");   // since 028-51
            tablePosM.setAccessible(true);
        } catch (NoSuchMethodException e) {
            tablePosM = null;
        }
        try {
            appWF = Reclaim.class.getDeclaredField("appW");
            appWF.setAccessible(true);
        } catch (NoSuchFieldException e) {
            appWF = null;
        }
    }

    static String s(long t) {
        return t <= 0 ? String.valueOf(t) : String.format("%.1f", (t - t0) / 1e7);
    }

    static String k(long p) {
        return p < 0 ? String.valueOf(p) : String.valueOf(p / 1000);
    }

    @SuppressWarnings("unchecked")
    static List<Reclaim.IterationInfo> rows(Reclaim rc) throws Exception {
        return (List<Reclaim.IterationInfo>) rowsF.get(tableF.get(rc));
    }

    /** Prints the table if a row began, ended, became safe or was cut since the last print. */
    public static void show(Database database, long now, String phase) {
        try {
            init();
            Db db = ((DatabaseImp) database).getDb();
            Reclaim rc = db.internal().reclaim();
            StringBuilder sb = new StringBuilder();
            StringBuilder sig = new StringBuilder();
            for (Reclaim.IterationInfo row : rows(rc)) {
                sig.append(row.pStart).append(row.done).append(row.cut).append(row.pSafe).append(',');
                sb.append(String.format("%n    [S %s ts %s C %s rw %s %s te %s E %s P %s %s]",
                        k(row.pStart), s(row.tStart), k(row.pCut), k(row.rewritten),
                        row.done ? "D" : "-", s(row.tEnd), k(row.pEnd), k(row.pSafe),
                        row.cut ? "X" : "-"));
            }
            if (!sig.toString().equals(lastRows)) {
                lastRows = sig.toString();
                System.out.println(String.format("  ROWS %s now %s L %s fp %s fa %s sp %s mp %s%s",
                        phase, s(now), k(db.getStreamLength()), k(db.getFirstAvailablePos()),
                        s(database.getFirstAvailableLookupTime().units()),
                        k(db.internal().getStartupPosForEvict()),
                        k(db.getLastTransPosOfLastValidMetaBlock()), sb));
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /** After a maintain() loop: M1's parts, printed when they change (now aside). */
    public static void m1(Database database, long now, String phase) {
        try {
            init();
            show(database, now, phase);
            Db db = ((DatabaseImp) database).getDb();
            Reclaim rc = db.internal().reclaim();
            List<Reclaim.IterationInfo> rows = rows(rc);
            long fp = db.getFirstAvailablePos();
            long L = db.getStreamLength();
            long lastPStart = rows.isEmpty() ? 0 : rows.get(rows.size() - 1).pStart;
            long lastTStart = rows.isEmpty() ? Long.MIN_VALUE : rows.get(rows.size() - 1).tStart;
            boolean q = now - lastTStart >= rc.getRetainDuration() / 4;
            boolean wait = false;
            for (Reclaim.IterationInfo row : rows) {
                if (row.done && !row.cut && row.pCut > fp) wait = true;
            }
            String next = rows.isEmpty() || tablePosM == null ? "-" : k(L - (Long) tablePosM.invoke(rc));
            boolean begin = (Boolean) beginDueM.invoke(rc, now);
            String w = appWF == null ? "" : " w " + k(appWF.getLong(rc));
            String m1 = String.format("L %s fp %s kept %s q %s wait %s own %s next %s%s begin %s",
                    k(L), k(fp), k(L - fp), q, wait, k(lastPStart - fp), next, w, begin);
            String sig = m1.replace(" q true", "").replace(" q false", "");
            if (!sig.equals(lastM1)) {
                lastM1 = sig;
                System.out.println(String.format("  M1 %s now %s fa %s %s", phase, s(now),
                        s(database.getFirstAvailableLookupTime().units()), m1));
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * The stream's files: each one's first position (its name times 100,000) and length, in
     * kB, against fp and the stream length: the storage drops whole files only.
     */
    public static void files(Database database, String dir) {
        Db db = ((DatabaseImp) database).getDb();
        java.io.File[] fs = new java.io.File(dir).listFiles((d, n) -> n.endsWith(".bergdb"));
        java.util.Arrays.sort(fs);
        StringBuilder sb = new StringBuilder();
        long total = 0;
        for (java.io.File f : fs) {
            long first = Long.parseLong(f.getName().substring(0, 14)) * 100_000L;
            sb.append(String.format(" [%s +%s]", k(first), k(f.length())));
            total += f.length();
        }
        System.out.println(String.format("  FILES L %s fp %s kept %s files %s:%s",
                k(db.getStreamLength()), k(db.getFirstAvailablePos()),
                k(db.getStreamLength() - db.getFirstAvailablePos()), k(total), sb));
    }
}
