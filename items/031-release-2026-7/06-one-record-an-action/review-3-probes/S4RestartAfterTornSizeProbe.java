package bergdb.core;

import java.io.File;

import bergdb.stream.FileStream;

/**
 * Review probe (s4, 028-67): a file database whose last record a crash cut within its size
 * field (1 to 4 bytes kept, a prefix of the append). Start 1 completes the record and
 * starts; then the database is stopped and started again, with no crash: starts 2 and 3.
 */
public class S4RestartAfterTornSizeProbe {
    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        S4TornFillFileProbe.rm(base);
        File orig = new File(base, "orig");
        orig.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        long last;
        try (Db db = Db.builder().testSetup(new FileStream(orig)).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("a", "a-value"));
            clock.setTime(20);
            Trans t = db.trans().put("b", new byte[100000]).build();
            db.execute(t);
            last = t.tpos;
        }
        for (int cutIn = 1; cutIn <= 8; cutIn++) {
            File d = new File(base, "c" + cutIn);
            S4TornFillFileProbe.copy(orig, d);
            S4TornFillFileProbe.cut(d, last + cutIn);
            StringBuilder sb = new StringBuilder("cut " + cutIn + " bytes into the record at "
                    + last + ":");
            for (int start = 1; start <= 3; start++) {
                try (Db db = Db.builder().testSetup(new FileStream(d)).clock(clock).start()) {
                    sb.append(" start " + start + " ok (a "
                            + (DbUtil.get(db, Long.MAX_VALUE, "a") != null) + ");");
                } catch (RuntimeException e) {
                    String m = String.valueOf(e.getMessage());
                    sb.append(" start " + start + " " + e.getClass().getSimpleName() + ": "
                            + m.substring(0, Math.min(130, m.length())));
                    break;
                }
            }
            System.out.println(sb);
        }
        S4TornFillFileProbe.rm(base);
    }
}
