package bergdb.core;
import java.io.IOException;
import java.util.Random;
import bergdb.nanotest.Assert;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;
/**
 * bergdb 015-87: DbTesterRestart.testReclaimSettingsKeptOverRestarts, run against any jar, to
 * show that it fails before the change (0fec98f) and passes after. With "getters" it checks
 * the values after each restart, as the test does; without, it compares only the streams.
 * Output: probe-output.txt. From java/ of a clone, J the jar to test:
 *
 *   javac -d /tmp/p -cp J SettingsRestartProbe.java
 *   java -ea -cp /tmp/p:J bergdb.core.SettingsRestartProbe getters
 *   java -ea -cp /tmp/p:J bergdb.core.SettingsRestartProbe
 */
public class SettingsRestartProbe {
    public static void main(String[] a) throws IOException {
        boolean getters = a.length > 0 && a[0].equals("getters");
        Object[] plain = settingsRun(false, getters);
        Object[] restarts = null;
        try {
            restarts = settingsRun(true, getters);
        } catch (AssertionError e) {
            System.out.println("FAILED in the run with restarts: " + e.getMessage());
            return;
        }
        System.out.println("plain:    cut=" + plain[0] + " length=" + plain[1]);
        System.out.println("restarts: cut=" + restarts[0] + " length=" + restarts[1]);
        System.out.println(java.util.Arrays.equals((byte[]) plain[2], (byte[]) restarts[2])
                ? "SAME STREAM from the decided cut" : "STREAMS DIFFER from the decided cut");
    }
    static Object[] settingsRun(boolean restarts, boolean getters) throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                .maxNodeSize8().start();
        try {
            Random rnd = new Random(1);
            for (int i = 1; i <= 2000; i++) {
                clock.setTime(i * Clock.UNITS_PER_SEC / 10);
                byte[] value = new byte[1 + rnd.nextInt(40)];
                rnd.nextBytes(value);
                db.execute(db.trans().put("/k/" + rnd.nextInt(500), value));
                if (i == 100) {
                    db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                    db.setReclaimInternalFraction(0.1);
                }
                if (restarts && i >= 100 && i % 50 == 0 && i < 2000) {
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    stream = stream.copy();
                    db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                            .maxNodeSize8().start();    // The settings not set again.
                    if (getters) Assert.assertEquals("retain after a restart", 1 * Clock.UNITS_PER_SEC,
                            db.getRetainDuration());
                    if (getters) Assert.assertTrue("fraction after a restart",
                            db.getInternalFraction() == 6554 / 65536.0);
                }
            }
            db.sync(SyncLevel.ORDINARY);
            long cut = Math.max(stream.getFirstPos(), db.getFirstAvailablePos());
            if (getters) Assert.assertTrue("reclaim cut, restarts=" + restarts, db.getFirstAvailablePos() > 0);
            byte[] bytes = new byte[(int) (stream.getLength() - cut)];
            stream.read(cut, bytes, 0, bytes.length);
            return new Object[] {cut, stream.getLength(), bytes};
        } finally {
            db.stop();
        }
    }
    
}
