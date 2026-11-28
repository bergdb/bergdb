import bergdb.pub.*;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.concurrent.atomic.*;

/**
 * 031-08, UA-7: a maintain(100) call beside 8 writer threads that commit without a pause,
 * with and without the calling thread's interrupt flag set: the CPU time that the calling
 * thread uses in 5 s while the call waits (ThreadMXBean).
 *
 * Usage: java -cp bergdb-release.jar:. MaintainSpins
 */
public class MaintainSpins {
    public static void main(String[] a) throws Exception {
        ThreadMXBean mx = ManagementFactory.getThreadMXBean();
        for (boolean interrupted : new boolean[] {false, true}) {
            try (Database db = Factory.database().memory().start()) {
                db.setStartupDistanceInMb(5);
                db.setRetainDuration(Duration.seconds(1));
                Connection c0 = db.connection();
                for (int i = 0; i < 20; i++) { WBuilder w = c0.w(); for (int j = 0; j < 400; j++) w.put("/d/k" + j + ".bin", new byte[300]); w.execute(); }
                AtomicBoolean stop = new AtomicBoolean();
                Thread[] ts = new Thread[8];
                for (int i = 0; i < 8; i++) {
                    final int id = i;
                    ts[i] = new Thread(() -> {
                        Connection c = db.connection();
                        int k = 0;
                        while (!stop.get()) c.put("/w" + id + "/k" + (k++ % 500) + ".bin", new byte[200]);
                    });
                    ts[i].start();
                }
                Thread.sleep(500);
                AtomicLong calls = new AtomicLong();
                Thread m = new Thread(() -> {
                    if (interrupted) Thread.currentThread().interrupt();
                    db.maintain(100);
                    calls.incrementAndGet();
                });
                m.start();
                Thread.sleep(200);
                long cpu0 = mx.getThreadCpuTime(m.getId());
                Thread.sleep(5000);
                long cpu1 = mx.getThreadCpuTime(m.getId());
                boolean alive = m.isAlive();
                stop.set(true);
                for (Thread t : ts) t.join();
                m.join();
                System.out.println((interrupted ? "interrupt flag set: " : "no interrupt: ") + (alive ? "the call had not returned after 5.2 s"
                        : "the call returned") + "; its thread used " + (cpu1 - cpu0) / 1_000_000 + " ms of CPU in those 5 s");
            }
        }
    }
}
