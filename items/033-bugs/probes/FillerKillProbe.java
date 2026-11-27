package bergdb.core;

import java.io.File;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

/**
 * Ported for bergdb 033, 2026-11-27: maintain() calls through 031-04's shim M (maintain(int)
 * with budget B, -Dbudget, 100 by default, on main since 031-04 and 031-06; maintain() on
 * 2026.6), so that one probe runs on both; what it checks is unchanged.
 *
 * bergdb 028-59's probe, 2026-11-25: a crash between maintain()'s filler put and its delete, as
 * a killed JVM, on a database in a directory. The parent starts a child JVM that runs
 * StopAtProbe's scenario (R = 1 s, a put of /a, VAL bytes, then maintain() calls 1 ms apart)
 * on a FileStream in DIR, with the test clock; at the record of the filler's put the child
 * waits 100 ms (the write buffer's time is 10 ms) and halts (Runtime.halt: no stop, no close,
 * no shutdown hooks). The parent then starts the database in DIR, with a clock 100 s on, and
 * makes CALLS calls 1 ms apart: prints whether the filler is live at the start and after the
 * calls, and the stream kept. The startup distance is set as in StopAtProbe ("bN": by the
 * builder where it has the method, 2026.5).
 *   java -ea -cp out:bergdb.jar bergdb.core.FillerKillProbe DIR SD VAL CALLS
 */
public class FillerKillProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final long[] FILL = Keys.toSegments("/#i/dreclaim/-fill.txt");

    static Db start(File dir, AtomicLong time, String sdArg) throws Exception {
        DbBuilder b = Db.builder().testSetup(new FileStream(dir)).clock(time::get);
        boolean builderSd = sdArg.startsWith("b"), byBuilder = false;
        int sd = Integer.parseInt(builderSd ? sdArg.substring(1) : sdArg);
        if (builderSd) {
            try {
                DbBuilder.class.getMethod("startupDistance", int.class).invoke(b, sd);
                byBuilder = true;
            } catch (ReflectiveOperationException e) {}
        }
        Db d = b.start();
        if (!byBuilder && d.getStartupDistance() != sd) d.setStartupDistance(sd);
        if (d.getRetainDuration() != SEC) d.setRetainDuration(SEC);
        return d;
    }

    static void child(File dir, String sd, int val) throws Exception {
        AtomicLong time = new AtomicLong(SEC);
        Db d = start(dir, time, sd);
        final int[] fills = {0};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                for (int i = 0; i < x.transNodes.valueCount; i++) {
                    if (Arrays.equals(FILL, x.transNodes.keys[i]) && fills[0]++ == 0) {
                        System.out.println("child: the filler's put written, length "
                                + d.getStreamLength() + "; halting");
                        System.out.flush();
                        try { Thread.sleep(100); } catch (InterruptedException e) {}
                        Runtime.getRuntime().halt(3);
                    }
                }
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
        time.addAndGet(MS);
        d.execute(d.trans().put("/a0", new byte[val]).build());
        for (int i = 0; i < 3000; i++) {
            time.addAndGet(MS);
            M.call(d);
        }
        System.out.println("child: no filler written");
        Db.testHooks = null;
        d.close();
    }

    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        if (a.length > 4 && a[4].equals("child")) {
            child(dir, a[1], Integer.parseInt(a[2]));
            return;
        }
        int calls = Integer.parseInt(a[3]);
        String java = System.getProperty("java.home") + "/bin/java";
        Process p = new ProcessBuilder(java, "-ea", "-cp", System.getProperty("java.class.path"),
                FillerKillProbe.class.getName(), a[0], a[1], a[2], a[3], "child").inheritIO().start();
        System.out.println("child exit " + p.waitFor());
        AtomicLong t = new AtomicLong(100 * SEC);
        Db d = start(dir, t, a[1]);
        boolean atStart = d.getOne(Long.MAX_VALUE, FILL, d.newGetData()) != null;
        System.out.println("started: filler live " + atStart + ", kept "
                + (d.getStreamLength() - d.getFirstAvailablePos()));
        for (int i = 0; i < calls; i++) { t.addAndGet(MS); M.call(d); }
        boolean after = d.getOne(Long.MAX_VALUE, FILL, d.newGetData()) != null;
        System.out.println("after " + calls + " calls: filler live " + after + ", kept "
                + (d.getStreamLength() - d.getFirstAvailablePos()) + " (length "
                + d.getStreamLength() + ", fp " + d.getFirstAvailablePos() + ")");
        d.close();
    }
}
