package bergdb.core;

import java.io.File;
import java.lang.management.ManagementFactory;

import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * 024-17's ValueProbe (section 4.2) for bergdb 024-25: one size, 8 MiB (L4), 6 puts; run on
 * the build before and after CRC32C. Not product code. Usage: java -Xmx8g -cp
 * probe:build/bergdb.jar bergdb.core.ValueProbe25 DIR
 *
 * For each value size: a database in DIR with 100,000 small keys and the default builder
 * (eviction by budget, cache size indicator 200 MB, startup distance 50 MB, FileStream with
 * forced appends); then 3 puts of one value each (execute time, sync time, bytes the
 * thread allocated), a small put just after (does it wait for the buffer?), 5 gets of each
 * (time, bytes allocated), the heap held after a GC; then a restart (time, bytes the starting
 * thread allocated, heap after it) and a get after the restart.
 */
public class ValueProbe25 {

    static final com.sun.management.ThreadMXBean TB =
            (com.sun.management.ThreadMXBean) ManagementFactory.getThreadMXBean();

    static long alloc() {
        return TB.getCurrentThreadAllocatedBytes();
    }

    static long used() {
        Runtime rt = Runtime.getRuntime();
        System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }

    static Db open(File dir) throws Exception {
        return Db.builder().stream("main", new FileStream(dir)).start();
    }

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        int[] sizes = {8388608};
        System.out.println("size     what           ms       allocMB  note");
        for (int size : sizes) {
            LimitProbe.deleteDir(dir);
            dir.mkdirs();
            Db db = open(dir);
            byte[] small = new byte[8];
            for (int i = 0; i < 100000; i += 1000) {
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 1000; j++) b.put(LimitProbe.key(j), small);
                db.execute(b.build());
            }
            db.sync(SyncLevel.ORDINARY);
            long base = used();
            for (int k = 0; k < 6; k++) {
                byte[] v = new byte[size];
                new java.util.Random(k).nextBytes(v);
                long s0 = db.getStreamLength();
                long a0 = alloc();
                long t0 = System.nanoTime();
                db.execute(db.trans().put("/big/" + k, v).build());
                long t1 = System.nanoTime();
                long a1 = alloc();
                db.sync(SyncLevel.ORDINARY);
                long t2 = System.nanoTime();
                db.execute(db.trans().put("/small/" + k, small).build());
                long t3 = System.nanoTime();
                p(size, "put" + k, (t1 - t0) / 1e6, (a1 - a0) / 1e6,
                        "sync " + f((t2 - t1) / 1e6) + " ms, next small put " + f((t3 - t2) / 1e6)
                        + " ms, stream +" + (db.getStreamLength() - s0));
                v = null;
            }
            p(size, "heap held", 0, (used() - base) / 1e6, "after 3 puts and a GC, MB");
            GetData gd = db.newGetData();
            for (int r = 0; r < 5; r++) {
                for (int k = 0; k < 3; k++) {
                    long a0 = alloc();
                    long t0 = System.nanoTime();
                    byte[] got = db.getOne(Long.MAX_VALUE, Keys.toSegments(Keys.toBytes("/big/" + k)), gd);
                    long t1 = System.nanoTime();
                    if (r == 4 || (r == 0 && k == 0)) {
                        p(size, "get" + k + " r" + r, (t1 - t0) / 1e6, (alloc() - a0) / 1e6,
                                "length " + got.length);
                    }
                }
            }
            db.close();
            long a0 = alloc();
            long t0 = System.nanoTime();
            db = open(dir);
            long t1 = System.nanoTime();
            p(size, "restart", (t1 - t0) / 1e6, (alloc() - a0) / 1e6, "heap after "
                    + f(used() / 1e6) + " MB");
            long t2 = System.nanoTime();
            byte[] got = db.getOne(Long.MAX_VALUE, Keys.toSegments(Keys.toBytes("/big/2")),
                    db.newGetData());
            p(size, "get after", (System.nanoTime() - t2) / 1e6, 0, "length " + got.length);
            db.close();
        }
        LimitProbe.deleteDir(dir);
    }

    static String f(double d) {
        return String.format("%.1f", d);
    }

    static void p(int size, String what, double ms, double mb, String note) {
        System.out.printf("%-8d %-14s %-8.1f %-8.1f %s%n", size, what, ms, mb, note);
    }
}
