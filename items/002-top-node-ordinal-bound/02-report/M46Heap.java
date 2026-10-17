package bergdb.core;

import bergdb.stream.MemoryStream;

/**
 * Bergdb item 002 (M46): heap kept per transaction for one hot key, today (no eviction).
 * The in-memory stream's bytes are subtracted.
 *
 * Usage: java -Xmx4g -cp bergdb.jar:. bergdb.core.M46Heap NODESIZE N
 */
public final class M46Heap {
    static long used() {
        for (int i = 0; i < 3; i++) System.gc();
        Runtime rt = Runtime.getRuntime();
        return rt.totalMemory() - rt.freeMemory();
    }

    public static void main(String[] args) {
        int maxNode = Integer.parseInt(args[0]);
        int n = Integer.parseInt(args[1]);
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        if (maxNode == 8) b.maxNodeSize8(); else b.maxNodeSize30();
        Db db = b.start();
        byte[] v = new byte[16];
        long h0 = used(), s0 = stream.getLength();
        for (int i = 0; i < n; i++) {
            clock.setTime(10L * (i + 1));
            db.execute(db.trans().put("/hot", v).build());
        }
        long h1 = used(), s1 = stream.getLength();
        long heap = (h1 - h0) - (s1 - s0);
        System.out.printf("node=%d tx=%d: heap kept %.1f MB besides the stream (%.0f bytes per transaction, "
                + "%.0f per top node made)%n", maxNode, n, heap / 1e6, heap / (double) n,
                heap / (double) (db.internal().superRoot().topNodeId + 1));
        db.stop();
    }
}
