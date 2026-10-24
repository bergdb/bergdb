package bergdb.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import bergdb.dag.Keys;
import bergdb.stream.MemoryStream;

/**
 * Bergdb 005-31's first step: the bound of option A (Dag.dirtyNodeBound, the index nodes a
 * transaction can make dirty or create) against what the transaction's got-dirty nodes take
 * when it has run (TransSeq.recordBytes, the bytes take() counts for it), on 007-02's probe
 * and on loads of new keys. The record limit is the real one, so nothing is refused.
 *
 * Usage: java -ea [-Dm=8|14|62] -cp CLASSES:bergdb.jar bergdb.core.BoundProbe, or probe.sh,
 * which runs it at the four node sizes into bound-m*.txt. The class first on the class path
 * (the jar's index hides the package otherwise).
 */
public class BoundProbe {
    static String key(int k) { return String.format("/k/%06d", k); }

    public static void main(String[] args) {
        System.out.println("node size " + new BoundProbe().maxNodeSize() + "; bound in nodes "
                + "and in bytes at the largest size (32 + 16 (M + 1) + 16 a node); actual: the "
                + "got-dirty nodes after the transaction, TransSeq.recordBytes");
        for (int every : new int[] {20, 40, 100, 200, 1000}) {
            run("update of every " + every + "th of 40,000 keys", every, 0, false);
        }
        run("load of 2,000 new keys under a new prefix", 0, 2000, true);
        run("load of 20,000 new keys under a new prefix", 0, 20000, true);
        run("load of 2,000 new random keys among them", 0, 2000, false);
        run("load of 20,000 new random keys among them", 0, 20000, false);
    }

    int maxNodeSize() {
        Db db = builder().testSetup().build();
        int m = db.internal().maxNodeSize();
        db.close();
        return m;
    }

    /** The node size of -Dm=8, 14 or 62; the default (30) otherwise. */
    static DbBuilder builder() {
        DbBuilder b = Db.builder();
        String m = System.getProperty("m", "30");
        if (m.equals("8")) b.maxNodeSize8();
        if (m.equals("14")) b.maxNodeSize14();
        if (m.equals("62")) b.maxNodeSize62();
        return b;
    }

    static void run(String what, int every, int load, boolean prefix) {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long time = 1000 * 1000;
        clock.setTime(time);
        Db db = builder().testSetup(stream).clock(clock).startupDistance(20 * 1000).start();
        List<Integer> order = new ArrayList<Integer>();
        for (int k = 0; k < 40000; k++) order.add(k);
        Collections.shuffle(order, new Random(7));
        for (int i = 0; i < 400; i++) {
            clock.setTime(time += 1000);
            Trans.Builder b = db.trans();
            for (int j = 0; j < 100; j++) b.put(key(order.get(i * 100 + j)), "v");
            db.execute(b.build());
        }
        for (int i = 0; i < 2000; i++) {
            clock.setTime(time += 1000);
            db.execute(db.trans().put("/x", "a" + i).build());
        }

        clock.setTime(time += 1000);
        Trans.Builder b = db.trans();
        Random r = new Random(11);
        if (every > 0) {
            for (int k = 0; k < 40000; k += every) b.put(key(k), "w");
        } else if (prefix) {
            for (int k = 0; k < load; k++) b.put(String.format("/new/%06d", k), "w");
        } else {
            for (int k = 0; k < load; k++) b.put(String.format("/k/%06d.%d", r.nextInt(40000), k), "w");
        }
        Trans t = b.build();
        long[][] keys = new long[t.kvs.length][];
        boolean[] deletes = new boolean[t.kvs.length];
        for (int i = 0; i < keys.length; i++) keys[i] = t.kvs[i].getKey();
        long nodes;
        synchronized (db.internal().getWriteLock()) {
            nodes = db.internal().dag().dirtyNodeBound(Long.MAX_VALUE, keys, deletes,
                    db.newGetData());
        }
        db.execute(t);
        TransSeq.TransInfo info = db.internal().transSeq().last();
        long actual = TransSeq.recordBytes(info);
        int m = db.internal().maxNodeSize();
        long bound = nodes * (32 + 16L * (m + 1) + 16);
        System.out.printf("  %s: record %d bytes; bound %d nodes, %d bytes; actual %d nodes, %d "
                + "bytes; bound / actual %.2f (nodes %.2f)%n", what, t.nextPos - t.tpos, nodes,
                bound, info.gotDirtyNodes.size(), actual, (double) bound / actual,
                (double) nodes / info.gotDirtyNodes.size());
        db.close();
    }
}
