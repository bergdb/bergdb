package bergdb.core;

import java.util.Locale;

import bergdb.stream.DummyStream;

/**
 * Props' MEM (bergdb.dev.props.Mem) with a chosen maximum node size (bergdb 005-38): one
 * million KVs, keys "0" to "999999" in that order, empty values, 100 a transaction, a
 * DummyStream, the test setup (no eviction, retain forever); the heap in use after
 * System.gc(), after minus before, per KV. Usage: java -Dnode=8|14|30|62 bergdb.core.MemNode
 */
public class MemNode {
    public static void main(String[] args) throws Exception {
        int node = Integer.getInteger("node", 30);
        int n = 1000 * 1000;
        DbBuilder b = Db.builder().testSetup().mainStream(new DummyStream());
        if (node == 8) b.maxNodeSize8();
        else if (node == 14) b.maxNodeSize14();
        else if (node == 30) b.maxNodeSize30();
        else if (node == 62) b.maxNodeSize62();
        else throw new IllegalArgumentException("node " + node);
        Db db = b.start();
        long empty = usedMem();
        int batchSize = 100;
        for (int i = 0; i < n / batchSize; i++) {
            Trans.Builder t = db.trans();
            for (int j = 0; j < batchSize; j++) t.put("" + (i * batchSize + j), new byte[0]);
            db.execute(t.build());
        }
        long full = usedMem();
        System.out.println(String.format(Locale.ROOT, "MEM:%.0f node %d (%.1f bytes per KV), stream %d bytes",
                (double) (full - empty) / n, node, (double) (full - empty) / n, db.getStreamLength()));
        db.stop();
        System.exit(0);
    }

    static long usedMem() {
        Runtime rt = Runtime.getRuntime();
        System.gc(); System.gc(); System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }
}
