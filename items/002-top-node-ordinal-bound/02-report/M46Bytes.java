package bergdb.core;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.stream.MemoryStream;

/**
 * Bergdb item 002 (M46): what top nodes cost in the stream. Runs a small hot workload on an
 * in-memory database, then reads every record of the stream and adds up the bytes of the
 * top node versions, their slots, and the slots that are unset (their ordinal's bit is 0).
 *
 * Usage: java -cp bergdb.jar:. bergdb.core.M46Bytes NODESIZE KEYS N STARTUP_DISTANCE
 */
public final class M46Bytes {
    public static void main(String[] args) {
        int maxNode = Integer.parseInt(args[0]);
        int keys = Integer.parseInt(args[1]);
        int n = Integer.parseInt(args[2]);
        int sd = Integer.parseInt(args[3]);
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        DbBuilder b = Db.builder().testSetup(stream).clock(clock).startupDistance(sd);
        if (maxNode == 8) b.maxNodeSize8(); else if (maxNode == 14) b.maxNodeSize14();
        else if (maxNode == 62) b.maxNodeSize62(); else b.maxNodeSize30();
        Db db = b.start();
        Random rnd = new Random(1);
        byte[] v = new byte[16];
        for (int i = 0; i < n; i++) {
            clock.setTime(10L * (i + 1));
            String k = keys == 1 ? "/hot" : "/k/" + rnd.nextInt(keys);
            db.execute(db.trans().put(k, v).build());
        }
        long tops = db.internal().superRoot().topNodeId + 1;
        long topVersions = 0, topBytes = 0, slots = 0, unset = 0, keyBytes = 0, valueBytes = 0, records = 0;
        Map<Long, Integer> versionsPerTop = new HashMap<Long, Integer>();
        synchronized (db.internal().getWriteLock()) {
            NodeStream.TransIterator it = db.internal().nodeStream().createTransIterator(0);
            while (it.next()) {
                StoredTrans st = it.getStoredTrans();
                records++;
                for (StoredNode sn : st.nodes) {
                    Node node = sn.getNode();
                    if (node instanceof TopNode) {
                        TopNode t = (TopNode) node;
                        topVersions++;
                        topBytes += StoredTopNode.getByteSize(t);
                        slots += t.pointersLength;
                        for (int i = 0; i < t.pointersLength; i++) {
                            if ((t.topNodeId & (1L << i)) == 0) unset++;
                        }
                        Integer c = versionsPerTop.get(t.getId());
                        versionsPerTop.put(t.getId(), c == null ? 1 : c + 1);
                    } else if (node instanceof KeyNode) {
                        keyBytes += StoredKeyNode.getByteSize((KeyNode) node);
                    } else {
                        valueBytes += 0;
                    }
                }
            }
        }
        long len = stream.getLength();
        System.out.printf("node=%d keys=%d tx=%d sd=%d: stream %d bytes (%.1f per tx), %d records; %d tops made, "
                + "%d top versions written (%d distinct), top bytes %.1f%% of the stream (%.1f per tx), slots %d "
                + "(%.1f per version, %.1f%% unset), key node bytes %.1f%%%n",
                maxNode, keys, n, sd, len, len / (double) n, records, tops, topVersions, versionsPerTop.size(),
                100.0 * topBytes / len, topBytes / (double) n, slots, slots / (double) topVersions,
                100.0 * unset / slots, 100.0 * keyBytes / len);
        db.stop();
    }
}
