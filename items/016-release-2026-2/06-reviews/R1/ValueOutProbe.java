package bergdb.core;

import java.util.ArrayList;
import java.util.List;

import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.stream.MemoryStream;

/**
 * Probe for review R1 (016-06): the capacity controller's batch takes the written values of a
 * pinned key node (Eviction.unswizzleValues, Residents.valueOut), including values the writer
 * put into it after it was last counted (Residents.added at its creation, grown at its writes;
 * a value the writer adds is counted nowhere until then: Cache3.pointerCreated and Db's
 * valueNodeCreated call Residents.added, which returns for a value). valueOut subtracts them
 * all, down to 0; Residents.grown does nothing for an object counted 0, so the leaf is not
 * counted again while it stays resident. A database with a large startup distance (its
 * leaves stay dirty, in D), 20 transactions of 1,000-byte values into one leaf, one batch
 * with a budget of 1,000 bytes, the budget back, 30 more transactions; the counts of the
 * dirty canonical leaves against their bytes, and the resident bytes against an exact count.
 * Usage (before the jar): java -ea -cp probes:build/bergdb.jar bergdb.core.ValueOutProbe
 */
public class ValueOutProbe {
    static long exact(Db db) {
        Db.Internal in = db.internal();
        final List<Node> d = new ArrayList<Node>();
        in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) { d.add(node); }
        });
        long b = 0;
        for (Node o : Residents.walk(in.superRoot(), in.cache().nodes(), d)) {
            if (o.isIndexNode()) b += Residents.bytesOf(o);
        }
        return b;
    }

    static void leaves(String when, Db db) {
        StringBuilder s = new StringBuilder();
        for (Node o : db.internal().cache().nodes()) {
            if (o instanceof KeyNode && ((KeyNode) o).isSegmentLeaf()) {
                KeyNode k = (KeyNode) o;
                s.append(" [leaf " + k.getId() + (k.isDirty() ? " dirty" : " clean") + ": counted "
                        + k.countedMemSize + ", bytes " + Residents.bytesOf(k) + "]");
            }
        }
        System.out.println(when + ": resident bytes " + db.internal().cache().residents().bytes()
                + ", exact " + exact(db) + ";" + s);
    }

    public static void main(String[] args) {
        CoreTestClock clock = new CoreTestClock();
        long time = 1000 * 1000;
        Db db = Db.builder().testSetup(new MemoryStream()).clock(clock).testId()
                .startupDistance(Integer.parseInt(args.length > 0 ? args[0] : "50000000")).start();
        int more = Integer.parseInt(args.length > 1 ? args[1] : "30");
        StringBuilder big = new StringBuilder();
        for (int i = 0; i < 1000; i++) big.append('x');
        try {
            for (int t = 0; t < 20; t++) {
                clock.setTime(time += 100000);
                db.execute(db.trans().put("k" + (100 + t), big.toString() + t).build());
            }
            leaves("after 20 transactions", db);
            Db.Internal in = db.internal();
            long budget = in.eviction().budget();
            in.eviction().setBudget(1000);
            synchronized (in.getWriteLock()) {
                in.eviction().sweep(db, false);
            }
            in.eviction().setBudget(budget);
            leaves("after one batch", db);
            List<KeyNode> zero = new ArrayList<KeyNode>();
            for (Node o : in.cache().nodes()) {
                if (o instanceof KeyNode && ((KeyNode) o).countedMemSize == 0) zero.add((KeyNode) o);
            }
            for (int t = 20; t < 20 + more; t++) {
                clock.setTime(time += 100000);
                db.execute(db.trans().put("k" + (100 + t), big.toString() + t).build());
            }
            leaves("after " + more + " more", db);
            for (KeyNode k : zero) {
                Node now = in.cache().getNode(k.getId());
                System.out.println("  leaf " + k.getId() + " counted 0 after the batch: now "
                        + (k.isDirty() ? "dirty" : "clean, written at " + k.getSpos())
                        + ", in its handle " + (now == k) + ", counted " + k.countedMemSize
                        + ", bytes " + Residents.bytesOf(k));
            }
        } finally {
            db.close();
        }
    }
}
