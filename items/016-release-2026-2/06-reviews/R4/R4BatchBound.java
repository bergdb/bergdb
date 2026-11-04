package bergdb.core;

import bergdb.dag.KeyNode;
import bergdb.stream.MemoryStream;

/** One full node-table map is larger than the documented ordinary batch. */
public final class R4BatchBound {
    public static void main(String[] args) {
        try (Db db = Db.builder().testSetup(new MemoryStream()).audit(0).start()) {
            Db.Internal in = db.internal();
            Eviction eviction = in.eviction();
            final int count = 5000;
            synchronized (in.getWriteLock()) {
                int added = 0;
                for (long id = 100001; added < count; id += 2) {
                    if (Cache3.mapIndex(id) != 0) continue;
                    KeyNode node = KeyNode.nodeWithTime(10);
                    node.setId(id);
                    node.setSpos(1000000000L + 8L * added);
                    in.cache().register(node);
                    added++;
                }
                long full = in.cache().residents().bytes();
                long budget = full / 10 * 9;
                eviction.setBudget(budget); // no asynchronous batch; same watermarks
                if (full > budget + (budget - Eviction.lowOf(budget)))
                    throw new AssertionError("unexpected pressure");
                long before = eviction.figures()[1];
                long[] result = eviction.sweep(db, false);
                long released = eviction.figures()[1] - before;
                System.out.println("ordinary batch limit=" + Eviction.BATCH
                        + "; pressure=false; colliding resident nodes=" + count);
                System.out.println("one sweep released=" + released + "; maps=" + result[1]);
                if (released <= Eviction.BATCH)
                    throw new AssertionError("expected the entire overfull map to be visited");
            }
        }
    }
}
