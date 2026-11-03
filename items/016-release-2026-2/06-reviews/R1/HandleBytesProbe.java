package bergdb.core;

import java.util.IdentityHashMap;

import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Pointee;
import bergdb.dag.TopNode;
import bergdb.stream.MemoryStream;

/**
 * Probe for review R1 (016-06): the resident bytes (Residents) count no handle, live or dead,
 * where 009-02, 4.7 says "Handles are counted too": a live handle with its table entry as the
 * table's (79 bytes, T1a), and each pointer of a resident object that holds a handle with the
 * handle's 32 bytes. A database of 20,000 keys under the random schedule (seed 1), read once;
 * then the handles that the pointers of the resident objects hold, and the live handles of
 * the table, against Residents.bytes(). Usage (before the jar):
 * java -cp probes:build/bergdb.jar bergdb.core.HandleBytesProbe
 */
public class HandleBytesProbe {
    public static void main(String[] args) {
        CoreTestClock clock = new CoreTestClock();
        long time = 1000 * 1000;
        Db db = Db.builder().testSetup(new MemoryStream()).clock(clock).testId()
                .evictionSchedule(Eviction.Schedule.RANDOM, 1).start();
        try {
            for (int t = 0; t < 200; t++) {
                clock.setTime(time += 100000);
                Trans.Builder b = db.trans();
                for (int j = 0; j < 100; j++) b.put("key" + (t * 100 + j), "value" + t);
                db.execute(b.build());
            }
            for (int k = 0; k < 20000; k += 3) DbUtil.get(db, "key" + k);
            Db.Internal in = db.internal();
            in.evictNow(Eviction.Schedule.RANDOM, 2);
            Cache3 table = in.cache();
            long live = table.handles().size();
            IdentityHashMap<Handle, Boolean> held = new IdentityHashMap<Handle, Boolean>();
            long heldPointers = 0, dead = 0;
            for (Node o : table.nodes()) {
                for (int i = 0; i < o.getSize(); i++) {
                    Pointee p = o.getPointee(i);
                    if (p instanceof Handle) {
                        heldPointers++;
                        if (((Handle) p).isDead()) dead++;
                        held.put((Handle) p, Boolean.TRUE);
                    }
                }
            }
            long counted = table.residents().bytes();
            long byPlan = 79 * live + 32 * heldPointers;
            KeyNode k = new KeyNode(false);
            for (int i = 0; i < 30; i++) k.addToEnd(bergdb.dag.Klong.createKey(new byte[] {(byte) i}),
                    new Handle(1001 + 2 * i), 1000 + 8 * i);
            System.out.println("resident bytes (Residents): " + counted + ", resident objects "
                    + table.nodes().size() + ", live handles " + live);
            System.out.println("pointers of resident objects that hold a handle: " + heldPointers
                    + " (dead " + dead + ", distinct handles " + held.size() + ")");
            System.out.println("not counted, by 009-02 4.7's rule: " + byPlan + " bytes ("
                    + (100 * byPlan / Math.max(1, counted)) + " percent of the resident bytes)");
            System.out.println("a key node with 30 handle pointers: Residents.bytesOf "
                    + Residents.bytesOf(k) + ", getMemSize " + k.getMemSize());
        } finally {
            db.close();
        }
    }
}
