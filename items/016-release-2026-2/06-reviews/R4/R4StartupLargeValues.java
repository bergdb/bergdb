package bergdb.core;

import java.lang.reflect.Field;
import java.util.List;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.stream.MemoryStream;

/** The writer's admission list is also populated by replay, but not drained at startup. */
public final class R4StartupLargeValues {
    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(stream).clock(clock).audit(0).start()) {
            clock.setTime(1000000);
            byte[] value = new byte[1200 * 1024];
            db.execute(db.trans().put("a", value).put("b", value).put("c", value).build());
        }
        try (Db db = Db.builder().testSetup(stream.copy()).clock(clock)
                .cacheSizeIndicator(1).evictionSchedule(Eviction.Schedule.BUDGET, 1)
                .audit(0).start()) {
            Eviction eviction = db.internal().eviction();
            eviction.awaitBatch();
            Field field = Eviction.class.getDeclaredField("largeValues");
            field.setAccessible(true);
            List<?> pending = (List<?>) field.get(eviction);
            long payload = 0;
            int pointers = 0;
            synchronized (db.internal().getWriteLock()) {
                for (Object entry : pending) payload += ((ValueNode) ((Object[]) entry)[2]).getValue().length;
                for (Node node : db.internal().cache().nodes()) {
                    for (int i = 0; i < node.getSize(); i++)
                        if (node.getPointee(i) instanceof ValueNode) pointers++;
                }
                System.out.println("after restart and eviction: resident bytes="
                        + db.internal().cache().residents().bytes() + "; resident value pointers=" + pointers);
                System.out.println("admission list retains=" + pending.size()
                        + " entries; payload bytes=" + payload);
            }
            if (payload == 0) throw new AssertionError("no startup retention reproduced");
        }
    }
}
