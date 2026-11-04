package bergdb.core;

import java.lang.reflect.Field;
import bergdb.dag.Node;
import bergdb.stream.MemoryStream;

/** A budget decrease stops above its budget after formerly pinned nodes become clean. */
public final class R4StalePinned {
    private static long field(Eviction e, String name) throws Exception {
        Field f = Eviction.class.getDeclaredField(name);
        f.setAccessible(true);
        return f.getLong(e);
    }

    public static void main(String[] args) throws Exception {
        for (int n : new int[] {500}) {
            CoreTestClock clock = new CoreTestClock();
            try (Db db = Db.builder().testSetup(new MemoryStream()).clock(clock).testId()
                    .maxNodeSize8().startupDistance(2000).audit(0).start()) {
                Db.Internal in = db.internal();
                Eviction e = in.eviction();
                long time = 1000000;
                for (int i = 0; i < n; i++) {
                    clock.setTime(time += 10000);
                    db.execute(db.trans().put("k" + i, new byte[100]).build());
                }
                db.setCacheSizeIndicator(1);
                e.awaitBatch();
                long oldPin;
                synchronized (in.getWriteLock()) {
                    oldPin = field(e, "pinnedOfLastRound");
                }
                db.setCacheSizeIndicator(Long.MAX_VALUE);
                clock.setTime(time += 10000);
                db.execute(db.trans().put("flush", new byte[10000]).build());
                long actualPin = 0;
                synchronized (in.getWriteLock()) {
                    for (Node node : in.cache().nodes()) {
                        if (!Eviction.detachable(node, in.superRoot(), in.newestWrittenTop()))
                            actualPin += Residents.bytesWithoutValues(node);
                    }
                }
                long before = in.cache().residents().bytes();
                System.out.println("n=" + n + "; old pinned=" + oldPin
                        + "; current pinned without values=" + actualPin + "; before=" + before);
                if (actualPin >= oldPin) continue;
                long budget = (actualPin + oldPin) / 2;
                db.setCacheSizeIndicator(budget);
                e.awaitBatch();
                long after = in.cache().residents().bytes();
                long candidates = 0;
                synchronized (in.getWriteLock()) {
                    for (Node node : in.cache().nodes()) {
                        if (Eviction.detachable(node, in.superRoot(), in.newestWrittenTop()))
                            candidates += Residents.countedBytes(node);
                    }
                }
                System.out.println("budget=" + budget + "; after=" + after
                        + "; detachable bytes left=" + candidates + "; trigger=" + field(e, "trigger"));
                if (after > budget && after - candidates <= budget) {
                    Field threadField = Eviction.class.getDeclaredField("evictor");
                    threadField.setAccessible(true);
                    Thread thread = (Thread) threadField.get(e);
                    long end = System.nanoTime() + 1000000000L;
                    while (thread.getState() != Thread.State.WAITING && System.nanoTime() < end)
                        Thread.yield();
                    System.out.println("evictor state=" + thread.getState()
                            + "; bytes after it settles=" + in.cache().residents().bytes());
                    if (thread.getState() != Thread.State.WAITING)
                        throw new AssertionError("evictor did not settle");
                    return;
                }
            }
        }
        throw new AssertionError("no stale pin case found");
    }
}
