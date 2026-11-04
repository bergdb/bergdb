package bergdb.core;

import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import bergdb.dag.Handle;
import bergdb.stream.MemoryStream;

/** Empty-handle cleanup can invalidate Audit.check's unlocked handle snapshot. */
public final class R4AuditSnapshot {
    private static void await(CountDownLatch latch) {
        try {
            if (!latch.await(5, TimeUnit.SECONDS)) throw new AssertionError("latch timeout");
        } catch (InterruptedException x) { throw new AssertionError(x); }
    }

    private static void blockedIn(Thread thread, String className, String method) {
        long end = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
        while (System.nanoTime() < end) {
            if (thread.getState() == Thread.State.BLOCKED) {
                for (StackTraceElement frame : thread.getStackTrace())
                    if (frame.getClassName().equals(className) && frame.getMethodName().equals(method))
                        return;
            }
            Thread.yield();
        }
        throw new AssertionError("thread not blocked in " + className + "." + method);
    }

    public static void main(String[] args) throws Exception {
        try (Db db = Db.builder().testSetup(new MemoryStream()).audit(1).start()) {
            Db.Internal in = db.internal();
            Cache3 cache = in.cache();
            long earlyId = 100001;
            while (Cache3.mapIndex(earlyId) != 0) earlyId += 2;
            Handle empty = cache.liveOrNewHandle(earlyId);
            long lateId = earlyId + 2;
            while (Cache3.mapIndex(lateId) != Cache3.maps() - 1) lateId += 2;
            Object lateMap = cache.getLock(lateId);
            for (Handle h : cache.handles())
                if (cache.getLock(h.id) == lateMap) throw new AssertionError("late map not empty");
            CountDownLatch mapHeld = new CountDownLatch(1);
            CountDownLatch releaseMap = new CountDownLatch(1);
            AtomicReference<List<String>> result = new AtomicReference<>();
            AtomicReference<Throwable> problem = new AtomicReference<>();
            Thread blocker = new Thread(() -> {
                synchronized (lateMap) { mapHeld.countDown(); await(releaseMap); }
            }, "map-barrier");
            Thread auditor = new Thread(() -> {
                try {
                    synchronized (in.getWriteLock()) { result.set(Audit.check(db)); }
                } catch (Throwable x) { problem.set(x); }
            }, "audit-writer");
            try {
                synchronized (in.oracle()) {
                    auditor.start();
                    blockedIn(auditor, "bergdb.core.Audit$Oracle", "latest");
                    // table.nodes() is finished. Pause the later handles() snapshot at its last map.
                    blocker.start();
                    await(mapHeld);
                }
                blockedIn(auditor, "bergdb.core.Cache3", "handles");
                cache.dropIfEmpty(empty); // reader cleanup; it does not take writeLock
                releaseMap.countDown();
                auditor.join(5000);
                blocker.join(5000);
                if (auditor.isAlive() || blocker.isAlive() || problem.get() != null)
                    throw new AssertionError("probe did not complete", problem.get());
                System.out.println("reader removed its empty handle: dead=" + empty.isDead()
                        + "; still in table=" + (cache.liveHandle(earlyId) != null));
                System.out.println("audit result=" + result.get());
                if (result.get().isEmpty()) throw new AssertionError("false alarm not reproduced");
            } finally {
                releaseMap.countDown();
                if (blocker.getState() != Thread.State.NEW) blocker.join(5000);
                auditor.join(5000);
            }
        }
    }
}
