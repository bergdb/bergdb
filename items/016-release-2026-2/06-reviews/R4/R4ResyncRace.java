package bergdb.core;

import java.util.Arrays;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.ValueNode;

/** A reader adds a value after its holder was visited but before the total is set. */
public final class R4ResyncRace {
    public static void main(String[] args) throws Exception {
        Residents residents = new Residents();
        KeyNode holder = KeyNode.nodeWithTime(10);
        holder.addToEnd(Klong.createKey(new byte[] {1}), null, 1000);
        KeyNode last = KeyNode.nodeWithTime(10);
        residents.added(holder);
        residents.added(last);
        ValueNode value = new ValueNode(new byte[100], 1000);
        AtomicReference<Throwable> problem = new AtomicReference<>();
        Object writeLock = new Object();
        Thread resync = new Thread(() -> {
            try {
                synchronized (writeLock) { residents.resync(Arrays.asList(holder, last)); }
            } catch (Throwable x) { problem.set(x); }
        }, "resync-writer");
        synchronized (last) {
            resync.start();
            long end = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
            while (resync.getState() != Thread.State.BLOCKED) {
                if (System.nanoTime() >= end) throw new AssertionError("resync did not reach last node");
                Thread.yield();
            }
            // The only monitor that can block resync is 'last', so holder was counted.
            synchronized (holder) {
                holder.setPointee(1, value);
                residents.valueIn(holder, value);
            }
        }
        resync.join(5000);
        if (resync.isAlive() || problem.get() != null)
            throw new AssertionError("resync failed", problem.get());
        long sum = (long) Residents.counted(holder) + Residents.counted(last);
        System.out.println("after concurrent resync/load: total=" + residents.bytes()
                + "; sum of node counts=" + sum + "; lost bytes=" + (sum - residents.bytes()));
        residents.released(holder);
        residents.released(last);
        System.out.println("after releasing every resident: bytes=" + residents.bytes()
                + "; objects=" + residents.objects());
        if (residents.bytes() >= 0) throw new AssertionError("expected the lost update to reproduce");
    }
}
