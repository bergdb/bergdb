package bergdb.core;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.LockSupport;

import bergdb.stream.MemoryStream;

/**
 * bergdb 005-48, group commit: StreamDigest's workloads with syncs, the path that the
 * prototype changes. Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
 *
 * Mode "syncs": the transactions of a configuration, draw for draw as in StreamDigest, with a
 * sync(ORDINARY) after every 7th, and a second thread that calls sync(ORDINARY) in a loop
 * (with a pause of 50 us) while they run. With the prototype every sync has what is buffered
 * written at once, so the appends of the write buffer end at points that depend on timing;
 * without it they end at the buffer's timer. Prints a DIGEST line in StreamDigest's format
 * (StreamDigest compare compares two outputs), and checks that the stream from the decided
 * cut (sha256) is the one of StreamDigest's mode plain, run in the same JVM.
 *
 * The physical cut waits for durability, so firstPos and sha256all may differ between runs
 * (StreamDigest's Javadoc); sha256, from the decided cut, may not.
 *
 * Usage: java -cp JAR:STRESS:CLASSES bergdb.core.SyncDigest all|quick|NAME...
 * STRESS is a build's build/stress (StreamDigest), CLASSES this class.
 */
public class SyncDigest {

    static String runSyncs(StreamDigest w, long[] syncCount) throws InterruptedException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        final Db db = w.start(stream, clock);
        final AtomicBoolean done = new AtomicBoolean();
        final AtomicLong syncs = new AtomicLong();
        final Throwable[] failure = new Throwable[1];
        Thread syncer = new Thread(new Runnable() {
            public void run() {
                try {
                    while (!done.get()) {
                        db.sync(SyncLevel.ORDINARY);
                        syncs.incrementAndGet();
                        LockSupport.parkNanos(50000);
                    }
                } catch (Throwable e) {
                    failure[0] = e;
                }
            }
        });
        syncer.start();
        for (int i = 0; i < w.n; i++) {
            clock.setTime(w.times[i]);
            Trans.Builder b = db.trans();
            String[] ks = w.keys.get(i);
            byte[][] vs = w.values.get(i);
            for (int j = 0; j < ks.length; j++) {
                if (vs[j] == StreamDigest.DELETED) b.delete(ks[j]);
                else b.put(ks[j], vs[j]);
            }
            db.execute(b.build());
            if (i % 7 == 6) {
                db.sync(SyncLevel.ORDINARY);
                syncs.incrementAndGet();
            }
        }
        done.set(true);
        syncer.join();
        if (failure[0] != null) throw new RuntimeException("the syncer failed", failure[0]);
        db.sync(SyncLevel.STRONG);
        long cut = Math.max(stream.getFirstPos(), db.getFirstAvailablePos());
        String line = "DIGEST " + w.name + " syncs length=" + stream.getLength()
                + " firstPos=" + stream.getFirstPos()
                + " firstAvailablePos=" + db.getFirstAvailablePos()
                + " firstAvailableTime=" + db.getFirstAvailableLookupTime()
                + " sha256all=" + StreamDigest.digest(stream, stream.getFirstPos())
                + " sha256=" + StreamDigest.digest(stream, cut);
        db.stop();
        syncCount[0] = syncs.get();
        return line;
    }

    static String sha(String line) {
        return line.substring(line.indexOf(" sha256=") + 8);
    }

    public static void main(String[] args) throws Exception {
        if (args.length == 0) {
            System.out.println("Usage: SyncDigest all|quick|NAME...");
            System.exit(2);
        }
        java.util.Set<String> wanted = new java.util.HashSet<String>(java.util.Arrays.asList(args));
        int configs = 0, diffs = 0;
        for (String[] c : StreamDigest.CONFIGS) {
            boolean take = wanted.contains("all") || wanted.contains(c[0])
                    || (wanted.contains("quick") && !c[0].equals("l2-default-100MB"));
            if (!take) continue;
            configs++;
            StreamDigest w = new StreamDigest(c[0], Long.parseLong(c[1]), c[2]);
            System.out.println("CONFIG " + c[0] + " seed=" + c[1] + " " + c[2]);
            long t0 = System.nanoTime();
            long[] syncs = new long[1];
            String line = runSyncs(w, syncs);
            System.out.println(line);
            System.out.println("  " + c[0] + " syncs: " + syncs[0] + " syncs, "
                    + (System.nanoTime() - t0) / 1000000 + " ms");
            String plain = w.run("plain");
            if (!sha(plain).equals(sha(line))) {
                diffs++;
                System.out.println("MODES DIFFER: " + c[0] + " syncs differs from plain after the decided cut");
                System.out.println("  plain: " + plain);
            }
        }
        System.out.println("Done: " + configs + " configurations; "
                + (diffs == 0 ? "syncs gives the stream of plain" : diffs + " differences from plain"));
    }
}
