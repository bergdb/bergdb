package bergdb.core;

import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-04: the calls of a full pass against kept / budget, and the longest call. N
 * keys of VAL bytes put (500 a transaction, 4-byte keys), startup distance SD, the retain
 * duration forever while they are put, then R = 1 s and calls of maintain(B), a call a
 * millisecond of a test clock: the calls until the pass is done (the last done row, one
 * that cuts at its own pStart: a commit's iteration that the calls continue first is
 * counted in), until its cut, and 2,000
 * more, which must write nothing. B may be a list, b1,b2,...: after the first pass, a put of
 * 10 bytes (the application's) and the next pass with the next budget. -Drounds=K puts
 * the keys K times, so that (K - 1) / K of the stream kept is dead at the first pass. With LAT > 0, a thread commits a put of 10 bytes every
 * LAT ms of wall time during the calls, and the longest commit is printed (P1: a commit
 * waits for at most one part of a call); the database is then written to, so the pass is
 * followed by more.
 *   java -Xmx..g -cp out:bergdb.jar bergdb.core.PassProbe N VAL B [SD [LAT [CALLS]]]
 */
public class PassProbe {
    /** -Dnocalls=true: a sleep of 1 ms in place of each call, for the commits' own latency. */
    static final boolean NO_CALLS = Boolean.getBoolean("nocalls");
    
    /** The number of the call that runs (from 0), for the committer's thread. */
    static volatile long callNo;
    
    static byte[] key(int b, int k) {
        return new byte[] {(byte) b, (byte) (k >> 16), (byte) (k >> 8), (byte) k};
    }

    public static void main(String[] a) throws Exception {
        final int n = Integer.parseInt(a[0]), val = Integer.parseInt(a[1]);
        final String[] budgets = a[2].split(",");
        final int sd = a.length > 3 ? Integer.parseInt(a[3]) : 50_000_000;
        final int lat = a.length > 4 ? Integer.parseInt(a[4]) : 0;
        final int maxCalls = a.length > 5 ? Integer.parseInt(a[5]) : Integer.MAX_VALUE;
        final long ms = Clock.UNITS_PER_SEC / 1000;
        final AtomicLong time = new AtomicLong(Clock.UNITS_PER_SEC);
        final Db d = Db.builder().mainStream(new CutStream()).clock(time::get).start();
        d.setStartupDistance(sd);
        final long f0 = System.nanoTime();
        final int rounds = Integer.getInteger("rounds", 1);     // -Drounds=4: 3/4 dead
        for (int r = 0; r < rounds; r++) {
            for (int i = 0; i < n; i += 500) {
                Trans.Builder t = d.trans();
                for (int k = i; k < i + 500 && k < n; k++) t.put(key(0x10, k), new byte[val]);
                time.addAndGet(ms);
                d.execute(t.build());
            }
        }
        d.setRetainDuration(Clock.UNITS_PER_SEC);
        System.out.println(String.format("n %d val %d sd %d rounds %d: put in %.1f s; uptime: %s",
                n, val, sd, rounds, (System.nanoTime() - f0) / 1e9, uptime()));
        for (int pass = 0; pass < budgets.length; pass++) {
            if (pass > 0) {
                time.addAndGet(ms);
                d.execute(d.trans().put(key(0x30, pass), new byte[10]).build());
            }
            pass(d, time, Integer.parseInt(budgets[pass]), lat, maxCalls);
        }
        d.close();
    }
    
    static String uptime() {
        try {
            Process p = new ProcessBuilder("uptime").start();
            return new String(p.getInputStream().readAllBytes()).trim();
        } catch (java.io.IOException e) {
            return "?";
        }
    }
    
    static void pass(Db d, AtomicLong time, int b, int lat, int maxCalls) throws Exception {
        final long ms = Clock.UNITS_PER_SEC / 1000;
        final long kept0 = d.getStreamLength() - d.getFirstAvailablePos();
        final long fp0 = d.getFirstAvailablePos();
        System.out.println(String.format(" budget %d: stream kept %d bytes; kept / budget %.1f "
                + "calls; JVM uptime %.3f s", b, kept0, kept0 / (b * 1000.0), jvmUptime()));
        final Reclaim rc = d.internal().reclaim();
        final long[] maxCommit = new long[2];     // the longest commit, and the call it came in
        final boolean[] stop = new boolean[1];
        Thread committer = null;
        if (lat > 0) {
            committer = new Thread(() -> {
                for (int i = 0; !stop[0]; i++) {
                    long t0 = System.nanoTime();
                    d.execute(d.trans().put(key(0x20, i % 1000), new byte[10]).build());
                    final long dt = System.nanoTime() - t0;
                    if (dt > maxCommit[0]) {
                        maxCommit[0] = dt;
                        maxCommit[1] = callNo;
                    }
                    try {
                        Thread.sleep(lat);
                    } catch (InterruptedException e) {
                        return;
                    }
                }
            });
            committer.start();
        }
        long calls = 0, callsDone = -1, callsCut = -1, maxCall = 0, sumCall = 0;
        long writtenDone = -1, len0 = d.getStreamLength(), lenCut = -1, lastWrite = -1;
        final long it0 = rc.getIterationCount();
        while (calls < maxCalls) {
            time.addAndGet(ms);
            final long l = d.getStreamLength(), t0 = System.nanoTime();
            if (NO_CALLS) {
                Thread.sleep(1);
            } else {
                M.call(d, b);
            }
            callNo = calls + 1;
            final long dt = System.nanoTime() - t0;
            maxCall = Math.max(maxCall, dt);
            sumCall += dt;
            calls++;
            if (d.getStreamLength() != l) lastWrite = calls;
            final Reclaim.IterationInfo done;
            synchronized (d.internal().getWriteLock()) {    // the committer's thread
                done = rc.lastDoneRow();
            }
            if (callsDone < 0 && done != null && done.pCut == done.pStart && done.pStart > fp0) {
                callsDone = calls;
                writtenDone = d.getStreamLength() - len0;
            }
            if (callsCut < 0 && d.getFirstAvailablePos() > fp0) {
                callsCut = calls;
                lenCut = d.getStreamLength();
            }
            if (callsCut > 0 && calls >= callsCut + 2000) break;
        }
        stop[0] = true;
        if (committer != null) committer.join();
        System.out.println(String.format("  pass done after %d calls (%.2f of kept / budget), "
                + "wrote %d bytes (%.2f of kept); cut after %d calls; then %d calls, the last "
                + "call that wrote %d, %s; kept %d bytes", callsDone,
                callsDone / (kept0 / (b * 1000.0)), writtenDone, writtenDone / (double) kept0,
                callsCut, calls - callsCut, lastWrite,
                d.getStreamLength() == lenCut ? "nothing written after the cut"
                        : (d.getStreamLength() - lenCut) + " bytes written after the cut",
                d.getStreamLength() - d.getFirstAvailablePos()));
        System.out.println(String.format("  calls: the longest %.1f ms, the mean %.3f ms%s",
                maxCall / 1e6, sumCall / 1e6 / calls,
                lat > 0 ? String.format("; the longest commit %.1f ms, in call %d", maxCommit[0] / 1e6,
                        maxCommit[1]) : ""));
        System.out.println(String.format("  calls ended at JVM uptime %.3f s; uptime: %s",
                jvmUptime(), uptime()));
    }
    
    /** The JVM's uptime in seconds, as -Xlog's uptime decoration, to find the GC pauses of the calls. */
    static double jvmUptime() {
        return java.lang.management.ManagementFactory.getRuntimeMXBean().getUptime() / 1000.0;
    }
}
