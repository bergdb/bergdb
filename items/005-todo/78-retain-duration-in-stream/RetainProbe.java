package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import bergdb.common.StringUtil;
import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * The probe of bergdb 005-78 (U2), 2026-11-05: the retain duration is not kept in the
 * stream, so a restart that does not set it again gives another stream. It runs
 * StreamDigest's l3-* workloads (StreamDigest's constructor, draw for draw) in these modes:
 *
 *   plain          the retain duration set at the start; no restarts.
 *   restarts-each  set after each start (StreamDigest's restarts); a restart every 'every'.
 *   restarts-once  set after the first start only; a restart every 'every'.
 *   restarts-50    set after the first start only; a restart every 50 commits.
 *   call-100       not set at the start; set after commit 100; no restarts.
 *   after-call     as call-100, with a restart right after the call, then every 50 commits.
 *   p3             plain, with an internal transaction after commit 10 that writes two KVs,
 *                  under reclaim's prefix and outside it (form B's record); at the end, are
 *                  they found after the cuts, and after a restart from the cut stream?
 *
 * Each run prints its length, the cut, sha256 from the decided cut (as StreamDigest), the
 * records by kind and the iterations (Reclaim.Stats, summed over the starts), and the cuts;
 * a run that differs from its reference (plain; after-call: call-100) prints the first
 * differing byte and the transaction there. plain also prints P5's costs: one call of
 * setStartupDistance (form A) and one internal transaction with a 30-byte value (form B).
 *
 * Build and run (in a clone at the base; no file in java/ changes):
 *
 *   cd java && ./build.sh
 *   mkdir -p /tmp/probe && javac -nowarn -d /tmp/probe -cp build/bergdb.jar:build/stress \
 *       ../items/005-todo/78-retain-duration-in-stream/RetainProbe.java
 *   java -ea -cp /tmp/probe:build/bergdb.jar:build/stress bergdb.core.RetainProbe all
 *   java -ea -Dstepreserve=N ... bergdb.core.RetainProbe l3-node8     (P4: the step reserve)
 *
 * The output of 2026-11-05 on 0c6c4be is probe.txt, beside this file (design.md, section
 * 4.1). Every database it starts is stopped; a restart starts on MemoryStream.copy(), as
 * StreamDigest does (a closed MemoryStream refuses appends).
 */
public class RetainProbe {
    static final String[] MODES = {
        "plain", "restarts-each", "restarts-once", "restarts-50", "call-100", "after-call", "p3"};

    static final String P3_KEY_RECLAIM = DbConstants.INTERNAL_PREFIX + "dreclaim/-probe.txt";
    static final String P3_KEY_OTHER = DbConstants.INTERNAL_PREFIX + "probe/retain.txt";

    final StreamDigest w;

    RetainProbe(StreamDigest w) {
        this.w = w;
    }

    /** One run's results. */
    static final class Run {
        String mode;
        MemoryStream stream;
        long[] endOf;                   // Stream length after commit i and its reclaim records.
        int starts;
        int firstRestart = -1;          // The commit after which the first restart came.
        long user, step, table;         // Records by kind, summed over the starts.
        long splitSteps;
        final List<long[]> iterations = new ArrayList<long[]>();    // pStart, tStart, steps.
        final List<long[]> cuts = new ArrayList<long[]>();          // pos, decidedTime.
        long length, firstPos, fap, fat;
        String sha;
        String extra = "";
    }

    Db start(MemoryStream stream, CoreTestClock clock, boolean setRetain, Run r) {
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        if (w.startupDistance > 0) b.startupDistance(w.startupDistance);
        if (w.maxNode == 8) b.maxNodeSize8();
        if (w.maxNode == 14) b.maxNodeSize14();
        if (w.maxNode == 30) b.maxNodeSize30();
        if (w.maxNode == 62) b.maxNodeSize62();
        Db db = b.start();
        synchronized (db.internal().getWriteLock()) {
            db.internal().reclaim().enableStats();
        }
        if (setRetain) db.setRetainDuration(retain());
        r.starts++;
        return db;
    }

    long retain() {
        return w.retain * Clock.UNITS_PER_SEC;
    }

    /** Adds the session's statistics to the run's. */
    static void harvest(Db db, Run r) {
        synchronized (db.internal().getWriteLock()) {
            Reclaim.Stats st = db.internal().reclaim().enableStats();
            r.user += st.user.records;
            r.step += st.step.records;
            r.table += st.table.records;
            for (Reclaim.Stats.Iteration it : st.iterations) {
                // An iteration that goes on over a restart is in both sessions' Stats.
                int k = r.iterations.size();
                long[] last = k == 0 ? null : r.iterations.get(k - 1);
                if (last != null && last[0] == it.pStart) last[2] += it.steps;
                else r.iterations.add(new long[] {it.pStart, it.tStart, it.steps});
                r.splitSteps += it.splitSteps;
            }
            for (Reclaim.Stats.Cut c : st.cuts) {
                r.cuts.add(new long[] {c.pos, c.decidedTime});
            }
        }
    }

    Run run(String mode) {
        boolean retainFirst = !mode.equals("call-100") && !mode.equals("after-call");
        boolean retainEach = mode.equals("restarts-each");
        int callAt = retainFirst ? -1 : 100;
        boolean restartAfterCall = mode.equals("after-call");
        int every = mode.equals("restarts-each") || mode.equals("restarts-once") ? w.every
                : mode.equals("restarts-50") || mode.equals("after-call") ? 50 : 0;

        Run r = new Run();
        r.mode = mode;
        r.endOf = new long[w.n];
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = start(stream, clock, retainFirst, r);
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
            r.endOf[i] = db.getStreamLength();

            boolean restart = false;
            if (i + 1 == callAt) {
                db.setRetainDuration(retain());
                restart = restartAfterCall;
            }
            if (mode.equals("p3") && i + 1 == 10) {
                Trans t = db.trans()
                        .put(Keys.toSegments(P3_KEY_RECLAIM), StringUtil.toBytes("retain=100"))
                        .put(Keys.toSegments(P3_KEY_OTHER), StringUtil.toBytes("retain=100"))
                        .build();
                t.isInternal = true;
                db.execute(t);
                r.extra += " p3written=" + db.getStreamLength();
            }
            if (every > 0 && (i + 1) % every == 0 && i + 1 < w.n
                    && (callAt < 0 || i + 1 > callAt || !restartAfterCall)) {
                restart = true;
            }
            if (restart && i + 1 < w.n) {
                if (r.firstRestart < 0) r.firstRestart = i;
                db.sync(SyncLevel.ORDINARY);
                harvest(db, r);
                db.stop();
                stream = stream.copy();
                db = start(stream, clock, retainEach, r);
            }
        }
        db.sync(SyncLevel.ORDINARY);
        long cut = Math.max(stream.getFirstPos(), db.getFirstAvailablePos());
        r.length = stream.getLength();
        r.firstPos = stream.getFirstPos();
        r.fap = db.getFirstAvailablePos();
        r.fat = db.getFirstAvailableLookupTime();
        r.sha = StreamDigest.digest(stream, cut);
        r.stream = stream.copy();
        harvest(db, r);

        if (mode.equals("p3")) {
            r.extra += " found=" + found(db, P3_KEY_RECLAIM) + "," + found(db, P3_KEY_OTHER);
            db.stop();
            stream = stream.copy();
            Run dummy = new Run();
            db = start(stream, clock, true, dummy);
            r.extra += " foundAfterRestart=" + found(db, P3_KEY_RECLAIM) + ","
                    + found(db, P3_KEY_OTHER);
        }
        if (mode.equals("plain")) {
            // P5: what one call costs, after the digest.
            long l0 = db.getStreamLength();
            clock.setTime(w.times[w.n - 1] + 1);
            Trans t = db.trans().put(Keys.toSegments(P3_KEY_OTHER), new byte[30]).build();
            t.isInternal = true;
            db.execute(t);
            long l1 = db.getStreamLength();
            clock.setTime(w.times[w.n - 1] + 2);
            db.setStartupDistance(db.getStartupDistance() * 2);
            long l2 = db.getStreamLength();
            r.extra += " costB=" + (l1 - l0) + " costA=" + (l2 - l1);
        }
        db.stop();
        return r;
    }

    static String found(Db db, String key) {
        byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key), db.newGetData());
        return v == null ? "no" : "yes";
    }

    /** The first position from which a and b differ, or -1 (from the larger first pos). */
    static long firstDiff(MemoryStream a, MemoryStream b) throws IOException {
        long from = Math.max(a.getFirstPos(), b.getFirstPos());
        long to = Math.min(a.getLength(), b.getLength());
        byte[] x = new byte[65536], y = new byte[65536];
        for (long pos = from; pos < to; pos += x.length) {
            int chunk = (int) Math.min(x.length, to - pos);
            a.read(pos, x, 0, chunk);
            b.read(pos, y, 0, chunk);
            for (int k = 0; k < chunk; k++) {
                if (x[k] != y[k]) return pos + k;
            }
        }
        return a.getLength() == b.getLength() ? -1 : to;
    }

    void print(Run r) {
        int k = r.iterations.size();
        long lastIter = k == 0 ? -1 : r.iterations.get(k - 1)[1];
        long lastCut = r.cuts.isEmpty() ? -1 : r.cuts.get(r.cuts.size() - 1)[1];
        System.out.println("RUN " + w.name + " " + r.mode + " length=" + r.length
                + " firstPos=" + r.firstPos + " fap=" + r.fap + " fat=" + r.fat
                + " retained=" + (r.length - r.firstPos)
                + " starts=" + r.starts + " firstRestartAfter=" + r.firstRestart
                + " user=" + r.user + " step=" + r.step
                + " table=" + r.table + " iterations=" + r.iterations.size()
                + " lastIterationT=" + lastIter + " cuts=" + r.cuts.size()
                + " lastCutT=" + lastCut + " splitSteps=" + r.splitSteps
                + " sha256=" + r.sha.substring(0, 16) + r.extra);
    }

    /**
     * Where r leaves ref: the first commit after which the two streams have other lengths
     * (endOf), and the bytes from the larger first position up to that commit's start.
     */
    void compare(Run ref, Run r) throws IOException {
        int i = 0;
        while (i < w.n && ref.endOf[i] == r.endOf[i]) i++;
        if (i == w.n && ref.sha.equals(r.sha) && ref.length == r.length
                && firstDiff(ref.stream, r.stream) < 0) {
            System.out.println("  SAME " + w.name + " " + r.mode + " = " + ref.mode
                    + " (lengths after every commit, sha256 from the cut, bytes from "
                    + Math.max(ref.firstPos, r.firstPos) + ")");
            return;
        }
        long before = i == 0 ? 0 : ref.endOf[i - 1];
        long from = Math.max(ref.stream.getFirstPos(), r.stream.getFirstPos());
        String bytes = "not compared (both cut past it)";
        if (from < before) {
            long d = firstDiffUpTo(ref.stream, r.stream, from, before);
            bytes = d < 0 ? "equal from " + from + " to " + before : "first differ at " + d;
        }
        String refIt = "none", rIt = "none";
        for (long[] it : ref.iterations) {
            if (it[0] > before && refIt.equals("none")) refIt = "pStart=" + it[0] + " t=" + it[1];
        }
        for (long[] it : r.iterations) {
            if (it[0] > before && rIt.equals("none")) rIt = "pStart=" + it[0] + " t=" + it[1];
        }
        System.out.println("  DIFFER " + w.name + " " + r.mode + " from " + ref.mode
                + ": the lengths part at commit " + i + " (t=" + (i < w.n ? w.times[i] : -1)
                + ", starts at " + before + "; ends " + (i < w.n ? ref.endOf[i] : -1)
                + " against " + (i < w.n ? r.endOf[i] : -1) + "); bytes before it " + bytes
                + "; next iteration from there: " + ref.mode + " " + refIt + ", " + r.mode
                + " " + rIt + "; sha256 " + (ref.sha.equals(r.sha) ? "same" : "differs")
                + "; retained " + (ref.length - ref.firstPos) + " against "
                + (r.length - r.firstPos));
    }

    static long firstDiffUpTo(MemoryStream a, MemoryStream b, long from, long to)
            throws IOException {
        byte[] x = new byte[65536], y = new byte[65536];
        for (long pos = from; pos < to; pos += x.length) {
            int chunk = (int) Math.min(x.length, to - pos);
            a.read(pos, x, 0, chunk);
            b.read(pos, y, 0, chunk);
            for (int k = 0; k < chunk; k++) {
                if (x[k] != y[k]) return pos + k;
            }
        }
        return -1;
    }

    public static void main(String[] args) throws IOException {
        List<String> wanted = java.util.Arrays.asList(args);
        System.out.println("PROBE 005-78 stepreserve=" + Long.getLong("stepreserve", -1));
        for (String[] c : StreamDigest.CONFIGS) {
            if (!c[0].startsWith("l3-")) continue;
            if (!wanted.contains("all") && !wanted.contains(c[0])) continue;
            StreamDigest w = new StreamDigest(c[0], Long.parseLong(c[1]), c[2]);
            System.out.println("CONFIG " + c[0] + " " + c[2]);
            RetainProbe p = new RetainProbe(w);
            Run plain = null, call100 = null;
            for (String mode : MODES) {
                Run r = p.run(mode);
                p.print(r);
                if (mode.equals("plain")) plain = r;
                else if (mode.equals("call-100")) {
                    call100 = r;
                    p.compare(plain, r);
                } else if (mode.equals("after-call")) {
                    p.compare(call100, r);
                } else if (!mode.equals("p3")) {
                    p.compare(plain, r);
                }
            }
        }
    }
}
