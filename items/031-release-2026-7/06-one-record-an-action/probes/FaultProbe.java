package bergdb.core;

import java.io.IOException;
import java.util.*;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06's probe of Codex's second test (2026-11-27): a failure or a stop injected
 * at four points of a record that carries B, S, P or C, a commit's and a part's:
 *
 *   plan-stop, plan-fail   before the plan (TestHooks.beforePlan): stop(), or an exception;
 *   go-stop, go-fail       between the plan and the append, at the go point (kvApplied, the
 *                          batch's first operation): stop(), or an exception;
 *   append-fail            during the append: the stream refuses the bytes from the middle
 *                          of the record on (a torn record, a storage failure);
 *   apply-stop, apply-fail after the append, before Maintenance.apply (beforeApply).
 *
 * Each must end as a refusal with nothing written and reclaim's memory unchanged, an
 * accepted record, or a failed database; then a start from the stream must have the memory
 * that the running database had at that boundary (the uninterrupted run's after record k,
 * or after record k - 1 when the action is not in the stream), and the actions continued
 * from there (record k's action again if it is not in the stream; for a part, the call
 * ended after its parts in the stream) must give the uninterrupted run's stream. A torn
 * record (append-fail) is an input (031-05, review F2): its continuation is checked to be a
 * function of the torn stream (alone and with restarts) and the bytes before it the
 * reference's.
 *
 * Usage, as P2CrashProbe, compiled with it:
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.FaultProbe SEED ACTIONS SD [PER_KIND]
 */
public class FaultProbe {
    static final String[] POINTS = {"plan-stop", "plan-fail", "go-stop", "go-fail",
            "append-fail", "apply-stop", "apply-fail"};

    static String point;
    static int armAt = -1;          // the record (1-based) to inject at
    static int seen;                // records begun (beforePlan) or written, by the hooks
    static boolean injected;
    static FailingStream failing;

    /** A CutStream that refuses the bytes from position 'failAt' on (append-fail). */
    static final class FailingStream extends CutStream {
        volatile long failAt = -1;
        @Override
        public void append(byte[] source, int offset, int length) throws IOException {
            final long len = getLength();
            if (failAt >= 0 && len + length > failAt) {
                final int part = (int) Math.max(0, failAt - len);
                super.append(source, offset, part);
                failAt = -1;
                injected = true;
                throw new IOException("append-fail, injected at " + (len + part));
            }
            super.append(source, offset, length);
        }
    }

    static final class Injected extends RuntimeException {
        Injected(String p) { super("injected: " + p); }
    }

    static void installHook() {
        Db.testHooks = new Db.TestHooks() {
            boolean first;
            public int maintainMaxParts() {
                return P2CrashProbe.maxParts;
            }
            public void beforePlan(Db.ExecuteData x) {
                if (!P2CrashProbe.countOn) return;
                first = true;
                if (P2CrashProbe.records + 1 == armAt && point.startsWith("plan-")) {
                    injected = true;
                    if (point.equals("plan-stop")) P2CrashProbe.cur.stop();
                    else throw new Injected(point);
                }
            }
            public void kvApplied(long[] key, byte[] value) {
                if (!P2CrashProbe.countOn || !first) return;
                first = false;
                if (P2CrashProbe.records + 1 == armAt && point.startsWith("go-")) {
                    injected = true;
                    if (point.equals("go-stop")) P2CrashProbe.cur.stop();
                    else throw new Injected(point);
                }
            }
            public void beforeApply(Db.ExecuteData x) {
                if (!P2CrashProbe.countOn) return;
                if (P2CrashProbe.records + 1 == armAt && point.startsWith("apply-")) {
                    injected = true;
                    if (point.equals("apply-stop")) P2CrashProbe.cur.stop();
                    else {
                        P2CrashProbe.records++;     // the record is in the stream
                        throw new Injected(point);
                    }
                }
            }
            public void transExecuted(Db.ExecuteData x) {
                if (!P2CrashProbe.countOn) return;
                P2CrashProbe.Rec rc = new P2CrashProbe.Rec();
                rc.tpos = x.trans.tpos;
                rc.end = x.trans.nextPos;
                rc.action = P2CrashProbe.curAction;
                rc.part = x.trans.part;
                rc.carries = x.plan != null;
                if (rc.part) P2CrashProbe.partsInCall++;
                rc.partsBefore = P2CrashProbe.partsInCall;
                if (P2CrashProbe.recs != null) {
                    rc.memory = P2CrashProbe.memory(P2CrashProbe.cur);
                    kinds.add(kinds(x.plan));
                    P2CrashProbe.recs.add(rc);
                }
                P2CrashProbe.records++;
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
    }

    static List<String> kinds = new ArrayList<>();
    
    static DbState state(Db d) throws Exception {
        java.lang.reflect.Field f = Db.class.getDeclaredField("state");
        f.setAccessible(true);
        return (DbState) f.get(d);
    }

    /** B, S, P, C of a record's plan. */
    static String kinds(Maintenance.Plan plan) {
        if (!(plan instanceof Reclaim.RecordPlan)) return "";
        Reclaim.RecordPlan p = (Reclaim.RecordPlan) plan;
        StringBuilder b = new StringBuilder();
        for (Reclaim.IterationInfo row : p.rows) {
            if (row.pStart == p.l0 && !row.done) { b.append('B'); break; }
        }
        if (p.next != null) b.append('S');
        for (Reclaim.IterationInfo row : p.rows) {
            if (row.pSafe == p.l0) { b.append('P'); break; }
        }
        if (p.cut != null) b.append('C');
        return b.toString();
    }

    public static void main(String[] args) throws Exception {
        long seed = Long.parseLong(args[0]);
        int n = Integer.parseInt(args[1]);
        int sd = Integer.parseInt(args[2]);
        int perKind = args.length > 3 ? Integer.parseInt(args[3]) : 6;
        installHook();
        List<P2CrashProbe.Action> as = P2CrashProbe.workload(seed, n, sd);
        List<P2CrashProbe.Rec> rs = new ArrayList<>();
        P2CrashProbe.Image ref = P2CrashProbe.reference(as, rs);
        // The records to inject at: per kind, commits and parts, up to perKind each.
        Map<String, List<Integer>> chosen = new TreeMap<>();
        for (int k = 2; k <= rs.size(); k++) {
            P2CrashProbe.Rec rc = rs.get(k - 1);
            for (char c : kinds.get(k - 1).toCharArray()) {
                String key = c + (rc.part ? " part" : " commit");
                List<Integer> l = chosen.computeIfAbsent(key, x -> new ArrayList<>());
                if (l.size() < perKind) l.add(k);
            }
        }
        System.out.println("seed " + seed + ", actions " + as.size() + ", records " + rs.size()
                + ", reference digest " + ref.digest() + "; records chosen: " + chosen);
        Map<String, P2CrashProbe.Image> refs = new HashMap<>();
        for (String pt : POINTS) {
            point = pt;
            int refused = 0, accepted = 0, failed = 0, memSame = 0, contSame = 0, bad = 0, notHit = 0;
            List<String> bads = new ArrayList<>();
            TreeSet<Integer> ks = new TreeSet<>();
            for (List<Integer> l : chosen.values()) ks.addAll(l);
            for (int k : ks) {
                P2CrashProbe.Rec rc = rs.get(k - 1);
                P2CrashProbe.Action at = as.get(rc.action);
                FailingStream s = new FailingStream();
                P2CrashProbe.countOn = false; P2CrashProbe.recs = null;
                Db d = P2CrashProbe.start(s);
                P2CrashProbe.cur = d;
                P2CrashProbe.records = 0; P2CrashProbe.countOn = true;
                injected = false;
                armAt = k;
                if (pt.equals("append-fail")) {
                    // From the middle of record k on; armed when record k - 1 is written.
                    s.failAt = -1;
                }
                String memBefore = null;
                boolean returned = true;
                int i = 0;
                for (; i < as.size(); i++) {
                    P2CrashProbe.curAction = i; P2CrashProbe.partsInCall = 0;
                    if (pt.equals("append-fail") && i == rc.action) {
                        s.failAt = rc.tpos + (rc.end - rc.tpos) / 2;
                    }
                    if (i == rc.action) memBefore = P2CrashProbe.memory(d);
                    returned = P2CrashProbe.run(d, as.get(i));
                    if (injected || P2CrashProbe.records >= k) break;
                }
                P2CrashProbe.countOn = false;
                armAt = -1;
                boolean dbFailed = state(d) == DbState.FAILED;
                String memAfter = P2CrashProbe.memory(d);
                try { d.sync(SyncLevel.ORDINARY); } catch (RuntimeException e) { }
                try { d.close(); } catch (RuntimeException e) { }
                s.failAt = -1;      // the buffer's bytes reach the stream at the sync or close
                if (!injected) {
                    notHit++;
                    if (pt.equals("append-fail") && bads.size() < 10) bads.add("not hit at " + k
                            + ": stream " + s.getLength() + ", record " + rc.tpos + ".." + rc.end);
                    continue;
                }
                CutStream c = s.copy();
                final boolean torn = pt.equals("append-fail");
                final boolean inStream = c.getLength() >= rc.end;
                String outcome;
                if (torn) {
                    outcome = "torn";
                    failed++;
                } else if (inStream) {
                    outcome = "accepted";
                    accepted++;
                } else if (dbFailed) {
                    outcome = "failed";
                    failed++;
                } else {
                    outcome = "refused";
                    refused++;
                    // A refusal changes nothing: the stream and reclaim's memory as before.
                    if (c.getLength() != rc.tpos || !memAfter.equals(rs.get(k - 2).memory)) {
                        bad++;
                        bads.add(pt + " at " + k + ": refused, but the stream " + c.getLength()
                                + " (before " + rc.tpos + ") or memory changed");
                        continue;
                    }
                }
                if (!torn && !inStream && c.getLength() != rc.tpos) {
                    bad++;
                    bads.add(pt + " at " + k + " (" + outcome + "): stream " + c.getLength()
                            + ", the record at " + rc.tpos + ".." + rc.end);
                    continue;
                }
                // The start's memory and the continuation.
                Db b = P2CrashProbe.start(c);
                P2CrashProbe.cur = b;
                String want = inStream ? rc.memory : rs.get(k - 2).memory;
                if (P2CrashProbe.memory(b).equals(want)) memSame++;
                else if (!torn) {
                    bad++;
                    bads.add(pt + " at " + k + " (" + outcome + "): the start's memory\n"
                            + P2CrashProbe.memory(b) + "the running one's\n" + want);
                }
                int next = inStream ? rc.action + 1 : rc.action;
                P2CrashProbe.Image wantImage = ref;
                if (at.kind == 'm') {
                    int parts = inStream ? rc.partsBefore : rc.partsBefore - 1;
                    String key = rc.action + "/" + parts;
                    wantImage = refs.get(key);
                    if (wantImage == null) {
                        List<P2CrashProbe.Action> bs = new ArrayList<>(as);
                        P2CrashProbe.Action lim = at.copy();
                        lim.arg = -parts - 1;
                        bs.set(rc.action, lim);
                        wantImage = P2CrashProbe.reference(bs, null);
                        refs.put(key, wantImage);
                    }
                    next = rc.action + 1;
                }
                CutStream c2 = c.copy();
                P2CrashProbe.Image got = P2CrashProbe.finish(b, c, as, next, 0);
                String why;
                if (torn) {
                    Db b2 = P2CrashProbe.start(c2);
                    P2CrashProbe.cur = b2;
                    P2CrashProbe.Image got2 = P2CrashProbe.finish(b2, c2, as, next, 9);
                    why = P2CrashProbe.compare(got, got2);
                } else {
                    why = P2CrashProbe.compare(wantImage, got);
                }
                if (why == null) contSame++;
                else {
                    bad++;
                    bads.add(pt + " at " + k + " (" + at + ", " + outcome + "): " + why);
                }
            }
            System.out.println(pt + ": " + refused + " refused, " + accepted + " accepted, "
                    + failed + " failed (a torn record for append-fail); the start's memory as "
                    + "the running one's " + memSame + "; continued to the reference "
                    + "(append-fail: the same with restarts) " + contSame + "; bad " + bad
                    + "; not hit " + notHit);
            for (int j = 0; j < Math.min(10, bads.size()); j++) System.out.println("  " + bads.get(j));
        }
    }
}
