package bergdb.core;

import java.security.MessageDigest;
import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06's probe of "one record an action": 031-05's P2CrashProbe for the design (e).
 * A seeded workload of actions, each with its time (puts of 0 to MAXV bytes at KEYS keys,
 * some of up to 8 keys, deletes, empty transactions, setters of the startup distance and
 * of the retain duration, maintain(B) calls, and a last empty transaction).
 *
 * The uninterrupted run gives the reference stream and its records. Checked there: every
 * record is one action's (031-06, rule 1): a commit appends exactly one, a setter one if it
 * changes the setting, else none, a maintain() call one a part (Trans.part), and nothing
 * else appends; so the records are as many as the accepted actions.
 *
 * For each record k: a run of the same actions up to record k, where the database is
 *   crash:    failed by the test hook after record k (transExecuted throws: P7);
 *   pre:      failed after record k's append, before Maintenance.apply (beforeApply throws);
 *   stop:     stopped there (transExecuted calls stop());
 * then a start from the stream, and the actions after record k's: the next action after
 * it, or for a part of a call that wrote p parts, the reference with that call ended after
 * p parts (Db.maintain(int, int)) and the action after the call. -Drestart=N restarts the
 * continued database every N actions too. The continued stream must equal the reference:
 * the same length, the same decided cut, and the same bytes from the first position kept.
 *
 * torn (-Dtorn=N, every N-th record): record k is torn, the stream cut inside it by 1 byte,
 * half of it, or all but 1 byte; a start (recovery keeps it as an aborted record, 014-01),
 * and record k's action and the rest; the same torn stream continued again with a restart
 * after the next action must give the same stream (the continuation is a function of the
 * torn stream), and the record's action must not be accepted (its KVs are absent before
 * it is run again). A torn record is an input, as the reviews of 031-05 state (F2).
 *
 * Usage (from java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT P2CrashProbe.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.P2CrashProbe SEED ACTIONS SD [crash|pre|stop|all|torn]
 *   -Dkeys=200 -Dmaxv=3000 -Dbudget=100 -Dmaint=8 (percent of actions that are calls)
 *   -Dnode=8 or 30; -Dfrom=K -Dto=K; -Dstride=N; -Drestart=N; -Dtorn=N
 * The variants of the review of 031-05 by Fable (its ReviewProbe), each the same in the
 * reference and the continued runs:
 *   -Dreader=1   a reader's currentTime() just before every action;
 *   -Drefuse=1   a refused transaction before every action (its key transformation throws:
 *                refused before the plan, nothing written);
 *   -Dclock=back every 7th action's clock 5 ms before the action before's; =still: one time
 *                for all actions (the records' times from the last record's);
 *   -Devict=1    eviction at every transaction (Eviction.Schedule.EVERY).
 *
 * This copy (review-main-probes/, the review of the landed diff, 2026-11-27) is the item's
 * probes/P2CrashProbe.java with landing.md's appendix applied (a part by
 * Db.TestHooks.maintainMaxParts(), not Db.maintain(int, int)) and the review's variants:
 *   -Dlimit=N    StoredTrans.recordLimit lowered to N, so that the record's room
 *                (Db.recordDirtyFits) plans steps again; a put that the limit refuses
 *                (005-17, 005-31) is an action with no record;
 *   -Dbig=P -Dbigkeys=K   P percent of the puts have 2 to K + 1 keys with small values;
 *   -Dreserve=N  DbBuilder.testStepReserve(N) at every start: split steps;
 *   -Dxform=1    a third of the puts by a value transformation that reads the value before;
 *                every fifth of those gives null, a delete;
 *   -Ddeep=1     keys of 14 segments;
 *   -Dtornall=true   the torn mode tears the records of parts and setters too.
 * The reference's line also gives the plans made again by the room (Reclaim.Stats).
 */
public class P2CrashProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final AtomicLong time = new AtomicLong(SEC);
    static final int KEYS = Integer.getInteger("keys", 200), MAXV = Integer.getInteger("maxv", 3000);
    static final int B = Integer.getInteger("budget", 100), MAINT = Integer.getInteger("maint", 8);
    static final int NODE = Integer.getInteger("node", 0);
    static final int RESTART = Integer.getInteger("restart", 0);
    static final boolean READER = Integer.getInteger("reader", 0) == 1;
    static final boolean REFUSE = Integer.getInteger("refuse", 0) == 1;
    static final String CLOCK = System.getProperty("clock", "");
    static final boolean EVICT = Integer.getInteger("evict", 0) == 1;
    static long refusedCalls;
    // review-main's variants (031-06, review of the landed diff):
    static final long LIMIT = Long.getLong("limit", 0);          // StoredTrans.recordLimit
    static final long RESERVE = Long.getLong("reserve", 0);      // DbBuilder.testStepReserve
    static final int BIG = Integer.getInteger("big", 0);         // percent of puts with many keys
    static final int BIGKEYS = Integer.getInteger("bigkeys", 60);
    static final boolean XFORM = Integer.getInteger("xform", 0) == 1;   // value transformations
    static final boolean DEEP = Integer.getInteger("deep", 0) == 1;     // keys of many segments
    static final java.util.BitSet refusedActions = new java.util.BitSet();
    static long refusedByLimit, xforms;
    static String roomStats = "";
    static String keyOf(int k) {
        if (!DEEP) return "/k" + k;
        StringBuilder b = new StringBuilder("/k" + (k % 7));
        for (int x = k, i = 0; i < 12; i++, x /= 3) b.append("/s").append(x % 3);
        return b.append("/k").append(k).toString();
    }
    static volatile int maxParts = Integer.MAX_VALUE;

    static final class Action {
        char kind;          // 'p' put(s), 'd' delete, 'e' empty, 'm' maintain, 's' sd, 'r' retain
        long time;
        String[] keys;
        byte[][] values;
        int arg;
        Action copy() {
            Action a = new Action();
            a.kind = kind; a.time = time; a.keys = keys; a.values = values; a.arg = arg;
            return a;
        }
        public String toString() { return kind + "@" + time + (kind == 'm' ? "/" + arg : ""); }
    }

    /** A record of the reference run. */
    static final class Rec {
        long tpos, end;
        int action;
        boolean part;
        int partsBefore;    // of the same call, the parts up to and including it
        boolean carries;    // the record carries maintenance (a plan)
        String memory;      // reclaim's memory after it (memory())
    }
    
    /**
     * Reclaim's memory that decides what it writes (031-06, rule 5): a, the first available
     * position and time, the settings, and the table's rows; a start must give the same
     * memory as apply() gave the running database at every record boundary.
     */
    static String memory(Db d) {
        Reclaim r = d.internal().reclaim();
        StringBuilder b = new StringBuilder();
        b.append("a=").append(r.appA).append(" first=").append(r.getFirstAvailablePos())
                .append('/').append(r.getFirstAvailableLookupTime()).append(" retain=")
                .append(r.getRetainDuration()).append(" f=").append(r.getInternalFractionUnits())
                .append('\n');
        for (Reclaim.IterationInfo row : r.rowsForProbe()) b.append(row.serialize()).append("--\n");
        return b.toString();
    }

    static List<Action> workload(long seed, int n, int sd) {
        Random r = new Random(seed);
        List<Action> as = new ArrayList<>();
        long t = SEC;
        Action a = new Action(); a.kind = 's'; a.arg = sd; a.time = t += MS; as.add(a);
        a = new Action(); a.kind = 'r'; a.arg = 1; a.time = t += MS; as.add(a);
        for (int i = 0; i < n; i++) {
            a = new Action();
            t += 1 + r.nextInt(200) * MS / 4;
            a.time = t;
            if (CLOCK.equals("back") && i % 7 == 6) a.time = t - 5 * MS;    // the clock goes back
            if (CLOCK.equals("still")) a.time = SEC + 10 * MS;              // and stands still
            int c = r.nextInt(100);
            if (c < MAINT) {
                a.kind = 'm'; a.arg = B;
            } else if (c < MAINT + 1) {
                a.kind = 's'; a.arg = sd + (r.nextBoolean() ? 1 : -1) * r.nextInt(sd / 2 + 1);
            } else if (c < MAINT + 2) {
                a.kind = 'r'; a.arg = 1 + r.nextInt(3);
            } else if (c < MAINT + 5) {
                a.kind = 'e';
            } else if (c < MAINT + 20) {
                a.kind = 'd'; a.keys = new String[] {keyOf(r.nextInt(KEYS))};
            } else {
                a.kind = 'p';
                int m = 1 + (r.nextInt(10) == 0 ? r.nextInt(8) : 0);
                final boolean big = BIG > 0 && r.nextInt(100) < BIG;
                if (big) m = 2 + r.nextInt(BIGKEYS);
                TreeSet<String> ks = new TreeSet<>();
                while (ks.size() < m) ks.add(keyOf(r.nextInt(KEYS)));
                a.keys = ks.toArray(new String[0]);
                a.values = new byte[m][];
                for (int j = 0; j < m; j++) {
                    a.values[j] = new byte[big ? r.nextInt(40) : r.nextInt(10) == 0 ? r.nextInt(MAXV * 4) : r.nextInt(MAXV)];
                    r.nextBytes(a.values[j]);
                }
            }
            as.add(a);
        }
        a = new Action(); a.kind = 'e'; a.time = t + MS; as.add(a);
        return as;
    }

    static Db start(CutStream s) {
        if (s.getLength() == 0) time.set(SEC);
        DbBuilder b = Db.builder().testSetup(s).clock(time::get);
        if (NODE == 8) b.maxNodeSize8();
        if (NODE == 30) b.maxNodeSize30();
        if (EVICT) b.evictionSchedule(Eviction.Schedule.EVERY, 1);
        if (RESERVE > 0) b.testStepReserve(RESERVE);
        return b.start();
    }

    static boolean run(Db d, Action a) {
        time.set(a.time);
        try {
            if (READER) d.currentTime();
            if (REFUSE) {
                try {
                    d.execute(d.trans().put(bergdb.dag.Keys.toSegments("/refused"), new KeyTransformation() {
                        public void transform(Trans t, int i) {
                            throw new IllegalStateException("refused on purpose");
                        }
                    }, new byte[] {1}, null).build());
                    throw new IllegalStateException("a refused transaction was taken");
                } catch (bergdb.pub.util.DbException e) {
                    if (e instanceof DbFailedException || e instanceof DbStoppingException) throw e;
                    refusedCalls++;
                }
            }
            switch (a.kind) {
            case 'p': {
                Trans.Builder b = d.trans();
                for (int j = 0; j < a.keys.length; j++) {
                    if (XFORM && (a.time + j) % 3 == 0) {
                        // A value transformation that depends on the value before: the first
                        // bytes of it, then the value given; every 5th gives null, a delete.
                        final boolean del = (a.time + j) % 5 == 0;
                        b.put(bergdb.dag.Keys.toSegments(a.keys[j]), null, a.values[j], new ValueTransformation() {
                            public byte[] transform(long tt, byte[] in, byte[] prev) {
                                if (del) return null;
                                if (prev == null) return in;
                                byte[] o = new byte[Math.min(8, prev.length) + in.length];
                                System.arraycopy(prev, 0, o, 0, Math.min(8, prev.length));
                                System.arraycopy(in, 0, o, Math.min(8, prev.length), in.length);
                                return o;
                            }
                        });
                        xforms++;
                    } else {
                        b.put(a.keys[j], a.values[j]);
                    }
                }
                try {
                    d.execute(b.build());
                } catch (bergdb.pub.util.DbException e) {
                    if (e instanceof DbFailedException || e instanceof DbStoppingException) throw e;
                    if (LIMIT == 0) throw e;
                    // Refused by its size or its index nodes at the lowered limit: no record.
                    if (countOn && recs != null) refusedActions.set(curAction);
                    refusedByLimit++;
                }
                break;
            }
            case 'd': d.execute(d.trans().delete(a.keys[0]).build()); break;
            case 'e': d.execute(d.trans().build()); break;
            case 's': d.setStartupDistance(a.arg); break;
            case 'r': d.setRetainDuration(a.arg * SEC); break;
            case 'm':
                if (a.arg < 0) {
                    maxParts = -a.arg - 1;
                    try {
                        d.maintain(B);
                    } finally {
                        maxParts = Integer.MAX_VALUE;
                    }
                } else {
                    d.maintain(a.arg);
                }
                break;
            default: throw new IllegalStateException();
            }
            return true;
        } catch (Crash | DbStoppingException | DbFailedException e) {
            return false;
        } catch (bergdb.storage.StreamIoException e) {
            return false;
        }
    }

    static final class Crash extends RuntimeException {
        Crash() { super("crash"); }
    }

    static int curAction, records, partsInCall, stopAt = -1;
    static String mode = "crash";
    static boolean countOn;
    static List<Rec> recs;
    static Db cur;

    static void installHook() {
        Db.testHooks = new Db.TestHooks() {
            public int maintainMaxParts() {
                return maxParts;
            }
            public void beforeApply(Db.ExecuteData x) {
                if (countOn && mode.equals("pre") && records + 1 == stopAt) {
                    records++;
                    throw new Crash();
                }
            }
            public void transExecuted(Db.ExecuteData x) {
                if (!countOn) return;
                Rec rc = new Rec();
                rc.tpos = x.trans.tpos;
                rc.end = x.trans.nextPos;
                rc.action = curAction;
                rc.part = x.trans.part;
                rc.carries = x.plan != null;
                if (recs != null) rc.memory = memory(cur);
                if (rc.part) partsInCall++;
                rc.partsBefore = partsInCall;
                if (recs != null) recs.add(rc);
                records++;
                if (records == stopAt) {
                    if (mode.equals("crash")) throw new Crash();
                    if (mode.equals("stop")) cur.stop();
                }
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
    }

    static final class Image {
        long length, cut, first, decided;
        byte[] bytes;
        String digest() throws Exception {
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            md.update(bytes);
            return String.format("%064x", new java.math.BigInteger(1, md.digest())).substring(0, 16);
        }
    }

    static Image image(CutStream s, long decided) throws Exception {
        Image im = new Image();
        im.decided = decided;
        im.length = s.getLength();
        im.cut = s.getCut();
        im.first = s.getFirstPos();
        im.bytes = new byte[(int) (im.length - im.first)];
        s.read(im.first, im.bytes, 0, im.bytes.length);
        return im;
    }

    /** Runs the actions from 'from' on d, restarting every RESTART actions; d's image. */
    static Image finish(Db d, CutStream s, List<Action> as, int from, int restart) throws Exception {
        for (int i = from; i < as.size(); i++) {
            curAction = i;
            partsInCall = 0;
            if (!run(d, as.get(i))) throw new IllegalStateException("action " + i + " threw");
            char k = as.get(i).kind;
            if ((k == 's' || k == 'r') && recs != null && !recs.isEmpty()
                    && recs.get(recs.size() - 1).action == i) {
                // A setter sets its field after its record, in its call (Reclaim.setSettings).
                recs.get(recs.size() - 1).memory = memory(d);
            }
            if (restart > 0 && (i - from) % restart == restart - 1 && i + 1 < as.size()) {
                d.sync(SyncLevel.ORDINARY);
                d.close();
                CutStream c = s.copy();
                s = c;
                d = start(s);
                cur = d;
            }
        }
        d.sync(SyncLevel.ORDINARY);
        final long decided = d.getFirstAvailablePos();
        d.close();
        return image(s, decided);
    }

    /** The records of each action in the reference: the rule of one record an action. */
    static int[] recordsOf(List<Action> as, List<Rec> rs) {
        int[] n = new int[as.size()];
        for (Rec r : rs) n[r.action]++;
        for (Rec r : rs) {
            char k = as.get(r.action).kind;
            if (r.part != (k == 'm')) throw new IllegalStateException("record at " + r.tpos
                    + " of action " + r.action + " (" + k + "): part " + r.part);
        }
        for (int i = 0; i < as.size(); i++) {
            char k = as.get(i).kind;
            if ((k == 'p' || k == 'd' || k == 'e') && n[i] != (refusedActions.get(i) ? 0 : 1)) {
                throw new IllegalStateException("commit " + i + " appended " + n[i] + " records");
            }
            if ((k == 's' || k == 'r') && n[i] > 1) {
                throw new IllegalStateException("setter " + i + " appended " + n[i] + " records");
            }
        }
        return n;
    }

    static Image reference(List<Action> as, List<Rec> into) throws Exception {
        CutStream s = new CutStream();
        countOn = false; stopAt = -1; recs = null;
        Db d = start(s);
        cur = d;
        final Reclaim.Stats st;
        synchronized (d.internal().getWriteLock()) { st = d.internal().reclaim().enableStats(); }
        recs = into; records = 0; countOn = true;
        Image im = finish(d, s, as, 0, 0);
        if (into != null) roomStats = "room: first copy " + st.roomFirstCopy + ", no step " + st.roomNoStep;
        countOn = false; recs = null;
        return im;
    }

    static String compare(Image a, Image b) {
        if (a.length != b.length) return "length " + a.length + " " + b.length;
        if (a.decided != b.decided) return "first available pos " + a.decided + " " + b.decided;
        long from = Math.max(a.first, b.first);
        for (long p = from; p < a.length; p++) {
            if (a.bytes[(int) (p - a.first)] != b.bytes[(int) (p - b.first)]) return "byte at " + p;
        }
        return null;
    }

    public static void main(String[] args) throws Exception {
        long seed = Long.parseLong(args[0]);
        int n = Integer.parseInt(args[1]);
        int sd = Integer.parseInt(args[2]);
        String modes = args.length > 3 ? args[3] : "all";
        if (LIMIT > 0) StoredTrans.recordLimit = LIMIT;
        installHook();
        List<Action> as = workload(seed, n, sd);
        List<Rec> rs = new ArrayList<>();
        Image ref = reference(as, rs);
        int[] per = recordsOf(as, rs);
        int calls = 0, accepted = 0, parts = 0, carries = 0, commits = 0, setters = 0;
        for (int i = 0; i < as.size(); i++) {
            char k = as.get(i).kind;
            if (k == 'm') { calls++; parts += per[i]; accepted += per[i]; }
            else if (k == 's' || k == 'r') { setters += per[i]; accepted += per[i]; }
            else if (!refusedActions.get(i)) { commits++; accepted++; }
        }
        long firstCut = Long.MAX_VALUE;
        for (Rec r : rs) if (r.carries && !r.part) carries++;
        System.out.println("seed " + seed + ", actions " + as.size() + " (" + calls + " calls of "
                + B + "), sd " + sd + (RESTART > 0 ? ", restart every " + RESTART : "")
                + (READER ? ", a reader's time before each" : "") + (REFUSE ? ", a refused "
                + "transaction before each (" + refusedCalls + ")" : "") + (CLOCK.isEmpty() ? ""
                : ", clock " + CLOCK) + (EVICT ? ", eviction at every transaction" : "")
                + ": records " + rs.size() + " = accepted actions " + accepted + " ("
                + commits + " commits, " + carries + " carrying maintenance; " + setters
                + " setters; " + parts + " parts), length " + ref.length + ", cut " + ref.cut
                + ", decided " + ref.decided + ", digest " + ref.digest()
                + (LIMIT > 0 ? "; record limit " + LIMIT + ", refused by it " + refusedActions.cardinality() : "")
                + (XFORM ? "; value transformations " + xforms : "") + "; " + roomStats);
        Reclaim.Stats st = null;
        if (rs.size() != accepted) throw new IllegalStateException("records != accepted actions");
        Map<String, Image> refs = new HashMap<>();
        int from = Integer.getInteger("from", 1), to = Integer.getInteger("to", rs.size());
        int stride = Integer.getInteger("stride", 1);
        List<String> ms = new ArrayList<>();
        if (modes.equals("all")) ms.addAll(Arrays.asList("crash", "pre", "stop"));
        else ms.add(modes);
        for (String m : ms) {
            mode = m;
            if (m.equals("torn")) { torn(as, rs, ref); continue; }
            int same = 0, diff = 0, stopsExact = 0, afterCut = 0, memSame = 0, memDiff = 0;
            List<String> diffs = new ArrayList<>();
            for (int k = from; k <= to; k += stride) {
                Rec rc = rs.get(k - 1);
                Action at = as.get(rc.action);
                CutStream s = new CutStream();
                countOn = false; recs = null; stopAt = -1;
                Db d = start(s);
                cur = d;
                records = 0; countOn = true; stopAt = k;
                for (int i = 0; i < as.size(); i++) {
                    curAction = i; partsInCall = 0;
                    run(d, as.get(i));
                    if (records >= k) break;
                }
                countOn = false; stopAt = -1;
                try { d.close(); } catch (RuntimeException e) { /* failed: closes anyway */ }
                CutStream c = s.copy();
                if (c.getCut() > 0) afterCut++;
                if (c.getLength() == rc.end) stopsExact++;
                else {
                    diff++;
                    diffs.add(m + " at record " + k + " (" + at + "): stream " + c.getLength()
                            + " where the record ends at " + rc.end);
                    continue;
                }
                int next = rc.action + 1;
                Image want = ref;
                if (at.kind == 'm') {
                    String key = rc.action + "/" + rc.partsBefore;
                    want = refs.get(key);
                    if (want == null) {
                        List<Action> bs = new ArrayList<>(as);
                        Action lim = at.copy();
                        lim.arg = -rc.partsBefore - 1;
                        bs.set(rc.action, lim);
                        want = reference(bs, null);
                        refs.put(key, want);
                    }
                }
                Db b = start(c);
                cur = b;
                // The start's memory is the running database's after record k (rule 5).
                if (memory(b).equals(rc.memory)) memSame++;
                else {
                    memDiff++;
                    if (diffs.size() < 20) diffs.add(m + " at record " + k + " (" + at
                            + "): the start's memory\n" + memory(b) + "the running one's\n" + rc.memory);
                }
                Image got = finish(b, c, as, next, RESTART);
                String why = compare(want, got);
                if (why == null) same++;
                else {
                    diff++;
                    if (diffs.size() < 20) diffs.add(m + " at record " + k + " (" + at + "): " + why);
                }
            }
            System.out.println(m + ": " + same + " the same, " + diff + " different; "
                    + stopsExact + " ended at the record, " + afterCut + " after a physical cut; "
                    + "the start's memory the running one's at " + memSame + ", other at " + memDiff);
            for (String x : diffs) System.out.println("  " + x);
        }
    }

    /** The torn mode: see the class comment. */
    static void torn(List<Action> as, List<Rec> rs, Image ref) throws Exception {
        int every = Integer.getInteger("torn", 7);
        int same = 0, diff = 0, notAccepted = 0, prefixSame = 0, n = 0;
        List<String> diffs = new ArrayList<>();
        for (int k = 2; k <= rs.size(); k += every) {
            Rec rc = rs.get(k - 1);
            Action at = as.get(rc.action);
            final boolean other = at.kind == 'm' || at.kind == 's' || at.kind == 'r';
            if (other && !Boolean.getBoolean("tornall")) continue;   // commits only, but with -Dtornall=true
            long len = rc.end - rc.tpos;
            for (long cutAt : new long[] {rc.tpos + 1, rc.tpos + len / 2, rc.end - 1}) {
                // The run up to record k - 1, then record k's append is cut at 'cutAt'.
                mode = "crash";
                CutStream s = new CutStream();
                countOn = false; recs = null; stopAt = -1;
                Db d = start(s);
                cur = d;
                records = 0; countOn = true; stopAt = k;
                for (int i = 0; i < as.size(); i++) {
                    curAction = i; partsInCall = 0;
                    run(d, as.get(i));
                    if (records >= k) break;
                }
                countOn = false; stopAt = -1;
                try { d.close(); } catch (RuntimeException e) { }
                CutStream c = s.copy();
                c.truncate(cutAt);
                n++;
                // Continued twice from the same torn stream: alone, and with a restart.
                CutStream c1 = c.copy(), c2 = c.copy();
                Db b1 = start(c1);
                cur = b1;
                boolean absent = at.kind == 'e' || other || absent(b1, at);
                if (absent) notAccepted++;
                Image g1 = finish(b1, c1, as, rc.action, 0);
                Db b2 = start(c2);
                cur = b2;
                Image g2 = finish(b2, c2, as, rc.action, 25);
                String why = compare(g1, g2);
                if (why == null) same++;
                else { diff++; if (diffs.size() < 20) diffs.add("torn at " + cutAt + " (record " + k + "): " + why); }
                // The prefix before the torn record is the reference's.
                boolean pre = true;
                long f = Math.max(g1.first, ref.first);
                for (long p = f; p < rc.tpos && pre; p++) {
                    pre = g1.bytes[(int) (p - g1.first)] == ref.bytes[(int) (p - ref.first)];
                }
                if (pre) prefixSame++;
            }
        }
        System.out.println("torn: " + n + " torn records (commits): " + same + " continued the same "
                + "with and without a restart, " + diff + " different; " + notAccepted
                + " with the action not accepted; " + prefixSame + " with the reference's bytes before it");
        for (String x : diffs) System.out.println("  " + x);
    }

    /** Whether the put or delete of 'a' is absent from d: its KVs have the values before it. */
    static boolean absent(Db d, Action a) {
        if (a.kind == 'd') return true;     // A delete's effect is not told apart here.
        for (int j = 0; j < a.keys.length; j++) {
            byte[] v = DbUtil.get(d, a.keys[j]);
            if (v != null && Arrays.equals(v, a.values[j]) && a.values[j].length > 8) return false;
        }
        return true;
    }
}
