package bergdb.core;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
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
 * bergdb 031-05's probe of the goal "every write a function of the stream and the user
 * actions": a crash, or a stop, at every record boundary of a seeded workload, inside
 * commits and inside maintain() calls, and the continued stream compared, byte for byte,
 * with the uninterrupted run's.
 *
 * The workload is a list of actions, each with its time (a test clock set before it): the
 * settings (startup distance SD, retain duration 1 s), puts of values of 0 to MAXV bytes at
 * KEYS keys, deletes, empty transactions, a few setters, and maintain(B) calls. The
 * uninterrupted run gives the reference stream and its records, each with the action that
 * wrote it and whether it is the action's own (a user record, a setter's, a part of a
 * call) or maintenance written before it.
 *
 * For each record k: a run of the same actions up to record k, where the database is
 * crashed (the test hook throws after record k: the database fails and nothing more is
 * appended, P7) or stopped (the hook calls stop()); then a start from the stream, and the
 * actions after it, by the rule of 031-05, section 4:
 *   an execute or a setter whose record is in the stream is accepted: the next action
 *   follows; one whose record is not (record k was maintenance before it) is not, and is
 *   called again with the same time;
 *   a maintain() call counts as accepted with the parts it wrote, m: the reference is then
 *   the uninterrupted run with that call made with at most m parts (Db.maintain(int, int)).
 * The continued stream must equal the reference: the same length, the same cut, and the
 * same bytes from the first position kept.
 *
 * Usage (from java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT P2CrashProbe.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.P2CrashProbe SEED ACTIONS SD [crash|stop|both]
 *   -Dproto315.eager=true  the commit's maintenance in its own call (D2), else deferred (D1)
 *   -Dkeys=200 -Dmaxv=3000 -Dbudget=100 -Dmaint=8 (percent of actions that are calls)
 *   -Dnode=8 or 30: the largest node size (DbBuilder.maxNodeSize8, maxNodeSize30)
 *   -Dfrom=K -Dto=K  a range of records only; -Dstride=N every N-th record only
 * On a jar without Db.maintain(int, int) (031-04's), boundaries inside calls are skipped.
 */
public class P2CrashProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final AtomicLong time = new AtomicLong(SEC);
    static final int KEYS = Integer.getInteger("keys", 200), MAXV = Integer.getInteger("maxv", 3000);
    static final int B = Integer.getInteger("budget", 100), MAINT = Integer.getInteger("maint", 8);
    static final int NODE = Integer.getInteger("node", 0);     // 8 or 30, else the default
    static Method maintainParts;
    static Field inPart;

    /** An action: its kind, its time, and its data. */
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
        long end;
        int action;
        boolean own;        // the action's own record; else maintenance written before it
        boolean part;       // a part of a maintain() call
        int partsBefore;    // of the same call, the parts written up to and including it
        boolean ownDone;    // the action's own record is this one or before it
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
                a.kind = 'd'; a.keys = new String[] {"/k" + r.nextInt(KEYS)};
            } else {
                a.kind = 'p';
                int m = 1 + (r.nextInt(10) == 0 ? r.nextInt(8) : 0);
                TreeSet<String> ks = new TreeSet<>();
                while (ks.size() < m) ks.add("/k" + r.nextInt(KEYS));
                a.keys = ks.toArray(new String[0]);
                a.values = new byte[m][];
                for (int j = 0; j < m; j++) {
                    a.values[j] = new byte[r.nextInt(10) == 0 ? r.nextInt(MAXV * 4) : r.nextInt(MAXV)];
                    r.nextBytes(a.values[j]);
                }
            }
            as.add(a);
        }
        // A last empty transaction: the maintenance due after the last action is then written
        // before it, in every run (the deferred design leaves the last action's for the next).
        a = new Action(); a.kind = 'e'; a.time = t + MS; as.add(a);
        return as;
    }

    /** A start; a creating one at the workload's first time, so that every run is alike. */
    static Db start(CutStream s) {
        if (s.getLength() == 0) time.set(SEC);
        DbBuilder b = Db.builder().testSetup(s).clock(time::get);
        if (NODE == 8) b.maxNodeSize8();
        if (NODE == 30) b.maxNodeSize30();
        return b.start();
    }

    /** Runs one action; true if it returned, false if it threw (a crash or a stop). */
    static boolean run(Db d, Action a) {
        time.set(a.time);
        try {
            switch (a.kind) {
            case 'p': {
                Trans.Builder b = d.trans();
                for (int j = 0; j < a.keys.length; j++) b.put(a.keys[j], a.values[j]);
                d.execute(b.build());
                break;
            }
            case 'd': d.execute(d.trans().delete(a.keys[0]).build()); break;
            case 'e': d.execute(d.trans().build()); break;
            case 's': d.setStartupDistance(a.arg); break;
            case 'r': d.setRetainDuration(a.arg * SEC); break;
            case 'm':
                if (a.arg < 0) {
                    maintainParts.invoke(d, B, -a.arg - 1);     // at most -arg - 1 parts
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
            return false;       // maintain()'s sync outside the lock, at a stop (its Javadoc)
        } catch (java.lang.reflect.InvocationTargetException e) {
            Throwable c = e.getCause();
            if (c instanceof Crash || c instanceof DbStoppingException || c instanceof DbFailedException) {
                return false;
            }
            throw new RuntimeException(c);
        } catch (IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    static final class Crash extends RuntimeException {
        Crash() { super("crash"); }
    }

    /** The hook state of a run. */
    static int curAction, records, partsInCall, stopAt = -1;
    static boolean crashMode, countOn, ownSeen;
    static List<Rec> recs;
    static Db cur;

    static void installHook() {
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (!countOn) return;
                Rec rc = new Rec();
                rc.end = x.trans.nextPos;
                rc.action = curAction;
                boolean part = false;
                try {
                    part = inPart != null && inPart.getBoolean(cur.internal().reclaim());
                } catch (IllegalAccessException e) {
                    throw new RuntimeException(e);
                }
                rc.part = part;
                if (part) partsInCall++;
                rc.partsBefore = partsInCall;
                rc.own = part || !x.trans.isInternal()
                        || (x.trans.isInternal() && !Reclaim.isOwnRecord(x.transNodes));
                if (rc.own) ownSeen = true;
                rc.ownDone = ownSeen;
                if (recs != null) recs.add(rc);
                records++;
                if (records == stopAt) {
                    if (crashMode) throw new Crash();
                    cur.stop();
                }
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
    }

    /** The stream's bytes from its first position, its length and its cut, after a close. */
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

    /** Runs the actions from 'from' on d; returns d's image after a close. */
    static Image finish(Db d, CutStream s, List<Action> as, int from) throws Exception {
        for (int i = from; i < as.size(); i++) {
            curAction = i;
            partsInCall = 0; ownSeen = false;
            if (!run(d, as.get(i))) throw new IllegalStateException("action " + i + " threw");
        }
        d.sync(SyncLevel.ORDINARY);
        final long decided = d.getFirstAvailablePos();
        d.close();
        return image(s, decided);
    }

    /** The uninterrupted run; its records in 'recs' if given. */
    static Image reference(List<Action> as, List<Rec> into) throws Exception {
        CutStream s = new CutStream();
        countOn = false; stopAt = -1; recs = null;
        Db d = start(s);
        cur = d;
        recs = into; records = 0; countOn = true;
        Image im = finish(d, s, as, 0);
        countOn = false; recs = null;
        return im;
    }

    static String compare(Image a, Image b) {
        if (a.length != b.length) return "length " + a.length + " " + b.length;
        // The decided cut; the physical one waits for durability (StreamDigest's comment).
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
        String mode = args.length > 3 ? args[3] : "both";
        try {
            maintainParts = Db.class.getDeclaredMethod("maintain", int.class, int.class);
            maintainParts.setAccessible(true);
            inPart = Reclaim.class.getDeclaredField("inPart");
            inPart.setAccessible(true);
        } catch (ReflectiveOperationException e) {
            maintainParts = null; inPart = null;
        }
        boolean eager = Boolean.getBoolean("proto315.eager");
        installHook();
        List<Action> as = workload(seed, n, sd);
        List<Rec> rs = new ArrayList<>();
        Image ref = reference(as, rs);
        int calls = 0;
        for (Action a : as) if (a.kind == 'm') calls++;
        int inCalls = 0, maint = 0;
        for (Rec r : rs) { if (r.part) inCalls++; if (!r.own) maint++; }
        System.out.println("seed " + seed + ", actions " + as.size() + " (" + calls + " calls of "
                + B + "), sd " + sd + ", " + (eager ? "eager (D2)" : "deferred (D1)")
                + ": records " + rs.size() + " (" + inCalls + " parts of calls, " + maint
                + " other maintenance), length " + ref.length + ", cut "
                + ref.cut + ", digest " + ref.digest());
        if (Boolean.getBoolean("twice")) {
            Image again = reference(as, null);
            System.out.println("reference again: " + compare(ref, again) + ", length " + again.length);
        }
        Map<String, Image> refs = new HashMap<>();
        int from = Integer.getInteger("from", 1), to = Integer.getInteger("to", rs.size());
        int stride = Integer.getInteger("stride", 1);
        for (String m : new String[] {"crash", "stop"}) {
            if (!mode.equals("both") && !mode.equals(m)) continue;
            crashMode = m.equals("crash");
            int same = 0, diff = 0, skipped = 0, stopsExact = 0;
            List<String> diffs = new ArrayList<>();
            for (int k = from; k <= to; k += stride) {
                Rec rc = rs.get(k - 1);
                Action at = as.get(rc.action);
                if (at.kind == 'm' && maintainParts == null) { skipped++; continue; }
                // The run up to record k.
                CutStream s = new CutStream();
                countOn = false; recs = null; stopAt = -1;
                Db d = start(s);
                cur = d;
                records = 0; countOn = true; stopAt = k;
                int i = 0;
                boolean returned = true;
                for (; i < as.size(); i++) {
                    curAction = i; partsInCall = 0; ownSeen = false;
                    returned = run(d, as.get(i));
                    if (records >= k) break;
                }
                countOn = false; stopAt = -1;
                try { d.close(); } catch (RuntimeException e) { /* failed: closes anyway */ }
                CutStream c = s.copy();
                if (c.getLength() == rc.end) stopsExact++;
                else {
                    diff++;
                    diffs.add(m + " at record " + k + " (" + at + ", own " + rc.own + "): stream "
                            + c.getLength() + " where the record ends at " + rc.end);
                    continue;
                }
                // The continuation, by the rule.
                int next;
                Image want;
                if (at.kind == 'm') {
                    next = rc.action + 1;
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
                } else {
                    next = rc.ownDone ? rc.action + 1 : rc.action;
                    want = ref;
                }
                Db b = start(c);
                cur = b;
                Image got = finish(b, c, as, next);
                String why = compare(want, got);
                if (why == null) same++;
                else {
                    diff++;
                    if (diffs.size() < 20) diffs.add(m + " at record " + k + " (" + at + ", own "
                            + rc.own + ", returned " + returned + "): " + why);
                }
            }
            System.out.println(m + ": " + same + " the same, " + diff + " different, "
                    + skipped + " skipped (inside calls, no maintain(int, int)); "
                    + stopsExact + " ended at the record");
            for (String x : diffs) System.out.println("  " + x);
        }
    }
}
