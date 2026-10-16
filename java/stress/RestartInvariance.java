package bergdb.core;

import java.util.*;

import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.NodeVisitor;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.stream.MemoryStream;

/**
 * Targeted test of the restart invariant, written 2026-10-12.
 * See docs/startup-invariants.md, invariants INV-RESTART, INV-ID and
 * INV-LOOKUP.
 *
 * Runs the same deterministic sequence of transactions twice: run A without
 * restarts, run B with a restart (sync, stop, start) after every N
 * transactions. If restarts are transparent, as the 2015-2016 design intends,
 * the two streams have the same content (raw bytes may differ in padding),
 * and the TransSeq (the dirty set D) is the same after each restart.
 *
 * At a checkpoint after every N transactions it compares, for A and B:
 * the TransSeq checksum, INV-ID (D holds the Dag's own objects, every dirty
 * index node is in D, one object per id), and lookups against the history.
 * At the end, it compares the streams transaction by transaction.
 *
 * In package bergdb.core to reach Db internals.
 *
 * Usage: java [-Dprop=value ...] -cp bergdb.jar:. bergdb.core.RestartInvariance seed
 *
 * Properties:
 *   n=N        Number of transactions (default 3000).
 *   keys=N     Number of distinct keys (default 500).
 *   sd=N       Startup distance in bytes (default 10000; 0: Db default, 50 MB).
 *   maxnode=N  Max node size: 8, 14, 30 or 62 (default: Db default).
 *   every=N    Restart after every N transactions in run B (default 250).
 *   valsize=N  Value size 1..N bytes (default 40).
 *   del=1      Include deletes (default 0).
 *   long=1     Half of the keys are /long/N, 7 bytes or more: two key segments.
 *   bigtrans=N One transaction in ten has up to N keys (default: all have 1 to 3).
 *   empty=P    P percent of the transactions have no keys (default 0).
 *   nodel=P    P percent of the transactions only delete keys that never exist (default 0).
 *   retain=S   Reclaim on, with a retain duration of S seconds (level 3); transactions
 *              are then 0.01 to 0.2 s apart. Lookups are checked from the first
 *              available lookup time, and the streams from the cut.
 * Debug aids:
 *   trace=true         Print the path of the first bad lookup per checkpoint.
 *   watch=ID, at=I     Print node ID and its children before transaction I.
 */
public class RestartInvariance {
    static final byte[] DELETED = null;

    final long seed;
    final int n = Integer.getInteger("n", 3000);
    final int keyCount = Integer.getInteger("keys", 500);
    final int startupDistance = Integer.getInteger("sd", 10000);
    final int maxNode = Integer.getInteger("maxnode", 0);
    final int every = Integer.getInteger("every", 250);
    final int valsize = Integer.getInteger("valsize", 40);
    final boolean del = "1".equals(System.getProperty("del"));
    final boolean longKeys = "1".equals(System.getProperty("long"));
    final int bigTrans = Integer.getInteger("bigtrans", 0);
    final int empty = Integer.getInteger("empty", 0);
    final int nodel = Integer.getInteger("nodel", 0);
    final int retain = Integer.getInteger("retain", 0);
    final long timeScale = retain > 0 ? bergdb.pub.util.Clock.UNITS_PER_SEC / 100 : 1;

    final List<String[]> keys = new ArrayList<String[]>();      // per transaction
    final List<byte[][]> values = new ArrayList<byte[][]>();    // per transaction, null = delete
    final long[] times;

    RestartInvariance(long seed) {
        this.seed = seed;
        Random rnd = new Random(seed);
        times = new long[n];
        long time = 10;
        for (int i = 0; i < n; i++) {
            time += (1 + rnd.nextInt(20)) * timeScale;
            times[i] = time;
            // Transactions that change nothing (F1-008-11, 8.5, for M18). No draw when both
            // are 0, so that the other workloads stay the same.
            int idle = empty + nodel > 0 ? rnd.nextInt(100) : 100;
            if (idle < empty + nodel) {
                int c = idle < empty ? 0 : 1 + rnd.nextInt(3);
                String[] ks = new String[c];
                for (int j = 0; j < c; j++) ks[j] = "/missing/" + i + "/" + j;
                keys.add(ks);
                values.add(new byte[c][]);      // DELETED
                continue;
            }
            int opCount = 1 + rnd.nextInt(3);
            if (bigTrans > 0 && rnd.nextInt(10) == 0) {
                opCount = 1 + rnd.nextInt(bigTrans);
            }
            LinkedHashMap<String, byte[]> ops = new LinkedHashMap<String, byte[]>();
            for (int o = 0; o < opCount; o++) {
                String prefix = longKeys && rnd.nextBoolean() ? "/long/" : "/k/";
                String k = prefix + rnd.nextInt(keyCount);
                if (del && rnd.nextInt(5) == 0) {
                    ops.put(k, DELETED);
                } else {
                    byte[] v = new byte[1 + rnd.nextInt(valsize)];
                    rnd.nextBytes(v);
                    ops.put(k, v);
                }
            }
            keys.add(ops.keySet().toArray(new String[0]));
            values.add(ops.values().toArray(new byte[0][]));
        }
    }

    /** Result of one run. */
    static class Run {
        MemoryStream stream;
        Db db;
        long[] tpos;
        Map<Integer, Long> transSeqSums = new TreeMap<Integer, Long>();   // after trans i
        Map<Integer, Long> dbSums = new TreeMap<Integer, Long>();
        Map<Integer, String> identity = new TreeMap<Integer, String>();  // violations
        Map<Integer, String> lookups = new TreeMap<Integer, String>();   // violations
        List<String> restartNotes = new ArrayList<String>();
        String startupFailure;      // a failed restart, and the run stops there
        int executed;               // number of transactions executed
    }

    /**
     * Checks lookups against the transaction history (INV-LOOKUP): the latest value
     * of every key, and 300 lookups at random historical times, after trans i.
     * Returns null if OK, else the first violation and the count.
     */
    String lookupViolations(Db db, int i) {
        Random rnd = new Random(seed * 31 + i);
        int bad = 0;
        String first = null;
        for (int j = 0; j < keyCount + 300; j++) {
            String k = "/k/" + (j < keyCount ? j : rnd.nextInt(keyCount));
            long t = j < keyCount ? Long.MAX_VALUE : times[rnd.nextInt(i + 1)] - rnd.nextInt(2);
            if (t < db.getFirstAvailableLookupTime()) continue;     // Cut by reclaim.
            byte[] expected = expectedValue(k, t, i);
            String problem = null;
            try {
                byte[] actual = DbUtil.get(db, t, k);
                if (!Arrays.equals(expected, actual)) {
                    problem = "get(" + k + ", t=" + t + "): expected "
                            + (expected == null ? "null" : expected.length + " bytes") + ", got "
                            + (actual == null ? "null" : actual.length + " bytes");
                }
            } catch (RuntimeException e) {
                problem = "get(" + k + ", t=" + t + ") failed: " + e;
            }
            if (problem != null) {
                bad++;
                if (first == null) {
                    first = problem;
                    if (Boolean.getBoolean("trace")) trace(db, k, t);
                }
            }
        }
        return bad == 0 ? null : bad + " bad lookups, first: " + first;
    }

    /**
     * Debug aid (-Dtrace=true): repeats a failing lookup and prints every pointer
     * followed, and the last node before the failure.
     */
    static void trace(Db db, String k, long t) {
        System.out.println("TRACE get(" + k + ", t=" + t + ")");
        bergdb.dag.GetData gd = db.newGetData();
        final bergdb.dag.PointerFollower real = gd.pointerFollower;
        final Node[] last = new Node[1];
        gd.pointerFollower = new bergdb.dag.PointerFollower() {
            public Node followPointer(Node pred, int idx, bergdb.dag.OpData op) {
                last[0] = pred;
                Node mem = pred.getPointerNode(idx);
                long pos = pred.getPointerPos(idx);
                System.out.println("  from " + pred.getClass().getSimpleName() + " id="
                        + pred.getId() + " spos=" + pred.getSpos() + " ptr[" + idx + "] -> "
                        + (mem != null ? "memory node id=" + mem.getId()
                                : "stream pos " + pos + (pos % 2 != 0 ? " (odd, a vpos?)" : "")));
                return real.followPointer(pred, idx, op);
            }
        };
        try {
            db.getOne(t, bergdb.dag.Keys.toSegments(k), gd);
            System.out.println("  no failure on repeat");
        } catch (RuntimeException e) {
            System.out.println("  failed: " + e);
            if (last[0] != null) {
                String[] lines = last[0].print().split("\n");
                System.out.println("  last node before failure:");
                for (int i = 0; i < Math.min(lines.length, 70); i++) {
                    System.out.println("    " + lines[i]);
                }
            }
        }
    }

    /** Value of key k at lookup time t, after transactions 0..i. */
    byte[] expectedValue(String k, long t, int i) {
        byte[] result = null;
        for (int x = 0; x <= i && times[x] <= t; x++) {
            String[] ks = keys.get(x);
            for (int j = 0; j < ks.length; j++) {
                if (ks[j].equals(k)) result = values.get(x)[j];
            }
        }
        return result;
    }

    Db start(MemoryStream stream, CoreTestClock clock) {
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        if (startupDistance > 0) b.startupDistance(startupDistance);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        Db db = b.start();
        if (retain > 0) db.setRetainDuration(retain * bergdb.pub.util.Clock.UNITS_PER_SEC);
        return db;
    }

    Run run(boolean withRestarts, Set<Integer> checkpoints) {
        Run r = new Run();
        r.stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        r.db = start(r.stream, clock);
        r.tpos = new long[n];

        for (int i = 0; i < n; i++) {
            if (i == Integer.getInteger("at", -1)) {
                watch(r.db, Long.getLong("watch", -1), withRestarts ? "B" : "A", i);
            }
            clock.setTime(times[i]);
            Trans.Builder b = r.db.trans();
            String[] ks = keys.get(i);
            byte[][] vs = values.get(i);
            for (int j = 0; j < ks.length; j++) {
                if (vs[j] == DELETED) b.delete(ks[j]);
                else b.put(ks[j], vs[j]);
            }
            Trans t = b.build();
            r.db.execute(t);
            r.tpos[i] = t.tpos;

            boolean restartHere = withRestarts && (i + 1) % every == 0 && i + 1 < n;
            if (restartHere) {
                r.db.sync(SyncLevel.STRONG);
                long before = r.stream.getLength();
                r.db.stop();
                r.stream = r.stream.copy();
                try {
                    r.db = start(r.stream, clock);
                } catch (RuntimeException e) {
                    r.startupFailure = "restart after trans " + i + " failed: " + e;
                    r.executed = i + 1;
                    return r;
                }
                long after = r.stream.getLength();
                if (after != before) {
                    r.restartNotes.add("restart after trans " + i + ": stream length "
                            + before + " -> " + after);
                }
            }

            if (checkpoints.contains(i)) {
                r.transSeqSums.put(i, r.db.internal().transSeq().checksum());
                r.dbSums.put(i, DbUtil.checksum(r.db));
                String v = identityViolations(r.db);
                if (v != null) r.identity.put(i, v);
                String l = lookupViolations(r.db, i);
                if (l != null) r.lookups.put(i, l);
            }
        }
        r.db.sync(SyncLevel.STRONG);
        return r;
    }

    /**
     * Debug aid (-Dwatch=id -Dat=i): prints the in-memory objects of node 'id'
     * just before transaction i, with the dirty flag of each child.
     */
    static void watch(final Db db, final long id, String run, int i) {
        final List<Node> found = new ArrayList<Node>();
        final Map<Long, Node> memById = new HashMap<Long, Node>();
        db.internal().dag().visitMemoryNodes(new NodeVisitor() {
            public void visit(TopNode node) { add(node); }
            public void visit(KeyNode node) { add(node); }
            public void visit(ValueNode node) {}
            private void add(Node node) {
                memById.put(node.getId(), node);
                if (node.getId() == id) found.add(node);
            }
        });
        System.out.println("WATCH run " + run + " before trans " + i + ": node " + id
                + ", objects in Dag memory: " + found.size());
        for (Node node : found) {
            System.out.println("  object@" + System.identityHashCode(node) + " dirty="
                    + node.isDirty() + " spos=" + node.getSpos());
            for (int p = 0; p < node.getSize(); p++) {
                Node child = node.getPointerNode(p);
                long pos = node.getPointerPos(p);
                if (child == null && pos == -1) continue;
                if (child != null) {
                    System.out.println("    [" + p + "] mem  -> id " + child.getId()
                            + " spos=" + child.getSpos() + " "
                            + child.getClass().getSimpleName() + " dirty=" + child.isDirty());
                } else {
                    long cid = db.internal().nodeStream().readNodeHeader(pos).id();
                    Node inMem = memById.get(cid);
                    System.out.println("    [" + p + "] stream " + pos + " -> id " + cid
                            + (inMem == null ? " (not in Dag memory)"
                                    : " (in Dag memory, dirty=" + inMem.isDirty() + ")"));
                }
            }
        }
    }

    /**
     * Checks INV-ID, one object per node (docs/levels.md, level 2): every
     * queued node (in D) is the node table's object for its id and is dirty, every dirty
     * node in Dag memory is queued, and no id has two dirty objects. Old snapshots of a
     * node, in pointers that named old versions, are allowed. Returns null if OK, else a
     * description.
     */
    static String identityViolations(Db db) {
        final Cache3 table = db.internal().cache();
        final Set<Node> queued = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        final int[] counts = new int[2];    // notInTable, notDirty
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                queued.add(node);
                if (table.getNode(node.getId()) != node) counts[0]++;
                if (!node.isDirty()) counts[1]++;
            }
        });

        final int[] mem = new int[2];       // dirty but not queued, two dirty objects
        final Map<Long, Node> dirtyById = new HashMap<Long, Node>();
        db.internal().dag().visitMemoryNodes(new NodeVisitor() {
            public void visit(TopNode node) { check(node); }
            public void visit(KeyNode node) { check(node); }
            public void visit(ValueNode node) {}
            private void check(Node node) {
                if (!node.isDirty()) return;
                if (!queued.contains(node)) mem[0]++;
                Node other = dirtyById.put(node.getId(), node);
                if (other != null && other != node) mem[1]++;
            }
        });

        if (counts[0] == 0 && counts[1] == 0 && mem[0] == 0 && mem[1] == 0) return null;
        return "queued nodes not in the node table: " + counts[0]
                + ", queued but not dirty: " + counts[1]
                + ", dirty in Dag but not queued: " + mem[0]
                + ", ids with two dirty objects: " + mem[1];
    }

    void compare() {
        Set<Integer> checkpoints = new TreeSet<Integer>();
        for (int i = every - 1; i < n; i += every) checkpoints.add(i);
        checkpoints.add(n - 1);

        Run a = run(false, checkpoints);
        Run b = run(true, checkpoints);

        System.out.println("seed=" + seed + " n=" + n + " keys=" + keyCount + " sd="
                + startupDistance + " maxnode=" + maxNode + " every=" + every
                + " valsize=" + valsize + " del=" + del + " retain=" + retain
                + (empty + nodel > 0 ? " empty=" + empty + " nodel=" + nodel : ""));
        if (retain > 0) {
            // The cut decided by reclaim; the physical cut (pretruncate) waits for durability,
            // and MemoryStream drops whole 1 MB arrays only.
            long ca = a.db.getFirstAvailablePos(), cb = b.db.getFirstAvailablePos();
            long ta = a.db.getFirstAvailableLookupTime(), tb = b.db.getFirstAvailableLookupTime();
            System.out.println("CUT: A=" + ca + " B=" + cb + ", first available lookup time A="
                    + ta + " B=" + tb + (ca == cb && ta == tb ? ", same" : ", DIFFERENT"));
        }
        System.out.println("stream length A=" + a.stream.getLength() + " B=" + b.stream.getLength());
        for (String note : b.restartNotes) System.out.println("  " + note);
        
        if (b.startupFailure != null) {
            // Was the stream B wrote before the failed restart the same as A's? If so, the
            // startup fails to read a stream that the run without restarts also wrote.
            long len = b.stream.getLength();
            long diff = firstDiff(a.stream, b.stream);
            System.out.println("STARTUP FAILED: " + b.startupFailure);
            if (diff < 0 || diff >= len) {
                System.out.println("STREAM: identical up to the failed restart (" + len + " bytes)");
            } else {
                int ti = transAt(a.tpos, diff);
                System.out.println("STREAM: first byte difference at " + diff 
                        + ", in transaction " + ti + ", last restart before it: after trans " 
                        + lastRestart(ti));
            }
            return;
        }

        // 1. Stream identity.

        long diff = firstDiff(a.stream, b.stream);
        if (diff < 0) {
            System.out.println("STREAM: identical");
        } else {
            int ti = transAt(a.tpos, diff);
            System.out.println("STREAM: first byte difference at " + diff + ", in transaction "
                    + ti + ", last restart before it: after trans " + lastRestart(ti));
            printNodeAt("A", a, ti >= 0 ? a.tpos[ti] : -1, diff);
            printNodeAt("B", b, ti >= 0 ? a.tpos[ti] : -1, diff);

            // Semantic comparison: same tpos, and same transaction content when the
            // order of got-dirty ids and in-memory hash names are ignored.

            int si = -1;
            for (int i = Math.max(ti, 0); i < n; i++) {
                if (a.tpos[i] != b.tpos[i]
                        || !sameLines(normalized(a, a.tpos[i]), normalized(b, b.tpos[i]))) {
                    si = i;
                    break;
                }
            }
            if (si < 0) {
                System.out.println("STREAM: semantically identical (only got-dirty order differs)");
            } else {
                System.out.println("STREAM: first semantic difference in transaction " + si
                        + " (tpos A=" + a.tpos[si] + ", B=" + b.tpos[si]
                        + "), last restart before it: after trans " + lastRestart(si));
                printTrans("A", a, a.tpos[si]);
                printTrans("B", b, b.tpos[si]);
                String[] la = normalized(a, a.tpos[si]).split("\n");
                String[] lb = normalized(b, b.tpos[si]).split("\n");
                int shownLines = 0;
                for (int j = 0; j < Math.max(la.length, lb.length) && shownLines < 12; j++) {
                    String x = j < la.length ? la[j] : "";
                    String y = j < lb.length ? lb[j] : "";
                    if (!x.equals(y)) {
                        System.out.println("  line " + j + " A: " + x.trim());
                        System.out.println("  line " + j + " B: " + y.trim());
                        shownLines++;
                    }
                }
            }
        }

        // 2. TransSeq (D) and Dag checksums after each restart.

        int tsDiffs = 0, dbDiffs = 0;
        Integer firstTs = null;
        for (int i : checkpoints) {
            if (!a.transSeqSums.get(i).equals(b.transSeqSums.get(i))) {
                tsDiffs++;
                if (firstTs == null) firstTs = i;
            }
            if (!a.dbSums.get(i).equals(b.dbSums.get(i))) dbDiffs++;
        }
        System.out.println("TRANSSEQ: " + tsDiffs + " of " + checkpoints.size()
                + " checkpoints differ" + (firstTs == null ? "" : ", first after trans " + firstTs));
        System.out.println("KV CHECKSUM: " + dbDiffs + " of " + checkpoints.size()
                + " checkpoints differ");

        // 3. Dirty-set identity.

        System.out.println("IDENTITY A (no restarts): " + a.identity.size() + " of "
                + checkpoints.size() + " checkpoints violate");
        for (Map.Entry<Integer, String> e : a.identity.entrySet()) {
            System.out.println("  A after trans " + e.getKey() + ": " + e.getValue());
            break;
        }
        System.out.println("IDENTITY B (restarts): " + b.identity.size() + " of "
                + checkpoints.size() + " checkpoints violate");
        int shown = 0;
        for (Map.Entry<Integer, String> e : b.identity.entrySet()) {
            System.out.println("  B after trans " + e.getKey() + ": " + e.getValue());
            if (++shown == 3) break;
        }

        // 4. Lookups against the transaction history.

        System.out.println("LOOKUP A (no restarts): " + a.lookups.size() + " of "
                + checkpoints.size() + " checkpoints violate");
        for (Map.Entry<Integer, String> e : a.lookups.entrySet()) {
            System.out.println("  A after trans " + e.getKey() + ": " + e.getValue());
            break;
        }
        System.out.println("LOOKUP B (restarts): " + b.lookups.size() + " of "
                + checkpoints.size() + " checkpoints violate");
        shown = 0;
        for (Map.Entry<Integer, String> e : b.lookups.entrySet()) {
            System.out.println("  B after trans " + e.getKey() + ": " + e.getValue());
            if (++shown == 3) break;
        }
    }

    static long firstDiff(MemoryStream s1, MemoryStream s2) {
        long len = Math.min(s1.getLength(), s2.getLength());
        byte[] b1 = new byte[65536], b2 = new byte[65536];
        long from = Math.max(s1.getFirstPos(), s2.getFirstPos());    // After a cut by reclaim.
        try {
            for (long pos = from; pos < len; pos += b1.length) {
                int chunk = (int) Math.min(b1.length, len - pos);
                s1.read(pos, b1, 0, chunk);
                s2.read(pos, b2, 0, chunk);
                for (int i = 0; i < chunk; i++) {
                    if (b1[i] != b2[i]) return pos + i;
                }
            }
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
        return s1.getLength() == s2.getLength() ? -1 : len;
    }

    static int transAt(long[] tpos, long pos) {
        int result = -1;
        for (int i = 0; i < tpos.length; i++) {
            if (tpos[i] <= pos) result = i;
        }
        return result;
    }

    /**
     * Prints the stored node of the transaction at tpos that contains stream
     * position pos, with its pointers.
     */
    static void printNodeAt(String name, Run r, long tpos, long pos) {
        if (tpos < 0) return;
        try {
            StoredTrans t = StoredTrans.parse(tpos, r.db.internal().nodeStream().readTransBytes(tpos));
            long best = -1;
            for (StoredNode sn : t.nodes) {
                long spos = sn.getNode().getSpos();
                if (spos <= pos && spos > best) best = spos;
            }
            if (best < 0) {
                System.out.println("  " + name + ": position " + pos + " is in the transaction header");
                return;
            }
            String[] lines = r.db.internal().nodeStream().readNode(best).print().split("\n");
            System.out.println("  " + name + ": node at " + best + " (difference at offset "
                    + (pos - best) + "):");
            for (int i = 0; i < Math.min(lines.length, 40); i++) {
                System.out.println("    " + lines[i]);
            }
        } catch (RuntimeException e) {
            System.out.println("  " + name + ": cannot print node, " + e);
        }
    }

    /** True if the texts have the same non-empty lines, ignoring surrounding spaces. */
    static boolean sameLines(String x, String y) {
        List<String> lx = new ArrayList<String>(), ly = new ArrayList<String>();
        for (String l : x.split("\n")) if (l.trim().length() > 0) lx.add(l.trim());
        for (String l : y.split("\n")) if (l.trim().length() > 0) ly.add(l.trim());
        return lx.equals(ly);
    }

    int lastRestart(int ti) {
        return (ti / every) * every - 1;
    }

    /**
     * Transaction text without in-memory hash names (like "K/ff") and with
     * the got-dirty (id, spos) pairs sorted.
     */
    static String normalized(Run r, long tpos) {
        String s;
        try {
            StoredTrans t = StoredTrans.parse(tpos, r.db.internal().nodeStream().readTransBytes(tpos));
            s = t.print();
            // Node contents too: klongs and pointer positions of each stored node.
            StringBuilder nodes = new StringBuilder();
            for (StoredNode sn : t.nodes) {
                nodes.append(r.db.internal().nodeStream().readNode(sn.getNode().getSpos()).print());
            }
            s = s + "\n" + nodes;
        } catch (RuntimeException e) {
            return "unparsable: " + e;
        }
        StringBuilder b = new StringBuilder();
        for (String line : s.split("\n")) {
            line = line.replaceAll("([KVT])/[^ ]*", "$1");     // in-memory hash names
            if (line.trim().startsWith("got dirty:")) {
                String[] parts = line.trim().substring("got dirty:".length()).trim().split("\\s+");
                List<String> pairs = new ArrayList<String>();
                for (int i = 0; i + 1 < parts.length; i += 2) pairs.add(parts[i] + " " + parts[i + 1]);
                Collections.sort(pairs);
                line = "got dirty: " + pairs;
            }
            b.append(line).append('\n');
        }
        return b.toString();
    }

    static void printTrans(String name, Run r, long tpos) {
        try {
            byte[] bytes = r.db.internal().nodeStream().readTransBytes(tpos);
            String s = StoredTrans.parse(tpos, bytes).print();
            String[] lines = s.split("\n");
            System.out.println("---- transaction in run " + name + " ----");
            for (int i = 0; i < Math.min(lines.length, 40); i++) {
                System.out.println("  " + lines[i]);
            }
            if (lines.length > 40) System.out.println("  ... (" + lines.length + " lines)");
        } catch (RuntimeException e) {
            System.out.println("---- transaction in run " + name + ": cannot print, " + e);
        }
    }

    public static void main(String[] args) {
        new RestartInvariance(Long.parseLong(args[0])).compare();
    }
}
