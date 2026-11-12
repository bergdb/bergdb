package bergdb.core;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.*;

import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Kvt;
import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.KlongWithPointer;
import bergdb.dag.Node;
import bergdb.dag.Pointee;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * Writes a trace of a Java run in the terms of the Lean model, for the checker in lean/
 * (lake exe tracecheck). The mapping from Java to the model (α) is in bergdb 011-11, section 2;
 * the trace format is docs/trace-format.md. Written 2026-10-15 for F1-008-11, WP C1.
 *
 * Run A executes a deterministic workload without restarts and records, after every
 * transaction, the changes to P, the record R(i) and D. Run B (probe=K) executes the same
 * workload with a restart after every K transactions, checks the lookups after each restart,
 * and compares its stream and D with run A's. The trace is written when both runs are done,
 * because the levels (section 8.4) are computed from the final structure.
 *
 * In package bergdb.core to reach Db internals.
 *
 * Usage: java [-Dprop=value ...] -cp bergdb.jar:stress bergdb.core.TraceExport seed out.trace
 *
 * Properties:
 *   n=N        transactions after R(0) (default 60)
 *   keys=N     distinct keys (default 50)
 *   maxnode=N  node size 8, 14, 30 or 62 (default 8)
 *   sd=N       startup distance in bytes (default 500)
 *   ops=N      KVs per transaction, at most (default 4); exact=1: exactly ops
 *   bulk=N     one transaction in ten puts N new keys in sorted order (default 0)
 *   del=P      percent of KVs that delete a key of the key space (default 0)
 *   nodel=P    percent of transactions that delete only keys that never exist (default 0)
 *   empty=P    percent of transactions without KVs (default 0)
 *   long=1     half of the keys get two key segments
 *   shape=S    the workload's shape, UnlinkFuzz's (bergdb 024-12): fifo puts new keys in
 *              increasing order and deletes the oldest, a window of about keys/4 live keys;
 *              long3 gives the keys 1 to 5 segments with shared prefixes, the keys of
 *              long=2 below (default: none)
 *   valsize=N  value sizes 1..N bytes (default 20)
 *   probe=K    run B: a restart after every K transactions (default 0: no run B)
 *   live=1     LIVE lines: Java's own live children, for each node, at each of its times
 *   tree=1     trace format 3 (bergdb 024-12, section 2.6; docs/trace-format.md, section 4):
 *              the lines the tree model needs: TREE, BASE, OP, KN, GET and SCAN; gets=N: N GET lines and one SCAN line after each transaction (default 4)
 *   retain=S   reclaim on, with a retain duration of S seconds, as RestartInvariance's option
 *              (default 0: off); transactions are then 0.01 to 0.2 s apart
 *   maint=K    a call of Db.maintain() after every K-th user transaction, in runs A, B and
 *              E; its records are in the call of that transaction (bergdb 024-32; default
 *              0: none)
 *   rune=S     run E: run A's workload with the eviction schedule S (values, every, random,
 *              or budget, the capacity controller, with the budget evictbudget=B; Eviction;
 *              default: no run E); slotevery=N: SLOT lines after every N-th
 *              transaction (default 1); evictseed=N: the random schedule's seed (default: the
 *              seed); ereads=N: N lookups after each transaction of run E, of random keys at
 *              random times, checked against the workload (default 0); erestart=K: a restart
 *              of run E after every K-th transaction (default 0: none); ereads and erestart
 *              since bergdb item 009, step 4c
 *   long=2     the keys of UnlinkFuzz's long shape (A2A3Check2.longShapeKey: 1 to 5 segments,
 *              shared prefixes), which makes and empties many small segment trees
 *              (bergdb 024-09, step A1); the trace's CONFIG line says long=false for it
 *
 * The last line on stdout (not in the trace; bergdb 024-09, step A1) has the Dag's counters of
 * this JVM, so of runs A, B and E together, a rerun at a start included: nodes unlinked by a
 * delete's climb (Dag.statUnlinked), nodes that a transaction made and took back
 * (statTakenBack) and the segment roots among them (statRootsTakenBack), root collapses
 * (statCollapses) and empty keys pointed to the next child (statRelabels). conformance.sh
 * sums them over a set's traces, and requires a take-back of its draining configurations.
 *
 * With reclaim (bergdb item 001, WP R2; bergdb 001-07, 2.7) every executed
 * transaction is a record, reclaim's steps and table stores too: run A records each through
 * Db's test hooks (Db.TestHooks), and the trace has, besides version 1's lines, the touch of
 * each step (TOUCH), the first available time when it changes (FA), each cut decided (CUT)
 * and each move of the stream's first position (PHYSCUT; plan 001-01, 8.2). The stream is a
 * CutStream, which refuses every read below the cut. Run B also restarts right after each cut,
 * looks up from the first available time on, and compares the streams from the cut.
 *
 * Run E (rune=S; bergdb item 001, WP J4; plan 001-01, 8.2) executes run A's workload with a
 * forced eviction schedule (Eviction), compares its stream with run A's (a PROBE line on the
 * last record), and records at the end of each user transaction's call, in its last record,
 * a SLOT line for every slot of every resident canonical index object (the node table's):
 * the object's node, the pointee, the record the slot serializes, as the writer would write
 * it (NodeCollection.resolvePointers: a memory slot its object's position, a stream slot the
 * version it names after Rule R; - for a vpos), and the slot's kind: canon (a memory slot to
 * the pointee's canonical object), mem (to another object, or to a value), stream, or dead (a
 * stream slot below the stream's first position, M33). The checker's C-P compares them with
 * the model's INV-SLOT. Runs A and B run without eviction, whatever the property evict says.
 *
 * Run E's handle state (bergdb item 009, step 4c; items/009-handles/02-implementation-plan.md,
 * 4.10): with the SLOT lines, and under the write lock, so that the capacity controller's
 * eviction thread runs no batch meanwhile, run E records its memory as the Lean model's memory
 * with handles (lean/SIS/Handle.lean, HMem; the mapping of bergdb 009-05, section
 * 2): HMEM, the startup the state comes from and the stream's first record; HTABLE, the node
 * table's entries; HANDLE, every handle that the table or a pointer of an object holds, with
 * its node, state, object and written position; HOBJ, every object that a handle holds, and
 * the super root and D's, with its node, whether it is canonical, its position, the number of
 * entries of its history and the history's hash (historyHash); HPTR, every pointer of an
 * object to an index node, with its pointee, the record it names and the handle it holds. A
 * handle has the same number in every state of run E, an object a number in its state. Values
 * have no handles (009-02, 4.8) and are left out. The checker's C-H checks them against the
 * model's invariants with handles (lean/SIS/HandleTheorems.lean), a history by its hash. Run
 * E's reads (ereads) leave versions read in handles, and take pointers that hold dead handles
 * through the slow path; after a restart (erestart) the state recorded for the transaction is
 * the startup's, and HMEM names the record it read last.
 */
public class TraceExport {
    final long seed;
    final int n = Integer.getInteger("n", 60);
    final int keyCount = Integer.getInteger("keys", 50);
    final int maxNode = Integer.getInteger("maxnode", 8);
    final int startupDistance = Integer.getInteger("sd", 500);
    final int ops = Integer.getInteger("ops", 4);
    final boolean exact = "1".equals(System.getProperty("exact"));
    final int bulk = Integer.getInteger("bulk", 0);
    final int del = Integer.getInteger("del", 0);
    final int nodel = Integer.getInteger("nodel", 0);
    final int empty = Integer.getInteger("empty", 0);
    final boolean longKeys = "1".equals(System.getProperty("long"));
    final String shape = System.getProperty("shape", "");
    final int valsize = Integer.getInteger("valsize", 20);
    final int probe = Integer.getInteger("probe", 0);
    final boolean live = "1".equals(System.getProperty("live"));
    final boolean tree = "1".equals(System.getProperty("tree"));
    final int treeGets = Integer.getInteger("gets", 4);
    /** maint=K: a call of Db.maintain() after every K-th user transaction (bergdb 024-32). */
    final int maint = Integer.getInteger("maint", 0);
    final int retain = Integer.getInteger("retain", 0);
    final String runE = System.getProperty("rune", "");
    final int slotEvery = Integer.getInteger("slotevery", 1);
    final int eReads = Integer.getInteger("ereads", 0);
    final int eRestart = Integer.getInteger("erestart", 0);
    final long timeScale = retain > 0 ? bergdb.pub.util.Clock.UNITS_PER_SEC / 100 : 1;
    /** long=2: UnlinkFuzz's long key shape. */
    final boolean longShape = "2".equals(System.getProperty("long"));

    // The workload: per transaction, keys and values (null value: delete).
    final List<String[]> wkeys = new ArrayList<String[]>();
    final List<byte[][]> wvalues = new ArrayList<byte[][]>();
    final long[] times;
    /** Run A, for user transaction i: its record, and the last record of its call (the
     *  same without reclaim; with it, the steps and table stores reclaim runs after it). */
    final int[] userRec, userLast;

    final List<String> errors = new ArrayList<String>();

    TraceExport(long seed) {
        this.seed = seed;
        Random rnd = new Random(seed);
        times = new long[n];
        userRec = new int[n];
        userLast = new int[n];
        long time = 10;
        int nextNew = keyCount;     // keys of bulk loads, beyond the key space
        int fifoNext = 0, fifoFirst = 0;
        for (int i = 0; i < n; i++) {
            time += (1 + rnd.nextInt(20)) * timeScale;
            times[i] = time;
            List<String> ks = new ArrayList<String>();
            List<byte[]> vs = new ArrayList<byte[]>();
            int r = rnd.nextInt(100);
            if (r < empty) {
                // no KVs
            } else if (r < empty + nodel) {
                int c = 1 + rnd.nextInt(ops);
                for (int j = 0; j < c; j++) {
                    ks.add("/missing/" + i + "/" + j);
                    vs.add(null);
                }
            } else if (shape.equals("fifo")) {
                int c = 1 + rnd.nextInt(ops);
                int window = Math.max(2, keyCount / 4);
                for (int j = 0; j < c; j++) {
                    if (fifoNext - fifoFirst >= window || (fifoNext > fifoFirst && rnd.nextInt(3) == 0)) {
                        ks.add(key(fifoFirst++));
                        vs.add(null);
                    }
                    ks.add(key(fifoNext++));
                    vs.add(value(rnd));
                }
            } else if (bulk > 0 && rnd.nextInt(10) == 0) {
                List<String> sorted = new ArrayList<String>();
                for (int j = 0; j < bulk; j++) sorted.add(key(nextNew++));
                Collections.sort(sorted);
                for (String k : sorted) {
                    ks.add(k);
                    vs.add(value(rnd));
                }
            } else {
                int c = exact ? ops : 1 + rnd.nextInt(ops);
                Set<String> seen = new HashSet<String>();
                for (int j = 0; j < c; j++) {
                    String k = key(rnd.nextInt(keyCount));
                    if (!seen.add(k)) continue;
                    ks.add(k);
                    vs.add(rnd.nextInt(100) < del ? null : value(rnd));
                }
            }
            wkeys.add(ks.toArray(new String[0]));
            wvalues.add(vs.toArray(new byte[0][]));
        }
    }

    String key(int i) {
        // long=2 (bergdb 024-09) and shape=long3 (024-12) are one key rule, UnlinkFuzz's.
        if (longShape || shape.equals("long3")) return bergdb.dag.A2A3Check2.longShapeKey(i);
        return longKeys && i % 2 == 1 ? "/longer/key/" + i : "/k/" + i;
    }

    byte[] value(Random rnd) {
        byte[] v = new byte[1 + rnd.nextInt(valsize)];
        rnd.nextBytes(v);
        return v;
    }

    Db start(AppendOnlyStream stream, CoreTestClock clock) {
        return start(stream, clock, Eviction.Schedule.NONE);
    }

    /** With an eviction schedule (run E; the random schedule's seed: evictseed, else seed). */
    Db start(AppendOnlyStream stream, CoreTestClock clock, Eviction.Schedule schedule) {
        Db db = startOnly(stream, clock, schedule);
        // Since bergdb 015-87 kept in the stream: the first call commits reclaim's settings
        // (an internal record, kind=table), the calls after a restart write nothing.
        if (retain > 0) db.setRetainDuration(retain * bergdb.pub.util.Clock.UNITS_PER_SEC);
        return db;
    }

    /** Starts the database without setting the retain duration (run A sets it later). */
    Db startOnly(AppendOnlyStream stream, CoreTestClock clock, Eviction.Schedule schedule) {
        DbBuilder b = Db.builder().testSetup(stream).clock(clock).startupDistance(startupDistance)
                .evictionSchedule(schedule, Long.getLong("evictseed", seed));
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        return b.start();
    }

    /** A new stream: with reclaim a CutStream, which refuses reads below the cut. */
    AppendOnlyStream newStream() {
        return retain > 0 ? new CutStream() : new MemoryStream();
    }

    /** A copy of the stream, for a restart. */
    static AppendOnlyStream copyOf(AppendOnlyStream s) {
        return s instanceof CutStream ? ((CutStream) s).copy() : ((MemoryStream) s).copy();
    }

    // ======== The state of run A, in model terms ========

    /** An entry of a history: model time and value tokens (docs, 9.1). */
    static final class Ent {
        final int time;
        final String val;
        Ent(int time, String val) { this.time = time; this.val = val; }
        public boolean equals(Object o) {
            return o instanceof Ent && ((Ent) o).time == time && ((Ent) o).val.equals(val);
        }
        public int hashCode() { return time * 31 + val.hashCode(); }
        public String toString() { return time + " " + val; }
    }

    /** A node of P: kind and the Java object (null for the root). */
    static final class PNode {
        final long id;
        final Node obj;
        final int created;      // index of the creating record
        List<Ent> hist = new ArrayList<Ent>();
        PNode(long id, Node obj, int created) { this.id = id; this.obj = obj; this.created = created; }
        boolean isData() { return obj != null && obj.getType() != Node.TYPE_TOP_NODE
                && obj.getType() != Node.TYPE_KEY_NODE; }
    }

    /** A version in a record. */
    static final class Ver {
        long id;
        String kind;
        List<Ent> hist = new ArrayList<Ent>();
        TreeMap<Long, Integer> refs = new TreeMap<Long, Integer>();
        /** A top node's skip slots: slot, and the time its target's root time maps to. */
        List<int[]> skipTimes = new ArrayList<int[]>();
    }

    /** What run A saw for one record. */
    static final class Rec {
        int index;
        long tt, tpos;
        int sp;
        int top = -1;
        long topNode = -1;      // the node of the version that top names (model id)
        String topSrc = "derived";
        List<Long> newNodes = new ArrayList<Long>();
        List<long[]> addsNode = new ArrayList<long[]>();    // node id, index into adds
        List<Ent> adds = new ArrayList<Ent>();
        List<Ver> vers = new ArrayList<Ver>();
        List<Long> gd = new ArrayList<Long>();
        List<long[]> dirty = new ArrayList<long[]>();       // id, d
        List<String> live = new ArrayList<String>();
        List<String> probes = new ArrayList<String>();
        /** Run B: the first touches after the restart after this record, until the next. */
        List<String> firsts = new ArrayList<String>();
        /** Run E: the slots of the resident canonical objects after this record (SLOT). */
        List<String> slots = new ArrayList<String>();
        /** Run E: its handle state after this record (HMEM, HTABLE, HANDLE, HOBJ, HPTR). */
        List<String> handles = new ArrayList<String>();
        long transSeqSum;
        int puts, deletes;
        /** With reclaim: user, step or table; a step's touch; FA, CUT and PHYSCUT lines. */
        String kind = "user";
        List<Long> touch;
        List<String> reclaimLines = new ArrayList<String>();
        /** Trace format 3 (bergdb 024-12): BASE and OP; then KN, GET, SCAN. */
        List<String> treeHead = new ArrayList<String>();
        List<String> treeLines = new ArrayList<String>();
    }

    final Map<Long, PNode> nodes = new TreeMap<Long, PNode>();
    final Map<Long, Integer> idxByTt = new HashMap<Long, Integer>();
    final Map<Long, Integer> idxByTpos = new HashMap<Long, Integer>();
    final Map<Long, long[]> verByPos = new HashMap<Long, long[]>();     // position -> {record, id}
    final List<Rec> recs = new ArrayList<Rec>();
    final List<TopNode> topNodes = new ArrayList<TopNode>();            // by top node id
    long newestWrittenTopId = -1;
    long newestWrittenTopNum = -1;
    int newestWrittenTopRec = -1;

    int timeIndex(long tt, String context) {
        Integer i = idxByTt.get(tt);
        if (i == null) {
            error("time " + tt + " is not the time of a record (" + context + ")");
            return -1;
        }
        return i;
    }

    void error(String s) {
        if (errors.size() < 1000) errors.add(s);
    }

    /**
     * The model id of a Java node: its Java id plus one. Java's primordial key node has id 0,
     * and the model's root has id 0 (docs, 2.2).
     */
    static long mid(long javaId) {
        return javaId + 1;
    }

    static long hash(byte[] v) {
        long h = 0xcbf29ce484222325L;
        for (byte b : v) {
            h ^= (b & 0xff);
            h *= 0x100000001b3L;
        }
        return h & Long.MAX_VALUE;
    }

    /** The id of the node a pointer slot names, or -1 for none. */
    long childId(Node child, long pos, NodeStream ns, String context) {
        if (child != null) return mid(child.getId());
        if (pos == Spos.NULL) return -1;
        if (Spos.isVpos(pos)) return mid(pos);
        long[] v = verByPos.get(pos);
        if (v != null) return v[1];
        error("stream position " + pos + " is not the start of a known version (" + context + ")");
        return mid(ns.readNodeHeader(pos).id());
    }

    /** The entries of a key node (docs, 2.4), from its klongs and pointer slots. */
    List<Ent> keyEntries(KeyNode k, Node[] ptrs, long[] pos, int size, NodeStream ns,
            boolean memoryOnly, String context) {
        List<Ent> result = new ArrayList<Ent>();
        int t = -1;
        long prevDel = Klong.DELETE_NONE_BITMAP;
        for (int i = 0; i < size; i++) {
            long klong = k.klongs[i];
            switch (Klong.getIntType(klong)) {
            case Klong.INT_TYPE_TIME:
                t = timeIndex(Klong.getTime(klong), context);
                break;
            case Klong.INT_TYPE_KEY: {
                Node child = ptrs == null ? null : ptrs[i];
                long p = pos[i];
                if (memoryOnly && child == null) {
                    error("stream pointer in run A, " + context + ", slot " + i);
                }
                long y = childId(child, child == null ? p : Spos.NULL, ns, context);
                result.add(new Ent(t, "K " + Klong.getCompareValue(klong) + " " + y));
                break;
            }
            case Klong.INT_TYPE_DELETE_BITMAP: {
                long bits = (klong & ~prevDel) & 0x3fffffffffffffffL;
                prevDel = klong;
                TreeSet<Long> cs = new TreeSet<Long>();
                for (int j = 0; j < 62; j++) {
                    if ((bits & Klong.DELETE_BITS[j]) != 0) {
                        if (j >= i || Klong.getIntType(k.klongs[j]) != Klong.INT_TYPE_KEY) {
                            error("delete bit " + j + " of klong " + i + " names no earlier key klong ("
                                    + context + ")");
                            continue;
                        }
                        cs.add(Klong.getCompareValue(k.klongs[j]));
                    }
                }
                StringBuilder b = new StringBuilder("D " + cs.size());
                for (long c : cs) b.append(" ").append(c);
                result.add(new Ent(t, b.toString()));
                break;
            }
            default:
                error("bad klong type at " + i + " (" + context + ")");
            }
        }
        return result;
    }

    /** The entries of a top node (docs, 2.4). */
    List<Ent> topEntries(TopNode tn, boolean memoryOnly, NodeStream ns, String context) {
        List<Ent> result = new ArrayList<Ent>();
        int t = timeIndex(tn.rootTime, context);
        // With handles (bergdb item 009, step 3a): a pointer whose handle holds an object
        // that may serve it is a memory pointer to that object; any other a stream pointer
        // with the reference a record would get (Node.getSerializedRef).
        Node root = tn.getPointerNode(0);
        if (memoryOnly && root == null) error("stream root pointer in run A, " + context);
        long y = childId(root, root == null ? tn.getSerializedRef(0) : Spos.NULL, ns, context);
        result.add(new Ent(t, "R " + y));
        for (int j = 0; j < tn.pointersLength; j++) {
            TopNode z = (TopNode) tn.getPointerNode(j + 1);
            long p = z == null ? tn.getSerializedRef(j + 1) : tn.pointersPos[j];
            if (z == null && p == Spos.NULL) continue;
            if (memoryOnly && z == null) error("stream skip pointer in run A, " + context);
            result.add(new Ent(t, "S " + j + " " + childId(z, z == null ? p : Spos.NULL, ns, context)));
        }
        return result;
    }

    List<Ent> entriesOf(PNode pn, NodeStream ns) {
        if (pn.obj == null) {
            List<Ent> result = new ArrayList<Ent>();
            for (TopNode tn : topNodes) {
                result.add(new Ent(timeIndex(tn.rootTime, "root"), "T " + mid(tn.getId())));
            }
            return result;
        }
        if (pn.obj.isIndexNode()) return objectEntries(pn.obj, ns, true, "node " + pn.id);
        List<Ent> result = new ArrayList<Ent>();
        result.add(new Ent(pn.created, "V " + hash(((ValueNode) pn.obj).getValue())));
        return result;
    }

    /**
     * The entries of index object x (docs, 2.4): a key node's from its klongs and pointers, a
     * top node's from its pointers; a pointer's pointee from the object a pointer leads to
     * without a read, else from the reference a record would get. memoryOnly: run A's, whose
     * pointers all lead to objects (an error otherwise).
     */
    List<Ent> objectEntries(Node x, NodeStream ns, boolean memoryOnly, String context) {
        if (x instanceof TopNode) return topEntries((TopNode) x, memoryOnly, ns, context);
        KeyNode k = (KeyNode) x;
        int size = k.size;
        Node[] view = new Node[size];
        long[] refs = new long[size];
        for (int i = 0; i < size; i++) {
            if (Klong.getIntType(k.klongs[i]) != Klong.INT_TYPE_KEY) continue;
            view[i] = k.getPointerNode(i);
            refs[i] = view[i] == null ? k.getSerializedRef(i) : k.getPointerPos(i);
        }
        return keyEntries(k, view, refs, size, ns, memoryOnly, context);
    }

    /**
     * The hash of a history (bergdb item 009, step 4c; the checker's historyHash in
     * lean/Check/Trace.lean computes the same): FNV-1a with 64 bits (offset basis
     * 0xcbf29ce484222325, prime 0x100000001b3, arithmetic modulo 2^64) over the bytes of the
     * entries in their order, each as on an H line, then a newline (0x0a): the time (the
     * record index), a space, and the value, one of K c y (a key klong: compare value c,
     * child y), D n c1 ... cn (a delete bitmap: the n compare values it deletes, ascending),
     * R y (a top node's root pointer), S j z (its skip pointer j), T z (a root entry) and V h
     * (a value's data, h its hash); numbers in decimal ASCII, tokens separated by one space.
     * Written as an unsigned decimal.
     */
    static long historyHash(List<Ent> h) {
        long x = 0xcbf29ce484222325L;
        for (Ent e : h) {
            for (byte b : (e + "\n").getBytes(java.nio.charset.StandardCharsets.UTF_8)) {
                x ^= (b & 0xff);
                x *= 0x100000001b3L;
            }
        }
        return x;
    }

    /** Adds every node reachable through memory pointers, live or dead, to 'nodes'. */
    void walk(Db db, int index) {
        TopNode superRoot = db.internal().dag().getTopDs().getSuperRoot();
        Deque<Node> todo = new ArrayDeque<Node>();
        Set<Node> seen = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        todo.add(superRoot);
        while (!todo.isEmpty()) {
            Node x = todo.poll();
            if (!seen.add(x)) continue;
            register(x, index);
            if (x.isIndexNode()) {
                int size = x.getSize();
                for (int i = 0; i < size; i++) {
                    Node c = x.getPointerNode(i);
                    if (c != null) todo.add(c);
                }
            }
        }
    }

    void register(Node x, int index) {
        if (x.getType() == Node.TYPE_DELETE) return;
        PNode pn = nodes.get(mid(x.getId()));
        if (pn == null) {
            nodes.put(mid(x.getId()), new PNode(mid(x.getId()), x, index));
            if (x instanceof TopNode) {
                topNodes.add((TopNode) x);
                Collections.sort(topNodes, new Comparator<TopNode>() {
                    public int compare(TopNode a, TopNode b) {
                        return a.topNodeId < b.topNodeId ? -1 : a.topNodeId == b.topNodeId ? 0 : 1;
                    }
                });
            }
        } else if (pn.obj != x) {
            error("two objects for node " + mid(x.getId()) + " in run A");
        }
    }

    /** Parses R(i) into versions; updates the position map first. */
    void parseRecord(Db db, Rec rec) {
        NodeStream ns = db.internal().nodeStream();
        StoredTrans st = StoredTrans.parse(rec.tpos, ns.readTransBytes(rec.tpos));
        if (st.tt != rec.tt) error("R(" + rec.index + "): stored time " + st.tt + " != " + rec.tt);
        for (StoredNode sn : st.nodes) {
            Node x = sn.getNode();
            if (x.getType() == Node.TYPE_DELETE) continue;
            verByPos.put(x.getSpos(), new long[] {rec.index, mid(x.getId())});
        }
        Integer sp = idxByTpos.get(st.startupPos);
        if (sp == null && st.startupPos <= recs.get(0).tpos) sp = 0;     // 0: before R(0)
        if (sp == null) {
            error("R(" + rec.index + "): startup pos " + st.startupPos + " is not a record's start");
            sp = -1;
        }
        rec.sp = sp;
        for (StoredNode sn : st.nodes) {
            Node x = sn.getNode();
            String context = "version of " + mid(x.getId()) + " in R(" + rec.index + ")";
            Ver v = new Ver();
            v.id = mid(x.getId());
            switch (x.getType()) {
            case Node.TYPE_DELETE:
                rec.deletes++;
                continue;
            case Node.TYPE_VALUE:
                rec.puts++;
                v.kind = "D";
                v.hist.add(new Ent(rec.index, "V " + hash(((ValueNode) x).getValue())));
                break;
            case Node.TYPE_KEY_NODE: {
                KeyNode k = (KeyNode) x;
                v.kind = "I";
                v.hist = keyEntries(k, null, k.pos, k.size, ns, false, context);
                for (int i = 0; i < k.size; i++) {
                    if (Klong.getIntType(k.klongs[i]) == Klong.INT_TYPE_KEY) {
                        addRef(v, k.pos[i], ns, context);
                    }
                }
                break;
            }
            case Node.TYPE_TOP_NODE: {
                TopNode tn = (TopNode) x;
                v.kind = "I";
                v.hist = topEntries(tn, false, ns, context);
                addRef(v, tn.rootPointerPos, ns, context);
                for (int j = 0; j < tn.pointersLength; j++) {
                    if (tn.pointersPos[j] != Spos.NULL) {
                        addRef(v, tn.pointersPos[j], ns, context);
                        v.skipTimes.add(new int[] {j, timeIndex(tn.pointersTime[j], context)});
                    }
                }
                if (tn.topNodeId >= newestWrittenTopNum) {
                    newestWrittenTopNum = tn.topNodeId;
                    newestWrittenTopId = mid(tn.getId());
                    newestWrittenTopRec = rec.index;
                }
                break;
            }
            default:
                error("unknown node type in " + context);
                continue;
            }
            rec.vers.add(v);
        }
        rec.top = newestWrittenTopRec;
        rec.topNode = newestWrittenTopId;
        if (Spos.isValid(st.topPos) && !Spos.isVpos(st.topPos)) {
            // The record's own field (format 5, M18): the latest version of the newest
            // written top node. It must agree with the exporter's derivation.
            long[] v = verByPos.get(st.topPos);
            int fieldRec = v == null ? -1 : (int) v[0];
            if (fieldRec != newestWrittenTopRec || v == null || v[1] != newestWrittenTopId) {
                error("R(" + rec.index + "): topPos names R(" + fieldRec + "), the newest written top "
                        + "node's latest version is in R(" + newestWrittenTopRec + ")");
            }
            rec.topSrc = "field";
            rec.top = fieldRec;
            rec.topNode = v == null ? -1 : v[1];
        }
        for (int j = 0; j < st.gotDirtyIdsAndSpos.length / 2; j++) {
            rec.gd.add(mid(st.gotDirtyIdsAndSpos[2 * j]));
        }
    }

    void addRef(Ver v, long pos, NodeStream ns, String context) {
        if (pos == Spos.NULL || Spos.isVpos(pos)) return;
        long[] target = verByPos.get(pos);
        if (target == null) {
            error("reference to position " + pos + " that starts no version (" + context + ")");
            return;
        }
        if (target[0] < cutRecord) refsBelowCut++;
        Integer old = v.refs.put(target[1], (int) target[0]);
        if (old != null && old != (int) target[0]) {
            error("two references for node " + target[1] + ": R(" + old + ") and R(" + target[0]
                    + ") (" + context + ")");
        }
    }

    void recordDirty(Db db, final Rec rec) {
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                Integer d = idxByTpos.get(tpos);
                if (d == null) {
                    error("D: tpos " + tpos + " is not a record's start");
                    d = -1;
                }
                rec.dirty.add(new long[] {mid(node.getId()), d});
            }
        });
        rec.transSeqSum = db.internal().transSeq().checksum();
    }

    /** The changes of T(i): nodes not in 'before', and entries appended at time i. */
    void recordChanges(Map<Long, List<Ent>> before, Rec rec, NodeStream ns) {
        for (PNode pn : nodes.values()) {
            List<Ent> h = entriesOf(pn, ns);
            List<Ent> old = before.get(pn.id);
            int from = 0;
            if (old == null) {
                rec.newNodes.add(pn.id);
            } else {
                if (h.size() < old.size() || !h.subList(0, old.size()).equals(old)) {
                    error("T(" + rec.index + ") changed or removed entries of node " + pn.id
                            + ": before " + old + ", after " + h);
                    pn.hist = h;
                    continue;
                }
                from = old.size();
            }
            for (int j = from; j < h.size(); j++) {
                Ent e = h.get(j);
                if (e.time != rec.index) {
                    error("T(" + rec.index + ") added an entry at time " + e.time + " to node "
                            + pn.id);
                }
                rec.addsNode.add(new long[] {pn.id});
                rec.adds.add(e);
            }
            pn.hist = h;
        }
    }

    /** LIVE lines: Java's own live children of each node at each of its entry times. */
    void recordLive(Db db, Rec rec) {
        GetData gd = db.newGetData();
        // The root at every time up to this record (review-13-claude, 5.2: so that the
        // search's predecessor branch is compared too): at each record's time, and at the
        // last time before the next record, which the model also calls t.
        for (int t = 0; t <= rec.index; t++) {
            long[] tts = t < rec.index && recs.get(t + 1).tt - 1 > recs.get(t).tt
                    ? new long[] {recs.get(t).tt, recs.get(t + 1).tt - 1} : new long[] {recs.get(t).tt};
            for (long tt : tts) {
                TopNode s = db.internal().dag().getTopDs().findSuperRootAtTime(tt, gd);
                rec.live.add("LIVE 0 " + t + (s == null ? "" : " " + mid(s.getId())));
            }
        }
        for (PNode pn : nodes.values()) {
            if (pn.obj == null) continue;   // the root: above
            TreeSet<Integer> ts = new TreeSet<Integer>();
            for (Ent e : pn.hist) ts.add(e.time);
            ts.add(rec.index);
            for (int t : ts) {
                if (t < 0) continue;
                long tt = recs.get(t).tt;
                TreeSet<Long> children = new TreeSet<Long>();
                if (pn.obj instanceof TopNode) {
                    if (((TopNode) pn.obj).rootTime > tt) continue;
                    KeyNode r = (KeyNode) ((TopNode) pn.obj).getPointerNode(0);
                    if (r != null) children.add(mid(r.getId()));
                } else if (pn.obj instanceof KeyNode) {
                    // Java's own lookup: KeyNode.searchEq for each compare value.
                    KeyNode k = (KeyNode) pn.obj;
                    TreeSet<Long> cvs = new TreeSet<Long>();
                    for (int i = 0; i < k.size; i++) {
                        if (Klong.getIntType(k.klongs[i]) == Klong.INT_TYPE_KEY) {
                            cvs.add(Klong.getCompareValue(k.klongs[i]));
                        }
                    }
                    KlongWithPointer kwi = new KlongWithPointer();
                    for (long cv : cvs) {
                        k.searchEq(tt, cv, kwi);
                        if (kwi.klong == Klong.NULL) continue;
                        if (kwi.node != null) children.add(mid(kwi.node.getId()));
                        else error("LIVE: stream pointer in run A, node " + pn.id);
                    }
                } else {
                    continue;
                }
                StringBuilder b = new StringBuilder("LIVE " + pn.id + " " + t);
                for (long c : children) b.append(" ").append(c);
                rec.live.add(b.toString());
            }
        }
    }

    /** Run A: no restarts; records everything, each executed transaction through Db's test
     *  hooks, so that with reclaim its steps and table stores are records too. */
    AppendOnlyStream runA() {
        final AppendOnlyStream stream = newStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(1);
        // The retain duration is set below, once the hooks record: its call commits a
        // record of reclaim's settings, R(1) (bergdb 015-87).
        final Db db = startOnly(stream, clock, Eviction.Schedule.NONE);
        final NodeStream ns = db.internal().nodeStream();

        // R(0), the primordial record.
        Rec r0 = new Rec();
        r0.index = 0;
        r0.kind = "init";
        r0.tpos = RecoverableStream.META_BLOCK_SIZE;
        StoredTrans st0 = StoredTrans.parse(r0.tpos, ns.readTransBytes(r0.tpos));
        r0.tt = st0.tt;
        idxByTt.put(r0.tt, 0);
        idxByTpos.put(r0.tpos, 0);
        recs.add(r0);
        walk(db, 0);
        Map<Long, List<Ent>> before = new HashMap<Long, List<Ent>>();
        nodes.put(0L, new PNode(0L, null, 0));
        recordChanges(before, r0, ns);
        parseRecord(db, r0);
        recordDirty(db, r0);
        if (live) recordLive(db, r0);

        final List<ValueNode> created = new ArrayList<ValueNode>();
        final List<Node> touched = new ArrayList<Node>();
        if (tree) recordTreeInit(db, r0, ns);
        Db.TestHooks hooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                record(db, x, created, touched, ns);
                created.clear();
                touched.clear();
                treeOps.clear();
            }
            public void valueNodeCreated(ValueNode node, long[] key) {
                created.add(node);
                // The operation that Db.putKvs gave the Dag last changed it: a put, or a
                // delete that deleted (bergdb 024-12, section 2.6).
                if (!treeOps.isEmpty()) treeOps.get(treeOps.size() - 1)[2] = Boolean.TRUE;
            }
            public void kvApplied(long[] key, byte[] value) {
                treeOps.add(new Object[] {key.clone(), value, Boolean.FALSE});
            }
            public void nodeTouched(Node node) {
                touched.add(node);
            }
            public void nodeReplaced(Node node) {}
        };

        Db.testHooks = hooks;
        try {
            if (retain > 0) db.setRetainDuration(retain * bergdb.pub.util.Clock.UNITS_PER_SEC);
            for (int i = 0; i < n; i++) {
                clock.setTime(times[i]);
                Trans.Builder b = db.trans();
                String[] ks = wkeys.get(i);
                byte[][] vs = wvalues.get(i);
                for (int j = 0; j < ks.length; j++) {
                    if (vs[j] == null) b.delete(ks[j]);
                    else b.put(ks[j], vs[j]);
                }
                Trans t = b.build();
                userRec[i] = recs.size();
                db.execute(t);
                maintain(db, i);
                userLast[i] = recs.size() - 1;
                if (userLast[i] < userRec[i] || recs.get(userRec[i]).tt != t.tt) {
                    error("transaction " + i + ": no record, or not the first of its call");
                }
                if (retain > 0) afterCall(db, stream, i);
            }
        } finally {
            Db.testHooks = null;
        }
        db.sync(SyncLevel.ORDINARY);
        return stream;
    }

    /** Records R(i), the record of transaction x.trans, which Db has just appended. */
    void record(Db db, Db.ExecuteData x, List<ValueNode> created, List<Node> touched, NodeStream ns) {
        Map<Long, List<Ent>> before = new HashMap<Long, List<Ent>>();
        for (PNode pn : nodes.values()) before.put(pn.id, pn.hist);
        Trans t = x.trans;
        Rec rec = new Rec();
        rec.index = recs.size();
        rec.tt = t.tt;
        rec.tpos = t.tpos;
        if (idxByTt.containsKey(t.tt)) error("two records with time " + t.tt);
        idxByTt.put(t.tt, rec.index);
        idxByTpos.put(t.tpos, rec.index);
        recs.add(rec);

        for (ValueNode v : created) register(v, rec.index);
        for (Node y : x.transInfo.gotDirtyNodes) register(y, rec.index);
        walk(db, rec.index);
        recordChanges(before, rec, ns);
        parseRecord(db, rec);
        recordDirty(db, rec);
        if (live) recordLive(db, rec);
        if (retain > 0) recordReclaim(db, t, touched, rec);
        if (tree) recordTree(db, t, rec, ns);
    }

    // ======== Trace format 3: the lines of the tree model (bergdb 024-12, section 2.6) ========

    /** The operations that Db.putKvs gave the Dag in the transaction being executed: the
     *  key's segments, the value (null: a delete), and whether it made a value node. */
    final List<Object[]> treeOps = new ArrayList<Object[]>();
    /** The reads of the GET and SCAN lines: a generator of its own, so that the workload is
     *  the same with and without tree=1. */
    final Random treeRnd = new Random(0x5DEECE66DL);
    /** Every key of the workload, for the GET and SCAN lines. */
    List<String> treeKeys = null;

    static String segs(long[] key) {
        StringBuilder b = new StringBuilder("" + key.length);
        for (long c : key) b.append(" ").append(c);
        return b.toString();
    }

    /** A key node's klongs as on a KN line: T t, K c y, B b. */
    String klongs(PNode pn, NodeStream ns) {
        KeyNode k = (KeyNode) pn.obj;
        int size = k.size;
        String context = "KN of node " + pn.id;
        StringBuilder b = new StringBuilder("KN " + pn.id + " " + (k.isSegmentLeaf() ? 1 : 0)
                + " " + size);
        for (int i = 0; i < size; i++) {
            long klong = k.klongs[i];
            switch (Klong.getIntType(klong)) {
            case Klong.INT_TYPE_TIME:
                b.append(" T ").append(timeIndex(Klong.getTime(klong), context));
                break;
            case Klong.INT_TYPE_KEY: {
                Node child = k.getPointerNode(i);
                long y = childId(child, child == null ? k.getSerializedRef(i) : Spos.NULL, ns, context);
                b.append(" K ").append(Klong.getCompareValue(klong)).append(" ").append(y);
                break;
            }
            case Klong.INT_TYPE_DELETE_BITMAP:
                b.append(" B ").append(klong & 0x3fffffffffffffffL);
                break;
            default:
                error("bad klong type at " + i + " (" + context + ")");
            }
        }
        return b.toString();
    }

    /** R(0)'s lines: its key nodes. */
    void recordTreeInit(Db db, Rec rec, NodeStream ns) {
        for (PNode pn : nodes.values()) {
            if (pn.obj instanceof KeyNode) rec.treeLines.add(klongs(pn, ns));
        }
    }

    /** The lines of T(i) for the tree model: its first id, its operations, the key nodes
     *  it made or changed, and reads of Java at random times. */
    void recordTree(Db db, Trans t, Rec rec, NodeStream ns) {
        rec.treeHead.add("BASE " + mid(rec.tpos + 1));
        for (Object[] op : treeOps) {
            long[] key = (long[]) op[0];
            byte[] value = (byte[]) op[1];
            if (value != null) {
                rec.treeHead.add("OP P " + segs(key) + " " + hash(value));
            } else {
                rec.treeHead.add("OP " + (op[2] == Boolean.TRUE ? "D " : "N ") + segs(key));
            }
        }
        Set<Long> changed = new TreeSet<Long>(rec.newNodes);
        for (long[] a : rec.addsNode) changed.add(a[0]);
        for (long id : changed) {
            PNode pn = nodes.get(id);
            if (pn != null && pn.obj instanceof KeyNode) rec.treeLines.add(klongs(pn, ns));
        }
        if (treeKeys == null) {
            Set<String> all = new TreeSet<String>();
            for (String[] ks : wkeys) for (String k : ks) all.add(k);
            all.add("/absent");
            treeKeys = new ArrayList<String>(all);
        }
        // Reads, from the first available time on (a read below it may expire).
        final GetData gd = db.newGetData();
        for (int g = 0; g < treeGets; g++) {
            int ti = lastFa + treeRnd.nextInt(rec.index - lastFa + 1);
            long[] key = Keys.toSegments(treeKeys.get(treeRnd.nextInt(treeKeys.size())));
            try {
                byte[] v = db.internal().dag().getOne(recs.get(ti).tt, key, gd);
                rec.treeLines.add("GET " + ti + " " + segs(key) + " " + (v == null ? "-" : "" + hash(v)));
            } catch (RuntimeException e) {
                error("GET at R(" + rec.index + "), time " + ti + ": " + oneLine(e));
            }
        }
        if (treeGets > 0) {
            int ti = lastFa + treeRnd.nextInt(rec.index - lastFa + 1);
            boolean forward = treeRnd.nextInt(4) != 0;
            boolean inclusive = treeRnd.nextBoolean();
            boolean endInclusive = treeRnd.nextBoolean();
            int limit = 1 + treeRnd.nextInt(6);
            long[] start = treeRnd.nextInt(5) == 0 ? null
                    : Keys.toSegments(treeKeys.get(treeRnd.nextInt(treeKeys.size())));
            long[] end = !forward || treeRnd.nextInt(2) == 0 ? null
                    : Keys.toSegments(treeKeys.get(treeRnd.nextInt(treeKeys.size())));
            try {
                GetMany g = db.internal().dag().newGetMany();
                g.gd.pointerFollower = gd.pointerFollower;
                g.gd.pointerListener = gd.pointerListener;
                g.gd.cachePolicy = gd.cachePolicy;
                g.lookupTime = recs.get(ti).tt;
                g.actualLookupTime = recs.get(ti).tt;
                g.startKey = start;
                g.inclusive = inclusive;
                g.forward = forward;
                g.endKey = end;
                g.endInclusive = endInclusive;
                g.stopCondition = new GetMany.GetN(limit);
                db.internal().dag().getMany(g);
                StringBuilder b = new StringBuilder("SCAN " + ti + " " + (forward ? "F" : "B") + " "
                        + (inclusive ? 1 : 0) + " " + (endInclusive ? 1 : 0) + " " + limit + " "
                        + (start == null ? "-" : segs(start)) + " " + (end == null ? "-" : segs(end))
                        + " " + g.result.size());
                for (Kvt kvt : g.result) {
                    b.append(" ").append(segs(kvt.key)).append(" ").append(hash(kvt.value));
                }
                rec.treeLines.add(b.toString());
            } catch (RuntimeException e) {
                error("SCAN at R(" + rec.index + "), time " + ti + ": " + oneLine(e));
            }
        }
    }

    // ======== Reclaim (bergdb 001-07, 2.7) ========

    int lastFa = 0;             // the first available time, as a model time
    long lastCutPStart = -1;    // pStart of the newest row marked cut, or -1
    long lastFirstPos;          // the stream's first position
    final Set<Integer> cutCalls = new HashSet<Integer>();   // user transactions after which a cut is decided
    int refsBelowCut = 0;       // references of records after a cut to versions before it
    int cutRecord = 0;          // c of the newest cut decided, for the records after it

    /** The kind of R(i), its touch, the first available time and a cut decided at it. */
    void recordReclaim(Db db, Trans t, List<Node> touched, Rec rec) {
        rec.kind = !t.isInternal() ? "user" : t.touch ? "step" : "table";
        if (t.touch) {
            TreeSet<Long> ids = new TreeSet<Long>();
            for (Node x : touched) {
                long id = mid(x.getId());
                PNode pn = nodes.get(id);
                if (pn == null || pn.obj == null || pn.isData()) {
                    error("TOUCH of R(" + rec.index + "): node " + id + " is not an index node of P");
                }
                ids.add(id);
            }
            rec.touch = new ArrayList<Long>(ids);
        } else if (!touched.isEmpty()) {
            error("R(" + rec.index + "), without a touch, touched " + touched.size() + " nodes");
        }
        // fa(i): the tEnd of the newest row marked cut in the table as stored at or before
        // R(i); 0 before the first cut (bergdb 001-07, 2.4).
        Reclaim.IterationInfo row = db.internal().reclaim().lastCutRow();
        int fa = row == null ? 0 : timeIndex(row.tEnd, "the first available time at R(" + rec.index + ")");
        if (fa != lastFa) {
            rec.reclaimLines.add("FA " + fa);
            lastFa = fa;
        }
        if (row != null && row.pStart != lastCutPStart) {
            Integer c = idxByTpos.get(row.pCut);
            if (c == null) error("CUT at R(" + rec.index + "): pCut " + row.pCut + " is not a record's start");
            rec.reclaimLines.add("CUT " + (c == null ? -1 : c) + " " + fa);
            lastCutPStart = row.pStart;
            if (c != null) cutRecord = c;
        }
    }

    /**
     * With maint=K, a call of maintain() after every K-th user transaction, the same in
     * runs A, B and E (bergdb 024-32): its records belong to the call of transaction i, as
     * reclaim's after a commit do.
     */
    void maintain(Db db, int i) {
        if (maint > 0 && (i + 1) % maint == 0) {
            db.maintain();
        }
    }

    /** After the call of user transaction i: the cut decided in it, a move of the stream's
     *  first position (the physical cut, at the call's last record), and Java's first
     *  available time against the model's. */
    void afterCall(Db db, AppendOnlyStream stream, int i) {
        for (int r = userRec[i]; r <= userLast[i]; r++) {
            for (String line : recs.get(r).reclaimLines) {
                if (line.startsWith("CUT ")) cutCalls.add(i);
            }
        }
        long javaFa = db.getFirstAvailableLookupTime();
        long modelFa = lastFa == 0 ? 0 : recs.get(lastFa).tt;
        if (javaFa != modelFa) {
            error("after transaction " + i + ": Java's first available lookup time " + javaFa
                    + ", the table's " + modelFa);
        }
        long fp = stream.getFirstPos();
        if (fp == lastFirstPos) return;
        lastFirstPos = fp;
        Rec last = recs.get(userLast[i]);
        int c = -1;
        for (Rec r : recs) {
            if (r.tpos >= fp) {
                c = r.index;
                break;
            }
        }
        last.reclaimLines.add("PHYSCUT " + c);
        if (fp > db.getFirstAvailablePos()) {
            error("PHYSCUT after R(" + last.index + "): the first position " + fp
                    + " is above the decided cut, " + db.getFirstAvailablePos());
        }
    }

    /** The first touches go to this list: that of the last restart's record. */
    List<String> curFirsts = null;

    /** Records the first touches of run B as FIRST lines (docs/trace-format.md, 2). */
    final NodeCollection.FirstTouchListener firstTouches = new NodeCollection.FirstTouchListener() {
        public void firstTouch(long id, long ref, Node result, boolean read, boolean cutBack) {
            if (curFirsts == null) return;
            String n = Spos.isVpos(ref) ? "-" : recordOfPos(ref, "FIRST of node " + mid(id));
            String line;
            if (result.isCanonical()) {
                line = "FIRST " + mid(id) + " " + n + " - canonical 0";
            } else if (read && result.getSpos() == ref) {
                line = "FIRST " + mid(id) + " " + n + " " + n + " version " + (cutBack ? 1 : 0);
            } else {
                line = "FIRST " + mid(id) + " " + n + " "
                        + recordOfPos(result.getSpos(), "FIRST of node " + mid(id)) + " snapshot 0";
            }
            curFirsts.add(line);
        }
    };

    /** The record of the version at stream position pos. */
    String recordOfPos(long pos, String context) {
        long[] v = verByPos.get(pos);
        if (v == null) {
            error("stream position " + pos + " is not the start of a known version (" + context + ")");
            return "-";
        }
        return "" + v[0];
    }

    /** Run B: the same workload with restarts; compares with run A. */
    void runB(AppendOnlyStream streamA) {
        try {
            NodeCollection.firstTouchListener = firstTouches;
            runB0(streamA);
        } finally {
            NodeCollection.firstTouchListener = null;
            curFirsts = null;
        }
    }

    void runB0(AppendOnlyStream streamA) {
        AppendOnlyStream stream = newStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(1);
        Db db = start(stream, clock);
        TreeMap<String, TreeMap<Long, byte[]>> history = new TreeMap<String, TreeMap<Long, byte[]>>();
        for (int i = 0; i < n; i++) {
            clock.setTime(times[i]);
            Trans.Builder b = db.trans();
            String[] ks = wkeys.get(i);
            byte[][] vs = wvalues.get(i);
            for (int j = 0; j < ks.length; j++) {
                if (vs[j] == null) b.delete(ks[j]);
                else b.put(ks[j], vs[j]);
                TreeMap<Long, byte[]> h = history.get(ks[j]);
                if (h == null) history.put(ks[j], h = new TreeMap<Long, byte[]>());
                h.put(times[i], vs[j]);
            }
            Trans t = b.build();
            db.execute(t);
            maintain(db, i);
            // The user record, and the last record of the call (with reclaim, its steps and
            // table stores follow the user record; without, the two are the same).
            Rec recU = recs.get(userRec[i]);
            Rec recA = recs.get(userLast[i]);
            if (t.tpos != recU.tpos) {
                recA.probes.add("PROBE " + recA.index + " fail run B wrote R(" + recU.index + ") at "
                        + t.tpos + ", run A at " + recU.tpos);
            }
            checkM4(db, recA);

            // A restart after every probe transactions, and right after each cut decided.
            boolean restart = ((i + 1) % probe == 0 || cutCalls.contains(i)) && i + 1 < n;
            if (!restart) continue;
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            stream = copyOf(stream);
            curFirsts = recA.firsts;
            try {
                db = start(stream, clock);
            } catch (RuntimeException e) {
                recA.probes.add("PROBE " + recA.index + " fail restart failed: " + oneLine(e));
                return;
            }
            String problem = null;
            if (db.internal().transSeq().checksum() != recA.transSeqSum) {
                problem = "D differs after the restart";
            }
            if (problem == null) problem = lookupProblem(db, history, i);
            recA.probes.add("PROBE " + recA.index + (problem == null ? " ok" : " fail " + problem));
        }
        db.sync(SyncLevel.ORDINARY);
        long diff = firstDiff(streamA, stream);
        Rec last = recs.get(recs.size() - 1);
        last.probes.add("PROBE " + last.index + (diff < 0 ? " ok streams identical"
                : " fail streams differ at byte " + diff));
    }

    // ======== Run E: eviction (bergdb item 001, WP J4) ========

    int slotLines = 0;
    String evictionSummary = "";

    /** Run E: run A's workload with the eviction schedule runE; SLOT lines; compares the
     *  stream with run A's. */
    void runE(AppendOnlyStream streamA) {
        Eviction.Schedule schedule = Eviction.Schedule.valueOf(runE.toUpperCase());
        AppendOnlyStream stream = newStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(1);
        Db db = start(stream, clock, schedule);
        TreeMap<String, TreeMap<Long, byte[]>> history =
                new TreeMap<String, TreeMap<Long, byte[]>>();
        int started = 0;    // the last record that run E's last startup read
        for (int i = 0; i < n; i++) {
            clock.setTime(times[i]);
            Trans.Builder b = db.trans();
            String[] ks = wkeys.get(i);
            byte[][] vs = wvalues.get(i);
            for (int j = 0; j < ks.length; j++) {
                if (vs[j] == null) b.delete(ks[j]);
                else b.put(ks[j], vs[j]);
                TreeMap<Long, byte[]> h = history.get(ks[j]);
                if (h == null) history.put(ks[j], h = new TreeMap<Long, byte[]>());
                h.put(times[i], vs[j]);
            }
            Trans t = b.build();
            db.execute(t);
            maintain(db, i);
            Rec recU = recs.get(userRec[i]);
            Rec recA = recs.get(userLast[i]);
            if (t.tpos != recU.tpos) {
                recA.probes.add("PROBE " + recA.index + " fail run E wrote R(" + recU.index + ") at "
                        + t.tpos + ", run A at " + recU.tpos);
            }
            // Reads and a restart between transactions (bergdb item 009, step 4c).
            if (eReads > 0) {
                String problem = lookupProblem(db, history, i, 0, eReads,
                        new Random(seed * 37 + i));
                if (problem != null) {
                    recA.probes.add("PROBE " + recA.index + " fail run E (" + runE + "): "
                            + problem);
                }
            }
            if (eRestart > 0 && (i + 1) % eRestart == 0 && i + 1 < n) {
                db.sync(SyncLevel.ORDINARY);
                db.stop();
                stream = copyOf(stream);
                try {
                    db = start(stream, clock, schedule);
                } catch (RuntimeException e) {
                    recA.probes.add("PROBE " + recA.index + " fail run E (" + runE
                            + "): restart failed: " + oneLine(e));
                    return;
                }
                started = recA.index;
            }
            if ((i + 1) % slotEvery == 0 || i + 1 == n) {
                // Under the write lock: the capacity controller's eviction thread may run
                // batches after the call (bergdb item 009, step 3d), and the state recorded is
                // one between them (bergdb item 009, step 4c).
                synchronized (db.internal().getWriteLock()) {
                    List<String> lines = slots(db, recA);
                    recA.slots.addAll(lines);
                    slotLines += lines.size();
                    lines = handleState(db, recA, started);
                    recA.handles.addAll(lines);
                    handleLines += lines.size();
                }
            }
        }
        db.sync(SyncLevel.ORDINARY);
        evictionSummary = db.internal().eviction().summary();
        long diff = firstDiff(streamA, stream);
        Rec last = recs.get(recs.size() - 1);
        last.probes.add("PROBE " + last.index + (diff < 0 ? " ok run E (" + runE + "): streams identical"
                : " fail run E (" + runE + "): streams differ at byte " + diff));
    }

    /** The SLOT lines of run E's state now, between transactions, after record rec. */
    List<String> slots(Db db, Rec rec) {
        Db.Internal in = db.internal();
        Cache3 table = in.cache();
        NodeCollection nc = in.nodeCollection();
        long firstPos = in.nodeStream().getFirstPos();
        List<String> lines = new ArrayList<String>();
        for (Node x : table.nodes()) {
            if (!x.isIndexNode() || !x.isCanonical()) continue;
            int size = x.getSize();
            for (int i = 0; i < size; i++) {
                Node c = x.getPointerNode(i);
                // A stream pointer's reference: what a record would get (with handles,
                // bergdb item 009, step 3a: the newer of the pointer's and its dead handle's
                // written position).
                long pos = c == null ? x.getSerializedRef(i) : x.getPointerPos(i);
                if (Pointer.isNull(c, pos)) continue;
                String context = "SLOT of node " + mid(x.getId()) + " after R(" + rec.index + ")";
                long y;
                long ref;
                String kind;
                if (c != null) {
                    y = mid(c.getId());
                    ref = c.getSpos();
                    kind = c.isIndexNode() && c.isCanonical() && table.getNode(c.getId()) == c
                            ? "canon" : "mem";
                } else if (Spos.isVpos(pos)) {
                    y = mid(pos);
                    ref = pos;
                    kind = "stream";
                } else {
                    long[] v = verByPos.get(pos);
                    if (v == null) {
                        error("stream position " + pos + " is not the start of a known version ("
                                + context + ")");
                        continue;
                    }
                    y = v[1];
                    ref = pos;
                    if (pos < firstPos) {
                        kind = "dead";
                    } else {
                        kind = "stream";
                        Long newPos = nc.newestInSection(y - 1);
                        if (newPos != null && Spos.newer(newPos, ref)) ref = newPos;
                    }
                }
                String r = Spos.isVpos(ref) || !Spos.isValid(ref) ? "-" : recordOfPos(ref, context);
                lines.add("SLOT " + mid(x.getId()) + " " + y + " " + r + " " + kind);
            }
        }
        Collections.sort(lines);
        return lines;
    }

    // ======== Run E's handle state (bergdb item 009, step 4c) ========

    int handleLines = 0;

    /** Run E's handles, numbered in the order the exporter first meets them, so that a handle
     *  has the same number in every state of run E (the checker's C-H: a dead handle is never
     *  live again). */
    final Map<Handle, Integer> handleNumbers = new IdentityHashMap<Handle, Integer>();

    int handleNumber(Handle h) {
        Integer k = handleNumbers.get(h);
        if (k == null) handleNumbers.put(h, k = handleNumbers.size() + 1);
        return k;
    }

    /** A state's handles and objects, in the order the exporter meets them (handleState). */
    static final class HState {
        final List<Handle> handles = new ArrayList<Handle>();
        final Set<Handle> seen = Collections.newSetFromMap(new IdentityHashMap<Handle, Boolean>());
        final List<Node> objects = new ArrayList<Node>();
        final Map<Node, Integer> numbers = new IdentityHashMap<Node, Integer>();

        /** Handle h, and the object it holds. */
        void handle(Handle h) {
            if (!seen.add(h)) return;
            handles.add(h);
            object(h.obj);
        }

        /** Object o, numbered from 1 in its state. */
        void object(Node o) {
            if (o == null || numbers.containsKey(o)) return;
            numbers.put(o, objects.size() + 1);
            objects.add(o);
        }
    }

    /**
     * The handle lines of run E's state now, between transactions, after record rec (the
     * class comment): the node table's entries and handles, the super root and D's objects,
     * and, through the pointers of the objects to index nodes, the handles they hold, live or
     * dead, and the objects of those. started: the last record that the state's startup read.
     * The caller holds the write lock.
     */
    List<String> handleState(Db db, Rec rec, int started) {
        Db.Internal in = db.internal();
        String context = "the handle state after R(" + rec.index + ")";
        HState st = new HState();
        List<String> tableLines = new ArrayList<String>();
        for (Map.Entry<Long, Handle> e : in.cache().entries()) {
            tableLines.add("HTABLE " + mid(e.getKey()) + " " + handleNumber(e.getValue()));
            st.handle(e.getValue());
        }
        st.object(in.superRoot());
        final List<Node> dObjects = new ArrayList<Node>();
        in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                dObjects.add(node);
            }
        });
        for (Node x : dObjects) st.object(x);
        for (int j = 0; j < st.objects.size(); j++) {
            Node x = st.objects.get(j);
            if (!x.isIndexNode()) continue;
            int size = x.getSize();
            for (int i = 0; i < size; i++) {
                if (!NodeCollection.pointsToIndexNode(x, i)) continue;
                Pointee p = x.getPointee(i);
                if (p instanceof Handle) st.handle((Handle) p);
            }
        }

        // The stream's first record: the first that starts at or after its first position (a
        // cut by reclaim; R(0) without one).
        long firstPos = in.nodeStream().getFirstPos();
        int first = 0;
        for (Rec r : recs) {
            if (r.tpos >= firstPos) {
                first = r.index;
                break;
            }
        }
        List<String> lines = new ArrayList<String>();
        lines.add("HMEM " + started + " " + first);
        Collections.sort(tableLines);
        lines.addAll(tableLines);
        for (Handle h : st.handles) {
            Node o = h.obj;
            byte s = h.state();
            lines.add("HANDLE " + handleNumber(h) + " " + mid(h.id) + " "
                    + (s == Handle.LIVE ? "live" : s == Handle.LOADING ? "loading" : "dead") + " "
                    + (o == null ? "-" : "" + st.numbers.get(o)) + " "
                    + recordOrNone(h.writtenPos, context));
        }
        for (Node x : st.objects) {
            if (!x.isIndexNode()) {
                error("an object of node " + mid(x.getId()) + " that is not an index node ("
                        + context + ")");
                continue;
            }
            List<Ent> h = objectEntries(x, in.nodeStream(), false, "object of node "
                    + mid(x.getId()) + ", " + context);
            lines.add("HOBJ " + st.numbers.get(x) + " " + mid(x.getId()) + " "
                    + (x.isCanonical() ? "canon" : "snap") + " "
                    + recordOrNone(x.getSpos(), context) + " " + h.size() + " "
                    + Long.toUnsignedString(historyHash(h)));
        }
        for (Node x : st.objects) {
            if (!x.isIndexNode()) continue;
            int size = x.getSize();
            for (int i = 0; i < size; i++) {
                if (!NodeCollection.pointsToIndexNode(x, i)) continue;
                Pointee p = x.getPointee(i);
                long pos = x.getPointerPos(i);
                if (p == null && pos == Spos.NULL) continue;    // an unused skip pointer
                String where = "pointer " + i + " of node " + mid(x.getId()) + ", " + context;
                long y;
                if (Spos.isVpos(pos)) {
                    y = mid(pos);
                } else if (Spos.isValid(pos) && verByPos.containsKey(pos)) {
                    y = verByPos.get(pos)[1];
                } else {
                    error("stream position " + pos + " is not the start of a known version ("
                            + where + ")");
                    continue;
                }
                lines.add("HPTR " + st.numbers.get(x) + " " + y + " " + recordOrNone(pos, where)
                        + " " + (p instanceof Handle ? "" + handleNumber((Handle) p) : "-"));
            }
        }
        return lines;
    }

    /** The record of the version at stream position pos, or - for a vpos or none. */
    String recordOrNone(long pos, String context) {
        return Spos.isValid(pos) && !Spos.isVpos(pos) ? recordOfPos(pos, context) : "-";
    }

    /** The first position at which two streams differ, from the later first position of the
     *  two (after a cut by reclaim); -1 if they are the same. As RestartInvariance.firstDiff. */
    static long firstDiff(AppendOnlyStream s1, AppendOnlyStream s2) {
        long len = Math.min(s1.getLength(), s2.getLength());
        byte[] b1 = new byte[65536], b2 = new byte[65536];
        long from = Math.max(s1.getFirstPos(), s2.getFirstPos());
        try {
            for (long pos = from; pos < len; pos += b1.length) {
                int chunk = (int) Math.min(b1.length, len - pos);
                s1.read(pos, b1, 0, chunk);
                s2.read(pos, b2, 0, chunk);
                for (int i = 0; i < chunk; i++) {
                    if (b1[i] != b2[i]) return pos + i;
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return s1.getLength() == s2.getLength() ? -1 : len;
    }

    /** M4 (docs, 7.1): after T(i), no written node holds a stream pointer to a node in D. */
    void checkM4(Db db, Rec rec) {
        Set<Long> inD = new HashSet<Long>();
        for (long[] p : rec.dirty) inD.add(p[0]);
        NodeStream ns = db.internal().nodeStream();
        for (Ver v : rec.vers) {
            if (!"I".equals(v.kind)) continue;
            Node x = db.internal().cache().getNode(v.id - 1);
            if (x == null) continue;
            for (int j = 0; j < x.getSize(); j++) {
                if (x.getPointerNode(j) != null) continue;
                long pos = x.getPointerPos(j);
                if (pos == Spos.NULL || Spos.isVpos(pos) || pos < 0) continue;
                if (x instanceof KeyNode && Klong.getIntType(((KeyNode) x).klongs[j]) != Klong.INT_TYPE_KEY) {
                    continue;
                }
                long[] tv = verByPos.get(pos);      // not read: with reclaim it can be below the cut
                long y = tv != null ? tv[1] : mid(ns.readNodeHeader(pos).id());
                if (inD.contains(y)) {
                    rec.probes.add("PROBE " + rec.index + " fail M4: node " + v.id
                            + " holds a stream pointer to node " + y + ", which is in D");
                }
            }
        }
    }

    String lookupProblem(Db db, TreeMap<String, TreeMap<Long, byte[]>> history, int i) {
        return lookupProblem(db, history, i, history.size(), 200, new Random(seed * 31 + i));
    }

    /**
     * Lookups after user transaction i: each of the first 'latest' keys at the latest time,
     * then 'random' random keys at random times up to the transaction's; null if each gives
     * the workload's value.
     */
    String lookupProblem(Db db, TreeMap<String, TreeMap<Long, byte[]>> history, int i, int latest,
            int random, Random rnd) {
        final long fa = db.getFirstAvailableLookupTime();
        List<String> ks = new ArrayList<String>(history.keySet());
        if (ks.isEmpty()) return null;
        int bad = 0;
        String first = null;
        for (int j = 0; j < latest + random; j++) {
            String k = j < latest ? ks.get(j) : ks.get(rnd.nextInt(ks.size()));
            long t = j < latest ? Long.MAX_VALUE : times[rnd.nextInt(i + 1)] - rnd.nextInt(2);
            t = Math.max(t, fa);    // with reclaim, from the first available time on
            Map.Entry<Long, byte[]> e = history.get(k).floorEntry(t);
            byte[] expected = e == null ? null : e.getValue();
            try {
                byte[] actual = DbUtil.get(db, t, k);
                if (!Arrays.equals(expected, actual)) {
                    bad++;
                    if (first == null) first = "get(" + k + ", " + t + ") is wrong";
                }
            } catch (RuntimeException ex) {
                bad++;
                if (first == null) first = "get(" + k + ", " + t + ") failed: " + oneLine(ex);
            }
        }
        return bad == 0 ? null : bad + " bad lookups, first: " + first;
    }

    static String oneLine(Throwable e) {
        return String.valueOf(e).replace('\n', ' ');
    }

    // ======== Levels (docs, 8.4) ========

    final Map<Long, Integer> segment = new HashMap<Long, Integer>();
    final List<Long> unreached = new ArrayList<Long>();
    final Map<Long, Integer> height = new HashMap<Long, Integer>();

    long[] levels() {
        // Segments, from the root key nodes of the top nodes, through all pointers.
        Deque<KeyNode> todo = new ArrayDeque<KeyNode>();
        for (TopNode tn : topNodes) {
            KeyNode root = (KeyNode) tn.getPointerNode(0);
            if (root != null && !segment.containsKey(mid(root.getId()))) {
                segment.put(mid(root.getId()), 0);
                todo.add(root);
            }
        }
        while (!todo.isEmpty()) {
            KeyNode k = todo.poll();
            int g = segment.get(mid(k.getId()));
            for (int i = 0; i < k.size; i++) {
                if (Klong.getIntType(k.klongs[i]) != Klong.INT_TYPE_KEY) continue;
                Node c = k.getPointerNode(i);
                if (!(c instanceof KeyNode)) continue;
                int gc = k.isSegmentLeaf() ? g + 1 : g;
                Integer old = segment.get(mid(c.getId()));
                if (old == null) {
                    segment.put(mid(c.getId()), gc);
                    todo.add((KeyNode) c);
                } else if (old != gc) {
                    error("key node " + mid(c.getId()) + " in segments " + old + " and " + gc);
                }
            }
        }
        int maxG = 0, maxH = 0;
        for (PNode pn : nodes.values()) {
            if (pn.obj instanceof KeyNode) {
                if (!segment.containsKey(pn.id)) {
                    // A node that a later key of its transaction replaced (M1): the checker
                    // reports it as an A3 failure. Its level: as if in the first segment.
                    unreached.add(pn.id);
                    segment.put(pn.id, 0);
                }
                maxG = Math.max(maxG, segment.get(pn.id));
                maxH = Math.max(maxH, heightOf((KeyNode) pn.obj));
            }
        }
        long maxTop = 0;
        for (TopNode tn : topNodes) maxTop = Math.max(maxTop, tn.topNodeId);
        long keyMax = 1 + (long) maxG * (maxH + 1) + maxH;
        return new long[] {maxG, maxH, keyMax, maxTop};
    }

    int heightOf(KeyNode k) {
        Integer h = height.get(mid(k.getId()));
        if (h != null) return h;
        int result = 0;
        if (!k.isSegmentLeaf()) {
            int lo = Integer.MAX_VALUE, hi = -1;
            for (int i = 0; i < k.size; i++) {
                if (Klong.getIntType(k.klongs[i]) != Klong.INT_TYPE_KEY) continue;
                Node c = k.getPointerNode(i);
                if (!(c instanceof KeyNode)) continue;
                int hc = heightOf((KeyNode) c);
                lo = Math.min(lo, hc);
                hi = Math.max(hi, hc);
            }
            if (hi >= 0 && lo != hi) error("children of key node " + mid(k.getId()) + " at heights " + lo
                    + " to " + hi);
            result = hi + 1;
        }
        height.put(mid(k.getId()), result);
        return result;
    }

    long levelOf(PNode pn, long[] bounds) {
        long maxG = bounds[0], maxH = bounds[1], keyMax = bounds[2];
        if (pn.obj == null) return keyMax + 2 + TopNode.MAX_TOP_NODE_ID_VALUE;
        if (pn.obj instanceof TopNode) return keyMax + 1 + ((TopNode) pn.obj).topNodeId;
        if (pn.obj instanceof KeyNode) {
            return 1 + (maxG - segment.get(pn.id)) * (maxH + 1) + height.get(pn.id);
        }
        return 0;
    }

    // ======== Output ========

    void write(String file) throws IOException {
        long[] bounds = levels();
        PrintWriter out = new PrintWriter(new OutputStreamWriter(new FileOutputStream(file), "UTF-8"));
        out.println(tree ? "TRACE 3" : "TRACE 2");
        out.println("CONFIG seed=" + seed + " n=" + n + " keys=" + keyCount + " maxnode=" + maxNode
                + " sd=" + startupDistance + " ops=" + ops + " exact=" + exact + " bulk=" + bulk
                + " del=" + del + " nodel=" + nodel + " empty=" + empty + " long=" + longKeys
                + " valsize=" + valsize + " probe=" + probe + " live=" + live
                + (shape.isEmpty() ? "" : " shape=" + shape)
                + " segments=" + (bounds[0] + 1) + " height=" + bounds[1]
                + (retain > 0 ? " retain=" + retain : ""));
        if (tree) {
            KeyNode first = topNodes.isEmpty() ? null : (KeyNode) topNodes.get(0).getPointerNode(0);
            out.println("TREE " + maxNode + " " + bounds[0] + " " + bounds[1] + " "
                    + (first == null ? -1 : mid(first.getId()))
                    // the writer's thresholds of format 7 (bergdb 024-21; 024-22, J2 and J9):
                    // m, c and rule O's h; m is 1 below node size 8, where nothing merges;
                    // and option 2's theta (bergdb 024-23), 0 below node size 8
                    + " " + Dag.minFill(maxNode) + " " + Dag.mergeCap(maxNode) + " "
                    + Dag.splitAbove(maxNode) + " " + Dag.theta(maxNode));
        }
        for (String e : errors) out.println("ERROR " + e);
        if (!unreached.isEmpty()) {
            out.println("# key nodes that no top node reaches (A3 failures, M1): " + unreached.size());
        }
        for (Rec rec : recs) {
            out.println("TX " + rec.index);
            out.println("# tt=" + rec.tt + " tpos=" + rec.tpos + " puts=" + rec.puts + " deletes="
                    + rec.deletes + (retain > 0 ? " kind=" + rec.kind : ""));
            for (String s : rec.treeHead) out.println(s);
            for (long id : rec.newNodes) {
                PNode pn = nodes.get(id);
                out.println("NEW " + id + " " + levelOf(pn, bounds) + " " + (pn.isData() ? "D" : "I"));
            }
            for (int j = 0; j < rec.adds.size(); j++) {
                out.println("ADD " + rec.addsNode.get(j)[0] + " " + rec.adds.get(j));
            }
            for (String s : rec.treeLines) out.println(s);
            if (rec.touch != null) {
                StringBuilder tl = new StringBuilder("TOUCH");
                for (long x : rec.touch) tl.append(" ").append(x);
                out.println(tl);
            }
            out.println("REC " + rec.index + " " + rec.sp + " " + (rec.top < 0 ? "-" : "" + rec.top)
                    + " " + rec.topSrc + (rec.top < 0 || rec.topNode < 0 ? "" : " " + rec.topNode));
            for (Ver v : rec.vers) {
                out.println("VER " + v.id + " " + v.kind);
                for (Ent e : v.hist) out.println("H " + e);
                for (int[] st : v.skipTimes) out.println("SKIPT " + st[0] + " " + st[1]);
                for (Map.Entry<Long, Integer> f : v.refs.entrySet()) {
                    out.println("F " + f.getKey() + " " + f.getValue());
                }
            }
            StringBuilder gd = new StringBuilder("GD");
            for (long x : rec.gd) gd.append(" ").append(x);
            out.println(gd);
            StringBuilder dl = new StringBuilder("DIRTY");
            for (long[] p : rec.dirty) dl.append(" ").append(p[0]).append(" ").append(p[1]);
            out.println(dl);
            for (String s : rec.reclaimLines) out.println(s);
            for (String s : rec.live) out.println(s);
            for (String s : rec.probes) out.println(s);
            for (String s : rec.firsts) out.println(s);
            for (String s : rec.slots) out.println(s);
            for (String s : rec.handles) out.println(s);
            out.println("END " + rec.index);
        }
        out.println("DONE " + (recs.size() - 1));
        out.close();
    }

    /** The Dag's counters of this JVM, in one line (see the class comment). */
    static String dagCounters() {
        return "Dag counters: unlinked " + bergdb.dag.Dag.statUnlinked + ", taken back "
                + bergdb.dag.Dag.statTakenBack + ", roots taken back "
                + bergdb.dag.Dag.statRootsTakenBack + ", collapses " + bergdb.dag.Dag.statCollapses
                + ", empty keys pointed to the next child " + bergdb.dag.Dag.statRelabels;
    }

    public static void main(String[] args) throws IOException {
        if (args.length != 2) {
            System.out.println("Usage: TraceExport seed out.trace (properties: see the class comment)");
            System.exit(2);
        }
        TraceExport x = new TraceExport(Long.parseLong(args[0]));
        AppendOnlyStream a = x.runA();
        if (x.probe > 0) x.runB(a);
        if (!x.runE.isEmpty()) x.runE(a);
        x.write(args[1]);
        int probeFails = 0;
        for (Rec r : x.recs) for (String s : r.probes) if (s.contains(" fail ")) probeFails++;
        String rc = "";
        if (x.retain > 0) {
            int cuts = 0, phys = 0, steps = 0, tables = 0;
            for (Rec r : x.recs) {
                for (String s : r.reclaimLines) {
                    if (s.startsWith("CUT ")) cuts++;
                    if (s.startsWith("PHYSCUT ")) phys++;
                }
                if ("step".equals(r.kind)) steps++;
                if ("table".equals(r.kind)) tables++;
            }
            rc = " (" + (x.recs.size() - 1) + " records: " + steps + " steps, " + tables
                    + " table stores; " + cuts + " cuts decided, " + phys + " physical; "
                    + x.refsBelowCut + " references to versions before a cut)";
        }
        String re = x.runE.isEmpty() ? "" : " (run E: " + x.slotLines + " SLOT lines, "
                + x.handleLines + " handle lines, " + x.evictionSummary + ")";
        System.out.println("TraceExport seed=" + x.seed + " n=" + x.n + rc + re + ": "
                + x.nodes.size() + " nodes, " + x.errors.size() + " errors, " + probeFails
                + " probe failures; " + args[1]);
        System.out.println(dagCounters());
        if (Audit.EVERY > 0) System.out.println(Audit.summary());   // -Daudit=N (WP J1)
    }
}
