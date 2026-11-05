package bergdb.core;

import java.io.EOFException;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Locale;
import java.util.Random;

import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.stream.AppendOnlyStream;

/**
 * The node-size study of bergdb 005-38: WriteBench (the same load, the same report line,
 * so the byte counts are the same) and, besides:
 *
 * - each window: the written key nodes by segment of the key (s0 the first 7 bytes, s3 the
 *   last segment of a 24-byte key, whose leaves point to values) and height in that
 *   segment's tree (h0 a segment leaf): writes a put, bytes a node, klongs, TIME klongs and
 *   live keys (distinct compare values) a node;
 * - after the load: D (TransSeq's got-dirty nodes: count, stream bytes, memory estimate);
 *   heap bytes a key after full GCs (wb.heap); the current version of the tree by segment
 *   and height: nodes, klongs, live keys, array capacity (wb.tree); all key nodes reachable
 *   from the super root through any pointer, old versions included (wb.reach);
 * - an optional phase of wb.updates random puts to loaded keys (uniform, with replacement,
 *   SplittableRandom(2): the update phase of the coordinator's wb/WriteBench.java, so that
 *   the two tools give the same bytes at node 30), reported as the load is;
 * - each window also: the startup lag (stream end minus startup position) and D.
 *
 * Usage: as WriteBench, plus -Dwb.updates=N -Dwb.heap=true|false -Dwb.tree=true|false
 *        -Dwb.reach=true|false; java -cp cls:bergdb.jar bergdb.core.NodeSizeBench
 */
public class NodeSizeBench {
    static String prop(String n, String d) { return System.getProperty("wb." + n, d); }

    final int keys = Integer.parseInt(prop("keys", "1000000"));
    final String keytype = prop("keytype", "key24");
    final String order = prop("order", "random");
    final int sd = Integer.parseInt(prop("sd", "50000000"));
    final int tx = Integer.parseInt(prop("tx", "1000"));
    final int nodeSize = Integer.parseInt(prop("node", "30"));
    final int window = Integer.parseInt(prop("window", "1000000"));
    final long ring = Long.parseLong(prop("ring", "536870912"));
    final long updates = Long.parseLong(prop("updates", "0"));
    final boolean heap = Boolean.parseBoolean(prop("heap", "true"));
    final boolean tree = Boolean.parseBoolean(prop("tree", "true"));
    final boolean reach = Boolean.parseBoolean(prop("reach", "false"));
    final boolean trackReplaced = Boolean.parseBoolean(prop("replaced", "false"));

    static final int KEY_BYTES = 24;
    static final int NSEG = (KEY_BYTES + Klong.MAX_SIZE) / Klong.MAX_SIZE;   // 4

    /** Keeps the last 'ring' bytes. */
    static final class RingStream implements AppendOnlyStream {
        final byte[] buf;
        long length;
        RingStream(long size) { buf = new byte[(int) size]; }
        public long getLength() { return length; }
        public long getFirstPos() { return 0; }
        public synchronized void read(long p, byte[] d, int o, int n) throws IOException {
            if (p + n > length) throw new EOFException("read past end " + p);
            if (p < length - buf.length) throw new IOException("read before the ring: " + p + ", length " + length);
            for (int i = 0; i < n; i++) d[o + i] = buf[(int) ((p + i) % buf.length)];
        }
        public synchronized void append(byte[] s, int o, int n) {
            int at = (int) (length % buf.length);
            int first = Math.min(n, buf.length - at);
            System.arraycopy(s, o, buf, at, first);
            if (first < n) System.arraycopy(s, o + first, buf, 0, n - first);
            length += n;
        }
        public void pretruncate(long p) {}
        public void seekFirstPos(long p) {}
        public void close() {}
    }

    // WriteBench's kinds, for its report line: 0 value leaf, 1 link leaf, 2 + h inner node.
    static final int KINDS = 10;
    static final String[] KIND_NAMES = {"vleaf", "lleaf", "", "in1", "in2", "in3", "in4", "in5", "in6", "in7+"};

    // This tool's classes: segment s (0..NSEG-1) and height h (0..7): s * 8 + h; UNKNOWN last.
    static final int CLASSES = NSEG * 8 + 1;
    static final int UNKNOWN = NSEG * 8;

    static String className(int c) {
        return c == UNKNOWN ? "unk" : "s" + (c / 8) + "h" + (c % 8);
    }

    static final class Window {
        long puts, records, recordBytes, valueBytes, topBytes, topNodes, gotDirty, stillDirty, keyNodes;
        long streamStart, streamEnd;
        final long[] kindBytes = new long[KINDS], kindNodes = new long[KINDS], kindKlongs = new long[KINDS];
        final long[] cNodes = new long[CLASSES], cBytes = new long[CLASSES], cKlongs = new long[CLASSES],
                cTime = new long[CLASSES], cLive = new long[CLASSES], cOld = new long[CLASSES], cStill = new long[CLASSES],
                cOldStill = new long[CLASSES];
        final HashSet<Long> distinct = new HashSet<Long>();
    }

    final CoreTestClock clock = new CoreTestClock();
    long time = bergdb.pub.util.Clock.UNITS_PER_SEC;
    Window w = new Window();
    RingStream stream;
    Db db;
    final long[] scratch = new long[256];
    long lastStartupPos;
    /** Key nodes that a transaction replaced (no longer current), with wb.replaced. */
    final java.util.Set<Node> replaced = java.util.Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());

    static Node firstChild(KeyNode k) {
        int sz = k.size;
        for (int i = 0; i < sz; i++) {
            Node c = k.getPointerNode(i);
            if (c != null) return c;
        }
        return null;
    }

    static int kind(KeyNode k) {
        if (k.isSegmentLeaf()) {
            for (int i = 0; i < k.size; i++) {
                Node c = k.getPointerNode(i);
                if (c != null) return c instanceof ValueNode ? 0 : 1;
            }
            return 0;
        }
        int h = 0;
        Node n = k;
        while (n instanceof KeyNode && !((KeyNode) n).isSegmentLeaf()) {
            KeyNode kn = (KeyNode) n;
            Node c = null;
            for (int i = 0; i < kn.size && c == null; i++) c = kn.getPointerNode(i);
            if (c == null) break;
            n = c;
            h++;
        }
        return Math.min(KINDS - 1, 2 + Math.max(1, h));
    }

    /** Segment (from the key's start) and height, from the node's first children down. */
    static int classify(KeyNode k) {
        int h = 0;
        KeyNode n = k;
        while (!n.isSegmentLeaf()) {
            Node c = firstChild(n);
            if (!(c instanceof KeyNode)) return UNKNOWN;
            n = (KeyNode) c;
            if (++h > 40) return UNKNOWN;
        }
        int fromBottom = 0;
        while (true) {
            Node c = firstChild(n);
            if (c == null) return UNKNOWN;
            if (c instanceof ValueNode) break;
            if (!(c instanceof KeyNode)) return UNKNOWN;
            KeyNode m = (KeyNode) c;
            int guard = 0;
            while (!m.isSegmentLeaf()) {
                Node d = firstChild(m);
                if (!(d instanceof KeyNode) || ++guard > 40) return UNKNOWN;
                m = (KeyNode) d;
            }
            n = m;
            if (++fromBottom >= NSEG) return UNKNOWN;
        }
        int s = NSEG - 1 - fromBottom;
        return s * 8 + Math.min(7, h);
    }

    /** {TIME klongs, live keys} of a node: live keys are its distinct compare values. */
    int[] timeAndLive(KeyNode k, int[] out) {
        int sz = k.size;
        long[] kl = k.klongs;
        int t = 0, m = 0;
        for (int i = 0; i < sz; i++) {
            long x = kl[i];
            int type = Klong.getIntType(x);
            if (type == Klong.INT_TYPE_TIME) t++;
            else if (type == Klong.INT_TYPE_KEY) scratch[m++] = Klong.getCompareValue(x);
        }
        Arrays.sort(scratch, 0, m);
        int live = 0;
        for (int i = 0; i < m; i++) if (i == 0 || scratch[i] != scratch[i - 1]) live++;
        out[0] = t;
        out[1] = live;
        return out;
    }

    final int[] tl = new int[2];

    void recordWritten(Db.ExecuteData x) {
        TransNodes n = x.transNodes;
        lastStartupPos = x.startupPos.get();
        w.records++;
        w.recordBytes += x.trans.nextPos - x.trans.tpos;
        for (int i = 0; i < n.valueCount; i++) w.valueBytes += StoredValueNode.getByteSize(n.valueNodes[i], n.keys[i]);
        for (int i = 0; i < n.topCount; i++) {
            TopNode t = n.topNodes[i];
            w.topBytes += StoredTopNode.getByteSize(t);
            w.topNodes++;
            if (t.isDirty()) w.stillDirty++;
            w.distinct.add(t.getId());
        }
        for (int i = 0; i < n.keyCount; i++) {
            KeyNode k = n.keyNodes[i];
            int kd = kind(k);
            int bytes = StoredKeyNode.getByteSize(k);
            w.kindBytes[kd] += bytes;
            w.kindNodes[kd]++;
            w.kindKlongs[kd] += k.size;
            w.keyNodes++;
            if (k.isDirty()) w.stillDirty++;
            w.distinct.add(k.getId());
            int c = classify(k);
            timeAndLive(k, tl);
            w.cNodes[c]++;
            w.cBytes[c] += bytes;
            w.cKlongs[c] += k.size;
            w.cTime[c] += tl[0];
            w.cLive[c] += tl[1];
            if (k.isDirty()) w.cStill[c]++;
            if (trackReplaced && replaced.contains(k)) {
                w.cOld[c]++;
                if (k.isDirty()) w.cOldStill[c]++;
            }
        }
        w.gotDirty += x.transInfo.gotDirtyNodes.size();
    }

    byte[] key(int k) {
        byte[] b = new byte[KEY_BYTES];
        if (keytype.equals("key24")) {
            System.arraycopy("/scale/key/".getBytes(StandardCharsets.US_ASCII), 0, b, 0, 11);
            long v = k;
            for (int i = 23; i >= 11; i--) { b[i] = (byte) ('0' + v % 10); v /= 10; }
        } else if (keytype.equals("rnd24")) {
            long h = mix(k), h2 = mix(h);
            for (int i = 0; i < 8; i++) { b[i] = (byte) (h >>> (56 - 8 * i)); b[8 + i] = (byte) (h2 >>> (56 - 8 * i)); }
            for (int i = 0; i < 8; i++) b[16 + i] = (byte) ((long) k >>> (56 - 8 * i));
        } else throw new IllegalArgumentException(keytype);
        return b;
    }

    static long mix(long z) {
        z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9L;
        z = (z ^ (z >>> 27)) * 0x94d049bb133111ebL;
        return z ^ (z >>> 31);
    }

    void report(String phase, Window w, long putsSoFar) {
        long stream = w.streamEnd - w.streamStart;
        double p = w.puts;
        long keyBytes = 0;
        for (long b : w.kindBytes) keyBytes += b;
        long dirtyList = 16 * w.gotDirty;
        long otherRec = w.recordBytes - w.valueBytes - keyBytes - w.topBytes - dirtyList;
        StringBuilder s = new StringBuilder();
        if (!phase.isEmpty()) s.append(phase).append(' ');
        s.append(String.format(Locale.ROOT, "%d keys: B/put %.0f = value %.0f + key nodes %.0f + top %.0f + dirty list %.0f + rec other %.0f + meta %.0f;",
                putsSoFar, stream / p, w.valueBytes / p, keyBytes / p, w.topBytes / p, dirtyList / p, otherRec / p,
                (stream - w.recordBytes) / p));
        s.append(" nodes/put");
        for (int k = 0; k < KINDS; k++) {
            if (w.kindNodes[k] == 0) continue;
            s.append(String.format(Locale.ROOT, " %s %.3f (%.0f B, %.1f kl)", KIND_NAMES[k], w.kindNodes[k] / p,
                    (double) w.kindBytes[k] / w.kindNodes[k], (double) w.kindKlongs[k] / w.kindNodes[k]));
        }
        s.append(String.format(Locale.ROOT, " top %.3f; still dirty %.3f/put; writes/distinct %.2f; records %d",
                w.topNodes / p, w.stillDirty / p, (double) (w.keyNodes + w.topNodes) / Math.max(1, w.distinct.size()), w.records));
        final long[] d = new long[2];
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                d[0]++;
                d[1] += node instanceof KeyNode ? StoredKeyNode.getByteSize((KeyNode) node) : StoredTopNode.getByteSize((TopNode) node);
            }
        });
        long end = db.internal().nodeStream().getNextPos();
        s.append(String.format(Locale.ROOT, "; startup lag %.0f MB; D %d nodes, %.0f MB",
                (end - lastStartupPos) / 1e6, d[0], d[1] / 1e6));
        System.out.println(s);
        // The classes: writes a put, bytes, klongs, TIME klongs and live keys a node.
        StringBuilder c = new StringBuilder("  classes:");
        for (int k = 0; k < CLASSES; k++) {
            if (w.cNodes[k] == 0) continue;
            double nn = w.cNodes[k];
            c.append(String.format(Locale.ROOT, " %s %.4f/put %.0fB %.1fkl %.1ft %.1flive", className(k), nn / p,
                    w.cBytes[k] / nn, w.cKlongs[k] / nn, w.cTime[k] / nn, w.cLive[k] / nn));
            c.append(String.format(Locale.ROOT, " %.2fstill", w.cStill[k] / nn));
            if (trackReplaced) c.append(String.format(Locale.ROOT, " %.2fold %.2foldstill", w.cOld[k] / nn, w.cOldStill[k] / nn));
            c.append(';');
        }
        System.out.println(c);
        System.out.flush();
    }

    static long usedAfterGc() {
        Runtime rt = Runtime.getRuntime();
        for (int i = 0; i < 4; i++) System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }

    void printD() {
        final long[] d = new long[6];   // nodes, key nodes, top nodes, stream bytes, mem bytes, still marked dirty
        final long[] dc = new long[CLASSES];
        final long[] dcb = new long[CLASSES];
        TransSeq seq = db.internal().transSeq();
        seq.visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                d[0]++;
                if (node.isDirty()) d[5]++;
                if (node instanceof KeyNode) {
                    KeyNode k = (KeyNode) node;
                    d[1]++;
                    int b = StoredKeyNode.getByteSize(k);
                    d[3] += b;
                    d[4] += k.getMemSize();
                    int c = classify(k);
                    dc[c]++;
                    dcb[c] += b;
                } else if (node instanceof TopNode) {
                    d[2]++;
                    d[3] += StoredTopNode.getByteSize((TopNode) node);
                }
            }
        });
        StringBuilder s = new StringBuilder();
        s.append(String.format(Locale.ROOT, "D: %d transactions, %d nodes (%d key, %d top, %d marked dirty), %d stream bytes (%.1f MB), memory estimate %d bytes (%.1f MB, KeyNode.getMemSize)",
                seq.getSize(), d[0], d[1], d[2], d[5], d[3], d[3] / 1e6, d[4], d[4] / 1e6));
        System.out.println(s);
        StringBuilder t = new StringBuilder("  D classes:");
        for (int k = 0; k < CLASSES; k++) {
            if (dc[k] == 0) continue;
            t.append(String.format(Locale.ROOT, " %s %d (%.1f MB);", className(k), dc[k], dcb[k] / 1e6));
        }
        System.out.println(t);
    }

    void printTree() {
        TopNode top = db.internal().superRoot();
        KeyNode root = (KeyNode) top.getPointerNode(0);
        final long[] n = new long[CLASSES], kl = new long[CLASSES], live = new long[CLASSES], cap = new long[CLASSES],
                mem = new long[CLASSES], bytes = new long[CLASSES];
        long values = 0, nodes = 0, missing = 0;
        int maxDepth = 0;
        ArrayDeque<KeyNode> q = new ArrayDeque<KeyNode>();
        ArrayDeque<Integer> depth = new ArrayDeque<Integer>();
        q.add(root);
        depth.add(1);
        IdentityHashMap<KeyNode, Boolean> seen = new IdentityHashMap<KeyNode, Boolean>();
        while (!q.isEmpty()) {
            KeyNode k = q.poll();
            int dep = depth.poll();
            if (seen.put(k, Boolean.TRUE) != null) continue;
            nodes++;
            maxDepth = Math.max(maxDepth, dep);
            int c = classify(k);
            KeyNode last = k.lastVersion(Klong.MAX_TIME);
            int lv = 0;
            for (int i = 0; i < last.size; i++) {
                if (Klong.getIntType(last.klongs[i]) != Klong.INT_TYPE_KEY) continue;
                lv++;
                Node ch = last.getPointerNode(i);
                if (ch instanceof KeyNode) { q.add((KeyNode) ch); depth.add(dep + 1); }
                else if (ch instanceof ValueNode) values++;
                else if (ch == null) missing++;
            }
            n[c]++;
            kl[c] += k.size;
            live[c] += lv;
            cap[c] += k.klongs.length;
            mem[c] += k.getMemSize();
            bytes[c] += StoredKeyNode.getByteSize(k);
        }
        System.out.println(String.format(Locale.ROOT, "tree: %d current key nodes, %d values, %.2f key nodes a key, longest path %d key nodes (all segments), %d children not in memory",
                nodes, values, (double) nodes / keys, maxDepth, missing));
        for (int c = 0; c < CLASSES; c++) {
            if (n[c] == 0) continue;
            double nn = n[c];
            System.out.println(String.format(Locale.ROOT, "  tree %s: %d nodes, %.1f klongs, %.1f live keys, %.1f capacity, %.0f B on stream, %.0f B mem est. (a node); fill %.2f of %d",
                    className(c), n[c], kl[c] / nn, live[c] / nn, cap[c] / nn, bytes[c] / nn, mem[c] / nn, kl[c] / nn / nodeSize, nodeSize));
        }
    }

    /** All nodes reachable from the super root through any pointer: old versions included. */
    void printReach() {
        TopNode top = db.internal().superRoot();
        IdentityHashMap<Node, Boolean> seen = new IdentityHashMap<Node, Boolean>();
        ArrayDeque<Node> q = new ArrayDeque<Node>();
        q.add(top);
        long keyNodes = 0, topNodes = 0, valueNodes = 0, keyMem = 0;
        while (!q.isEmpty()) {
            Node x = q.poll();
            if (seen.put(x, Boolean.TRUE) != null) continue;
            if (x instanceof TopNode) topNodes++;
            if (x instanceof KeyNode) { keyNodes++; keyMem += ((KeyNode) x).getMemSize(); }
            int sz = x.getSize();
            for (int i = 0; i < sz; i++) {
                Node c = x.getPointerNode(i);
                if (c instanceof ValueNode) valueNodes++;       // pointers to values, not values
                else if (c != null) q.add(c);
            }
        }
        System.out.println(String.format(Locale.ROOT, "reach: %d key nodes (%.2f a key, mem est. %.1f B a key), %d top nodes, %d pointers to values, reachable through any pointer",
                keyNodes, (double) keyNodes / keys, (double) keyMem / keys, topNodes, valueNodes));
    }

    void put(int[] ord, int from, int to, byte[] value) {
        Trans.Builder tb = db.trans();
        for (int j = from; j < to; j++) {
            int k = ord[j];
            value[0] = (byte) (k >>> 24); value[1] = (byte) (k >>> 16); value[2] = (byte) (k >>> 8); value[3] = (byte) k;
            tb.put(key(k), value.clone());
        }
        time += bergdb.pub.util.Clock.UNITS_PER_SEC / 10000;
        clock.setTime(time);
        db.execute(tb.build());
    }

    void run() throws Exception {
        stream = new RingStream(ring);
        clock.setTime(time);
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).testId().noEvict();
        if (nodeSize == 8) b.maxNodeSize8();
        else if (nodeSize == 14) b.maxNodeSize14();
        else if (nodeSize == 30) b.maxNodeSize30();
        else if (nodeSize == 62) b.maxNodeSize62();
        else throw new IllegalArgumentException("node " + nodeSize);
        b.startupDistance(sd);
        db = b.build();
        db.start();
        int[] ord = new int[keys];
        for (int i = 0; i < keys; i++) ord[i] = i;
        if (order.equals("random")) {
            Random rnd = new Random(1);
            for (int i = keys - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        } else if (!order.equals("seq")) throw new IllegalArgumentException(order);
        long heap0 = heap ? usedAfterGc() : 0;
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) { recordWritten(x); }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) { if (trackReplaced) replaced.add(node); }
        };
        System.out.println(String.format(Locale.ROOT, "NodeSizeBench: %d keys %s %s, sd %d, tx %d, node %d, ring %d, updates %d",
                keys, keytype, order, sd, tx, nodeSize, ring, updates));
        long t0 = System.nanoTime();
        w.streamStart = db.internal().nodeStream().getNextPos();
        byte[] value = new byte[8];
        for (int i = 0; i < keys; i += tx) {
            int e = Math.min(keys, i + tx);
            put(ord, i, e, value);
            w.puts += e - i;
            if (w.puts >= window || e == keys) {
                w.streamEnd = db.internal().nodeStream().getNextPos();
                report("", w, e);
                Window nw = new Window();
                nw.streamStart = w.streamEnd;
                w = nw;
            }
        }
        long loadEnd = db.internal().nodeStream().getNextPos();
        double sec = (System.nanoTime() - t0) / 1e9;
        System.out.println(String.format(Locale.ROOT, "total: %d keys, stream %d bytes, %.1f B/key, %.1f s",
                keys, loadEnd, (double) loadEnd / keys, sec));
        Db.testHooks = null;
        w = new Window();
        printD();
        if (heap) {
            long heap1 = usedAfterGc();
            System.out.println(String.format(Locale.ROOT, "heap: %d bytes after the load, %d before, %.1f B a key (full GCs; the ring and the key order excluded)",
                    heap1, heap0, (double) (heap1 - heap0) / keys));
        }
        if (tree) printTree();
        if (reach) printReach();
        if (updates > 0) {
            Db.testHooks = new Db.TestHooks() {
                public void transExecuted(Db.ExecuteData x) { recordWritten(x); }
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void nodeTouched(Node node) {}
                public void nodeReplaced(Node node) { if (trackReplaced) replaced.add(node); }
            };
            java.util.SplittableRandom ur = new java.util.SplittableRandom(2);
            value[4] = 1;
            w = new Window();
            w.streamStart = db.internal().nodeStream().getNextPos();
            for (long i = 0; i < updates; i += tx) {
                Trans.Builder tb = db.trans();
                long e = Math.min(updates, i + tx);
                for (long j = i; j < e; j++) {
                    int k = ur.nextInt(keys);
                    value[0] = (byte) (k >>> 24); value[1] = (byte) (k >>> 16); value[2] = (byte) (k >>> 8); value[3] = (byte) k;
                    tb.put(key(k), value.clone());
                }
                time += bergdb.pub.util.Clock.UNITS_PER_SEC / 10000;
                clock.setTime(time);
                db.execute(tb.build());
                w.puts += e - i;
                if (w.puts >= window || e == updates) {
                    w.streamEnd = db.internal().nodeStream().getNextPos();
                    report("upd", w, e);
                    Window nw = new Window();
                    nw.streamStart = w.streamEnd;
                    w = nw;
                }
            }
            long end = db.internal().nodeStream().getNextPos();
            System.out.println(String.format(Locale.ROOT, "updates total: %d puts, %d bytes, %.1f B/put",
                    updates, end - loadEnd, (double) (end - loadEnd) / updates));
            Db.testHooks = null;
            w = new Window();
            printD();
            if (heap) {
                long heap2 = usedAfterGc();
                System.out.println(String.format(Locale.ROOT, "heap after the updates: %d bytes, %.1f B a key",
                        heap2, (double) (heap2 - heap0) / keys));
            }
        }
        System.out.println("NODESIZEBENCH OK");
        System.exit(0);
    }

    public static void main(String[] args) throws Exception {
        new NodeSizeBench().run();
    }
}
