package bergdb.core;

import java.io.EOFException;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.HashSet;
import java.util.Locale;
import java.util.Random;

import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.stream.AppendOnlyStream;

/**
 * The stream bytes a put costs, by kind, as a database is loaded (bergdb 005-38). A tool of
 * the item: it uses bergdb.jar as it is, through Db.testHooks. In memory, no eviction, infinite
 * retention; the stream keeps only its last wb.ring bytes (a read before them fails).
 *
 * For every window of wb.window puts: the stream's growth a put, split into the records'
 * value nodes, key nodes by kind and height, top nodes, the got-dirty list, the rest of the
 * records, and the rest of the stream (meta blocks); key node writes a put by kind; the
 * written nodes that stayed dirty; and writes a distinct node in the window.
 *
 * Usage: java -Dwb.keys=N [-Dwb.keytype=key24|rnd24] [-Dwb.order=random|seq] [-Dwb.sd=BYTES]
 *            [-Dwb.tx=PUTS] [-Dwb.node=8|14|30|62] [-Dwb.window=PUTS] -cp bergdb.jar:. bergdb.core.WriteBench
 */
public class WriteBench {
    static String prop(String n, String d) { return System.getProperty("wb." + n, d); }

    final int keys = Integer.parseInt(prop("keys", "1000000"));
    final String keytype = prop("keytype", "key24");
    final String order = prop("order", "random");
    final int sd = Integer.parseInt(prop("sd", "10000000"));
    final int tx = Integer.parseInt(prop("tx", "1000"));
    final int nodeSize = Integer.parseInt(prop("node", "30"));
    final int window = Integer.parseInt(prop("window", "1000000"));
    final long ring = Long.parseLong(prop("ring", "536870912"));
    final long updates = Long.parseLong(prop("updates", "0"));    // random puts to loaded keys after the load
    long lastStartupPos;

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

    // Kinds of key nodes: 0 value leaf (a segment leaf whose pointers name values), 1 link leaf
    // (a segment leaf whose pointers name the next segment's roots), 2 + h an inner node of
    // height h (1: its children are leaves).
    static final int KINDS = 10;
    static final String[] KIND_NAMES = {"vleaf", "lleaf", "", "in1", "in2", "in3", "in4", "in5", "in6", "in7+"};

    static final class Window {
        long puts, records, recordBytes, valueBytes, topBytes, topNodes, gotDirty, stillDirty, keyNodes;
        long streamStart, streamEnd;
        final long[] kindBytes = new long[KINDS], kindNodes = new long[KINDS], kindKlongs = new long[KINDS];
        final HashSet<Long> distinct = new HashSet<Long>();
    }

    final CoreTestClock clock = new CoreTestClock();
    long time = bergdb.pub.util.Clock.UNITS_PER_SEC;
    Window w = new Window();
    RingStream stream;
    Db db;

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

    void recordWritten(Db.ExecuteData x) {
        TransNodes n = x.transNodes;
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
            w.kindBytes[kd] += StoredKeyNode.getByteSize(k);
            w.kindNodes[kd]++;
            w.kindKlongs[kd] += k.size;
            w.keyNodes++;
            if (k.isDirty()) w.stillDirty++;
            w.distinct.add(k.getId());
        }
        w.gotDirty += x.transInfo.gotDirtyNodes.size();
        lastStartupPos = x.startupPos.get();
    }

    byte[] key(int k) {
        byte[] b = new byte[24];
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

    void report(Window w, long putsSoFar) {
        long stream = w.streamEnd - w.streamStart;
        double p = w.puts;
        long keyBytes = 0;
        for (long b : w.kindBytes) keyBytes += b;
        long dirtyList = 16 * w.gotDirty;
        long otherRec = w.recordBytes - w.valueBytes - keyBytes - w.topBytes - dirtyList;
        StringBuilder s = new StringBuilder();
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
        long dNodes = 0, dBytes = 0;
        try {
            java.lang.reflect.Field f = TransSeq.class.getDeclaredField("first");
            f.setAccessible(true);
            TransSeq.TransInfo info = (TransSeq.TransInfo) f.get(db.internal().transSeq());
            HashSet<Long> seen = new HashSet<Long>();
            for (; info != null; info = info.next) {
                for (Node nd : info.gotDirtyNodes) {
                    if (!seen.add(nd.getId())) continue;
                    dNodes++;
                    dBytes += nd instanceof KeyNode ? StoredKeyNode.getByteSize((KeyNode) nd) : StoredTopNode.getByteSize((TopNode) nd);
                }
            }
        } catch (ReflectiveOperationException e) {
            throw new RuntimeException(e);
        }
        long end = db.internal().nodeStream().getNextPos();
        s.append(String.format(Locale.ROOT, "; startup lag %.0f MB; D %d nodes, %.0f MB",
                (end - lastStartupPos) / 1e6, dNodes, dBytes / 1e6));
        System.out.println(s);
        System.out.flush();
    }

    void run() throws Exception {
        stream = new RingStream(ring);
        clock.setTime(time);
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).testId().retainForever().noEvict();
        if (nodeSize == 8) b.maxNodeSize8();
        else if (nodeSize == 14) b.maxNodeSize14();
        else if (nodeSize == 30) b.maxNodeSize30();
        else if (nodeSize == 62) b.maxNodeSize62();
        else throw new IllegalArgumentException("node " + nodeSize);
        b.startupDistance(sd);
        db = b.build();
        db.start();
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) { recordWritten(x); }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        int[] ord = new int[keys];
        for (int i = 0; i < keys; i++) ord[i] = i;
        if (order.equals("random")) {
            Random rnd = new Random(1);
            for (int i = keys - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        } else if (!order.equals("seq")) throw new IllegalArgumentException(order);
        System.out.println(String.format(Locale.ROOT, "WriteBench: %d keys %s %s, sd %d, tx %d, node %d", keys, keytype, order, sd, tx, nodeSize));
        long t0 = System.nanoTime();
        w.streamStart = db.internal().nodeStream().getNextPos();
        byte[] value = new byte[8];
        for (int i = 0; i < keys; i += tx) {
            Trans.Builder tb = db.trans();
            int e = Math.min(keys, i + tx);
            for (int j = i; j < e; j++) {
                int k = ord[j];
                value[0] = (byte) (k >>> 24); value[1] = (byte) (k >>> 16); value[2] = (byte) (k >>> 8); value[3] = (byte) k;
                tb.put(key(k), value.clone());
            }
            time += bergdb.pub.util.Clock.UNITS_PER_SEC / 10000;
            clock.setTime(time);
            db.execute(tb.build());
            w.puts += e - i;
            if (w.puts >= window || e == keys) {
                w.streamEnd = db.internal().nodeStream().getNextPos();
                report(w, e);
                Window nw = new Window();
                nw.streamStart = w.streamEnd;
                w = nw;
            }
        }
        long loadEnd = db.internal().nodeStream().getNextPos();
        System.out.println(String.format(Locale.ROOT, "load: %d keys, stream %d bytes, %.1f B/key, %.1f s",
                keys, loadEnd, (double) loadEnd / keys, (System.nanoTime() - t0) / 1e9));
        java.util.SplittableRandom ur = new java.util.SplittableRandom(2);
        value[4] = 1;
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
                System.out.print("upd ");
                report(w, (int) Math.min(Integer.MAX_VALUE, e));
                Window nw = new Window();
                nw.streamStart = w.streamEnd;
                w = nw;
            }
        }
        if (updates > 0) {
            long end = db.internal().nodeStream().getNextPos();
            System.out.println(String.format(Locale.ROOT, "updates: %d, stream %d bytes, %.1f B/update",
                    updates, end - loadEnd, (double) (end - loadEnd) / updates));
        }
        double sec = (System.nanoTime() - t0) / 1e9;
        System.out.println(String.format(Locale.ROOT, "total: %d keys, stream %d bytes, %.1f B/key, %.1f s",
                keys, db.internal().nodeStream().getNextPos(), (double) db.internal().nodeStream().getNextPos() / keys, sec));
        Db.testHooks = null;
        System.out.println("WRITEBENCH OK");
        System.exit(0);
    }

    public static void main(String[] args) throws Exception {
        new WriteBench().run();
    }
}
