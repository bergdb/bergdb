package bergdb.core;

import java.io.BufferedOutputStream;
import java.io.DataOutputStream;
import java.io.EOFException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.HashSet;
import java.util.Locale;
import java.util.Random;

import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;

/**
 * The stream bytes a put costs, by kind, as a database is loaded (bergdb 005-38), and, since
 * bergdb 005-49, every record's index bytes against its puts. A tool of the item: it uses
 * bergdb.jar as it is, through Db.testHooks. In memory, no eviction, infinite retention; the
 * stream keeps only its last wb.ring bytes (a read before them fails).
 *
 * For every window of wb.window puts: the stream's growth a put, split into the records'
 * value nodes, key nodes by kind and height, top nodes, the got-dirty list, the rest of the
 * records, and the rest of the stream (meta blocks); key node writes a put by kind; the
 * written nodes that stayed dirty; and writes a distinct node in the window.
 *
 * With -Dwb.rec=FILE (bergdb 005-49), one entry of 53 bytes a record, big-endian: the phase
 * (byte, 0 load, 1 updates), its puts, index nodes and got-dirty ids (ints), the bytes of
 * its value nodes, of the whole record (to the next record) and of its index nodes, the
 * startup lag after it (the stream's end minus the startup pos) and the stream's end (longs).
 *
 * Since bergdb 007-06, an entry has 77 bytes: the 53 above (phase 2 is a dummy transaction of
 * Db.setStartupDistance), then the section without its last record after the record (long:
 * the record's tpos minus the end of the record at the startup pos, R(s+1), ..., R(k-1) of
 * 007-01, section 3), D in nodes (int: the got-dirty ids in TransSeq), the debt (long: the sum
 * of TransSeq.recordBytes over TransSeq, each node's stream size plus 16 bytes) and the
 * startup distance in force (int). D and the debt are kept up to date a record (the debt with
 * each transaction's nodes at the sizes they had when it was added or taken) and recomputed
 * exactly every sd/100 bytes of stream; the drift is printed at the end.
 *
 * 007-06's workloads, after the load: -Dwb.utx=PUTS, the puts a transaction of the update
 * phase (default wb.tx; 1 for single puts); -Dwb.op=delete, wb.updates deletes of distinct
 * loaded keys in random order instead of random puts; -Dwb.lowerAt=PUTS -Dwb.lowerTo=BYTES
 * [-Dwb.lowerStep=BYTES], Db.setStartupDistance after that many update puts, in one call or
 * in calls lowering it by at most lowerStep each, back to back; or, with -Dwb.lowerGap=TX,
 * every TX update transactions to max(lowerTo, section / 2), following the section down; or,
 * with -Dwb.lowerPace=true and wb.lowerGap, in one call, with the deadline of a patched
 * TransSeq (TransSeq.deadlineDistance, a probe) at the lag, lowered every TX transactions to
 * max(2 lowerTo, lag): the pace catches up and the deadline does not fire.
 *
 * Usage: java -Dwb.keys=N [-Dwb.keytype=key24|rnd24] [-Dwb.order=random|seq] [-Dwb.sd=BYTES]
 *            [-Dwb.tx=PUTS] [-Dwb.node=8|14|30|62] [-Dwb.window=PUTS] [-Dwb.rec=FILE]
 *            -cp bergdb.jar:. bergdb.core.WriteBench
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
    final String recFile = prop("rec", "");
    final int utx = Integer.parseInt(prop("utx", prop("tx", "1000")));
    final String op = prop("op", "put");
    final long lowerAt = Long.parseLong(prop("lowerAt", "-1"));
    final int lowerTo = Integer.parseInt(prop("lowerTo", "0"));
    final int lowerStep = Integer.parseInt(prop("lowerStep", "0"));
    final int lowerGap = Integer.parseInt(prop("lowerGap", "0"));
    final boolean lowerPace = Boolean.parseBoolean(prop("lowerPace", "false"));
    long lastSection;           // the section without its last record, after the last record
    boolean following;          // lowerGap > 0: lowering in steps that follow the section
    int sdNow;                  // the startup distance in force

    // The records from the one at the startup pos to the last: tpos and nextPos (bergdb 007-06).
    long[] rTpos = new long[1 << 16], rNext = new long[1 << 16];
    int rHead, rTail;
    // Mirror of TransSeq: each TransInfo with its got-dirty count and recordBytes.
    TransSeq.TransInfo[] dInfo = new TransSeq.TransInfo[1 << 16];
    long[] dBytes = new long[1 << 16];
    int[] dCount = new int[1 << 16];
    int dHead, dTail;
    long dNodes, debt, lastWalk, walks, maxDrift, maxDebtSeen;
    double maxDriftRel;
    long spMisses, maxDriftUpd;      // startup pos not at a record start; drift in the update phase
    double maxDriftRelUpd;
    static java.lang.reflect.Field firstField;

    DataOutputStream rec;
    int phase;              // 0 load, 1 updates
    long lastStartupPos;
    long maxIndexBytes, maxRecordBytes, maxLag;    // over the update phase

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
        long indexBytes = 0;
        for (int i = 0; i < n.topCount; i++) indexBytes += StoredTopNode.getByteSize(n.topNodes[i]);
        for (int i = 0; i < n.keyCount; i++) {
            KeyNode k = n.keyNodes[i];
            int kd = kind(k);
            int b = StoredKeyNode.getByteSize(k);
            indexBytes += b;
            w.kindBytes[kd] += b;
            w.kindNodes[kd]++;
            w.kindKlongs[kd] += k.size;
            w.keyNodes++;
            if (k.isDirty()) w.stillDirty++;
            w.distinct.add(k.getId());
        }
        w.gotDirty += x.transInfo.gotDirtyNodes.size();
        lastStartupPos = x.startupPos.get();
        long recordBytes = x.trans.nextPos - x.trans.tpos;
        long lag = x.trans.nextPos - lastStartupPos;
        if (phase == 1) {
            maxIndexBytes = Math.max(maxIndexBytes, indexBytes);
            maxRecordBytes = Math.max(maxRecordBytes, recordBytes);
            maxLag = Math.max(maxLag, lag);
        }
        // The section without its last record (bergdb 007-06).
        if (rTail == rTpos.length) {
            int m = rTail - rHead;
            if (m * 2 > rTpos.length) {
                rTpos = java.util.Arrays.copyOf(rTpos, rTpos.length * 2);
                rNext = java.util.Arrays.copyOf(rNext, rNext.length * 2);
            }
            System.arraycopy(rTpos, rHead, rTpos, 0, m);
            System.arraycopy(rNext, rHead, rNext, 0, m);
            rHead = 0;
            rTail = m;
        }
        rTpos[rTail] = x.trans.tpos;
        rNext[rTail] = x.trans.nextPos;
        rTail++;
        while (rHead < rTail && rTpos[rHead] < lastStartupPos) rHead++;
        long endOfS = rHead < rTail && rTpos[rHead] == lastStartupPos ? rNext[rHead] : lastStartupPos;
        if (endOfS == lastStartupPos && lastStartupPos != 0) spMisses++;
        long sectionNoLast = Math.max(0, x.trans.tpos - endOfS);
        lastSection = sectionNoLast;
        trackDebt(x);
        if (rec != null) {
            try {
                rec.writeByte(phase);
                rec.writeInt(n.valueCount);
                rec.writeInt(n.keyCount + n.topCount);
                rec.writeInt(x.transInfo.gotDirtyNodes.size());
                rec.writeLong(n.valueRecordBytes);
                rec.writeLong(recordBytes);
                rec.writeLong(indexBytes);
                rec.writeLong(lag);
                rec.writeLong(x.trans.nextPos);
                rec.writeLong(sectionNoLast);
                rec.writeInt((int) dNodes);
                rec.writeLong(debt);
                rec.writeInt(sdNow);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    /** D and the debt after x (bergdb 007-06); see the class comment. */
    void trackDebt(Db.ExecuteData x) {
        TransSeq seq = db.internal().transSeq();
        TransSeq.TransInfo f;
        try {
            if (firstField == null) {
                firstField = TransSeq.class.getDeclaredField("first");
                firstField.setAccessible(true);
            }
            f = (TransSeq.TransInfo) firstField.get(seq);
        } catch (ReflectiveOperationException e) {
            throw new RuntimeException(e);
        }
        while (dHead < dTail && dInfo[dHead] != f) {
            debt -= dBytes[dHead];
            dNodes -= dCount[dHead];
            dInfo[dHead] = null;
            dHead++;
        }
        if (seq.last() == x.transInfo && x.transInfo != null
                && (dHead == dTail || dInfo[dTail - 1] != x.transInfo)) {
            if (dTail == dInfo.length) {
                int n = dTail - dHead;
                if (n * 2 > dInfo.length) {
                    dInfo = java.util.Arrays.copyOf(dInfo, dInfo.length * 2);
                    dBytes = java.util.Arrays.copyOf(dBytes, dBytes.length * 2);
                    dCount = java.util.Arrays.copyOf(dCount, dCount.length * 2);
                }
                System.arraycopy(dInfo, dHead, dInfo, 0, n);
                System.arraycopy(dBytes, dHead, dBytes, 0, n);
                System.arraycopy(dCount, dHead, dCount, 0, n);
                java.util.Arrays.fill(dInfo, n, dInfo.length, null);
                dHead = 0;
                dTail = n;
            }
            dInfo[dTail] = x.transInfo;
            dBytes[dTail] = TransSeq.recordBytes(x.transInfo);
            dCount[dTail] = x.transInfo.gotDirtyNodes.size();
            debt += dBytes[dTail];
            dNodes += dCount[dTail];
            dTail++;
        }
        if (x.trans.nextPos - lastWalk >= Math.max(100000, sdNow / 100)) {
            lastWalk = x.trans.nextPos;
            walks++;
            if (dTail - dHead != seq.getSize()) {
                throw new IllegalStateException("mirror of TransSeq: " + (dTail - dHead) + " != " + seq.getSize());
            }
            long exact = 0, nodes = 0;
            for (int i = dHead; i < dTail; i++) {
                dBytes[i] = TransSeq.recordBytes(dInfo[i]);
                exact += dBytes[i];
                nodes += dInfo[i].gotDirtyNodes.size();
            }
            if (nodes != dNodes) throw new IllegalStateException("D nodes " + dNodes + " != " + nodes);
            long drift = Math.abs(exact - debt);
            maxDrift = Math.max(maxDrift, drift);
            if (exact > 0) maxDriftRel = Math.max(maxDriftRel, (double) drift / exact);
            if (phase != 0) {
                maxDriftUpd = Math.max(maxDriftUpd, drift);
                if (exact > 0) maxDriftRelUpd = Math.max(maxDriftRelUpd, (double) drift / exact);
            }
            debt = exact;
        }
        maxDebtSeen = Math.max(maxDebtSeen, debt);
    }

    /** Db.setStartupDistance(to), in one call or in steps of at most lowerStep (bergdb 007-06). */
    void lower(long putsSoFar) {
        long p0 = db.internal().nodeStream().getNextPos();
        System.out.println(String.format(Locale.ROOT, "lower: after %d update puts, at stream %d, sd %d -> %d, step %d",
                putsSoFar, p0, sdNow, lowerTo, lowerStep));
        phase = 2;
        int calls = 0;
        int s = sdNow;
        do {
            s = lowerStep <= 0 ? lowerTo : Math.max(lowerTo, s - lowerStep);
            sdNow = Math.max(RecoverableStream.META_BLOCK_DISTANCE * 2, Math.min(1000 * 1000000, s));
            db.setStartupDistance(s);
            calls++;
        } while (s > lowerTo);
        phase = 1;
        System.out.println(String.format(Locale.ROOT, "lower: %d calls, %d stream bytes", calls,
                db.internal().nodeStream().getNextPos() - p0));
    }

    /**
     * With lowerGap > 0 (bergdb 007-06), the decrease follows the section down: every lowerGap
     * update transactions, the distance becomes max(lowerTo, section / 2), when that is lower,
     * so that the deadline at 2 sd stays near the section's end and the pace catches up.
     */
    void follow(long putsSoFar) {
        if (lowerPace) {
            long lag = db.internal().nodeStream().getNextPos() - lastStartupPos;
            long dl = Math.max(2L * lowerTo, lag);
            setDeadline(dl == 2L * lowerTo ? 0 : dl);
            if (dl == 2L * lowerTo) {
                following = false;
                System.out.println(String.format(Locale.ROOT, "pace: deadline at 2 sd after %d update puts, at stream %d",
                        putsSoFar, db.internal().nodeStream().getNextPos()));
            }
            return;
        }
        int target = (int) Math.max(lowerTo, Math.min(1000L * 1000000, lastSection / 2));
        if (target < sdNow) {
            phase = 2;
            sdNow = Math.max(RecoverableStream.META_BLOCK_DISTANCE * 2, target);
            db.setStartupDistance(target);
            phase = 1;
        }
        if (sdNow <= lowerTo) {
            following = false;
            System.out.println(String.format(Locale.ROOT, "follow: at %d after %d update puts, at stream %d",
                    lowerTo, putsSoFar, db.internal().nodeStream().getNextPos()));
        }
    }

    /** The probe of bergdb 007-06 in a patched bergdb.jar: TransSeq.deadlineDistance. */
    static void setDeadline(long d) {
        try {
            TransSeq.class.getField("deadlineDistance").setLong(null, d);
        } catch (ReflectiveOperationException e) {
            throw new RuntimeException("needs the 007-06 probe in TransSeq", e);
        }
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
        if (!recFile.isEmpty()) rec = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(recFile), 1 << 20));
        stream = new RingStream(ring);
        clock.setTime(time);
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).testId().retainForever().noEvict();
        if (nodeSize == 8) b.maxNodeSize8();
        else if (nodeSize == 14) b.maxNodeSize14();
        else if (nodeSize == 30) b.maxNodeSize30();
        else if (nodeSize == 62) b.maxNodeSize62();
        else throw new IllegalArgumentException("node " + nodeSize);
        b.startupDistance(sd);
        sdNow = sd;
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
        phase = 1;
        boolean delete = op.equals("delete");
        if (!delete && !op.equals("put")) throw new IllegalArgumentException(op);
        int[] dord = null;
        if (delete) {
            if (updates > keys) throw new IllegalArgumentException("more deletes than keys");
            dord = new int[keys];
            for (int i = 0; i < keys; i++) dord[i] = i;
            Random rnd = new Random(3);
            for (int i = keys - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = dord[i]; dord[i] = dord[j]; dord[j] = t; }
        }
        System.out.println(String.format(Locale.ROOT, "updates: %d %s, %d a transaction", updates, op, utx));
        long t1 = System.nanoTime();
        for (long i = 0; i < updates; i += utx) {
            if (lowerAt >= 0 && i <= lowerAt && lowerAt < i + utx) {
                if (lowerPace) {
                    // The pace uses the new distance at once; the deadline follows the lag down.
                    setDeadline(Math.max(2L * lowerTo, db.internal().nodeStream().getNextPos() - lastStartupPos));
                    lower(i);
                    following = true;
                } else if (lowerGap > 0) {
                    following = true;
                    System.out.println(String.format(Locale.ROOT, "follow: from %d after %d update puts, at stream %d, gap %d",
                            sdNow, i, db.internal().nodeStream().getNextPos(), lowerGap));
                } else {
                    lower(i);
                }
            }
            if (following && ((i - lowerAt) / utx) % lowerGap == 0) follow(i);
            Trans.Builder tb = db.trans();
            long e = Math.min(updates, i + utx);
            for (long j = i; j < e; j++) {
                if (delete) {
                    tb.delete(key(dord[(int) j]));
                    continue;
                }
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
            System.out.println(String.format(Locale.ROOT, "updates: %d, stream %d bytes, %.1f B/update, %.1f s",
                    updates, end - loadEnd, (double) (end - loadEnd) / updates, (System.nanoTime() - t1) / 1e9));
            System.out.println(String.format(Locale.ROOT, "updates: largest record %d bytes, largest index bytes %d,"
                    + " largest startup lag %.0f MB (%.2f sd)", maxRecordBytes, maxIndexBytes, maxLag / 1e6, (double) maxLag / sd));
            System.out.println(String.format(Locale.ROOT, "debt: %d exact walks, largest drift %d bytes (%.4f of the debt),"
                    + " largest debt %.0f MB; after the load %d bytes (%.4f); startup pos not at a record: %d",
                    walks, maxDrift, maxDriftRel, maxDebtSeen / 1e6, maxDriftUpd, maxDriftRelUpd, spMisses));
        }
        if (rec != null) rec.close();
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
