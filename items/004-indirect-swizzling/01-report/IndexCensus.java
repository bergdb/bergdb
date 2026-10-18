package bergdb.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.PointerFollower;
import bergdb.dag.TopNode;
import bergdb.stream.MemoryStream;

/**
 * A census of BergDB's index, and the cost of the read path's pointer follow, for bergdb
 * item 004 (004-01). A tool of the item, not part of BergDB: it uses the Java code as it is
 * (bergdb.jar) and changes nothing.
 *
 * An in-memory database (MemoryStream, no eviction, infinite retention) is loaded with N keys
 * in random order, 1,000 puts a transaction, and then updated (uniform random keys, 10 puts
 * a transaction). After each phase:
 *
 *   1. The latest tree: the index nodes a scan at the latest time visits (the current
 *      nodes), and their memory size (Node.getMemSize()).
 *   2. The resident objects (Residents.walk from the super root, the node table and D):
 *      index objects (canonical, snapshots; current or not) and values, and the in-degree
 *      of each object: how many memory pointers of resident objects point to it. Without
 *      eviction and with infinite retention, every index node made so far is resident.
 *   3. The stream: the index node versions written and the distinct index nodes (ids)
 *      written, from the records.
 *   4. Gets at the latest time, random keys, one thread: Db.getOne with the readers'
 *      follower as it is (a pointer lock and an access stamp per edge); with a follower
 *      that reads a memory pointer without the lock and without the stamp; with the stamp
 *      but no lock; and getOneInternal (no readSync) with the follower as it is. A memory
 *      pointer is all there is here (no eviction), so the other followers are safe in this
 *      single-threaded measurement only.
 *
 * Properties: keys (default 1000000), keytype (int4: 4-byte big-endian ints; pre16: an
 * 8-byte shared prefix and an 8-byte big-endian id; rnd16: 16 bytes, the first 8 a hash
 * of the id), valsize (default 8), maxnode (8, 14, 30, 62; default 30), updates (puts after
 * the load, default the keys), gets (default 1000000), threads (gets from this many threads
 * too: with the follower as it is, without lock and stamp, and without lock, stamp and
 * readSync; default 0: none).
 *
 * Usage: java -Xmx12g -cp bergdb.jar:CLASSES bergdb.core.IndexCensus
 */
public class IndexCensus {
    final int keys = Integer.getInteger("keys", 1000000);
    final String keytype = System.getProperty("keytype", "int4");
    final int valsize = Integer.getInteger("valsize", 8);
    final int maxNode = Integer.getInteger("maxnode", 30);
    final int updates = Integer.getInteger("updates", keys);
    final int gets = Integer.getInteger("gets", 1000000);
    final int threads = Integer.getInteger("threads", 0);

    final CoreTestClock clock = new CoreTestClock();
    long time = 1000000;
    Db db;

    byte[] key(int k) {
        if (keytype.equals("int4")) return KeyFactory.binaryIntKey(k);
        byte[] b = new byte[16];
        if (keytype.equals("pre16")) {
            byte[] p = "account:".getBytes();
            System.arraycopy(p, 0, b, 0, 8);
        } else if (keytype.equals("rnd16")) {
            long h = (k + 1) * 0x9E3779B97F4A7C15L;
            Bytes.longToBytesBE(h, b, 0);
        } else {
            throw new IllegalArgumentException("keytype " + keytype);
        }
        Bytes.longToBytesBE(k, b, 8);
        return b;
    }

    byte[] value(int k, int v) {
        byte[] b = new byte[valsize];
        for (int i = 0; i < valsize; i++) b[i] = (byte) (k * 31 + v + i);
        return b;
    }

    void execute(Trans.Builder b) {
        time += 10;
        clock.setTime(time);
        db.execute(b.build());
    }

    public static void main(String[] args) throws Exception {
        new IndexCensus().run();
    }

    void run() throws Exception {
        DbBuilder b = Db.builder().testSetup(new MemoryStream());
        b.clock(clock);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        db = b.start();
        System.out.println("IndexCensus: keys " + keys + ", keytype " + keytype + ", valsize "
                + valsize + ", maxnode " + maxNode + ", updates " + updates + "; "
                + System.getProperty("java.version"));

        int[] order = new int[keys];
        for (int i = 0; i < keys; i++) order[i] = i;
        Random rnd = new Random(1);
        for (int i = keys - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int t = order[i]; order[i] = order[j]; order[j] = t;
        }
        long s = System.nanoTime();
        for (int i = 0; i < keys; i += 1000) {
            Trans.Builder tb = db.trans();
            for (int j = i; j < Math.min(keys, i + 1000); j++) tb.put(key(order[j]), value(order[j], 0));
            execute(tb);
        }
        System.out.printf("load: %d puts in %.1f s%n", keys, (System.nanoTime() - s) / 1e9);
        census("after the load");
        timeGets("after the load");

        s = System.nanoTime();
        for (int i = 0; i < updates; i += 10) {
            Trans.Builder tb = db.trans();
            for (int j = 0; j < 10; j++) {
                int k = rnd.nextInt(keys);
                tb.put(key(k), value(k, i + 1));
            }
            execute(tb);
        }
        System.out.printf("updates: %d puts in %.1f s%n", updates, (System.nanoTime() - s) / 1e9);
        census("after the updates");
        timeGets("after the updates");
        db.stop();
    }

    /** Parts 1 to 3 of the class comment. */
    void census(String when) {
        // 1. The latest tree.
        final HashSet<Long> current = new HashSet<Long>();
        final long[] currentBytes = new long[1];
        final long[] values = new long[2];
        GetMany g = db.newGetMany();
        final PointerFollower real = g.gd.pointerFollower;
        g.gd.pointerFollower = new PointerFollower() {
            public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
                Node n = real.followPointer(predecessor, pointerIndex, op);
                if (n.isIndexNode()) {
                    if (current.add(n.getId())) currentBytes[0] += n.getMemSize();
                } else {
                    values[0]++;
                    values[1] += n.getMemSize();
                }
                return n;
            }
        };
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return CONTINUE;
            }
            public void eod() {}
        };
        db.getMany(g);

        // 2. The resident objects and their in-degrees.
        Db.Internal in = db.internal();
        long[] idx = new long[6];       // canonical, snapshot, current, not current, bytes, top
        long[] val = new long[2];       // count, bytes
        final IdentityHashMap<Node, int[]> indeg = new IdentityHashMap<Node, int[]>();
        long pointers = 0, memPointers = 0;
        synchronized (in.getWriteLock()) {
            final ArrayList<Node> d = new ArrayList<Node>();
            in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                public void node(Node node, long tpos, long lastTpos) {
                    d.add(node);
                }
            });
            List<Node> resident = Residents.walk(in.superRoot(), in.cache().nodes(), d);
            for (Node x : resident) {
                if (x.isIndexNode()) {
                    if (x.isCanonical()) idx[0]++; else idx[1]++;
                    if (current.contains(x.getId())) idx[2]++; else idx[3]++;
                    idx[4] += x.getMemSize();
                    if (x instanceof TopNode) idx[5]++;
                    int n = x.getSize();
                    for (int i = 0; i < n; i++) {
                        Node c = x.getPointerNode(i);
                        long p = x.getPointerPos(i);
                        if (c == null && p < 0) continue;
                        pointers++;
                        if (c == null) continue;
                        memPointers++;
                        int[] cnt = indeg.get(c);
                        if (cnt == null) indeg.put(c, cnt = new int[1]);
                        cnt[0]++;
                    }
                } else {
                    val[0]++;
                    val[1] += x.getMemSize();
                }
            }
        }
        long[] hIdx = new long[5], hVal = new long[5];     // in-degree 1, 2, 3-4, 5-8, 9+
        long multiIdx = 0, multiVal = 0;
        for (Map.Entry<Node, int[]> e : indeg.entrySet()) {
            int k = e.getValue()[0];
            int bucket = k == 1 ? 0 : k == 2 ? 1 : k <= 4 ? 2 : k <= 8 ? 3 : 4;
            if (e.getKey().isIndexNode()) {
                hIdx[bucket]++;
                if (k > 1) multiIdx++;
            } else {
                hVal[bucket]++;
                if (k > 1) multiVal++;
            }
        }

        // 3. The stream.
        long versions = 0, valueNodes = 0;
        HashSet<Long> written = new HashSet<Long>();
        synchronized (in.getWriteLock()) {
            NodeStream ns = in.nodeStream();
            NodeStream.TransIterator it = ns.createTransIterator(ns.getFirstPos());
            while (it.next()) {
                StoredTrans st = it.getStoredTrans();
                for (StoredNode sn : st.nodes) {
                    Node n = sn.getNode();
                    if (n.isIndexNode()) {
                        versions++;
                        written.add(n.getId());
                    } else {
                        valueNodes++;
                    }
                }
            }
        }

        System.out.println("census " + when + ":");
        System.out.printf("  latest tree: %d index nodes (%.2f keys per node), %.1f MB, %.1f bytes per key; %d values, %.1f MB%n",
                current.size(), (double) keys / current.size(), currentBytes[0] / 1e6,
                (double) currentBytes[0] / keys, values[0], values[1] / 1e6);
        System.out.printf("  resident: %d index objects (%.3f per key; %d canonical, %d snapshots; %d current, %d not current; %d top nodes), %.1f MB; %d values, %.1f MB%n",
                idx[0] + idx[1], (double) (idx[0] + idx[1]) / keys, idx[0], idx[1], idx[2], idx[3],
                idx[5], idx[4] / 1e6, val[0], val[1] / 1e6);
        System.out.printf("  pointers of resident index objects: %d, memory pointers %d%n", pointers, memPointers);
        System.out.printf("  in-degree (memory pointers to an object): index objects 1: %d, 2: %d, 3-4: %d, 5-8: %d, 9+: %d (%.1f%% more than one)%n",
                hIdx[0], hIdx[1], hIdx[2], hIdx[3], hIdx[4], 100.0 * multiIdx / Math.max(1, sum(hIdx)));
        System.out.printf("  in-degree: values 1: %d, 2: %d, 3-4: %d, 5-8: %d, 9+: %d (%.1f%% more than one)%n",
                hVal[0], hVal[1], hVal[2], hVal[3], hVal[4], 100.0 * multiVal / Math.max(1, sum(hVal)));
        System.out.printf("  stream: %d index node versions written, %d distinct index nodes written (%.3f per key), %d value nodes; %.1f MB%n",
                versions, written.size(), (double) written.size() / keys, valueNodes,
                in.nodeStream().getNextPos() / 1e6);
    }

    static long sum(long[] a) {
        long s = 0;
        for (long x : a) s += x;
        return s;
    }

    /** A follower that takes a memory pointer without the lock and the stamp. */
    static final class NoLock implements PointerFollower {
        final PointerFollower real;
        NoLock(PointerFollower real) {
            this.real = real;
        }
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node c = predecessor.getPointerNode(pointerIndex);
            if (c != null) return c;
            return real.followPointer(predecessor, pointerIndex, op);
        }
    }

    /** A follower that writes the stamp but takes no lock. */
    static final class StampNoLock implements PointerFollower {
        final PointerFollower real;
        StampNoLock(PointerFollower real) {
            this.real = real;
        }
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node c = predecessor.getPointerNode(pointerIndex);
            if (c != null) {
                if (predecessor instanceof KeyNode) {
                    ((KeyNode) predecessor).setPointerAccessData(pointerIndex, op.accessData);
                }
                return c;
            }
            return real.followPointer(predecessor, pointerIndex, op);
        }
    }

    /** Part 4 of the class comment. */
    void timeGets(String when) throws Exception {
        final long[][] segs = new long[gets][];
        Random rnd = new Random(2);
        for (int i = 0; i < gets; i++) segs[i] = Keys.toSegments(key(rnd.nextInt(keys)));
        String[] names = {"as it is", "no lock, no stamp", "stamp, no lock", "as it is, no readSync"};
        double[] med = new double[names.length];
        // Interleaved rounds, so that drift and the JIT affect all alike.
        double[][] ns = new double[names.length][5];
        for (int r = 0; r < 7; r++) {
            for (int f = 0; f < names.length; f++) {
                GetData gd = db.newGetData();
                PointerFollower real = gd.pointerFollower;
                if (f == 1) gd.pointerFollower = new NoLock(real);
                if (f == 2) gd.pointerFollower = new StampNoLock(real);
                long sum = 0;
                long s = System.nanoTime();
                for (int i = 0; i < gets; i++) {
                    byte[] v = f == 3 ? db.getOneInternal(Long.MAX_VALUE, segs[i], gd)
                            : db.getOne(Long.MAX_VALUE, segs[i], gd);
                    sum += v[0];
                }
                double t = (double) (System.nanoTime() - s) / gets;
                if (r >= 2) ns[f][r - 2] = t;
                if (sum == 42) System.out.print("");
            }
        }
        System.out.println("gets " + when + ", one thread, ns per get (median of 5 rounds of " + gets + "):");
        for (int f = 0; f < names.length; f++) {
            double[] x = ns[f].clone();
            Arrays.sort(x);
            med[f] = x[2];
            System.out.printf("  %-24s %7.1f (best %.1f)%n", names[f], med[f], x[0]);
        }
        if (threads > 1) timeGetsThreads(segs, when);
    }

    void timeGetsThreads(final long[][] segs, String when) throws Exception {
        String[] names = {"as it is", "no lock, no stamp", "no lock, no stamp, no readSync"};
        System.out.println("gets " + when + ", " + threads + " threads, million gets a second (median of 5 rounds):");
        for (int f = 0; f < names.length; f++) {
            final int ff = f;
            double[] rates = new double[5];
            for (int r = 0; r < 7; r++) {
                Thread[] ts = new Thread[threads];
                final java.util.concurrent.CyclicBarrier barrier = new java.util.concurrent.CyclicBarrier(threads + 1);
                for (int t = 0; t < threads; t++) {
                    final int tt = t;
                    ts[t] = new Thread(new Runnable() {
                        public void run() {
                            GetData gd = db.newGetData();
                            if (ff >= 1) gd.pointerFollower = new NoLock(gd.pointerFollower);
                            try {
                                barrier.await();
                            } catch (Exception e) {
                                throw new RuntimeException(e);
                            }
                            long sum = 0;
                            int n = segs.length;
                            for (int i = 0; i < n; i++) {
                                long[] k = segs[(i + tt * 7919) % n];
                                byte[] v = ff == 2 ? db.getOneInternal(Long.MAX_VALUE, k, gd)
                                        : db.getOne(Long.MAX_VALUE, k, gd);
                                sum += v[0];
                            }
                            if (sum == 42) System.out.print("");
                        }
                    });
                    ts[t].start();
                }
                barrier.await();
                long s = System.nanoTime();
                for (Thread t : ts) t.join();
                double rate = (double) segs.length * threads / ((System.nanoTime() - s) / 1e9);
                if (r >= 2) rates[r - 2] = rate;
            }
            Arrays.sort(rates);
            System.out.printf("  %-24s %6.2f (best %.2f)%n", names[f], rates[2] / 1e6, rates[4] / 1e6);
        }
    }
}
