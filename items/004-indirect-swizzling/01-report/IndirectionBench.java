import java.lang.invoke.MethodHandles;
import java.lang.invoke.VarHandle;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.SplittableRandom;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The cost of following a pointer, measured on a B-tree shaped graph of Java objects
 * (bergdb item 004, 004-01). Not BergDB's code: a tree of nodes like BergDB's key nodes
 * (arrays of 30 slots, 16 used, a linear search in each node), with values at the leaves,
 * and the edges followed in one of these ways:
 *
 *   direct       a Java reference: the child is ptr[i]
 *   lockstamp    BergDB's follow today: a striped monitor (PointerLocks: 128 locks,
 *                node.hashCode() + 13 * i), the reference read and the access stamp
 *                written into pos[i] under it
 *   lock         the monitor without the stamp
 *   stamp        the stamp without the monitor
 *   handle       indirect: ptr[i] is a handle, the child is handle.obj (a plain read)
 *   handleacq    the same with an acquire read of handle.obj (VarHandle.getAcquire)
 *   handleclock  handleacq, and a clock bit set in the handle if it is not set already
 *   hash         ptr[i] is not used; the child is found by its id (in pos[i]) in an
 *                open-addressing hash map of primitive longs
 *   chm          the same with java.util.concurrent.ConcurrentHashMap<Long, Object>
 *
 * Handles are allocated right before their objects (layout "before", the default: next to
 * the object's header and its first array, as a loader that makes the handle first would
 * place them), right after their objects and the objects' arrays ("child"), together with
 * their parent's other handles when the parent is linked ("parent"), or after the whole
 * tree in a random order ("scattered"). The layout only matters for the handle variants.
 *
 * Usage:
 *   java -Xms4g -Xmx4g IndirectionBench VARIANT KEYS THREADS [before|child|parent|scattered]
 *   java -Xms4g -Xmx4g IndirectionBench sizes
 * Prints one line: the variant, the keys, the threads, the layout, the tree's depth (edges
 * a lookup follows), the nanoseconds per lookup per thread (median and best of the
 * measured rounds) and the lookups per second of all threads together (median round).
 */
public final class IndirectionBench {
    static final int SLOTS = 30;
    static final int FILL = 16;
    static final int ROUNDS = 7;        // the first two are warm-up
    static final int WARMUP = 2;

    static final class Node {
        final long[] keys = new long[SLOTS];
        Object[] ptr;
        final long[] pos = new long[SLOTS];
        final boolean leaf;
        final long id;
        int size;

        Node(boolean leaf, long id, boolean withPtr) {
            this.leaf = leaf;
            this.id = id;
            if (withPtr) ptr = new Object[SLOTS];
        }
    }

    static final class Value {
        final long v;
        final long id;

        Value(long v, long id) {
            this.v = v;
            this.id = id;
        }
    }

    static final class Handle {
        Object obj;
        long pos;
        byte ref;

        Handle(Object obj) {
            this.obj = obj;
        }
    }

    static final VarHandle OBJ;
    static {
        try {
            OBJ = MethodHandles.lookup().findVarHandle(Handle.class, "obj", Object.class);
        } catch (ReflectiveOperationException e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    /** Open addressing, linear probing, long keys, for the variant hash. */
    static final class LongMap {
        final long[] keys;
        final Object[] vals;
        final int mask;
        final int shift;

        LongMap(int count) {
            int cap = Integer.highestOneBit(Math.max(4, count * 2 - 1)) << 1;
            keys = new long[cap];
            Arrays.fill(keys, Long.MIN_VALUE);
            vals = new Object[cap];
            mask = cap - 1;
            shift = 64 - Integer.numberOfTrailingZeros(cap);
        }

        int slot(long k) {
            return (int) ((k * 0x9E3779B97F4A7C15L) >>> shift);
        }

        void put(long k, Object v) {
            int i = slot(k);
            while (keys[i] != Long.MIN_VALUE && keys[i] != k) i = (i + 1) & mask;
            keys[i] = k;
            vals[i] = v;
        }

        Object get(long k) {
            int i = slot(k);
            while (true) {
                long x = keys[i];
                if (x == k) return vals[i];
                if (x == Long.MIN_VALUE) return null;
                i = (i + 1) & mask;
            }
        }
    }

    static final Object[] LOCKS = new Object[128];
    static {
        for (int i = 0; i < LOCKS.length; i++) LOCKS[i] = new Object();
    }

    static volatile long accessClock = 10000;

    final String variant;
    final String layout;
    final boolean scattered;
    final long[] keys;          // sorted
    Node root;
    int depth;
    long nextId = 1001;
    LongMap map;
    ConcurrentHashMap<Long, Object> chm;
    final List<Object> all = new ArrayList<Object>();      // objects to make handles for

    IndirectionBench(String variant, int n, String layout) {
        this.variant = variant;
        this.layout = layout;
        this.scattered = layout.equals("scattered");
        SplittableRandom rnd = new SplittableRandom(42);
        long[] k = new long[n];
        for (int i = 0; i < n; i++) k[i] = rnd.nextLong() >>> 1;
        Arrays.sort(k);
        int m = 0;
        for (int i = 0; i < n; i++) if (i == 0 || k[i] != k[i - 1]) k[m++] = k[i];
        keys = Arrays.copyOf(k, m);
        build();
    }

    boolean usesHandles() {
        return variant.startsWith("handle");
    }

    boolean usesIds() {
        return variant.equals("hash") || variant.equals("chm");
    }

    long newId() {
        long id = nextId;
        nextId += 2 * 37;           // sparse odd ids, as BergDB's vpos ids
        return id;
    }

    /**
     * The edge from n's slot i to child c, set the variant's way; h is c's handle when the
     * layout is child or before (made with c).
     */
    void link(Node n, int i, Object c, long cid, Handle h) {
        if (usesIds()) {
            n.pos[i] = cid;
        } else if (usesHandles() && (layout.equals("child") || layout.equals("before"))) {
            n.ptr[i] = h;
        } else if (usesHandles() && layout.equals("parent")) {
            n.ptr[i] = new Handle(c);
        } else {
            n.ptr[i] = c;
        }
    }

    /** A handle made before its object (layout before), else null. */
    Handle pre() {
        return usesHandles() && layout.equals("before") ? new Handle(null) : null;
    }

    /** The handle of object c, just made: pre's (layout before), a new one (child), or null. */
    Handle post(Handle pre, Object c) {
        if (pre != null) {
            pre.obj = c;
            return pre;
        }
        return usesHandles() && layout.equals("child") ? new Handle(c) : null;
    }

    void register(Object c, long cid) {
        if (usesIds()) {
            if (variant.equals("hash")) map.put(cid, c);
            else chm.put(cid, c);
        }
    }

    void build() {
        int nodesGuess = keys.length / FILL * 2 + 16;
        if (variant.equals("hash")) map = new LongMap(keys.length + nodesGuess);
        if (variant.equals("chm")) chm = new ConcurrentHashMap<Long, Object>(2 * (keys.length + nodesGuess));
        boolean withPtr = !usesIds();
        List<Node> level = new ArrayList<Node>();
        List<Handle> levelHandles = new ArrayList<Handle>();
        for (int i = 0; i < keys.length; i += FILL) {
            Handle hl = pre();
            Node leaf = new Node(true, newId(), withPtr);
            levelHandles.add(post(hl, leaf));
            int s = Math.min(FILL, keys.length - i);
            for (int j = 0; j < s; j++) {
                long vid = newId();
                Handle hv = pre();
                Value v = new Value(keys[i + j] ^ 0x5555L, vid);
                leaf.keys[j] = keys[i + j];
                link(leaf, j, v, vid, post(hv, v));
                register(v, vid);
                if (scattered && usesHandles()) all.add(v);
            }
            leaf.size = s;
            level.add(leaf);
        }
        depth = 1;
        while (level.size() > 1) {
            List<Node> up = new ArrayList<Node>();
            List<Handle> upHandles = new ArrayList<Handle>();
            for (int i = 0; i < level.size(); i += FILL) {
                Handle hp = pre();
                Node p = new Node(false, newId(), withPtr);
                upHandles.add(post(hp, p));
                int s = Math.min(FILL, level.size() - i);
                for (int j = 0; j < s; j++) {
                    Node c = level.get(i + j);
                    p.keys[j] = c.keys[0];
                    link(p, j, c, c.id, levelHandles.get(i + j));
                    register(c, c.id);
                    if (scattered && usesHandles()) all.add(c);
                }
                p.size = s;
                up.add(p);
            }
            level = up;
            levelHandles = upHandles;
            depth++;
        }
        root = level.get(0);
        if (usesHandles() && scattered) scatterHandles();
    }

    /** Layout scattered: handles made after the tree, in a random order. */
    void scatterHandles() {
        java.util.IdentityHashMap<Object, Handle> hs = new java.util.IdentityHashMap<Object, Handle>();
        Object[] objs = all.toArray();
        SplittableRandom rnd = new SplittableRandom(7);
        for (int i = objs.length - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            Object t = objs[i]; objs[i] = objs[j]; objs[j] = t;
        }
        for (Object o : objs) hs.put(o, new Handle(o));
        replace(root, hs);
        all.clear();
    }

    void replace(Node n, java.util.IdentityHashMap<Object, Handle> hs) {
        for (int i = 0; i < n.size; i++) {
            Object c = n.ptr[i];
            n.ptr[i] = hs.get(c);
            if (!n.leaf) replace((Node) c, hs);
        }
    }

    static int searchLte(Node n, long target) {
        final long[] k = n.keys;
        final int s = n.size;
        int i = 0;
        while (i + 1 < s && k[i + 1] <= target) i++;
        return i;
    }

    // One method per variant, so that each is compiled on its own.

    long lookupDirect(long target) {
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            Object c = n.ptr[i];
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupLockStamp(long target) {
        final long stamp = -accessClock;
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            int h = n.hashCode() + 13 * i;
            h = h < 0 ? -h : h;
            Object c;
            synchronized (LOCKS[h % 128]) {
                c = n.ptr[i];
                n.pos[i] = stamp;
            }
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupLock(long target) {
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            int h = n.hashCode() + 13 * i;
            h = h < 0 ? -h : h;
            Object c;
            synchronized (LOCKS[h % 128]) {
                c = n.ptr[i];
            }
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupStamp(long target) {
        final long stamp = -accessClock;
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            Object c = n.ptr[i];
            n.pos[i] = stamp;
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupHandle(long target) {
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            Object c = ((Handle) n.ptr[i]).obj;
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupHandleAcq(long target) {
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            Object c = OBJ.getAcquire((Handle) n.ptr[i]);
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupHandleClock(long target) {
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            Handle h = (Handle) n.ptr[i];
            Object c = OBJ.getAcquire(h);
            if (h.ref == 0) h.ref = 1;
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupHash(long target) {
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            Object c = map.get(n.pos[i]);
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long lookupChm(long target) {
        Node n = root;
        while (true) {
            int i = searchLte(n, target);
            Object c = chm.get(n.pos[i]);
            if (n.leaf) return ((Value) c).v;
            n = (Node) c;
        }
    }

    long run(int[] order) {
        long sum = 0;
        final long[] k = keys;
        switch (variant) {
        case "direct": for (int j : order) sum += lookupDirect(k[j]); break;
        case "lockstamp": for (int j : order) sum += lookupLockStamp(k[j]); break;
        case "lock": for (int j : order) sum += lookupLock(k[j]); break;
        case "stamp": for (int j : order) sum += lookupStamp(k[j]); break;
        case "handle": for (int j : order) sum += lookupHandle(k[j]); break;
        case "handleacq": for (int j : order) sum += lookupHandleAcq(k[j]); break;
        case "handleclock": for (int j : order) sum += lookupHandleClock(k[j]); break;
        case "hash": for (int j : order) sum += lookupHash(k[j]); break;
        case "chm": for (int j : order) sum += lookupChm(k[j]); break;
        default: throw new IllegalArgumentException(variant);
        }
        return sum;
    }

    static volatile long sink;

    public static void main(String[] args) throws Exception {
        if (args.length == 1 && args[0].equals("sizes")) {
            sizes();
            return;
        }
        String variant = args[0];
        int n = Integer.parseInt(args[1]);
        int threads = Integer.parseInt(args[2]);
        String layout = args.length > 3 ? args[3] : "before";
        if (!layout.equals("child") && !layout.equals("before") && !layout.equals("parent")
                && !layout.equals("scattered")) {
            throw new IllegalArgumentException("layout " + layout);
        }
        final IndirectionBench b = new IndirectionBench(variant, n, layout);
        System.gc();
        System.gc();
        final int perRound = n >= 1000000 ? 2000000 : 4000000;
        final int[][] orders = new int[threads][];
        for (int t = 0; t < threads; t++) {
            SplittableRandom rnd = new SplittableRandom(1000 + t);
            int[] o = new int[perRound];
            for (int i = 0; i < perRound; i++) o[i] = rnd.nextInt(b.keys.length);
            orders[t] = o;
        }
        final long[][] nanos = new long[threads][ROUNDS];
        Thread[] ts = new Thread[threads];
        final java.util.concurrent.CyclicBarrier barrier = new java.util.concurrent.CyclicBarrier(threads);
        for (int t = 0; t < threads; t++) {
            final int tt = t;
            ts[t] = new Thread(new Runnable() {
                public void run() {
                    try {
                        for (int r = 0; r < ROUNDS; r++) {
                            barrier.await();
                            long s = System.nanoTime();
                            sink += b.run(orders[tt]);
                            nanos[tt][r] = System.nanoTime() - s;
                        }
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                }
            });
            ts[t].start();
        }
        for (Thread t : ts) t.join();
        // Per round: the slowest thread's time gives the aggregate rate.
        double[] perLookup = new double[ROUNDS - WARMUP];
        double[] aggregate = new double[ROUNDS - WARMUP];
        for (int r = WARMUP; r < ROUNDS; r++) {
            long max = 0, total = 0;
            for (int t = 0; t < threads; t++) {
                max = Math.max(max, nanos[t][r]);
                total += nanos[t][r];
            }
            perLookup[r - WARMUP] = (double) total / threads / perRound;
            aggregate[r - WARMUP] = (double) perRound * threads / (max / 1e9);
        }
        double[] sorted = perLookup.clone();
        Arrays.sort(sorted);
        double[] agg = aggregate.clone();
        Arrays.sort(agg);
        System.out.printf("%-12s keys %9d threads %d layout %-9s depth %d  ns/lookup median %7.1f best %7.1f  lookups/s %6.2f M%n",
                variant, b.keys.length, threads, b.usesHandles() ? layout : "-", b.depth + 1,
                sorted[sorted.length / 2], sorted[0], agg[agg.length / 2] / 1e6);
    }

    /** The heap size of the objects, by allocating many and measuring the heap. */
    static void sizes() {
        final int count = 4000000;
        System.out.printf("Handle (obj, pos, ref): %.1f bytes%n", measure(count, new java.util.function.IntFunction<Object>() {
            public Object apply(int i) { return new Handle(null); }
        }));
        System.out.printf("Value (v, id): %.1f bytes%n", measure(count, new java.util.function.IntFunction<Object>() {
            public Object apply(int i) { return new Value(i, i); }
        }));
        System.out.printf("Node, 30 slots, with ptr: %.1f bytes%n", measure(count / 20, new java.util.function.IntFunction<Object>() {
            public Object apply(int i) { return new Node(true, i, true); }
        }));
        System.out.printf("byte[8]: %.1f bytes; byte[100]: %.1f bytes%n",
                measure(count, new java.util.function.IntFunction<Object>() {
                    public Object apply(int i) { return new byte[8]; }
                }), measure(count / 4, new java.util.function.IntFunction<Object>() {
                    public Object apply(int i) { return new byte[100]; }
                }));
    }

    static double measure(int count, java.util.function.IntFunction<Object> f) {
        Object[] keep = new Object[count];
        long before = used();
        for (int i = 0; i < count; i++) keep[i] = f.apply(i);
        long after = used();
        sink += keep.length;
        return (double) (after - before) / count;
    }

    static long used() {
        for (int i = 0; i < 3; i++) System.gc();
        Runtime rt = Runtime.getRuntime();
        return rt.totalMemory() - rt.freeMemory();
    }
}
