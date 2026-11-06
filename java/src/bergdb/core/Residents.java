package bergdb.core;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.dag.Handle;
import bergdb.dag.Pointee;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * What the database holds in memory, its bytes, and what it must keep: the resident
 * registry and the pins (bergdb item 001, WP J1; bergdb 001-08, 5.2 and 6.2,
 * row 7; bergdb 011-05, 4.1 and 4.2).
 *
 * <p><b>Resident objects</b> are the node objects the database holds: the objects of the
 * live handles (Cache3; canonical objects and versions read), and the values that pointers
 * of those objects hold. Objects read for one operation only (not cached,
 * `OpData.cachePolicy`) are not resident. {@link #walk} finds them all, from the roots: the
 * super root, the node table and D.</p>
 *
 * <p><b>Accounting</b>, without walks since bergdb item 009, step 3b
 * (items/009-handles/02-implementation-plan.md, 4.7): each index object is counted with its own
 * bytes (`Node.getMemSize()`), its live handle with the handle's entry in the node table, the
 * handles its pointers hold, and the values they hold (bytesOf; the handles since bergdb
 * 015-13), in its field `countedMemSize` (KeyNode, TopNode; -1 if not counted, so that a count
 * is never taken for "not counted", bergdb 015-15): from when it enters a handle (added) until
 * it leaves it (released); again when the writer writes it, as it may have grown, or replaces
 * it in the transaction that changed it (grown; bergdb 019-20), and after a start's rerun of the
 * transactions, which changes nodes of the startup section (resync; bergdb 019-21); and a
 * handle that a follow, or the start's linkD, puts into a pointer that held none (R5's F4 of
 * night 006-12), and a value a reader puts into, or
 * eviction takes from, a pointer of a counted object move that object's count (handleIn,
 * valueIn, valueOut). A dead handle stays counted in the pointers that hold it. A handle or a
 * value that two resident objects hold is counted for each, and a live handle that a pointer
 * holds also with its object's entry: an upper bound (009-02, 4.7). Between the writer's
 * changes to a canonical object and its write, the object is counted with its size at the last
 * count: the growth of its arrays and the pointers the writer added to it, with their values
 * and handles, are not counted until its write. It is pinned meanwhile (D, or the record being
 * written), and a batch of the capacity controller takes its written values
 * (Eviction.unswizzleValues), counted or not: so valueOut takes no more than the count holds
 * above the object's own bytes and its entry. The estimate does not drift: every byte added is
 * taken away with the object or the pointer it was added for, and no more; it is exact but for
 * the objects the writer changed since their last count, which it counts below their bytes
 * (bergdb 015-15). Before step 3b the estimate was made exact by walks of the resident objects
 * after each sweep (resync, which the test schedules still use, since bergdb 015-69 by
 * differences).</p>
 *
 * <p><b>Pins</b> (the model's `HMem.pinned`, lean/SIS/Handle.lean): the objects that eviction
 * must keep: the canonical objects of the nodes of D (TransSeq; dirty), those of the record
 * being written (TransNodes; their dirty flags are cleared before the record is appended, so
 * "not dirty" is not "written"), and the super root, which the model's root object stands
 * for. The objects of an operation in progress are pinned too; between transactions there
 * are none. See {@link #isPinned}.</p>
 *
 * <p>Synch note: the total is atomic. An object's countedMemSize is read and written under
 * the object's monitor, which a reader that puts a value into one of its pointers also
 * holds (KeyNode.setPointee), so that a count and an eviction of the object do not cross.</p>
 */
public final class Residents {
    private final AtomicLong bytes = new AtomicLong();
    private final AtomicLong objects = new AtomicLong();

    /** The bytes an index object is counted with, 0 if none; for eviction's pinned bytes. */
    static int countedBytes(Node node) {
        return Math.max(0, counted(node));
    }

    /**
     * The size an index object was counted with (its countedMemSize field), -1 if it is not
     * counted (bergdb 015-15: 0 before, which valueOut could reach for a counted object).
     */
    static int counted(Node node) {
        if (node instanceof KeyNode) return ((KeyNode) node).countedMemSize;
        if (node instanceof TopNode) return ((TopNode) node).countedMemSize;
        return -1;
    }

    private static void setCounted(Node node, int size) {
        if (node instanceof KeyNode) ((KeyNode) node).countedMemSize = size;
        else if (node instanceof TopNode) ((TopNode) node).countedMemSize = size;
    }

    /**
     * The bytes of a live handle with its entry in the node table, counted with the handle's
     * object (009-02, 4.7 and T1a: the handle, the HashMap's entry and its Long key; with JDK
     * 27's compact headers and compressed oops; bergdb 015-13).
     */
    static final int ENTRY_BYTES = 79;

    /**
     * The bytes of a handle, counted for each pointer of an index object that holds one,
     * live or dead (009-02, 4.7; bergdb 015-13): an upper bound, as a handle that several
     * pointers hold, or that the table holds too, is counted for each.
     */
    static final int HANDLE_BYTES = 32;

    /**
     * The bytes index object o is counted with now: its own, its live handle's entry
     * (ENTRY_BYTES), a handle's bytes for each of its pointers that holds a handle
     * (HANDLE_BYTES), and the bytes of the values its pointers hold (bergdb 015-13: before,
     * no handle was counted).
     */
    static int bytesOf(Node o) {
        int size = o.getMemSize() + ENTRY_BYTES;
        int n = o.getSize();
        for (int i = 0; i < n; i++) {
            Pointee p = o.getPointee(i);
            if (p instanceof Handle) size += HANDLE_BYTES;
            else if (p instanceof ValueNode) size += ((ValueNode) p).getMemSize();
        }
        return size;
    }

    /**
     * The bytes of bytesOf(o) without the values': o's own, its entry and the handles its
     * pointers hold (bergdb 015-13); valueOut's floor.
     */
    static int bytesWithoutValues(Node o) {
        int size = o.getMemSize() + ENTRY_BYTES;
        int n = o.getSize();
        for (int i = 0; i < n; i++) {
            if (o.getPointee(i) instanceof Handle) size += HANDLE_BYTES;
        }
        return size;
    }

    /**
     * An index object became resident: it entered a handle (made by the writer or by startup,
     * or a version read). Counted once. A value is counted with the objects that hold it.
     */
    public void added(Node node) {
        if (!node.isIndexNode()) return;
        synchronized (node) {
            if (counted(node) >= 0) return;
            int size = bytesOf(node);
            setCounted(node, size);
            bytes.addAndGet(size);
            objects.incrementAndGet();
        }
    }

    /** A version became canonical (Cache3.makeCanonical): counted already, or now. */
    public void promoted(Node node) {
        added(node);
    }

    /**
     * A canonical index object may have grown (it was written, or its transaction replaced it
     * after it changed it, bergdb 019-20): counted with its bytes now.
     */
    public void grown(Node node) {
        synchronized (node) {
            int old = counted(node);
            if (old < 0) return;
            int size = bytesOf(node);
            if (size != old) {
                setCounted(node, size);
                bytes.addAndGet(size - old);
            }
        }
    }

    /**
     * A resident index object left its handle (evicted, or replaced by a better object): its
     * count leaves the estimate. Returns the bytes it was counted with.
     */
    public int released(Node node) {
        if (!node.isIndexNode()) return 0;
        synchronized (node) {
            int size = counted(node);
            if (size < 0) return 0;
            setCounted(node, -1);
            bytes.addAndGet(-size);
            objects.decrementAndGet();
            return size;
        }
    }

    /**
     * A handle went into a pointer of 'holder' that held none (a follow's swizzle,
     * NodeCollection; a start's linkD, NodeCollection.linkToCanonical): the holder's count
     * takes the handle's bytes (bergdb 015-13). The caller holds the holder's monitor.
     * Nothing if the holder is not counted.
     */
    public void handleIn(Node holder) {
        int c = counted(holder);
        if (c < 0) return;
        setCounted(holder, c + HANDLE_BYTES);
        bytes.addAndGet(HANDLE_BYTES);
    }

    /**
     * Value v went into a pointer of 'holder' (a reader's load). The caller holds the
     * holder's monitor. Nothing if the holder is not counted (not resident).
     */
    public void valueIn(Node holder, ValueNode v) {
        int c = counted(holder);
        if (c < 0) return;
        int size = v.getMemSize();
        setCounted(holder, c + size);
        bytes.addAndGet(size);
    }

    /**
     * Value v left a pointer of 'holder' (eviction). The caller holds the holder's monitor.
     * Takes v's bytes from the holder's count, but not below the holder's bytes without its
     * values (bytesWithoutValues: its own, its entry and its handles, bergdb 015-13): v may
     * not be counted, as a value the writer put into the holder is counted from the holder's
     * write (bergdb 015-15). Before, a batch's values could take a pinned leaf's count to 0,
     * which then stayed.
     */
    public void valueOut(Node holder, ValueNode v) {
        int c = counted(holder);
        if (c < 0) return;
        int own = bytesWithoutValues(holder);
        int size = Math.min(v.getMemSize(), Math.max(0, c - own));
        if (size == 0) return;
        setCounted(holder, c - size);
        bytes.addAndGet(-size);
    }

    /**
     * Counts each index object of 'objects' (a walk's resident objects) that is counted with
     * its bytes now (bytesOf), values with their holders, and moves the total by the
     * difference, under the object's monitor; for the test schedules, and for a start after
     * its rerun of the transactions (DbStarter, bergdb 019-21). An object that is not
     * counted is skipped: it left its handle since the walk (released), or it is not
     * resident. The caller holds Db.writeLock, between transactions. Readers do not take that
     * lock: a load puts a value into an object, under the object's monitor (valueIn), before
     * or after the object's count here, and its bytes stay in the total either way. Until
     * bergdb 015-69 (016-06's R4-F4) the total was set to the sum of the walk's counts, and
     * so lost the bytes of a load into an object counted before the sum ended.
     */
    public void resync(Iterable<Node> objects) {
        for (Node o : objects) {
            if (!o.isIndexNode()) continue;
            synchronized (o) {
                int old = counted(o);
                if (old < 0) continue;
                int size = bytesOf(o);
                if (size != old) {
                    setCounted(o, size);
                    bytes.addAndGet(size - old);
                }
            }
        }
    }

    /** The estimated bytes of the resident objects. */
    public long bytes() {
        return bytes.get();
    }

    /** The resident index objects counted. */
    public long objects() {
        return objects.get();
    }

    /**
     * Object 'node' is pinned: eviction may neither unswizzle a slot that names it nor
     * release it. The canonical object of a node of D (dirty) or of the record being written,
     * or the super root. The caller holds Db.writeLock.
     */
    public static boolean isPinned(Node node, TopNode superRoot) {
        if (node == superRoot) return true;
        return node.isIndexNode() && node.isCanonical() && (node.isDirty() || node.isInTransNodes());
    }

    /**
     * The resident objects, each once, in the order a breadth-first walk meets them: every
     * object reachable through memory slots from the roots, the super root, the node table's
     * objects and D's. For the audit and the sweeps of eviction. The caller holds
     * Db.writeLock.
     */
    public static java.util.List<Node> walk(TopNode superRoot, Iterable<Node> tableObjects,
            Iterable<Node> dObjects) {
        Set<Node> seen = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        java.util.ArrayList<Node> order = new java.util.ArrayList<Node>();
        ArrayDeque<Node> todo = new ArrayDeque<Node>();
        if (superRoot != null) todo.add(superRoot);
        for (Node n : tableObjects) todo.add(n);
        for (Node n : dObjects) todo.add(n);
        while (!todo.isEmpty()) {
            Node x = todo.poll();
            if (!seen.add(x)) continue;
            order.add(x);
            if (x.isIndexNode()) {
                int size = x.getSize();
                for (int i = 0; i < size; i++) {
                    Node c = x.getPointerNode(i);
                    if (c != null) todo.add(c);
                }
            }
        }
        return order;
    }

    // ======== Tests ========

    /**
     * Accounting (bergdb item 009, step 3b): an object counted once, with its entry in the
     * node table and the values its pointers hold; a version that becomes canonical; growth;
     * a value in and out of a pointer; a release takes the object's count away, values
     * included.
     */
    @Nano
    public static void testAccounting() {
        Residents r = new Residents();
        final long e = ENTRY_BYTES;
        KeyNode k = KeyNode.nodeWithTime(5);
        k.setCanonical(true);
        r.added(k);
        long b1 = r.bytes();
        Assert.assertEquals(k.getMemSize() + e, b1);
        r.added(k);                                     // counted once
        Assert.assertEquals(b1, r.bytes());
        KeyNode s = KeyNode.nodeWithTime(6);            // a version read
        r.added(s);
        Assert.assertEquals(b1 + s.getMemSize() + e, r.bytes());
        s.setCanonical(true);
        r.promoted(s);                                  // counted already
        Assert.assertEquals(b1 + s.getMemSize() + e, r.bytes());
        for (int i = 0; i < 10; i++) {
            k.addToEnd(Klong.createTime(10 + i), null, Spos.NULL);
        }
        r.grown(k);
        Assert.assertEquals(k.getMemSize() + s.getMemSize() + 2 * e, r.bytes());
        ValueNode v = new ValueNode(new byte[100]);
        r.added(v);                                     // a value alone: not counted
        Assert.assertEquals(k.getMemSize() + s.getMemSize() + 2 * e, r.bytes());
        synchronized (s) {
            r.valueIn(s, v);
        }
        Assert.assertEquals(k.getMemSize() + s.getMemSize() + 2 * e + v.getMemSize(), r.bytes());
        synchronized (s) {
            r.valueOut(s, v);
        }
        Assert.assertEquals(k.getMemSize() + s.getMemSize() + 2 * e, r.bytes());
        synchronized (s) {
            r.valueIn(s, v);
        }
        Assert.assertEquals(s.getMemSize() + e + v.getMemSize(), (long) r.released(s));
        Assert.assertEquals(k.getMemSize() + e, r.bytes());
        Assert.assertEquals(0, r.released(s));          // released once
    }

    /**
     * Handles counted (bergdb 015-13; 009-02, 4.7): an index object with its entry in the
     * node table (ENTRY_BYTES) and a handle's bytes (HANDLE_BYTES) for each pointer that
     * holds one, live or dead; a follow's swizzle into a pointer that held none adds them
     * (handleIn), one that replaces a handle by another adds nothing; a value's pointer not.
     */
    @Nano
    public static void testHandlesCounted() {
        Residents r = new Residents();
        KeyNode child = KeyNode.nodeWithTime(4);
        KeyNode k = KeyNode.nodeWithTime(5);
        k.setCanonical(true);
        k.addToEnd(Klong.createKey(new byte[] {1}), null, 300);    // a stream pointer
        k.addToEnd(Klong.createKey(new byte[] {2}), null, 400);
        r.added(k);
        int own = k.getMemSize() + ENTRY_BYTES;
        Assert.assertEquals(own, counted(k));
        Handle h = Handle.of(child);
        synchronized (k) {                                  // a follow's swizzle
            k.setPointee(1, h);
            r.handleIn(k);
        }
        Assert.assertEquals(own + HANDLE_BYTES, counted(k));
        Assert.assertEquals(bytesOf(k), counted(k));
        Assert.assertEquals(own + HANDLE_BYTES, bytesWithoutValues(k));
        k.setPointee(1, new Handle(child.getId()));         // a dead handle resolved again
        Assert.assertEquals(bytesOf(k), counted(k));
        ValueNode v = new ValueNode(new byte[100], 400);
        synchronized (k) {
            k.setPointee(2, v);
            r.valueIn(k, v);
        }
        Assert.assertEquals(own + HANDLE_BYTES + v.getMemSize(), counted(k));
        Assert.assertEquals(bytesOf(k), counted(k));
        synchronized (k) {                                  // a batch takes the value
            k.setPointer(2, null, 400);
            r.valueOut(k, v);
        }
        Assert.assertEquals(own + HANDLE_BYTES, counted(k));
        Assert.assertEquals((long) own + HANDLE_BYTES, r.bytes());
        Assert.assertEquals(own + HANDLE_BYTES, r.released(k));
        Assert.assertEquals(0L, r.bytes());
    }

    /**
     * Counted apart from the size (bergdb 015-15): an object is not counted (-1) until it
     * enters a handle; a batch that takes a value a reader loaded and one the writer put in
     * (not counted) takes the count down to the object's own bytes and its entry in the node
     * table (bergdb 015-13), no further; a count of 0 is a count, which valueIn and the
     * object's write (grown) raise; a release takes the object counter back, once.
     */
    @Nano
    public static void testCountedApartFromSize() {
        Residents r = new Residents();
        KeyNode k = KeyNode.nodeWithTime(5);
        k.setCanonical(true);
        k.addToEnd(Klong.createKey(new byte[] {1}), null, 300);    // a stream pointer
        Assert.assertEquals(-1, counted(k));
        r.added(k);
        Assert.assertEquals(k.getMemSize() + ENTRY_BYTES, counted(k));
        ValueNode v = new ValueNode(new byte[200], 300);
        synchronized (k) {                                  // a reader's load: counted
            k.setPointee(1, v);
            r.valueIn(k, v);
        }
        Assert.assertEquals(bytesOf(k), counted(k));
        ValueNode w = new ValueNode(new byte[100], 400);
        k.addToEnd(Klong.createKey(new byte[] {2}), w, 400);    // the writer's: not counted
        Assert.assertTrue(counted(k) < bytesOf(k));
        synchronized (k) {                                  // a batch takes both
            k.setPointer(1, null, 300);
            r.valueOut(k, v);
            k.setPointer(2, null, 400);
            r.valueOut(k, w);
        }
        Assert.assertEquals(k.getMemSize() + ENTRY_BYTES, counted(k));
        Assert.assertEquals((long) k.getMemSize() + ENTRY_BYTES, r.bytes());
        k.countedMemSize = 0;                               // a count of 0 is a count
        r.bytes.set(0);
        synchronized (k) {
            k.setPointee(1, v);
            r.valueIn(k, v);
        }
        Assert.assertEquals(v.getMemSize(), counted(k));
        r.grown(k);
        Assert.assertEquals(bytesOf(k), counted(k));
        Assert.assertEquals((long) bytesOf(k), r.bytes());
        r.added(k);                                         // counted once
        Assert.assertEquals(1L, r.objects());
        Assert.assertEquals(bytesOf(k), r.released(k));
        Assert.assertEquals(-1, counted(k));
        Assert.assertEquals(0L, r.objects());
        Assert.assertEquals(0L, r.bytes());
        Assert.assertEquals(0, r.released(k));              // released once
        Assert.assertEquals(0L, r.objects());
    }

    /**
     * A resync (the test schedules) while a reader loads a value (bergdb 015-69, 016-06's
     * R4-F4): the reader does not take the write lock that the resync's caller holds, and
     * puts a value into an object that the resync has counted, under the object's monitor,
     * while the resync waits for the monitor of the next. The reader's bytes stay in the
     * total: once every object is released, the total is 0. Until 015-69 the resync set the
     * total to its own sum when it ended, which did not have them: -156 here.
     */
    @Nano
    public static void testResyncWithConcurrentLoad() throws InterruptedException {
        final Residents r = new Residents();
        final KeyNode holder = KeyNode.nodeWithTime(10);
        holder.addToEnd(Klong.createKey(new byte[] {1}), null, 1000);  // a stream pointer
        final KeyNode last = KeyNode.nodeWithTime(10);
        r.added(holder);
        r.added(last);
        ValueNode v = new ValueNode(new byte[100], 1000);
        final Throwable[] problem = new Throwable[1];
        Thread resync = new Thread(new Runnable() {
            public void run() {
                try {
                    r.resync(java.util.Arrays.<Node>asList(holder, last));
                } catch (Throwable x) {
                    problem[0] = x;
                }
            }
        }, "resync");
        synchronized (last) {
            resync.start();
            long end = System.nanoTime() + 5000L * 1000 * 1000;
            while (resync.getState() != Thread.State.BLOCKED && System.nanoTime() < end) {
                Thread.yield();
            }
            Assert.assertEquals(Thread.State.BLOCKED, resync.getState());  // at last's monitor
            synchronized (holder) {                         // a reader's load
                holder.setPointee(1, v);
                r.valueIn(holder, v);
            }
        }
        resync.join(5000);
        Assert.assertFalse(resync.isAlive());
        Assert.assertTrue("resync threw " + problem[0], problem[0] == null);
        Assert.assertEquals((long) counted(holder) + counted(last), r.bytes());
        Assert.assertEquals(bytesOf(holder), counted(holder));
        r.released(holder);
        r.released(last);
        Assert.assertEquals(0L, r.bytes());
        Assert.assertEquals(0L, r.objects());
    }

    /** Pins: the super root, and the canonical objects of D and of the record being written. */
    @Nano
    public static void testPinned() {
        KeyNode k = KeyNode.nodeWithTime(5);
        TopNode top = new TopNode(0, k, Spos.NULL, 5, Spos.NULL);
        Assert.assertTrue(isPinned(top, top));
        Assert.assertFalse(isPinned(k, top));
        k.setDirty(true);
        Assert.assertFalse(isPinned(k, top));           // a dirty snapshot: not D's object
        k.setCanonical(true);
        Assert.assertTrue(isPinned(k, top));
        k.setDirty(false);
        Assert.assertFalse(isPinned(k, top));
        k.setIsInTransNodes(true);
        Assert.assertTrue(isPinned(k, top));
    }

    /**
     * The first object of a live handle of db that is clean and not counted with its bytes
     * now (bytesOf), as a line of text; null if none. The writer's changes to a dirty object
     * are counted at its write (the class comment), so dirty objects are not checked. The
     * caller holds db's write lock, with no reader in a get.
     */
    static String misCounted(Db db) {
        return misCounted(db, false);
    }

    /**
     * As misCounted(db), and with 'dirty', the dirty objects too: for a database just
     * started, whose dirty objects (D, linked by DbStarter.linkD) the start counts with
     * their bytes (bergdb 019-21; R5's F4 of night 006-12).
     */
    static String misCounted(Db db, boolean dirty) {
        for (Node o : db.internal().cache().nodes()) {
            if (o.isDirty() && !dirty) continue;
            int c = counted(o);
            if (c >= 0 && c != bytesOf(o)) {
                return "the " + (o.isDirty() ? "dirty" : "clean") + " object of node "
                        + o.getId() + " is counted with " + c + " bytes, its bytes now "
                        + bytesOf(o);
            }
        }
        return null;
    }

    /**
     * A key node that a transaction changes and then replaces is counted with its bytes
     * after the transaction (bergdb 019-20; found by harness 6.5, 018-05): transactions of
     * three keys of 50, nodes of at most 8 entries. The writer adds a key to a written leaf
     * (KeyNode.addKlong grows its arrays), a later key of the transaction finds it full and
     * replaces it (Dag.handleFullNode), and toPreviousState cuts it back to its written
     * version; the transaction's end makes it clean again (Db.endOfTrans). Until 019-20 it
     * stayed counted with its bytes of before the growth, below its bytes, until it was
     * evicted: after transaction 10, 747 bytes against 939.
     */
    @Nano
    public static void testReplacedNodeCounted() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(new bergdb.stream.MemoryStream()).clock(clock).testId()
                .maxNodeSize8().startupDistance(200).audit(0).start();
        try {
            java.util.Random rnd = new java.util.Random(1);
            long time = 100 * STEP;
            for (int i = 0; i < 200; i++) {
                clock.setTime(time += STEP);
                Trans.Builder b = db.trans();
                java.util.TreeSet<Integer> keys = new java.util.TreeSet<Integer>();
                for (int j = 0; j < 3; j++) keys.add(rnd.nextInt(50));
                for (int k : keys) b.put("k" + k, "v" + i + "x".repeat(rnd.nextInt(100)));
                db.execute(b.build());
                synchronized (db.internal().getWriteLock()) {
                    String m = misCounted(db);
                    Assert.assertTrue("after transaction " + i + ": " + m, m == null);
                }
            }
        } finally {
            db.close();
        }
    }

    /**
     * A start counts the nodes of the startup section with their bytes after its rerun of
     * the transactions (bergdb 019-21; found by harness 6.5, 018-05): the rerun
     * (DbStarter.rerunTransactions) adds klongs to nodes that registerSectionNodes counted
     * before it: 20 transactions of three keys of 50, a startup distance of 3,000 bytes.
     * Until 019-21 they stayed counted below their bytes: 303 bytes against 362.
     */
    @Nano
    public static void testSectionNodesCountedAfterRerun() {
        CoreTestClock clock = new CoreTestClock();
        bergdb.stream.MemoryStream s = new bergdb.stream.MemoryStream();
        Db db0 = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                .startupDistance(3000).audit(0).start();
        long time = 100 * STEP;
        try {
            java.util.Random rnd = new java.util.Random(1);
            for (int i = 0; i < 20; i++) {
                clock.setTime(time += STEP);
                Trans.Builder b = db0.trans();
                java.util.TreeSet<Integer> keys = new java.util.TreeSet<Integer>();
                for (int j = 0; j < 3; j++) keys.add(rnd.nextInt(50));
                for (int k : keys) b.put("k" + k, "v" + i);
                db0.execute(b.build());
            }
        } finally {
            db0.close();
        }
        Db db = Db.builder().testSetup(s.copy()).clock(clock).testId().maxNodeSize8()
                .startupDistance(3000).audit(0).start();
        try {
            synchronized (db.internal().getWriteLock()) {
                String m = misCounted(db);
                Assert.assertTrue("after the start: " + m, m == null);
            }
        } finally {
            db.close();
        }
    }

    /**
     * A start counts the handles that linkD puts into the pointers of D's objects (bergdb
     * 019-21, R5's F4 of night 006-12): 400 transactions of three keys of 500, a startup
     * distance of 30,000 bytes, a restart; then every object of a live handle, dirty ones
     * included, is counted with its bytes now. Until the fix, the start's recount (019-21) ran
     * before linkD, whose links (NodeCollection.linkToCanonical) were not counted: in a
     * database opened for reads, D's objects stayed 32 bytes (HANDLE_BYTES) a linked pointer
     * below their bytes.
     */
    @Nano
    public static void testLinkedHandlesCountedAtStart() {
        CoreTestClock clock = new CoreTestClock();
        bergdb.stream.MemoryStream s = new bergdb.stream.MemoryStream();
        Db db0 = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                .startupDistance(30000).audit(0).start();
        long time = 100 * STEP;
        try {
            java.util.Random rnd = new java.util.Random(1);
            for (int i = 0; i < 400; i++) {
                clock.setTime(time += STEP);
                Trans.Builder b = db0.trans();
                java.util.TreeSet<Integer> keys = new java.util.TreeSet<Integer>();
                for (int j = 0; j < 3; j++) keys.add(rnd.nextInt(500));
                for (int k : keys) b.put("k" + k, "v" + i);
                db0.execute(b.build());
            }
        } finally {
            db0.close();
        }
        Db db = Db.builder().testSetup(s.copy()).clock(clock).testId().maxNodeSize8()
                .startupDistance(30000).audit(0).start();
        try {
            synchronized (db.internal().getWriteLock()) {
                String m = misCounted(db, true);
                Assert.assertTrue("after the start: " + m, m == null);
            }
        } finally {
            db.close();
        }
    }

    private static final long STEP = bergdb.pub.util.Clock.UNITS_PER_SEC / 100;
}
