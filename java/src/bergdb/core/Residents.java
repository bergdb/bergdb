package bergdb.core;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

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
 * (items/009-handles/02-implementation-plan.md, 4.7): each index object is counted with
 * its own bytes and those of the values its pointers hold (`Node.getMemSize()`), in its
 * field `countedMemSize` (KeyNode, TopNode; -1 if not counted, so that a count is never
 * taken for "not counted", bergdb 015-15): from when it enters a handle (added) until it
 * leaves it (released); again when the writer writes it, as it may have grown (grown); and
 * a value a reader puts into, or eviction takes from, a pointer of a counted object moves
 * that object's count (valueIn, valueOut). A value that two resident objects hold is
 * counted for each. Between the writer's changes to a canonical object and its write, the
 * object is counted with its size at the last count: the growth of its arrays and the
 * values the writer put into it are not counted until its write. It is pinned meanwhile
 * (D, or the record being written), and a batch of the capacity controller takes its
 * written values (Eviction.unswizzleValues), counted or not: so valueOut takes no more than
 * the count holds above the object's own bytes. The estimate does not drift: every byte
 * added is taken away with the object or the pointer it was added for, and no more; it is
 * exact but for the objects the writer changed since their last count, which it counts
 * below their bytes (bergdb 015-15). Before step 3b the estimate was made exact by walks of
 * the resident objects after each sweep (resync, which the audit and the test schedules
 * still use).</p>
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
     * The bytes index object o is counted with now: its own, and for a key node those of the
     * values its pointers hold.
     */
    static int bytesOf(Node o) {
        int size = o.getMemSize();
        if (o instanceof KeyNode) {
            KeyNode k = (KeyNode) o;
            int n = k.size;
            for (int i = 0; i < n; i++) {
                Pointee p = k.pointers[i];
                if (p instanceof ValueNode) size += ((ValueNode) p).getMemSize();
            }
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

    /** A canonical index object may have grown (it was written): counted with its bytes now. */
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
     * Takes v's bytes from the holder's count, but not below the holder's own bytes
     * (getMemSize): v may not be counted, as a value the writer put into the holder is counted
     * from the holder's write (bergdb 015-15). Before, a batch's values could take a pinned
     * leaf's count to 0, which then stayed.
     */
    public void valueOut(Node holder, ValueNode v) {
        int c = counted(holder);
        if (c < 0) return;
        int size = Math.min(v.getMemSize(), Math.max(0, c - holder.getMemSize()));
        if (size == 0) return;
        setCounted(holder, c - size);
        bytes.addAndGet(-size);
    }

    /**
     * Sets the estimate to the bytes of the resident objects 'objects' (a walk's), each index
     * object counted with its bytes now (bytesOf), values with their holders; for the test
     * schedules and the audit. The caller holds Db.writeLock, between transactions.
     */
    public void resync(Iterable<Node> objects) {
        long b = 0, n = 0;
        for (Node o : objects) {
            if (!o.isIndexNode()) continue;
            synchronized (o) {
                int size = bytesOf(o);
                setCounted(o, size);
                b += size;
                n++;
            }
        }
        bytes.set(b);
        this.objects.set(n);
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
     * Accounting (bergdb item 009, step 3b): an object counted once, with the values its
     * pointers hold; a version that becomes canonical; growth; a value in and out of a
     * pointer; a release takes the object's count away, values included.
     */
    @Nano
    public static void testAccounting() {
        Residents r = new Residents();
        KeyNode k = KeyNode.nodeWithTime(5);
        k.setCanonical(true);
        r.added(k);
        long b1 = r.bytes();
        Assert.assertEquals((long) k.getMemSize(), b1);
        r.added(k);                                     // counted once
        Assert.assertEquals(b1, r.bytes());
        KeyNode s = KeyNode.nodeWithTime(6);            // a version read
        r.added(s);
        Assert.assertEquals(b1 + s.getMemSize(), r.bytes());
        s.setCanonical(true);
        r.promoted(s);                                  // counted already
        Assert.assertEquals(b1 + s.getMemSize(), r.bytes());
        for (int i = 0; i < 10; i++) {
            k.addToEnd(Klong.createTime(10 + i), null, Spos.NULL);
        }
        r.grown(k);
        Assert.assertEquals((long) k.getMemSize() + s.getMemSize(), r.bytes());
        ValueNode v = new ValueNode(new byte[100]);
        r.added(v);                                     // a value alone: not counted
        Assert.assertEquals((long) k.getMemSize() + s.getMemSize(), r.bytes());
        synchronized (s) {
            r.valueIn(s, v);
        }
        Assert.assertEquals((long) k.getMemSize() + s.getMemSize() + v.getMemSize(), r.bytes());
        synchronized (s) {
            r.valueOut(s, v);
        }
        Assert.assertEquals((long) k.getMemSize() + s.getMemSize(), r.bytes());
        synchronized (s) {
            r.valueIn(s, v);
        }
        Assert.assertEquals((long) s.getMemSize() + v.getMemSize(), (long) r.released(s));
        Assert.assertEquals((long) k.getMemSize(), r.bytes());
        Assert.assertEquals(0, r.released(s));          // released once
    }

    /**
     * Counted apart from the size (bergdb 015-15): an object is not counted (-1) until it
     * enters a handle; a batch that takes a value a reader loaded and one the writer put in
     * (not counted) takes the count down to the object's own bytes, no further; a count of 0
     * is a count, which valueIn and the object's write (grown) raise; a release takes the
     * object counter back, once.
     */
    @Nano
    public static void testCountedApartFromSize() {
        Residents r = new Residents();
        KeyNode k = KeyNode.nodeWithTime(5);
        k.setCanonical(true);
        k.addToEnd(Klong.createKey(new byte[] {1}), null, 300);    // a stream pointer
        Assert.assertEquals(-1, counted(k));
        r.added(k);
        Assert.assertEquals(k.getMemSize(), counted(k));
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
        Assert.assertEquals(k.getMemSize(), counted(k));
        Assert.assertEquals((long) k.getMemSize(), r.bytes());
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
}
