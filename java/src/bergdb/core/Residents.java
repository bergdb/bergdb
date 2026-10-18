package bergdb.core;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

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
 * registry and the pins (bergdb item 001, WP J1; docs/level4-alignment.md, 5.2 and 6.2,
 * row 7; docs/level4-plan.md, 4.1 and 4.2). There is no eviction yet: nothing is released.
 *
 * <p><b>Resident objects</b> are the node objects the database holds: the canonical objects
 * (the node table's, Cache3), the snapshots that slots of resident objects name (versions
 * read for lookups at earlier times), and the values. Objects read for one operation only
 * (not cached, `OpData.cachePolicy`) are not resident. {@link #walk} finds them all, from
 * the roots: the super root, the node table and D.</p>
 *
 * <p><b>Accounting</b> (M40): an estimate of the bytes of the resident objects
 * (`Node.getMemSize()`), advanced when an object becomes resident (a node the writer
 * makes, a version read and put into a slot, an object made by startup), when a canonical
 * object grows (when it is written, by its size then), and, from J3 on, when an object is
 * released. A snapshot that a slot no longer names, and that the garbage collector frees,
 * stays counted until it is released (J3): the estimate is an upper bound.</p>
 *
 * <p><b>Pins</b> (the model's `Mem.pinned`, lean/SIS/Evict.lean): the objects that eviction
 * must keep: the canonical objects of the nodes of D (TransSeq; dirty), those of the record
 * being written (TransNodes; their dirty flags are cleared before the record is appended, so
 * "not dirty" is not "written"), and the super root, which the model's root object stands
 * for. The objects of an operation in progress are pinned too; between transactions there
 * are none. See {@link #isPinned}.</p>
 *
 * <p>Synch note: the counters are atomic: the writer advances them under Db.writeLock, and
 * readers that put a version into a slot under that slot's pointer lock. The size counted
 * for a canonical object is in its field `countedMemSize` (KeyNode, TopNode), written by the
 * writer or under the node table's lock.</p>
 */
public final class Residents {
    private final AtomicLong canonicalBytes = new AtomicLong();
    private final AtomicLong snapshotBytes = new AtomicLong();
    private final AtomicLong valueBytes = new AtomicLong();
    private final AtomicLong canonicalCount = new AtomicLong();
    private final AtomicLong snapshotCount = new AtomicLong();
    private final AtomicLong valueCount = new AtomicLong();

    /** The size a canonical index object was counted with (its countedMemSize field), 0 if none. */
    private static int counted(Node node) {
        if (node instanceof KeyNode) return ((KeyNode) node).countedMemSize;
        if (node instanceof TopNode) return ((TopNode) node).countedMemSize;
        return 0;
    }

    private static void setCounted(Node node, int size) {
        if (node instanceof KeyNode) ((KeyNode) node).countedMemSize = size;
        else if (node instanceof TopNode) ((TopNode) node).countedMemSize = size;
    }

    /** A node became resident: made by the writer or by startup, or read and put into a slot. */
    public void added(Node node) {
        int size = node.getMemSize();
        if (!node.isIndexNode()) {
            valueBytes.addAndGet(size);
            valueCount.incrementAndGet();
        } else if (node.isCanonical()) {
            if (counted(node) == 0) {
                setCounted(node, size);
                canonicalBytes.addAndGet(size);
                canonicalCount.incrementAndGet();
            }
        } else {
            snapshotBytes.addAndGet(size);
            snapshotCount.incrementAndGet();
        }
    }

    /**
     * A snapshot became canonical (the writer's follow, Cache3.makeCanonical): its bytes move
     * from the snapshots to the canonical objects.
     */
    public void promoted(Node node) {
        if (counted(node) != 0) return;
        int size = node.getMemSize();
        setCounted(node, size);
        canonicalBytes.addAndGet(size);
        canonicalCount.incrementAndGet();
        if (snapshotCount.get() > 0) {
            snapshotBytes.addAndGet(-size);
            snapshotCount.decrementAndGet();
        }
    }

    /** A canonical index object may have grown: it is counted with its size now. */
    public void grown(Node node) {
        int old = counted(node);
        if (old == 0) return;
        int size = node.getMemSize();
        if (size != old) {
            setCounted(node, size);
            canonicalBytes.addAndGet(size - old);
        }
    }

    /** The estimated bytes of the resident objects. */
    public long bytes() {
        return canonicalBytes.get() + Math.max(0, snapshotBytes.get()) + valueBytes.get();
    }

    public String summary() {
        return "resident: " + bytes() + " bytes; canonical " + canonicalCount.get() + " objects, "
                + canonicalBytes.get() + " bytes; snapshots " + snapshotCount.get() + ", "
                + Math.max(0, snapshotBytes.get()) + " bytes; values " + valueCount.get() + ", "
                + valueBytes.get() + " bytes";
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
     * The resident objects, by identity: every object reachable through memory slots from
     * the roots, the super root, the node table's objects and D's. For the audit (and the
     * sweeps of J2 on): it visits every resident slot once. The caller holds Db.writeLock.
     */
    public static Set<Node> walk(TopNode superRoot, Iterable<Node> tableObjects, Iterable<Node> dObjects) {
        Set<Node> seen = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        ArrayDeque<Node> todo = new ArrayDeque<Node>();
        if (superRoot != null) todo.add(superRoot);
        for (Node n : tableObjects) todo.add(n);
        for (Node n : dObjects) todo.add(n);
        while (!todo.isEmpty()) {
            Node x = todo.poll();
            if (!seen.add(x)) continue;
            if (x instanceof TopNode) {
                TopNode t = (TopNode) x;
                if (t.rootPointer != null) todo.add(t.rootPointer);
                for (TopNode z : t.pointers) if (z != null) todo.add(z);
            } else if (x instanceof KeyNode) {
                KeyNode k = (KeyNode) x;
                int size = k.size;
                for (int i = 0; i < size; i++) {
                    Node c = k.pointers[i];
                    if (c != null) todo.add(c);
                }
            }
        }
        return seen;
    }

    // ======== Tests ========

    /** Accounting: a canonical object, a snapshot that becomes canonical, growth, a value. */
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
        KeyNode s = KeyNode.nodeWithTime(6);            // a snapshot
        r.added(s);
        Assert.assertEquals(b1 + s.getMemSize(), r.bytes());
        s.setCanonical(true);
        r.promoted(s);                                  // its bytes move, the total stays
        Assert.assertEquals(b1 + s.getMemSize(), r.bytes());
        for (int i = 0; i < 10; i++) {
            k.addToEnd(Klong.createTime(10 + i), null, Spos.NULL);
        }
        r.grown(k);
        Assert.assertEquals((long) k.getMemSize() + s.getMemSize(), r.bytes());
        ValueNode v = new ValueNode(new byte[100]);
        r.added(v);
        Assert.assertEquals((long) k.getMemSize() + s.getMemSize() + v.getMemSize(), r.bytes());
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
