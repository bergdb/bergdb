package bergdb.core;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Locks for synchronizing node pointer access.
 * 
 * @author Frans Lundberg
 */
public class PointerLocks {
    private static final int POINTER_LOCK_COUNT = 128;
    
    private final Lock[] locks;
    
    public PointerLocks() {
        locks = new Lock[POINTER_LOCK_COUNT];
        for (int i = 0; i < POINTER_LOCK_COUNT; i++) {
            locks[i] = new Lock();
        }
    }
    
    /**
     * Returns a lock for the pointerIndex'th pointer of node 'node'.
     */
    public final Object getLock(final Node node, final int pointerIndex) {
        int value = node.hashCode() + 13 * pointerIndex;
        value = (value < 0) ? -value : value;
        return locks[value % POINTER_LOCK_COUNT];
    }

    /**
     * Special class for pointer lock object. 
     * Using a special class rather then Object can be useful 
     * when debugging. 
     */
    public static class Lock {}
    
    
    // ======== Tests ========
    
    @Nano private static void test1() {
        PointerLocks p = new PointerLocks();
        ValueNode node = new ValueNode(new byte[0]);
        Assert.assertTrue(p.getLock(node, 1) != p.getLock(node, 2));
    }
    
    @Nano private static void test2() {
        PointerLocks p = new PointerLocks();
        ValueNode node = new ValueNode(new byte[0]);
        Assert.assertTrue(p.getLock(node, 3) == p.getLock(node, 3));
    }
}
