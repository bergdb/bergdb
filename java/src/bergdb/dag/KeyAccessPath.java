package bergdb.dag;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Access path through the key nodes of the DB graph to access a certain KV.
 * Specialized, fast data structure. No repeated memory allocation, it is reused between
 * transactions in the DB object.
 */
public final class KeyAccessPath {
    int size;
    long[] klongs;
    KeyNode[] nodes;
    
    /**
     * The high-water mark: the number of entries of nodes that add() may have set since 
     * the last clear(), also through clearFast() and later adds. clear() nulls only these, 
     * not the whole array, whose length is that of the longest path ever followed
     * (bergdb 021-25, section Fix (c)).
     */
    private int used;
    
    public KeyAccessPath() {
        klongs = new long[16];
        nodes = new KeyNode[16];
    }
    
    /**
     * Sets size to 0. Memory leak warning: node references not set to null.
     */
    public final void clearFast() {
        size = 0;
    }
    
    /**
     * Sets depth to 0 and references to null; compare to clearFast, this method
     * avoids memory leaks. It nulls the entries below the high-water mark, every
     * entry set since the last clear().
     */
    public void clear() {
        final KeyNode[] nodes = this.nodes;
        final int used = this.used;
        for (int i = 0; i < used; i++) {
            nodes[i] = null;
        }
        this.used = 0;
        size = 0;
    }
    
    public final long getKlong(int index) {
        assert index < size;
        return klongs[index];
    }
    
    public final KeyNode get(int index) {
        assert index < size : "index=" + index + ", size=" + size;
        return nodes[index];
    }
    
    /**
     * Adds a node and what klong in parent that was used to get the node.
     * The first call to this method should be: add(Klong.NULL, spaceRootNode);.
     */
    public final void add(long klong, KeyNode node) {
        size++;
        if (klongs.length < size) {
            enlargeArrays();
        }
        klongs[size - 1] = klong;
        nodes[size - 1] = node;
        if (used < size) {
            used = size;
        }
    }
    
    private void enlargeArrays() {
        assert klongs.length == nodes.length : klongs.length + " != " + nodes.length;
        
        int size = klongs.length;
        int newSize = size + size * 3 / 5;      // floor(1.6 size), in integers (bergdb 005-79)
        
        long[] newKlongs = new long[newSize];
        System.arraycopy(klongs, 0, newKlongs, 0, size);
        klongs = newKlongs;
        
        KeyNode[] newNodes = new KeyNode[newSize];
        System.arraycopy(nodes, 0, newNodes, 0, size);
        nodes = newNodes;
    }
    
    
    // ==== Tests ====
    
    private static void assertNoNodes(KeyAccessPath p) {
        Assert.assertEquals(0, p.size);
        for (int i = 0; i < p.nodes.length; i++) {
            Assert.assertTrue("nodes[" + i + "] after clear()", p.nodes[i] == null);
        }
    }
    
    private static void addNodes(KeyAccessPath p, int count) {
        for (int i = 0; i < count; i++) {
            KeyNode node = new KeyNode();
            p.add(Klong.NULL, node);
            Assert.assertTrue(p.get(p.size - 1) == node);
        }
    }
    
    @Nano
    public static void testClearNullsTheNodes() {
        KeyAccessPath p = new KeyAccessPath();
        addNodes(p, 5);
        p.clear();
        assertNoNodes(p);
        
        addNodes(p, 3);
        p.clear();
        assertNoNodes(p);
        
        p.clear();
        assertNoNodes(p);
    }
    
    /**
     * Entries left by clearFast() before later, shorter paths: clear() nulls them too.
     */
    @Nano
    public static void testClearAfterClearFast() {
        KeyAccessPath p = new KeyAccessPath();
        addNodes(p, 6);
        p.clearFast();
        addNodes(p, 2);
        p.clearFast();
        addNodes(p, 4);
        Assert.assertEquals(4, p.size);
        p.clearFast();
        p.clear();
        assertNoNodes(p);
        
        addNodes(p, 1);
        p.clearFast();
        p.clear();
        assertNoNodes(p);
    }
    
    /**
     * Longer paths than the arrays' first length, after clearFast() too: clear() nulls 
     * the copied entries and the new ones, and a later shorter path's leftovers.
     */
    @Nano
    public static void testClearAfterEnlargement() {
        KeyAccessPath p = new KeyAccessPath();
        final int firstLength = p.nodes.length;
        addNodes(p, firstLength + 4);
        Assert.assertTrue(p.nodes.length > firstLength);
        p.clearFast();
        addNodes(p, 3 * firstLength);
        Assert.assertEquals(3 * firstLength, p.size);
        Assert.assertTrue(p.nodes.length >= 3 * firstLength);
        p.clearFast();
        addNodes(p, 2);
        p.clear();
        assertNoNodes(p);
        
        addNodes(p, 2 * firstLength);
        p.clearFast();
        addNodes(p, 1);
        p.clear();
        assertNoNodes(p);
    }
}
