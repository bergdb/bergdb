package bergdb.core;

import bergdb.coreds.KeyNode;

/**
 * Access path through the key nodes of the DB graph to access a certain KV.
 * Specialized, fast data structure. No repeated memory allocation, it is reused between
 * transactions in the DB object.
 */
public final class KeyAccessPath {
    int size;
    long[] klongs;
    KeyNode[] nodes;
    
    public KeyAccessPath() {
        klongs = new long[16];
        nodes = new KeyNode[16];
    }
    
    public final int getSize() {
        return size;
    }
    
    /**
     * Sets size to 0. Memory leak warning: node references not set to null.
     */
    public final void clearFast() {
        size = 0;
    }
    
    /**
     * Sets depth to 0 and references to null.
     */
    public void clear() {
        final int length = nodes.length;
        for (int i = 0; i < length; i++) {
            nodes[i] = null;
        }
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
     * Adds a node and what klong in parent that was used to get to the
     * node.
     */
    public final void add(long klong, KeyNode node) {
        size++;
        if (klongs.length < size) {
            enlargeArrays();
        }
        klongs[size - 1] = klong;
        nodes[size - 1] = node;
    }
    
    private void enlargeArrays() {
        assert klongs.length == nodes.length : klongs.length + " != " + nodes.length;
        
        int size = klongs.length;
        int newSize = (int) (size * 1.6);
        
        long[] newKlongs = new long[newSize];
        System.arraycopy(klongs, 0, newKlongs, 0, size);
        klongs = newKlongs;
        
        KeyNode[] newNodes = new KeyNode[newSize];
        System.arraycopy(nodes, 0, newNodes, 0, size);
        nodes = newNodes;
    }
}
