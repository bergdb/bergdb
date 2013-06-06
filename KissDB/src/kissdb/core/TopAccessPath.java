package kissdb.core;

/**
 * Specialized data structure for storing accessed top nodes.
 */
public class TopAccessPath {
    int size;
    TopNode[] nodes;
    
    public TopAccessPath() {
        size = 0;
        nodes = new TopNode[2];  // NOTE, small for now to test enlargement
    }
    
    public final int getSize() {
        return size;
    }
    
    /**
     * Sets size to 0. Memory leak warning: node reference not set to null.
     */
    public final void clearFast() {
        size = 0;
    }
    
    /**
     * Sets size to 0 and node references to null.
     */
    public final void clear() {
        final int s = this.size;
        
        for (int i = 0; i < s; i++) {
            nodes[i] = null;
        }
        
        size = 0;
    }
    
    public final TopNode get(int index) {
        assert index < size;
        return nodes[index];
    }
    
    /**
     * Adds a node.
     */
    public final void add(TopNode node) {
        size++;
        if (nodes.length < size) enlargeArray();
        nodes[size - 1] = node;
    }
    
    private void enlargeArray() {
        TopNode[] newNodes = new TopNode[(int) (nodes.length * 1.60)];
        System.arraycopy(nodes, 0, newNodes, 0, nodes.length);
        nodes = newNodes;
    }
}
