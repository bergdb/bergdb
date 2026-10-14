package bergdb.core;

import bergdb.dag.Node;

/**
 * A node read from the stream.
 * May contain additional data compare to the in-memory
 * representation of a node. See implementing classes.
 * 
 * @author Frans Lundberg
 */
public interface StoredNode {
    public Node getNode();
    public long getPrevPos();
}
