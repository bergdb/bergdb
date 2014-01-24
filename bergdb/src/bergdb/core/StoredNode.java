package bergdb.core;

import bergdb.dag.INode;

/**
 * A node read from the stream.
 * Subclasses may contain additional data compare to the in-memory
 * representation of a node.
 * 
 * @author Frans Lundberg
 */
public interface StoredNode {
    public INode getNode();
    public long getPrevPos();
}
