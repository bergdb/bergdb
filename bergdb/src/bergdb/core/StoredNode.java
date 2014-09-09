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

/*

LOG
===

140909. Thought the design of StoredNode having a reference to its INode instance
is bad. For example the field StoredValueNode.node. But actually, it is fine. I tried
to change it, but it just made things more complicated. It is nice to be able to serialize
directly from INode instance. This is also good for performance. TransNodes is used directly
for fastest possible serialization.

*/