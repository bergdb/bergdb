package bergdb.core;

import bergdb.dag.INode;

// TODO A. Refactor this.

/**
 * The data of a stored node in the stream.
 * 
 * @author Frans Lundberg
 */
public class StoredNode {
    /** The in-memory node object. */
    public INode node;
    
    /** Previous spos is available for stored key nodes. */
    public long sposPrevious;
    
    /** Node pointer choices - available for value nodes. */
    public byte[] choices;
    
    public StoredNode() {}
}
