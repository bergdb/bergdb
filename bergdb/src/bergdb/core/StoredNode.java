package bergdb.core;

/**
 * The data of a stored node in the state stream (a stream item).
 * Currently (2012-05), a "stream item" is always a node.
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
