package bergdb.dag;


/**
 * <p>A node of the DB graph. An INode can be serialized with toBytes(). 
 * Each INode implementation should also have a
 * "static KeyNode fromBytes(...) {" method that handles deserialization. 
 * That cannot be enforced with the interface (but with this documentation).</p>
 * 
 * <p>There are three types of nodes: TopNode, KeyNode, and ValueNode. Top nodes and key
 * nodes are called <i>index nodes</i> since that are used to index the value nodes.</p>
 * 
 * <p>Concurrency. The methods setPointer(), getMemSize() may be run from concurrent read 
 * operations.</p>
 * 
 * @author Frans Lundberg
 */
public interface INode {
    // 131101 Frans: removed getEvictPointer(). Access needs lock, Graph.getPointerLock().
    // 130502 Frans: changed constants to 10, 20, ... smart if we ever would want 
    // node type + serialization version in same number to save a byte.
    
    public static final byte TYPE_TOP_NODE = 10;
    public static final byte TYPE_KEY_NODE = 20;
    public static final byte TYPE_VALUE = 30;
    public static final byte TYPE_DELETE = 40;
    
    public byte getType();
    
    // TODO A. Rename. isIndexNode()..
    public boolean isTopOrKeyNode();
    
    public long getSpos();
    public void setSpos(long spos);
    
    /**
     * Sets a unique ID of the node. This ID does not change as the node
     * is appended to or written to stream.
     * Note, currently (2013-04) the ID is only used for debug and
     * assert reasons; it could be removed with maintained features.
     */
    public long getId();
    public void setId(long id);
    
    //public boolean isDirty();
    //public void setIsDirty(boolean b);
    
    public int getPointerCount();
    
    /**
     * This method is only used in DB.start() (and test methods).
     */
    public void getPointer(int index, Pointer pointer);
    
    public INode getPointerNode(int index);
    public long getPointerPos(int index);
    
    /**
     * Sets pointer node and spos at a given pointer index.
     */
    public void setPointer(int index, INode node, long spos);
    
    /**
     * Calls visitor.visit().
     */
    public void accept(NodeVisitor visitor);
    
    /**
     * Returns the number of in-memory out-bound pointer from this node.
     * This method is used for assertions and testing in general.
     */
    public int getMemoryPointerCount();
    
    /**
     * Returns multi-line print of the state of this node.
     * Good for debug to complement toString().
     */
    public String print();
    
    public void setPointerAccessData(int pointerIndex, long time);
    public long getPointerAccessData(int pointerIndex);
    
    /**
     * Returns an estimate of the size of the node object when stored in memory; when stored
     * in the DB node cache. A 64-bit JVM can be assumed.
     */
    public int getMemSize();
    
    ///**
    // * Returns the total byte size of the node when serialized with method toBytes().
    // */
    //public int getByteSize();
    
    /**
     * <p>Serialized the state of the node to a byte array at the given offset.
     * First 5 bytes must be the total byte size of the serialized node (little-endian
     * byte order, 4 bytes) followed by one byte that is the node type (TYPE_KEY_NODE for example).<p>
     * 
     * <p>Each class implementing INode should have a static method "fromBytes" that deserializes
     * the node.</p>
     * 
     * <pre>
     *     // Creates a node from the data in the byte buffer.
     *     // param buffer:  The byte buffer (read from the database stream).
     *     // param offset:  Offset into the buffer where the serialized node is stored.
     *     // param spos:    The stream position of the node.
     *     // throws:        StreamFormatException, StreamChecksumException
     *     fromBytes(byte[] buffer, int offset, long spos) { ...
     * </pre>
     * 
     * @param prevPos previous spos of node, or Spos.NULL is not applicable/unknown.
     * @return byte size of the serialized node.
     */
    //public int toBytes(byte[] buffer, int offset, long prevPos);
    
    /** Only used by class TransNodes. */
    public boolean isInTransNodes();
    
    /** Only used by class TransNodes. */
    public void setIsInTransNodes(boolean b);
}

/*

---- 130413 ----
getBytesSize(), toBytes() not needed. Done per node type instead.

---- 130429 ----
Changed node serialization. Updated documentation and interface for the change.

---- 130403 ----
Refactoring. Added parameter 'prevPos' to toBytes(). Not all node types need to store it.
Only KeyNode, actually.

---- Implementation note, 2012-05 ----
The special isInTransNodes() and setIsInTransNodes() methods are unortodox. They
provide a one-bit storage for the TransNodes data structure. This allows an important
performance optimization to be made.
*/