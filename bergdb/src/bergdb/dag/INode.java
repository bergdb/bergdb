package bergdb.dag;

// TODO D. isTopNode(), isKeyNode(), isValueNode() methods. Possible also toTopNode, toKeyNode, toValueNode methods.
// Code like:
//   if (inode.getType() == INode.KEY_NODE) { KeyNode k = (KeyNode) inode; print(k); ..
// can be improved to:
///  if (inode.isKeyNode) { print(inode.toKeyNode(); ..


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
 * operation threads.</p>
 * 
 * @author Frans Lundberg
 */
public interface INode {
    public static final byte TYPE_TOP_NODE = 10;
    public static final byte TYPE_KEY_NODE = 20;
    public static final byte TYPE_VALUE = 30;
    public static final byte TYPE_DELETE = 40;
    
    public byte getType();
    
    public boolean isIndexNode();
    
    public long getSpos();
    public void setSpos(long spos);
    
    public boolean isDirty();
    public void setDirty(boolean isDirty);
    
    /**
     * Sets a unique ID of the node. This ID does not change as the node
     * is appended to or written to stream.
     * Note, currently (2013-04) the ID is only used for debug and
     * assert reasons; it might be removed in the future.
     */
    public long getId();
    
    public int getPointerCount();
    
    /**
     * Returns pointer data in 'pointer' parameter.
     */
    public void getPointer(int index, Pointer pointer);
    
    public INode getPointerNode(int index);
    public long getPointerPos(int index);
    
    /**
     * Sets pointer node and spos (accessData) at a given pointer index.
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
     * in the node cache.
     */
    public int getMemSize();

    public boolean isKeyNode();
    public boolean isTopNode();
    public boolean isValueNode();
}
