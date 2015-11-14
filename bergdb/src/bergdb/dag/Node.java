package bergdb.dag;

/**
 * <p>A node of the db graph. A Node can be serialized with toBytes(). 
 * Each Node implementation should also have a
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
public interface Node {
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
    
    public long getId();
    public void setId(long id);
    
    /**
     * Returns the pointer size; note that this is not necessarily the total
     * number of out-bound pointers. It actually returns the max pointer index + 1.
     * getPointer() may return a null pointer for some indexes between 0 and 
     * getPointerCount() - 1.
     * 
     * Common usage (iterating pointers of a node):
     * <pre>
     * int size = node.getSize();
     * for (int i = 0; i &lt; size; i++) {
     *     node.getPointer(i, p);
     *     if (!p.isNull()) {
     *         // do something with pointer here
     *     }
     * }
     *</pre>
     */
    public int getSize();
    
    /**
     * Returns pointer count for the given lookup time.
     * 
     * @see #getSize()
     */
    public int getSizeAtTime(long lookupTime);
    
    /**
     * Returns pointer data in 'pointer' parameter.
     * pointer.node, pointer.pos, pointer.index are set.
     */
    public void getPointer(int index, Pointer pointer);
    
    public Node getPointerNode(int index);
    public long getPointerPos(int index);
    
    /**
     * Sets pointer node and spos (accessData) at a given pointer index.
     * Caller should synchronize on "pointer lock" (Db.pointerLocks).
     */
    public void setPointer(int index, Node node, long spos);
    
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
    
    /**
     * Like print(), but with indentation.
     */
    public String print(String indent);
    
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
    
    public boolean isInTransNodes();
}
