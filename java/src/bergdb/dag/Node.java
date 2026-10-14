package bergdb.dag;

/**
 * <p>A node in the Dag. There are three types of nodes: TopNode, KeyNode, 
 * and ValueNode. Top nodes and key nodes are called <i>index nodes</i> 
 * since that are used to index the value nodes.<p>
 * 
 * <p>Node ID. Each node has a unique node id (node.getId()). It is set when the node is
 * created. Db sets the id to a vpos (virtual stream position).</p>
 * 
 * <p>Node spos. Each node has an spos field value. When the node is created, 
 * this is set to the id of the node (the vpos given to it). Once the node
 * has been written to stream, the actual real stream position is used for the spos field.</p>
 * 
 * <p>A node has a number of pointers to other nodes. They can be iterated
 * with code like this:
 * 
 * <pre>
 * for (int i = 0; i &lt; node.getSize(); i++) {
 *     node.getPointer(i, p);
 *     if (!p.isNull()) {
 *         // do something with pointer here
 *     }
 * }
 * </pre>
 * 
 * <p>The Pointer object, p, is re-used for performance.</p>
 * 
 * <p>Concurrency: The methods setPointer(), getMemSize() are allowed to 
 * run from concurrent read operation threads.</p>
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
     * Returns the number of pointers of this node.
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
