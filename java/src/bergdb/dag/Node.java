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
    
    /**
     * The object that pointer i leads to without a read of the stream, or null (a stream
     * pointer): a value; or the object of the pointer's handle, if the handle is live and the
     * object may serve the pointer (Handle.usable; bergdb item 009, step 3a: the memory
     * pointer of before, as the walks, the audit and the trace exporter see it).
     */
    public Node getPointerNode(int index);
    
    /**
     * Pointer i's reference: the position or vpos it named when it was made, loaded, or last
     * resolved (since bergdb item 009, step 3a always this, never access data).
     */
    public long getPointerPos(int index);
    
    /**
     * What pointer i holds (bergdb item 009, step 3a): the pointee's handle, a value, or null
     * (not followed yet, or a value unswizzled).
     */
    public Pointee getPointee(int index);
    
    /** Sets what pointer i holds, under the node's monitor (009-02, 3.4, C2). */
    public void setPointee(int index, Pointee pointee);
    
    /** Sets pointer i's reference, under the node's monitor (009-02, 3.4, C2). */
    public void setRef(int index, long ref);
    
    /**
     * Sets what pointer i holds and its reference, under the node's monitor. Caller should
     * synchronize on "pointer lock" (Db.pointerLocks) after startup.
     */
    public void setPointer(int index, Pointee pointee, long ref);
    
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
     * The reference that pointer i is written with into a record: a memory pointer's
     * pointee's position (or vpos), a stream pointer's position; Spos.NULL for a null
     * pointer (bergdb item 009, step 1d: the one place that decides it). Read as a coherent
     * pair. A value node has no pointers.
     */
    public long getSerializedRef(int index);
    
    /**
     * Returns multi-line print of the state of this node.
     * Good for debug to complement toString().
     */
    public String print();
    
    /**
     * Like print(), but with indentation.
     */
    public String print(String indent);
    
    /**
     * Returns an estimate of the size of the node object when stored in memory; when stored
     * in the node cache.
     */
    public int getMemSize();

    public boolean isKeyNode();
    public boolean isTopNode();
    
    public boolean isValueNode();
    
    public boolean isInTransNodes();
    
    /**
     * True if this object is the canonical object of its node: the one object that holds
     * the node's whole history and can change. An object read from an older version of
     * the node, for lookups at older times, is not canonical (a snapshot). Value nodes
     * never change and are always canonical. See docs/levels.md, level 2.
     * Synch note: written by the writer, or under the node table's lock.
     */
    public boolean isCanonical();
    
    /** Sets isCanonical(). No effect for value nodes. */
    public void setCanonical(boolean isCanonical);
}
