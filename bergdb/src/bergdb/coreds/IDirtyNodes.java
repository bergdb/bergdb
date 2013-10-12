package bergdb.coreds;

/**
 * Interface to the collection of dirty nodes.
 * 
 * @author Frans Lundberg
 */
public interface IDirtyNodes {

    /**
     * Returns the number of nodes in the collection.
     * Caller must hold DB.writeLock.
     * This method is only used for monitoring.
     */
    public int getSize();
    
    /**
     * Adds an spos-to-INode mapping if spos != Spos.NULL.
     */
    public void put(long spos, INode node);
    
    /**
     * Removes one mapping.
     * 
     * @param spos  The key of the mapping to remove.
     * @throws AssertionError  If no key 'spos' exists.
     */
    public void remove(long spos);
    
    /**
     * Adds all nodes that are "too dirty" to "list". The too dirty nodes are the nodes in the 
     * collection with spos < dirtyLimit.
     * Caller must hold DB.writeLock.
     * The returned entries are removed from the collection and isDirty is set to 
     * false for all nodes returned.
     * 
     * @param dirtyLimit A node with an spos less than this is "too dirty".
     * @param list The list to add the too dirty nodes to.
     */
    public void getAndRemoveTooDirtyNodes(long dirtyLimit, TransactionNodesForMe list);

    
    /**
     * The method subset of core.TransactionNodes needed by this class.
     * This type is useful to minimize dependency, good for testing, mocks.
     */
    public static interface TransactionNodesForMe {
        public void addTopNode(TopNode node);
        public void addKeyNode(KeyNode node);
    }
}