package bergdb.coreds;


public interface IDirtyNodes {

    /**
     * Returns the number of nodes in the collection.
     * Caller must hold DB.writeLock.
     * This method is only used for monitoring.
     */
    public int getSize();

    // TODO A. Should we add mapping tpos -> node instead?
    public void add(INode node);
    
    public void remove(INode node);

    /**
     * Adds all nodes that are "too dirty" to "list". The too dirty nodes are the nodes in the 
     * collection with spos < dirtyLimit.
     * Caller must hold DB.writeLock.
     * The returned entries are removed from the collection.
     * 
     * @param dirtyLimit A node with an spos less than this is "too dirty".
     * @param list The list to add the too dirty nodes to.
     */
    public void getAndRemoveTooDirtyNodes(long dirtyLimit, TransactionNodesForMe list);

    
    // ---- Types ----
    
    public static interface TransactionNodesForMe {
        public void addTopNode(TopNode node);
        public void addKeyNode(KeyNode node);
    }
    
}