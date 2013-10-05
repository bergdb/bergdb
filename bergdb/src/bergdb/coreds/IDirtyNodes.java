package bergdb.coreds;

import bergdb.coreds.DirtyNodes1.TransactionNodesForMe;

public interface IDirtyNodes {

    /**
     * Returns the number of nodes in the collection.
     * Caller must hold DB.writeLock.
     * This method is only used for monitoring.
     */
    public abstract int getSize();

    public abstract void add(INode node);

    /**
     * Adds all nodes that are "too dirty" to "list". The too dirty nodes are the nodes in the 
     * collection with spos < dirtyLimit.
     * Caller must hold DB.writeLock.
     * The returned entries are removed from the collection.
     * 
     * @param dirtyLimit A node with an spos less than this is "too dirty".
     * @param list The list to add the too dirty nodes to.
     */
    public abstract void getAndRemoveTooDirtyNodes(long dirtyLimit, TransactionNodesForMe list);

}