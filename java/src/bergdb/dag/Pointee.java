package bergdb.dag;

/**
 * What a memory pointer of a key node holds (bergdb item 009; 009-02, 4.2, decision T4b): a
 * Handle, for a pointer to an index node, or a ValueNode, for a pointer to a value. Which of
 * them pointer i of a key node holds is also known from its klong
 * (NodeCollection.pointsToIndexNode). A top node's pointers are all to index nodes, so they
 * are Handles.
 */
public interface Pointee {
}
