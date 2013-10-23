package bergdb.graph;


/**
 * Iterates a sequence of klongs.
 */
public interface KlongIter {
    /**
     * Returns true if there is at least one more slong.
     */
    public boolean hasNext();
    
    /**
     * Advances iterator to next slong and returns it.
     */
    public long next();
    
    public INode getNode();
}
