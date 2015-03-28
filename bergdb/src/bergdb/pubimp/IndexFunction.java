package bergdb.pubimp;

/**
 * An index function describes how to create sort byte entries given
 * a DbObject. It also specifies the types of the composite levels.
 * 
 * @author Frans Lundberg
 */
public interface IndexFunction {
    // The idea is that this one day we could allow user to implement
    // computeSortBytes (maybe better with "computeIndexEntries").
    
    /**
     * Returns the types of the potentially composite index.
     * One type for each composite level.
     * The method must, of course, always return the same types.
     */
    public String[] getTypes();
    
    /**
     * Computes sortBytes for the given DbObject.
     */
    public void computeSortBytes(DbObject dbo, SortBytesBuilder b);
}
