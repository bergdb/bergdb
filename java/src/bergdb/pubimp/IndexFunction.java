package bergdb.pubimp;

/**
 * An index function describes how to create sort byte entries given
 * a DbObject. It also specifies the types of the composite levels.
 * 
 * @author Frans Lundberg
 */
public interface IndexFunction {
    // The idea is that one day we could allow user to implement createIndexEntries.
    
    /**
     * Returns the types of the potentially composite index.
     * One type for each composite level.
     * The method must, of course, always return the same types.
     */
    public String[] getTypes();
    
    /**
     * Creates index entries (zero or more) for the given DbObject
     * by calling appropriate methods of 'b'.
     */
    public void createIndexEntries(DbObject dbo, IndexEntryBuilder b);
}
