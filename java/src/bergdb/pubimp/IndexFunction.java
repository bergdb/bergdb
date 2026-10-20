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
     * Creates index entries (zero or more) for the given DbObject
     * by calling appropriate methods of 'b'.
     */
    public void createIndexEntries(DbObject dbo, IndexEntryBuilder b);
}
