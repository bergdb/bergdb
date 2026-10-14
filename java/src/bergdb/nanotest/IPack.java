package bergdb.nanotest;

/**
 * Provides a list of classes that belongs to a Java package.
 * 
 * @author Frans Lundberg
 */
public interface IPack {
    
    /**
     * Returns the public non-anomymous classes of the package.
     * Inner classes should be included if they are static.
     */
    public Class<?>[] getClasses();
}
