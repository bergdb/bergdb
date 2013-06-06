package kissdb.common;

/**
 * Provides package info.
 */
public interface IPack {
    /**
     * Returns the public non-anomymous classes of the package.
     * Inner classes are included if they are static.
     */
    public Class<?>[] getClasses();
}
