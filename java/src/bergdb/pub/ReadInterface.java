package bergdb.pub;

import bergdb.pub.util.DbException;


/**
 * An interface common to both RwEnvironment and to Connection that makes it possible to
 * create composable methods for reading data that can be used both for read-only operations 
 * and for read-write transactions.
 * 
 * @author Frans Lundberg
 */
public interface ReadInterface {
    
    /**
     * Checks whether a key-value entry with the given key exists.
     *
     * @throws IllegalArgumentException
     *             If key does not follow the allowed format, or is null, as for get(), in
     *             a connection and in an rw-transaction alike (bergdb 019-05).
     * @throws bergdb.pub.util.LookupTimeNotAvailableException  As Connection.get(): the
     *             read's lookup time is before the first available lookup time, or became so
     *             while it ran (bergdb 020-24-06, U6-6).
     * @see Connection#exists(String)
     */
    public boolean exists(String key) throws DbException;
    
    /**
     * Gets the object stored under the key, created from 'clazz', or null if no entry
     * exists for the key.
     *
     * <p>A byte[] returned (by byte[].class, or by Object.class at a value of bytes) is
     * the database's own array, not a copy: do not change it. A change of it changes
     * what later reads return, in every connection, until the value leaves memory or
     * the database restarts, while the stream keeps the committed bytes. To change
     * the bytes, copy them first, with clone() (bergdb 015-47).</p>
     *
     * <p>A class other than String, byte[], DbObject and Object is a Data Object class, or a
     * primitive, its wrapper or an array class for a value put as one, and the stored object
     * is converted to it as by Connection.get() (bergdb 020-09).</p>
     *
     * @throws ObjectCreationException  As Connection.get().
     * @throws DataFormatException  As Connection.get(), for a value read as a String that
     *             is not well-formed UTF-8 (bergdb 021-06).
     * @throws IllegalArgumentException  If key does not follow the allowed format, or is
     *             null, or if clazz is null, as for Connection.get() (bergdb 020-25).
     * @throws bergdb.pub.util.LookupTimeNotAvailableException  As Connection.get(): the
     *             read's lookup time is before the first available lookup time, or became so
     *             while it ran (bergdb 020-24-06, U6-6).
     * @see Connection#get(String, Class)
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
}
