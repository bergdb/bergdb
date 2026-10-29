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
     * @see Connection#exists(String)
     */
    public boolean exists(String key) throws DbException;
    
    /**
     * Gets the object stored under the key, created from 'clazz', or null if no entry
     * exists for the key.
     *
     * @see Connection#get(String, Class)
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
}
