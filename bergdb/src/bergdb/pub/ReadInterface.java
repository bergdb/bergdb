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
     * @see Connection#exists(String)
     */
    public boolean exists(String key) throws DbException;
    
    /**
     * @see Connection#get(String, Class)
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
}
