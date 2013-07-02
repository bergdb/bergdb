package bergdb.pubimp;

import bergdb.pub.ObjectCreationException;

/**
 * An implementation of this interface determines how a Java object is created based on a 
 * user-supplied Class parameter and a key-value entry in the database.
 * The key parameter may be supplied by the user, but it could also come from an iteration of
 * an index.
 * 
 * @author Frans Lundberg
 */
public interface KvToObject {
    
    /**
     * Creates a new object of a specified class that reflects the data in the
     * key-value pair read from the database.
     * NOTE Now uses ikey!
     * 
     * @param c     The class of the object to create.
     * @param ikey  The database ikey.
     * @param value The database value.
     * @return      The created object.
     * @throws ObjectCreationException  If the objection could not be created.
     */
    public <TYPE> TYPE createObject(Class<TYPE> c, String ikey, byte[] value) 
            throws ObjectCreationException;
}
