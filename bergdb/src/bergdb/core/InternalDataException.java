package bergdb.core;

import bergdb.pub.DbException;

/**
 * Thrown when data is missing from INTERNAL_PREFIX key space or if the data located there 
 * has a bad format. This should never happen if BergDB code is bug-free and the internal data has
 * not been modified by other software.
 * 
 * @author Frans Lundberg
 */
public class InternalDataException extends DbException {
    private static final long serialVersionUID = 1L;
    
    public InternalDataException(String message) {
        super(message);
    }
}
