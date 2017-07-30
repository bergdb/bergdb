package bergdb.pub.util;

/**
 * Thrown when a serious error condition occurred in the database.
 * This exception should be considered fatal to the database.
 * That means that after a DbException, the database should not be considered 
 * functional and should not be used anymore.
 * 
 * @author Frans Lundberg
 */
public class DbException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    
    public DbException(String message) {
        super(message);
    }
    
    public DbException(String message, Throwable cause) {
        super(message, cause);
    }
}

/*
The Pub user typically do not need to catch different fatal database exceptions:
StreamFormatException / StreamException / InternalDataException in different 
catch-clauses. It is enough to catch DBException.
The subclasses of DBException do not have to be a part of Pub layer, but they
can still be thrown by Core Layer and handled (as a DbException) by Pub layer.
*/