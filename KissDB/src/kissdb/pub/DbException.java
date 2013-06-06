package kissdb.pub;

/**
 * Thrown when a serious error condition occurred in the database.
 * This exception should be considered fatal to the database unless otherwise documented
 * for the method that throws the exception.
 * That means that after a DBException, the database should not be considered functional and should
 * not be used anymore.
 * 
 * @author Frans Lundberg
 */
public class DbException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public DbException(Throwable cause) {
        super(cause);
    }
    
    public DbException(String message) {
        super(message);
    }
}

/*
The Pub user really do not need to catch different fatal database exceptions:
StreamFormatException / StreamIOException / InternalDataException in different 
catch-clauses. It is enough to catch DBException.
The subclasses of DBException do not have to be a part of Layer Pub, but that
can still be thrown by Core Layer and handled (as a DBException) by Layer Pub.
*/