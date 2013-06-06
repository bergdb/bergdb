package kissdb.common;

/**
 * <p>A Bug is thrown because of a condition that should never occur in bug-free software. 
 * The code has a bug.
 * Assumptions are not fulfilled; the application should typically terminate when this exception
 * has been thrown.
 * This exception type can be used in KissDB code to assert an assumption.
 * This is to fail-fast, give a good error message for developers, and avoid data corruption
 * in the database.</p>
 */
public class Bug extends Error {
    private static final long serialVersionUID = 1L;
    
    public Bug(String message) {
        super(message);
    }

    public Bug(Exception e) {
        super(e);
    }
}
