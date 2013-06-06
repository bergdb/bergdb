package kissdb.stream;

/**
 * Thrown to indicate that the files in the directory are in an invalid state.
 * The files have been modified by other software in an incompatible way.
 * 
 * @author Frans Lundberg
 */
public class BadDirStateException extends java.io.IOException {
    private static final long serialVersionUID = 1L;

    public BadDirStateException(String message) {
        super(message);
    }
}
