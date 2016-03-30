package bergdb.stream;

import java.io.IOException;

/**
 * Thrown to indicate that the files in the directory if a FileStream 
 * are in an invalid state.
 * The files have been modified by other software in an incompatible way.
 * 
 * @author Frans Lundberg
 */
public class BadDirStateException extends IOException {
    private static final long serialVersionUID = 1L;

    public BadDirStateException(String message) {
        super(message);
    }
}
