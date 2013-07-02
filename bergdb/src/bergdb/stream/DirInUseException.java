package bergdb.stream;

import java.io.IOException;

/**
 * Thrown to indicate that directory is being used.
 * 
 * @author Frans Lundberg
 */
public class DirInUseException extends IOException {
    private static final long serialVersionUID = 1L;

    public DirInUseException(String message) {
        super(message);
    }
}