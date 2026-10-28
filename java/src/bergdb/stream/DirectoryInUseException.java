package bergdb.stream;

import java.io.IOException;

/**
 * Thrown by FileStream's constructor when another FileStream holds the directory, in this JVM
 * or in another process: a database that is open, or one that is still closing after stop()
 * (2026-10-28, bergdb 005-63). Nothing in the directory has been read or changed. The
 * directory can be opened when the other database is closed.
 *
 * @author Frans Lundberg
 */
public class DirectoryInUseException extends IOException {
    private static final long serialVersionUID = 1L;

    public DirectoryInUseException(String message) {
        super(message);
    }
}
