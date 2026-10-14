package bergdb.stream;

import java.io.IOException;

/**
 * Thrown by an AppendOnlyStream when a read asks for bytes before the first position of the
 * stream, bytes that pretruncate() has removed (or is removing). Written 2026-10-13
 * (docs/levels.md, W1).
 *
 * <p>It is not a failure of the stream. A read that was admitted before reclaim moved the
 * first available lookup time can reach such bytes. The stream is still correct and
 * usable; only that read has failed. A stream must not remember this exception as a fault
 * (FileStream did, 2026-10-13 and before, and the database stopped).</p>
 */
public class ReadBelowFirstPosException extends IOException {
    private static final long serialVersionUID = 1L;

    public ReadBelowFirstPosException(String message) {
        super(message);
    }
}
