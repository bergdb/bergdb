package bergdb.storage;

/**
 * Thrown to indicate that the software was trying to read an element
 * in the database stream (transaction, node, meta-block), but it does not support
 * parsing the version of the element. Typically, this means that the stream
 * was generated with a newer version of BergDB than this one. Or, a very old
 * version that is no longer supported by this newer software.
 * 
 * @author Frans Lundberg
 */
public class VersioningStreamException extends StreamException {
    private static final long serialVersionUID = 1L;

    public VersioningStreamException(String message) {
        super(message);
    }
}
