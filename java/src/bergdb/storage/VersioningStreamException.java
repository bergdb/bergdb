package bergdb.storage;

/**
 * Thrown to indicate that the software was trying to read an element
 * in the database stream (transaction, node, meta-block), but it does not support
 * parsing the version of the element. Typically, this means that the stream
 * was generated with a newer version of BergDB than this one. Or, a very old
 * version that is no longer supported by this newer software.
 * 
 * <p>The meta blocks (RecoverableStream), the records (StoredTrans) and the nodes throw it,
 * each for its own version. Since 2026-10-25 (bergdb 005-40) it is a StreamFormatException,
 * as BadMagicBytes is, so that the code that handles a stream it cannot read handles this
 * one too; before, the records and the nodes threw a plain StreamFormatException.</p>
 *
 * <p>The Pub API's start throws it too, before it reads the stream, for a database that an
 * earlier release encrypted, as its created.txt names a crypto key: release 2026.4 has no
 * encryption and cannot read such a stream (bergdb 020-28).</p>
 *
 * @author Frans Lundberg
 */
public class VersioningStreamException extends StreamFormatException {
    private static final long serialVersionUID = 1L;

    public VersioningStreamException(String message) {
        super(message);
    }
}
