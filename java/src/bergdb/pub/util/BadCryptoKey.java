package bergdb.pub.util;


/**
 * Thrown by a start when the stream, read with the crypto key given, or without one, is not
 * a BergDB stream where the start reads it first: the magic bytes of its last meta block, one
 * of the blocks written at every 200,000 bytes of the stream, so in a database of less than
 * 200 kB its first bytes. Likely, the key is missing, or the wrong one is used, also a key
 * for a database that is not encrypted; else, with any key, the right one too, the stream is
 * damaged there, or is not a BergDB stream. The message names the likely causes (bergdb
 * 005-33, 020-25, 020-24-07). The start has written nothing.
 * 
 * @author Frans Lundberg
 */
public class BadCryptoKey extends DbException {
    private static final long serialVersionUID = 1L;
    
    /** Creates the exception with the given message. */
    public BadCryptoKey(String message) {
        super(message);
    }
}
