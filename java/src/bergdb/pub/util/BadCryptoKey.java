package bergdb.pub.util;


/**
 * Thrown by a start when the stream does not begin as a BergDB stream read with the crypto
 * key given: the key is missing, or the wrong one is used, also a key for a database that
 * is not encrypted. Without a key, a stream that is not a BergDB stream, or is damaged at
 * its beginning, gives it too, as its message says (bergdb 005-33, 020-25). The start has
 * written nothing.
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
