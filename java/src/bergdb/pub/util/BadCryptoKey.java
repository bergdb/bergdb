package bergdb.pub.util;


/**
 * Thrown to indicate that the crypto key is missing or the
 * wrong one is used.
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
