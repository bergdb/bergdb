package bergdb.pub;

import java.security.SecureRandom;

import bergdb.common.SeedGenerator;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * An encryption for database stream encryption together with 
 * information about the encryption and the name of the encryption key.
 * 
 * @author Frans Lundberg
 */
public class CryptoKey {
    //
    // Strings are used to serialize and parse crypto keys.
    // Some consider this less secure than using char[]. However, clean
    // code is also important for security. Also, the user of this class
    // is likely to create String:s with key data in it anyway.
    // So, KISS took precedence.
    //
    
    /** Algorithm name, currently always 'salsa'. */
    private final String algo;
    
    /** Name of crypto key. Automatically generated. */
    private final String name;
    
    /** Key data. For 'salsa', it is a 8-byte nonce followed by a 32-byte key. */
    private final byte[] keyData;
    
    private CryptoKey(String name, String algo, byte[] keyData) {
        this.name = name;
        this.algo = algo;
        this.keyData = keyData;
    }

    /**
     * Returns the name of the crypto algorithm ('salsa').
     */
    public String getAlgo() {
        return algo;
    }
    
    /**
     * Returns the key data specific for the algorithm used.
     */
    public byte[] getKeyData() {
        return keyData;
    }
    
    /**
     * Generates a new 256-bit key.
     */
    public static CryptoKey generate() {
        SecureRandom random = createSecureRandom();
        
        byte[] nameBytes = new byte[4];
        random.nextBytes(nameBytes);
        String name = Util.toHex(nameBytes);
        
        String algo = "salsa";
        
        byte[] keyData = new byte[8 + 32];
        random.nextBytes(keyData);
        
        return new CryptoKey(name, algo, keyData);
    }
    
    /**
     * Parses a string that was created with serialize().
     * 
     * @throws CryptoKey.FormatException
     */
    public static CryptoKey parse(String serializedKey) {
        // Note: think about not printing serializedKey in log messages
        // and error messages.
        
        String[] parts = serializedKey.split("-");
        if (parts.length < 3) {
            throw new FormatException("serializedKey has too few parts (" + parts.length + ").");
        }
        
        String name = parts[0];
        String algo = parts[1];
        String keyDataString = parts[2];
        byte[] keyData;
        
        if (name.length() < 1) {
            throw new FormatException("Empty name not allowed");
        }
        
        if (algo.length() < 1) {
            throw new FormatException("Empty algo name not allowed");
        }
        
        try {
            keyData = Util.hexStringToBytes(keyDataString);
        } catch (IllegalArgumentException e) {
            throw new FormatException("Bad keyData format.");
        }
        
        if (keyData.length != 8 + 32) {
            throw new FormatException("Bad length of keyData. Expected 40 bytes.");
        }
        
        return new CryptoKey(name, algo, keyData);
    }
    
    /**
     * Returns the key and key info serialized to a String.
     */
    public String serialize() {
        StringBuilder b = new StringBuilder();
        b.append(name);
        b.append("-" + algo);
        b.append("-" + Util.toHex(keyData));
        return b.toString();
    }
    
    public String toStringWithMaskedKey() {
        StringBuilder b = new StringBuilder();
        b.append(name);
        b.append("-" + algo);
        b.append("-****");
        return b.toString();
    }
    
    public String toString() {
        return toStringWithMaskedKey();
    }
    
    public boolean equals(Object thatObject) {
        if (thatObject == null || !(thatObject instanceof CryptoKey)) {
            return false;
        }
        
        CryptoKey that = (CryptoKey) thatObject;
        
        return this.serialize().equals(that.serialize());
    }
    
    private static SecureRandom createSecureRandom() {
        SecureRandom r1 = new SecureRandom();
        byte[] seedBytes1 = new byte[64];
        r1.nextBytes(seedBytes1);     // r1 will self-seed.
        
        SeedGenerator g = new SeedGenerator();
        g.moreEntropy();
        g.moreEntropy();
        byte[] seedBytes2 = g.getSeed();
        
        byte[] seedBytes3 = Util.concat(seedBytes1, seedBytes2);
        
        SecureRandom random = new SecureRandom();
        random.setSeed(seedBytes3);
        
        return random;
    }
    
    /**
     * Thrown from method parse() if the string to be parsed
     * does not follow the expected format.
     */
    public static class FormatException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        
        public FormatException(String message) {
            super(message);
        }
    }
    
    public static void main(String[] args) {
        CryptoKey key = CryptoKey.generate();
        
        System.out.println("Generated key: " + key);
        System.out.println("Full serialized key: " + key.serialize());
    }
    
    
    // ======== Testing ========
    
    @Nano private static void testSerializeAndParse() {
        CryptoKey key1 = CryptoKey.generate();
        String string = key1.serialize();
        CryptoKey key2 = CryptoKey.parse(string);
     
        Assert.assertEquals(key1, key2);
    }
    
    @Nano private static void checksThatParsingBadStringGeneratesFormatException() {
        FormatException ex = null;
        
        try {
            CryptoKey.parse("aabbccdd-salsa-aabbGG");
        } catch (FormatException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
}
