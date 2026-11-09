package bergdb.pub;

import java.security.SecureRandom;

import bergdb.common.SeedGenerator;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * A key for the encryption of the database stream, with its algorithm and the name of
 * the key.
 * 
 * @author Frans Lundberg
 */
public class CryptoKey {
    //
    // Strings are used to serialize and parse crypto keys.
    // Some consider this less secure than using char[]. However, clean
    // code is also important for security. Also, the user of this class
    // is likely to create String:s with key data in it anyway.
    // So, KISS takes precedence.
    //
    
    /**
     * A CryptoKey instance that represents 'null' - no crypto key. Its serialize() string,
     * "null-null-", parses to it.
     */
    public static final CryptoKey NULL = new CryptoKey("null", null, new byte[0]);
    
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
     * Returns true if this is CryptoKey.NULL: no crypto key, no encryption.
     */
    public boolean isNull() {
        return algo == null;
    }
    
    /**
     * Returns the key data specific for the algorithm used, a new array: a change of it does
     * not change this key (2026-11-09, bergdb 020-20, N1: the key's own array, so a caller
     * could change the key).
     *
     * @return A copy of the key data.
     */
    public byte[] getKeyData() {
        return keyData.clone();
    }
    
    /**
     * Generates a new 256-bit key.
     */
    public static CryptoKey generate() {
        SecureRandom random = createSecureRandom();
        
        byte[] nameBytes = new byte[4];
        random.nextBytes(nameBytes);
        String name = StringUtil.toHex(nameBytes);
        
        String algo = "salsa";
        
        byte[] keyData = new byte[8 + 32];
        random.nextBytes(keyData);
        
        return new CryptoKey(name, algo, keyData);
    }
    
    /**
     * Parses a string that was created with serialize(); NULL's string gives NULL.
     * 
     * @throws CryptoKey.FormatException if the string is not in serialize()'s format.
     * @throws IllegalArgumentException if serializedKey is null.
     */
    public static CryptoKey parse(String serializedKey) {
        // Note: think about not printing serializedKey in log messages
        // and error messages.
        
        if (serializedKey == null) {
            // bergdb 020-21, 3: as every null argument of the API, not a NullPointerException.
            throw new IllegalArgumentException("serializedKey == null not allowed");
        }
        if (serializedKey.equals(NULL.serialize())) {
            // bergdb 020-21, 3 (020-19, section 6): NULL round-trips, as every key does.
            return NULL;
        }
        
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
            keyData = StringUtil.hexStringToBytes(keyDataString);
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
        b.append("-" + StringUtil.toHex(keyData));
        return b.toString();
    }
    
    /**
     * Returns the key as serialize() does, but with the key data replaced by "****":
     * for log messages and error messages.
     */
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
    
    /**
     * Returns a hash code consistent with equals(): equal keys have equal hash codes
     * (bergdb 015-45).
     */
    public int hashCode() {
        return serialize().hashCode();
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
        
        /** Creates the exception with the given message. */
        public FormatException(String message) {
            super(message);
        }
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
    
    /**
     * bergdb 015-45: equal keys have equal hash codes, as Object.hashCode() requires of a
     * class that overrides equals(); a HashSet then finds a key parsed again from its
     * serialized form.
     */
    @Nano private static void testHashCode() {
        CryptoKey key1 = CryptoKey.generate();
        CryptoKey key2 = CryptoKey.parse(key1.serialize());
        Assert.assertTrue("equal", key1.equals(key2));
        Assert.assertEquals("the hash codes of equal keys", key1.hashCode(), key2.hashCode());
        
        java.util.HashSet<CryptoKey> set = new java.util.HashSet<CryptoKey>();
        set.add(key1);
        Assert.assertTrue("a HashSet finds the equal key", set.contains(key2));
        Assert.assertTrue("NULL equals NULL, with equal hash codes", 
                CryptoKey.NULL.equals(CryptoKey.NULL) 
                && CryptoKey.NULL.hashCode() == CryptoKey.NULL.hashCode());
    }
    
    /**
     * bergdb 020-20, N1: getKeyData() gives a copy, so a change of the array it returns does
     * not change the key: neither a second getKeyData() nor serialize().
     */
    @Nano private static void testGetKeyDataGivesACopy() {
        CryptoKey key = CryptoKey.generate();
        String serialized = key.serialize();
        byte[] data = key.getKeyData();
        byte[] before = data.clone();
        for (int i = 0; i < data.length; i++) {
            data[i] ^= (byte) 0xff;
        }
        
        Assert.assertArrayEquals("a second getKeyData()", before, key.getKeyData());
        Assert.assertEquals("serialize()", serialized, key.serialize());
        Assert.assertTrue("equal to the key parsed from its serialized form", 
                key.equals(CryptoKey.parse(serialized)));
    }
    
    /**
     * bergdb 020-21, 3 (020-19, section 6): CryptoKey.NULL round-trips through serialize()
     * and parse(), as every key does: parse() refused its string, "null-null-", with a
     * FormatException. parse(null) throws IllegalArgumentException, as every null argument
     * of the API does, not NullPointerException.
     */
    @Nano private static void testNullRoundTrip() {
        CryptoKey key = CryptoKey.parse(CryptoKey.NULL.serialize());
        Assert.assertTrue(key.isNull());
        Assert.assertTrue(key == CryptoKey.NULL);
        try {
            CryptoKey.parse(null);
            throw new AssertionError("parse(null) not refused");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
        CryptoKey generated = CryptoKey.generate();
        Assert.assertEquals(generated, CryptoKey.parse(generated.serialize()));
    }
    
    @Nano private static void testNull1() {
        Assert.assertTrue(CryptoKey.NULL.isNull());
        
    }
    
    @Nano private static void testNull2() {
        CryptoKey key = CryptoKey.parse("7bcf4b7c-salsa-15fc30dde0914feb075a2c1f1fb95640da3e3d04da10fe9c349ad99a50deaab4aa803d057a0186cc");
        Assert.assertFalse(key.isNull());
    }
}
