package bergdb.core;

import java.security.SecureRandom;

import bergdb.common.SeedGenerator;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * A 16-byte (128-bit) database ID. An immutable class.
 * 
 * @author Frans Lundberg
 */
public class DatabaseId {
    private static final int SIZE = 16;
    
    /** 
     * A database ID used for testing; useful to have deterministic stream bytes
     * and to avoid overhead of creating a new one.
     */
    public static final DatabaseId TEST_ID = new DatabaseId(new byte[] {
        125, -18, -12, -118, -124, 102, -13, -121, -64, -69, 114, -99, 44, -118, -85, 56
    }, Type.NORMAL);
    
    public static final DatabaseId CREATE_LATER_MARKER = new DatabaseId(new byte[SIZE], Type.CREATE_LATER);
    
    private final byte[] id;
    private final Type type;
    
    private DatabaseId(byte[] id, Type type) {
        this.id = id;
        this.type = type;
    }
    
    /**
     * Creates a new random database id.
     */
    public static DatabaseId createRandom() {
        SecureRandom r = new SecureRandom();
        r.setSeed(new SeedGenerator().getSeed());
        byte[] id = new byte[SIZE];
        r.nextBytes(id);
        return new DatabaseId(id, Type.NORMAL);
    }
    
    /**
     * Creates a new database id based on the given bytes.
     */
    public static DatabaseId createFromBytes(byte[] bytes) {
        if (bytes == null) {
            throw new IllegalArgumentException("bytes == null not allowed");
        }
        
        if (bytes.length != SIZE) {
            throw new IllegalArgumentException("bad length of bytes, " + bytes.length);
        }
        
        if (Util.hasOnlyZeros(bytes)) {
            throw new IllegalArgumentException("Database ID cannot contain only zeros.");
        }
        
        return new DatabaseId(bytes.clone(), Type.NORMAL);
    }
    
    public byte[] getBytes() {
        byte[] result = new byte[id.length];
        System.arraycopy(id, 0, result, 0, id.length);
        return result;
    }
    
    public String toString() {
        return Util.toHexString(id);
    }
    
    public boolean equals(DatabaseId that) {
        return Util.areEqual(this.id, that.id);
    }
    
    public boolean isCreateLaterMarker() {
        return type == Type.CREATE_LATER;
    }
    
    private enum Type {
        NORMAL, CREATE_LATER
    }
    
    // ======== Tests ========
    
    
    @T private static void twoRandomIdsShouldNotBeEqual() {
        DatabaseId id1 = DatabaseId.createRandom();
        DatabaseId id2 = DatabaseId.createRandom();
        Assert.assertFalse(id1.equals(id2));
        Assert.assertFalse(id2.equals(id1));
    }
    
    @T private static void testCreateLater() {
        DatabaseId id1 = DatabaseId.CREATE_LATER_MARKER;
        DatabaseId id2 = DatabaseId.createRandom();
        
        Assert.assertTrue(id1.isCreateLaterMarker());
        Assert.assertFalse(id2.isCreateLaterMarker());
        Assert.assertFalse(id1.equals(id2));
    }
    
    @T private static void testThatNullBytesCannotBeCreated() {
        Exception ex = null;
        try {
            DatabaseId.createFromBytes(new byte[SIZE]);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T private static void testEquals() {
        byte[] bytes1 = new byte[DatabaseId.SIZE];
        byte[] bytes2 = new byte[DatabaseId.SIZE];
        byte[] bytes3 = new byte[DatabaseId.SIZE];
        
        bytes1[12] = 12;
        bytes2[12] = 12;
        bytes3[12] = 33;
        
        DatabaseId id1 = DatabaseId.createFromBytes(bytes1);
        DatabaseId id2 = DatabaseId.createFromBytes(bytes2);
        DatabaseId id3 = DatabaseId.createFromBytes(bytes3);
        
        Assert.assertTrue(id1.equals(id2));
        Assert.assertTrue(!id1.equals(id3));
        Assert.assertTrue(!id2.equals(id3));
    }
}
