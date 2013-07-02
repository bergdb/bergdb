package bergdb.core;

import java.security.SecureRandom;

import bergdb.common.SeedGenerator;
import bergdb.common.Util;


/**
 * A 16-byte (128-bit) database ID. An object of this class is immutable.
 */
public class DatabaseId {
    /**
     * The number of bytes in a database ID.
     */
    public static int SIZE = 16;
    
    /**
     * A database ID used for testing; useful to have deterministic stream bytes.
     */
    private static DatabaseId testId = new DatabaseId(new byte[] {
        125, -18, -12, -118, -124, 102, -13, -121, -64, -69, 114, -99, 44, -118, -85, 56
    });
    
    private final byte[] id;
    
    /**
     * Creates a new random database ID.
     * This may take some time to execute; in the order of 20 ms.
     */
    public DatabaseId() {
        SecureRandom r = new SecureRandom();
        r.setSeed(new SeedGenerator().getSeed());
        id = new byte[SIZE];
        r.nextBytes(id);
        //id = testId.getBytes();
    }
    
    /**
     * Creates a new object based in the id in 'bytes'.
     */
    public DatabaseId(byte[] bytes) {
        if (bytes == null) {
            throw new IllegalArgumentException("bytes == null not allowed");
        }
        
        if (bytes.length != SIZE) {
            throw new IllegalArgumentException("bad length of bytes, " + bytes.length);
        }
        
        if (Util.hasOnlyZeros(bytes)) {
            throw new IllegalArgumentException("Database ID cannot contain only zeros.");
        }
        
        this.id = bytes.clone();
    }
    
    public static DatabaseId getTestId() {
        return testId;
    }
    
    public byte[] getBytes() {
        byte[] result = new byte[id.length];
        System.arraycopy(id, 0, result, 0, id.length);
        return result;
    }
    
    public String toString() {
        return Util.toHexString(id);
    }
    
    public static void main(String[] args) {
        System.out.println(new DatabaseId());
        System.out.println(new DatabaseId());
        
        long t = System.nanoTime();
        DatabaseId id = new DatabaseId();
        t = System.nanoTime() - t;
        System.out.println("Time to create one ID: " + 1e-9*t);
        
        byte[] idBytes = id.getBytes();
        for (int i = 0; i < idBytes.length; i++) {
            System.out.print(idBytes[i] + " ");
        }
    }
}
