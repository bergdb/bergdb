package bergdb.pubimp;

import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Helper to build index entries (the sort bytes; the "middle part").
 * 
 * @author Frans Lundberg
 */
public class IndexEntryBuilder {
    private ArrayList<byte[]> entries;
    private ArrayList<byte[]> current;
    
    public IndexEntryBuilder() {
        entries = new ArrayList<byte[]>();
        current = new ArrayList<byte[]>();
    }
    
    /**
     * Adds sort bytes; advanced low-level method.
     */
    public IndexEntryBuilder addBytes(byte[] bytes) {
        current.add(bytes);
        return this;
    }
    
    public IndexEntryBuilder addLong(long value) {
        current.add(sortBytesFromLong(value));
        return this;
    }
    
    public IndexEntryBuilder addDouble(double value) {
        current.add(IndexEntryBuilder.sortBytesFromDouble(value));
        return this;
    }
    
    public IndexEntryBuilder addString(String value) {
        addString(value, UnicodeCollator.INSTANCE);
        return this;
    }
    
    public IndexEntryBuilder addString(String value, KCollator collator) {
        addBytes(sortBytesFromString(collator, value));
        return this;
    }
    
    public IndexEntryBuilder clearEntry() {
        current.clear();
        return this;
    }
    
    /**
     * Called to indicate that the current index entry is done. 
     * Start defining the next one.
     */
    public IndexEntryBuilder entryDone() {
        byte[] entryBytes = concat(current);
        entries.add(entryBytes);        
        current.clear();
        return this;
    }
    
    /**
     * Returns the full result.
     */
    public byte[][] done() {
        int n = entries.size();
        byte[][] result = new byte[n][];
        
        for (int i = 0; i < n; i++) {
            result[i] = entries.get(i);
        }
        
        return result;
    }

    private static final long SIGNBIT = 0x8000000000000000L;
    
    public static byte[] sortBytesFromDouble(double doubleValue) {
        //
        // From http://www.cygnus-software.com/papers/comparingfloats/comparingfloats.htm:
        // The IEEE float and double formats were designed so that the numbers are lexicographically
        // ordered, which – in the words of IEEE architect William Kahan means 
        // "if two floating-point numbers in the same format are ordered ( say x < y ), then they 
        // are ordered the same way when their bits are reinterpreted as Sign-Magnitude integers."
        //
        // Note, we do not store a long "Sign-Magnitude", but in two's-complement representation.
        // So, we *cannot* simply do:
        //     return createIndexKey(index, keyname, Double.doubleToLongBits(doubleValue));
        // 
        // See http://stackoverflow.com/questions/7534230/converting-from-sign-magnitude-to-twos-complement.
        //
        // Note, this will not sort -0.0 before 0.0. They are considered the same.
        // Sorting Double.POSITIVE_INFINITY and Double.NEGATIVE_INFINITY works as expected.
        //
        
        long x = Double.doubleToLongBits(doubleValue);
        long twosComplement = (x & IndexEntryBuilder.SIGNBIT) == 0 ? x : -(x & ~IndexEntryBuilder.SIGNBIT);
        return sortBytesFromLong(twosComplement);
    }

    private static final long LONGMAX = 9223372036854775807L;   // 2^63-1
    
    /**
     * Returns a long composite index part to an index entry key.
     */
    public static byte[] sortBytesFromLong(long longValue) {
        //
        // 'longValue' is converted. Range of Java's "long" is: 
        // [-9223372036854775808 to +9223372036854775807]
        // That is: [-2^63 to 2^63-1].
        // To add 2^63 (mod 2^64), we add 2^63-1 first and then we add 1.
        // This converts like this to unsigned values:
        // Long.MIN_VALUE (-2^63)  -> 0.
        // 0                       -> 2^63     (9223372036854775808)
        // 1                       -> 2^63 + 1 (9223372036854775809)
        // Long.MAX_VALUE (2^63-1) -> 2^64     
        // Seems correct :-)
        //
        
        long sortValue = (longValue + IndexEntryBuilder.LONGMAX) + 1;
        byte[] bytes = new byte[8];
        Bytes.longToBytesBE(sortValue, bytes, 0);
        return bytes;
    }

    public static byte[] sortBytesFromString(KCollator collator, String stringValue) {
        assert collator != null : "collator is null";
        if (stringValue == null) {
            // Not an assert: a null field of the user's object is no Error, which would fail
            // the database (bergdb 019-42).
            throw new IllegalArgumentException("A null String cannot be indexed.");
        }
        
        byte[] sortBytes = collator.getSortBytes(stringValue);
        return sortBytes;
    }

    private static byte[] concat(ArrayList<byte[]> list) {
        assert list != null;
        int totalSize = 0;
        
        for (byte[] bytes : list) {
            totalSize += bytes.length;
        }
        
        byte[] result = new byte[totalSize];
        
        int offset = 0;
        for (byte[] bytes : list) {
            System.arraycopy(bytes, 0, result, offset, bytes.length);
            offset += bytes.length;
        }
        
        return result;        
    }
    
    @Nano
    private static void testSanity() {
        IndexEntryBuilder b = new IndexEntryBuilder();
        
        b.addBytes(new byte[]{10});
        b.addBytes(new byte[]{20});
        b.entryDone();
        
        byte[][] result = b.done();
        
        Assert.assertEquals(1, result.length);
        Assert.assertEquals(2, result[0].length);
        Assert.assertEquals(10, result[0][0]);
        Assert.assertEquals(20, result[0][1]);
    }
    
    @Nano
    private static void testTwoEntries() {
        IndexEntryBuilder b = new IndexEntryBuilder();
        
        b.addBytes(new byte[]{10});
        b.entryDone();
        b.addBytes(new byte[]{20});
        b.entryDone();
        
        byte[][] result = b.done();
        
        Assert.assertEquals(2, result.length);
        Assert.assertEquals(1, result[0].length);
        Assert.assertEquals(1, result[1].length);
        Assert.assertEquals(10, result[0][0]);
        Assert.assertEquals(20, result[1][0]);
    }
    
    @Nano
    public static void testUnicodeString() throws UnsupportedEncodingException {
        IndexEntryBuilder b = new IndexEntryBuilder();
        b.addString("Natalia");
        b.entryDone();
        byte[][] result = b.done();
        
        Assert.assertEquals(1, result.length);
        Assert.assertEquals(7 + 1, result[0].length);
    }
}
