package bergdb.common;

import java.util.Comparator;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Compares two byte arrays in lexicographical order.
 * 
 * @author Frans Lundberg
 */
public class ByteArrayComparator implements Comparator<byte[]> {
    public int compare(byte[] arr1, byte[] arr2) {
        return ByteArrayComparator.compareArrays(arr1, arr2); 
    }
    
    public static final int compareArrays(byte[] arr1, byte[] arr2) {
        final boolean firstShorter = arr1.length < arr2.length;
        final int minLength = firstShorter ? arr1.length : arr2.length;
        int i;
        
        for (i = 0; i < minLength; i++) {
            int diff = (arr1[i] & 0xff) - (arr2[i] & 0xff);
            if (diff != 0) {
                return diff;
            }
        }
        
        return arr1.length == arr2.length ? 0 : (firstShorter ? -1 : +1);
    }
    
    @Nano
    private static void test0() {
        int result = ByteArrayComparator.compareArrays(new byte[]{1}, new byte[]{2});
        Assert.assertEquals(true, result < 0);
    }
    
    @Nano
    private static void test1() {
        int result = ByteArrayComparator.compareArrays(new byte[]{100}, new byte[]{2});
        Assert.assertEquals(true, result > 0);
    }
    
    @Nano
    private static void test2() {
        int result = ByteArrayComparator.compareArrays(new byte[]{-100}, new byte[]{-100});
        Assert.assertEquals(true, result == 0);
    }
    
    @Nano
    private static void testLengthDiff() {
        int result = ByteArrayComparator.compareArrays(new byte[]{1, 2}, new byte[]{1, 2, 0});
        Assert.assertEquals(true, result < 0);
    }
    
    @Nano
    private static void testEmptyFirst() {
        int result = ByteArrayComparator.compareArrays(new byte[]{0}, new byte[]{});
        Assert.assertEquals(true, result > 0);
    }
}
