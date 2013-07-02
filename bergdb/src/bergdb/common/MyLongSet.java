package bergdb.common;

import java.util.HashSet;
import java.util.Iterator;

import bergdb.nanotest.Assert;

/**
 * An specialized, limited (add/iterate/clear) implementation of a set of long values.
 * Efficient for sets no larger then 128 values. When the number of values exceeds 128, this class 
 * becomes a simple wrapper around java.util.HashSet.
 * The class is not thread safe.
 * 
 * @author Frans Lundberg
 */
public final class MyLongSet implements Iterable<Long> {
    private int size;
    private long[] array;
    private HashSet<Long> hash;
    private static final int MAX_ARRAY_SIZE = 128;
    
    public MyLongSet() {
        hash = null;
        clear();
    }
    
    public void clear() {
        this.size = 0;
        if (isHash()) {
            this.hash = null;
        }
        this.array = new long[8];
    }
    
    public final boolean isHash() {
        return hash != null;
    }
    
    /**
     * Returns true iff set is stored this.array and available from
     * getArray().
     */
    public final boolean isArray() {
        return hash == null;
    }
    
    public final HashSet<Long> getHashSet() {
        if (!isHash()) {
            throw new IllegalStateException("Not hash, use getArray() instead.");
        }
        
        return hash;
    }
    
    /**
     * Use this method for fast array iteration.
     */
    public final long[] getArray() {
        if (isHash()) {
            throw new IllegalStateException("Not an array, HashSet used.");
        }
        return array;
    }
    
    public final int size() {
        return size;
    }

    public final boolean isEmpty() {
        return size == 0;
    }

    public final boolean contains(long value) {
        if (isHash()) {
            return hash.contains(value);
        } else {
            boolean result = false;
            for (int i = 0; i < size; i++) {
                if (array[i] == value) {
                    result = true;
                    break;
                }
            }
            return result;
        }
    }

    public boolean add(long value) {
        if (isHash()) {
            return hash.add(value);
        } else {
            final int length = array.length;
            for (int i = 0; i < length; i++) {
                if (array[i] == value) {
                    return false;
                }
            }
            
            addToArray(value);
            return true;
        }
    }
    
    /**
     * Adds a new unique long value to array or to newly created hash set if array is full.
     */
    private void addToArray(long value) {
        if (size == array.length) {
            if (array.length >= MAX_ARRAY_SIZE) {
                this.hash = new HashSet<Long>(MAX_ARRAY_SIZE * 2);
                for (int i = 0; i < size; i++) {
                    hash.add(array[i]);
                }
                array = null;
                hash.add(value);
            } else {
                long[] newArray = new long[array.length * 2];
                System.arraycopy(array, 0, newArray, 0, size);
                this.array = newArray;
                array[size] = value;
                size++;
            }
        } else {
           array[size] = value;
           size++;
        }
    }
    
    /**
     * Returns an iterator. 
     * When isHash() == false, it may be faster to call getArray() and iterate it from
     * 0 to size().
     */
    public Iterator<Long> iterator() {
        if (isHash()) {
            return hash.iterator();
        }
        
        return new Iterator<Long>() {
            private int index = 0;   // Index to next long value.

            public boolean hasNext() {
                return index < size;
            }

            public Long next() {
                long result = array[index];
                index++;
                return result;
            }

            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }
    
    public static void test1() {
        MyLongSet s = new MyLongSet();
        s.add(1);
        s.add(123);
        s.add(-20);
        s.add(1);
        
        Assert.assertEquals(3, s.size());
        Assert.assertTrue(s.contains(-20));
        Assert.assertTrue(s.contains(123));
        Assert.assertTrue(s.contains(1));
        Assert.assertEquals("contains 0", false, s.contains(0));
    }
    
    public static void test2() {
        // A larger set (exceeds 128).
        
        MyLongSet s = new MyLongSet();
        for (int i = 0; i < 200; i++) {
            s.add(i);
        }
        
        Assert.assertTrue(s.isHash());
        long sum = 0;
        for (long v : s.getHashSet()) {
            sum += v;
        }
        
        Assert.assertEquals(199*100, sum);
    }
    
    public static void test3() {
        MyLongSet s = new MyLongSet();
        for (int i = 0; i < 100; i++) {
            s.add(i);
        }
        
        Assert.assertFalse(s.isHash());
        long sum = 0;
        long[] arr = s.getArray();
        
        for (int i = 0; i < s.size(); i++) {
            sum += arr[i];
        }
        
        Assert.assertEquals(99*50, sum);
    }

    public static void testIterator1() {
        MyLongSet s = new MyLongSet();
        for (int i = 0; i < 100; i++) {
            s.add(i);
        }
        
        long sum = 0;
        for (long v : s) {
            sum += v;
        }
        
        Assert.assertEquals(99*50, sum);
    }
    
    public static void testIterator2() {
        MyLongSet s = new MyLongSet();
        for (int i = 0; i < 200; i++) {
            s.add(i);
        }
        
        long sum = 0;
        for (long v : s) {
            sum += v;
        }
        
        Assert.assertEquals(199*100, sum);
    }
}
