package bergdb.pubimp;

import java.io.ByteArrayOutputStream;
import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;


/**
 * <p>An instance of this class represents an array of values as it is stored in the database.
 * A DbArray object is immutable. The array elements each have independent types.
 * Each element can be of any of the seven DbObject types:</p>
 * 
 * <pre>
 * n - boolean
 * l - integer, 64 bits
 * d - double
 * s - string
 * b - byteArray
 * a - array, nested array, a DbArray.
 * o - object, a DbObject.
 * </pre>
 * 
 * <p>The array may be of zero length. It is never null, and no element is null: an array has
 * no absent element (bergdb 020-04, section 2.1). Its bytes are Binson's: 0x42, the
 * elements, 0x43 (bergdb 020-07, section 4.1).</p>
 *
 * <p>Experimental in 2026.3, with known faults; it may change in a later release (bergdb
 * 018-01, D6).</p>
 * 
 * @author Frans Lundberg
 */
public class DbArray extends DbValue implements Iterable<DbValue> {
    private final byte[] bytes;     // the array's encoding: 0x42, the elements, 0x43
    private final int elementCount;
    private int height;             // its levels, 1 or more; 0 until computed
    
    private DbArray(byte[] bytes, int elementCount, int height) {
        super('a');
        assert elementCount >= 0;
        assert bytes.length >= 2;
        this.bytes = bytes;
        this.elementCount = elementCount;
        this.height = height;
    }
    
    /**
     * Returns the number of elements in the array.
     */
    public int getSize() {
        return elementCount;
    }
    
    public String toString() {
        return "a:" + elementCount;
    }
    
    int height() {
        if (height == 0) {
            height = ObjectFormat.heightAt(bytes, 0);
        }
        return height;
    }
    
    public int getByteSize() {
        return bytes.length;
    }
    
    public int write(byte[] b, int offset) {
        System.arraycopy(bytes, 0, b, offset, bytes.length);
        offset += bytes.length;
        return offset;
    }
    
    @SuppressWarnings("unchecked")
    public <TYPE> TYPE toJavaObject(Class<TYPE> c, ClassToObject c2o) {
        if (c == null) {
            throw new IllegalArgumentException("c == null not allowed");
        }
        
        if (c2o == null) {
            throw new IllegalArgumentException("c2o == null not allowed");
        }
        
        Object result;
        
        if (c.isArray()) {
            Class<?> componentType = c.getComponentType();
            assert componentType != null;
            
            int size = this.getSize();
            Object array = Array.newInstance(componentType, size);
            int index = 0;
            
            for (DbValue v : this) {
                Array.set(array, index++, v.toJavaObject(componentType, c2o));
            }
            result = array;
        } else {
            result = super.toJavaObject(c, c2o);
        }
        
        return (TYPE) result;
    }
    
    public int[] toIntArray() {
        int[] result = new int[elementCount];
        int index = 0;
        
        for (DbValue v : this) {
            result[index++] = v.toInt();
        }
        return result;
    }
    
    public long[] toLongArray() {
        long[] result = new long[elementCount];
        int index = 0;
        
        for (DbValue v : this) {
            result[index++] = v.toLong();
        }
        return result;
    }
    
    public double[] toDoubleArray() {
        double[] result = new double[elementCount];
        int index = 0;
        
        for (DbValue v : this) {
            result[index++] = v.toDouble();
        }
        return result;
    }
    
    public Iterator<DbValue> iterator() {
        return new ElementIterator();
    }
    
    /** The array at 'p' of checked bytes, a copy of its bytes (bergdb 020-07, section 4.1). */
    static DbArray read(byte[] b, int p) {
        byte[] bytes = Arrays.copyOfRange(b, p, ObjectFormat.valueEnd(b, p));
        int count = 0;
        for (int q = 1; (bytes[q] & 0xff) != ObjectFormat.ARRAY_END; 
                q = ObjectFormat.valueEnd(bytes, q)) {
            count++;
        }
        return new DbArray(bytes, count, 0);
    }
    
    /** The elements, each read by its type byte. */
    private class ElementIterator implements Iterator<DbValue> {
        private int offset = 1;
        
        public boolean hasNext() {
            return (bytes[offset] & 0xff) != ObjectFormat.ARRAY_END;
        }

        public DbValue next() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            DbValue result = DbValue.read(bytes, offset);
            offset = ObjectFormat.valueEnd(bytes, offset);
            return result;
        }

        /**
         * Always throws UnsupportedOperationException.
         * 
         * @throws UnsupportedOperationException
         */
        public void remove() {
            throw new UnsupportedOperationException();   
        }
    }
    
    /**
     * A builder object used to create a DbArray.
     * The builder object is not thread-safe, use it from one thread.
     */
    public static class Builder {
        private final ByteArrayOutputStream out = new ByteArrayOutputStream();
        private int elementCount = 0;
        private int height = 1;
        
        public Builder() {
            out.write(ObjectFormat.ARRAY_START);
        }
        
        /**
         * Adds an element.
         * 
         * @throws IllegalArgumentException  If 'value' is null: an array has no absent
         *      element, and BergDB stores no null (bergdb 020-04, section 2.1).
         */
        public Builder add(DbValue value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed: an array has "
                        + "no absent element (bergdb 020-04, section 2.1)");
            }
            
            int byteSize = value.getByteSize();
            byte[] buffer = new byte[byteSize];
            value.write(buffer, 0);
            out.write(buffer, 0, buffer.length);
            elementCount++;
            height = Math.max(height, 1 + value.height());
            return this;
        }
        
        /**
         * Builds the array.
         * 
         * @throws IllegalArgumentException  If it has more than 15 levels of arrays and
         *      objects: an array is at level 2 or below, and no level is above 16 (bergdb
         *      020-07, R14).
         */
        public DbArray build() {
            if (height > ObjectFormat.MAX_LEVELS - 1) {
                throw new IllegalArgumentException("The array has " + height + " levels of "
                        + "arrays and objects; an array is at level 2 or below, and no level "
                        + "is above " + ObjectFormat.MAX_LEVELS + " (bergdb 020-07, R14).");
            }
            byte[] b = Arrays.copyOf(out.toByteArray(), out.size() + 1);
            b[b.length - 1] = (byte) ObjectFormat.ARRAY_END;
            return new DbArray(b, elementCount, height);
        }
    }
    
    // ---- Tests ----
    
    @Nano
    public static void test0() {
        DbArray a = new DbArray.Builder().build();
        Assert.assertEquals(0, a.getSize());
    }
    
    @Nano
    public static void test1() {
        DbArray a = new DbArray.Builder().add(new DbDouble(1.2)).add(new DbString("hello")).build();
        Assert.assertEquals(2, a.getSize());
        Assert.assertEquals(1 + 9 + 7 + 1, a.getByteSize());
        Assert.assertEquals(1, a.height());
    }
    
    @Nano
    public static void testIterator0() {
        DbArray a = new DbArray.Builder().build();
        Assert.assertEquals(0, a.getSize());
        
        for (DbValue v : a) {
            throw new RuntimeException("We should not get here! v = " + v);
        }
    }
    
    @Nano
    public static void testIterator1() {
        DbArray a = new DbArray.Builder().add(new DbLong(3)).build();
        Assert.assertEquals(1, a.getSize());
        Assert.assertEquals(1 + 2 + 1, a.getByteSize());     // 42, the integer 10 03, 43
        
        for (DbValue v : a) {
            Assert.assertEquals(v.getType(), 'l');
            Assert.assertEquals(3, v.toInt());
        }
    }
}
