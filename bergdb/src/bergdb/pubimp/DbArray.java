package bergdb.pubimp;

import java.io.ByteArrayOutputStream;
import java.lang.reflect.Array;
import java.util.Iterator;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadFormatException;


/**
 * <p>An instance of this class represents an array of values as it is stored in the database.
 * A DbArray object is immutable. The array elements each have independent types.
 * Each element can be of any of the eight DbObject types:</p>
 * 
 * <pre>
 * n - boolean
 * i - int 
 * l - long
 * d - double
 * s - string
 * b - byteArray
 * a - array, nested array, a DbArray.
 * o - object, a DbObject.
 * </pre>
 * 
 * <p>The array may be of zero length and it may have the value null.</p>
 * 
 * @author Frans Lundberg
 */
public class DbArray extends DbValue implements Iterable<DbValue> {
    private final byte[] bytes;     // bytes that encodes the elements of the array
    private final int elementCount;
    
    private DbArray(byte[] bytes, int elementCount) {
        super('a');
        assert elementCount >= 0;
        
        if (bytes == null) {
            throw new IllegalArgumentException("bytes == null not allowed");
        }
        
        if (bytes.length < 1) {
            throw new IllegalArgumentException("bytes.length too small, " + bytes.length);
        }
        
        this.bytes = bytes;
        this.elementCount = elementCount;
    }
    
    /**
     * Returns the internal serialized form of the DbArray.
     * The returned array is not a copy, the caller must not modify the bytes.
     */
    public byte[] getBytes() {
        assert bytes != null;
        return bytes;
    }
    
    /**
     * Returns the number of elements in the array.
     */
    public int getSize() {
        return elementCount;
    }
    
    public String toString() {
        String result = isNull() ? "a:null" : "a:" + elementCount;
        return result;
    }
    
    public boolean isNull() {
        return bytes[0] == 'Z';
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
        
        if (isNull()) {
            return null;
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
        if (isNull()) {
            return null;
        }
        
        int[] result = new int[elementCount];
        int index = 0;
        
        for (DbValue v : this) {
            result[index++] = v.toInt();
        }
        return result;
    }
    
    public long[] toLongArray() {
        if (isNull()) {
            return null;
        }
        
        long[] result = new long[elementCount];
        int index = 0;
        
        for (DbValue v : this) {
            result[index++] = v.toLong();
        }
        return result;
    }
    
    public double[] toDoubleArray() {
        if (isNull()) {
            return null;
        }
        
        double[] result = new double[elementCount];
        int index = 0;
        
        for (DbValue v : this) {
            result[index++] = v.toDouble();
        }
        return result;
    }
    
    public String[] toStringArray() {
        if (isNull()) {
            return null;
        }
        
        String[] result = new String[elementCount];
        int index = 0;
        
        for (DbValue v : this) {
            result[index++] = v.toString();
        }
        return result;
    }
    
    public Iterator<DbValue> iterator() {
        return new ElementIterator(bytes, 0);
    }
    
    public static DbArray parse(byte[] buffer, int offset) {
        int offset0 = offset;
        ElementIterator iter = new ElementIterator(buffer, offset);
        while (iter.hasNext()) {
            iter.next();
        }
        
        int size = iter.getOffset() - offset0;
        byte[] bytes = new byte[size];
        
        try {
            System.arraycopy(buffer, offset, bytes, 0, size);
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new ArrayIndexOutOfBoundsException("offset=" + offset 
                    + ", buffer.length=" + buffer.length + ", bytes.length=" 
                    + bytes.length + ", size=" + size);
        }
        
        DbArray result = new DbArray(bytes, iter.getElementCount());
        return result;
    }
    
    private static class ElementIterator implements Iterator<DbValue> {
        private final byte[] bytes;
        private int offset;
        private char nextType;
        private int elementCount = 0;
        
        ElementIterator(byte[] bytes, int offset) {
            assert bytes != null;
            assert offset >= 0;
            assert offset < bytes.length : "offset=" + offset + ", bytes.length=" + bytes.length;
            this.bytes = bytes;
            this.offset = offset;
            this.nextType = (char) bytes[offset];
            this.offset++;
        }
        
        public boolean hasNext() {
            return nextType != 'z' && nextType != 'Z';
        }

        public DbValue next() {
            if (!hasNext()) {
                throw new IllegalStateException("No next value.");
            }
            
            char type = nextType;
            DbValue result;
            
            switch (type) {
            case 'n':
                result = DbBoolean.parse(bytes, offset);
                break;
            case 'i':
                result = DbInt.parse(bytes, offset);
                break;
            case 'l':
                result = DbLong.parse(bytes, offset);
                break;
            case 'd':
                result = DbDouble.parse(bytes, offset);
                break;
            case 's':
                result = DbString.parse(bytes, offset);
                break;
            case 'b':
                result = DbByteArray.parse(bytes, offset);
                break;
            case 'a':
                result = DbArray.parse(bytes, offset);
                break;
            case 'o':
                result = DbObject.parse(bytes, offset);
                break;
            default:
                throw new BadFormatException("Bad type: " + type);
            }
            
            offset += result.getByteSize();
            nextType = (char) bytes[offset];
            offset += 1;
            elementCount++;            
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
        
        public int getOffset() {
            return offset;
        }
        
        public int getElementCount() {
            return elementCount;
        }
    }
    
    /**
     * A builder object used to create a DbArray.
     * The builder object is not thread-safe, use it from one thread.
     */
    public static class Builder {
        private final ByteArrayOutputStream out = new ByteArrayOutputStream();
        private int elementCount = 0;
        
        public Builder() {
        }
        
        /**
         * Returns the special null-value DbArray that represent an array with the value null.
         */
        public static DbArray buildNull() {
            DbArray result = new DbArray(new byte[]{(byte) 'Z'}, 0);
            return result;
        }
        
        public Builder add(DbValue value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed");
            }
            
            int byteSize = value.getByteSize();
            byte[] buffer = new byte[byteSize];
            value.write(buffer, 0);
            out.write(value.getType());
            out.write(buffer, 0, buffer.length);
            elementCount++;
            return this;
        }
        
        public DbArray build() {
            out.write('z');     // 'z' to mark end of array. No more elements.
            return new DbArray(out.toByteArray(), elementCount);
        }
    }
    
    // ---- Tests ----
    
    @T
    public static void test0() {
        DbArray a = new DbArray.Builder().build();
        Assert.assertEquals(0, a.getSize());
    }
    
    @T
    public static void test1() {
        DbArray a = new DbArray.Builder().add(new DbDouble(1.2)).add(new DbString("hello")).build();
        Assert.assertEquals(2, a.getSize());
        Assert.assertFalse(a.isNull());
    }
    
    @T
    public static void testNull() {
        DbArray a = DbArray.Builder.buildNull();
        Assert.assertTrue(a.isNull());
    }
    
    @T
    public static void testIterator0() {
        DbArray a = new DbArray.Builder().build();
        Assert.assertEquals(0, a.getSize());
        
        for (DbValue v : a) {
            throw new RuntimeException("We should not get here! v = " + v);
        }
    }
    
    @T
    public static void testIterator1() {
        DbArray a = new DbArray.Builder().add(new DbInt(3)).build();
        Assert.assertEquals(1, a.getSize());
        Assert.assertEquals(1 + 4 + 1, a.getByteSize());
        
        for (DbValue v : a) {
            Assert.assertEquals(v.getType(), 'i');
            Assert.assertEquals(3, v.toInt());
        }
    }
}
