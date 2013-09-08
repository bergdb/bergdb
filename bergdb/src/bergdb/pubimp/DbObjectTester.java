package bergdb.pubimp;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Arrays;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadFormatException;

/**
 * Class that tests DbObject and company (DbValue, DbBoolean, DbInt, ...).
 * 
 * @author Frans Lundberg
 */
public class DbObjectTester {
    
    @T
    public static void test0() {
        DbObject obj = new DbObject.Builder().addString("a", "b").build();
        
        Assert.assertEquals(1, obj.getFieldCount());
        Assert.assertEquals("b", obj.getString("a"));
        Assert.assertNull(obj.getString("lastName"));
    }
    
    @T
    public static void test1() {
        DbObject obj = new DbObject.Builder().addString("firstName", "Nalia").build();
        
        Assert.assertEquals(1, obj.getFieldCount());
        Assert.assertEquals("Nalia", obj.getString("firstName"));
        Assert.assertNull(obj.getString("lastName"));
    }
    
    @T
    public static void test2() {
        DbObject obj = new DbObject.Builder()
            .addString("firstName", "Ron")
            .addString("lastName", "Paul").build();
        
        Assert.assertEquals(2, obj.getFieldCount());
        Assert.assertEquals("Ron", obj.getString("firstName"));
        Assert.assertEquals("Paul", obj.getString("lastName"));
        Assert.assertNull(obj.getString("phone"));
    }
    
    @T
    public static void testAssumption1() {
        byte[] b1 = new byte[]{1, 2, 3};
        byte[] b2 = new byte[]{1, 2, 3};
        
        Assert.assertFalse(b1.equals(b2));
        
        b2[1] = 9;
        Assert.assertFalse(b1.equals(b2));
    }
    
    @T
    public static void testAssumption2() {
        byte[] b1 = new byte[]{1, 2, 3};
        byte[] b2 = new byte[]{1, 2, 3};
        
        Assert.assertTrue(Arrays.equals(b1, b2));
        
        b2[1] = 9;
        Assert.assertFalse(Arrays.equals(b1, b2));
    }
    
    @T
    public static void testLong() {
        DbObject obj = new DbObject.Builder()
        .addString("firstName", "Ron")
        .addLong("birth", 1940L).build();
    
        Assert.assertEquals(2, obj.getFieldCount());
        Assert.assertEquals("Ron", obj.getString("firstName"));
        Assert.assertEquals(1940L, obj.getLong("birth"));
    }
    
    private static class TestClass1 {
        public String s = "a string";
        public long value = 12;
    }
    
    private static class TestClass2 extends TestClass1 {
        public String sub = "Sub!";
    }
    
    @T
    public static void testSetObjectFields1() {
        // Simplest possible test for setting object fields.
        TestClass1 object = new TestClass1();
        DbObject t = new DbObject.Builder().addString("s", "Hello there!").build();
        t.toJavaObject(object, new KvToObjectImp());
        
        Assert.assertEquals("Hello there!", object.s);
    }
    
    @T
    public static void testSetObjectFields2() {
        // Tests multiple fields and field types.
        TestClass1 object = new TestClass1();
        DbObject t = new DbObject.Builder()
            .addString("s", "Hello there!").addLong("value", 222L).addString("notMatching", "Not").build();
        t.toJavaObject(object, new KvToObjectImp());
        
        Assert.assertEquals("Hello there!", object.s);
        Assert.assertEquals(222L, object.value);
    }
    
    @T
    public static void testSetObjectFields3() {
        // Tests inheritance.
        TestClass2 object = new TestClass2();
        DbObject t = new DbObject.Builder()
            .addString("s", "Hello there!")
            .addLong("value", 222L)
            .addString("notMatching", "Not")
            .addString("sub", "Nautilus").build();
        t.toJavaObject(object, new KvToObjectImp());
        
        Assert.assertEquals("Hello there!", object.s);
        Assert.assertEquals(222L, object.value);
        Assert.assertEquals("Nautilus", object.sub);
    }
    
    private static class TestClass3 {
        @SuppressWarnings("unused")
        public String name = "T3";
        public long[] ids = new long[]{123, 444};
    }
    
    @T
    public static void tSetObjectFields4() {
        // Tests setting a long array.
        
        TestClass3 object = new TestClass3();
        
        DbObject t = new DbObject.Builder()
            .addString("s", "Hello there!")
            .addArray("ids", new DbArray.Builder().add(new DbLong(1)).add(new DbLong(2)).add(new DbLong(44)).build())
            .build();
        
        Assert.assertArrayEquals(new long[]{123, 444}, object.ids);
        t.toJavaObject(object, new KvToObjectImp());
        Assert.assertArrayEquals(new long[]{1, 2, 44}, object.ids);
    }
    
    @T
    public static void testBadFormatException() {
        byte[] bytes = new byte[3];
        BadFormatException ex = null;
        
        try {
            new DbObject(bytes);
        } catch (BadFormatException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testString1() {
        TestClass1 object = new TestClass1();
        object.s = null;
        object.value = 123;
        
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("s", 's'));
        Assert.assertNull(to.getString("s"));
    }
    
    private static class ByteArrayClass {
        @SuppressWarnings("unused")
        byte[] field;
    }
    
    @T
    public static void testByteArray1() {
        ByteArrayClass object = new ByteArrayClass();
        object.field = new byte[]{-1, 123, Byte.MAX_VALUE};
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'b'));
        byte[] array = to.getByteArray("field");
        Assert.assertEquals(3, array.length);
        //Assert.assertEquals(-1, array[0]);   // :
        //Assert.assertEquals(123, array[1]);  // - 
        Assert.assertEquals(Byte.MAX_VALUE, array[2]);   // *
    }
    
    @T
    public static void testByteArray2() {
        ByteArrayClass object = new ByteArrayClass();
        object.field = new byte[0];
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'b'));
        byte[] array = to.getByteArray("field");
        Assert.assertEquals(0, array.length);
    }
    
    @T
    public static void testByteArray3() {
        ByteArrayClass object = new ByteArrayClass();
        object.field = null;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'b'));
        byte[] array = to.getByteArray("field");
        Assert.assertNull(array);
    }
    
    private static class BooleanClass {
        boolean field;
        public BooleanClass() {}
    }
    
    @T
    public static void testBoolean1() {
        BooleanClass object = new BooleanClass();
        object.field = true;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'n'));
        Assert.assertEquals('n', to.getType("field"));
        Assert.assertEquals(true, to.getBoolean("field"));
    }
    
    @T
    public static void testBoolean2() {
        BooleanClass object = new BooleanClass();
        object.field = false;
        DbObject dbo = DbObject.toDbObject(object);
        Assert.assertTrue(dbo.has("field", 'n'));
        Assert.assertEquals('n', dbo.getType("field"));
        Assert.assertEquals(false, dbo.getBoolean("field"));
        BooleanClass b = dbo.toJavaObject(BooleanClass.class, new KvToObjectImp());
        Assert.assertEquals(false, b.field);
    }
    
    
    private static class IntClass {
        int field;
    }
    
    @T
    public static void testInt1() {
        IntClass object = new IntClass();
        object.field = 1234567890;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'i'));
        Assert.assertEquals('i', to.getType("field"));
        Assert.assertEquals(1234567890, to.getInt("field"));
    }
    
    @T
    public static void testInt2() {
        IntClass object = new IntClass();
        object.field = -1234567890;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'i'));
        Assert.assertEquals('i', to.getType("field"));
        Assert.assertEquals(-1234567890, to.getInt("field"));
        
        IntClass o2 = new IntClass();
        o2.field = 2;
        to.toJavaObject(o2, new KvToObjectImp());
        Assert.assertEquals(-1234567890, o2.field);
    }
    
    public static class FloatClass {
        public float field;
    }
    
    public static class Nested {
        public int myInt = 11;
        public String myString = "hello";
        public String toString() {
            return "Nested, myInt=" + myInt;
        }
    }
    
    public static class ObjectClass {
        public int myInt = 12;
        public Nested nested = new Nested();
        public String toString() {
            return "ObjectClass myInt=" + myInt;
        }
    }
    
    @T
    public static void testObject1() {
        // Tests storing an instance of ObjectClass in a DbObject.
        
        ObjectClass obj = new ObjectClass();
        DbObject to = DbObject.toDbObject(obj);
        
        Assert.assertTrue(to.has("myInt", 'i'));
        Assert.assertFalse(to.has("myInt", 'l'));
        Assert.assertEquals('o', to.getType("nested"));
        Assert.assertEquals(12, to.getInt("myInt"));
        
        DbObject nested = to.getObject("nested");
        Assert.assertTrue("assert nested not null", nested != null);
        Assert.assertEquals(11, nested.getInt("myInt"));
        Assert.assertEquals("hello", nested.getString("myString"));
    }
    
    @T
    public static void testObject2() {
        // Similar to testObject1, but 'nested' is null.
        
        ObjectClass obj = new ObjectClass();
        obj.nested = null;
        DbObject dbo = DbObject.toDbObject(obj);
        
        Assert.assertEquals('o', dbo.getType("nested"));
        Assert.assertEquals(12, dbo.getInt("myInt"));
        
        DbObject nested = dbo.getObject("nested");
        Assert.assertTrue("assert nested.isNull()", nested.isNull());
    }
    
    public static class MultiLevelClass {
        public long myLong = 1234;
        public ObjectClass obj = new ObjectClass();
    }
    
    @T
    public static void testObjectMultiLevel() {
        // 3-level object: MultiLevelClass-ObjectClass-Nested.
        
        MultiLevelClass m = new MultiLevelClass();
        
        DbObject to = DbObject.toDbObject(m);
        Assert.assertEquals(1234, to.getLong("myLong"));
        
        DbObject objectClass = to.getObject("obj");
        Assert.assertEquals(12, objectClass.getInt("myInt"));
        
        DbObject nested = objectClass.getObject("nested");
        Assert.assertEquals(11, nested.getInt("myInt"));
        Assert.assertEquals("hello", nested.getString("myString"));
    }
    
    @T
    public static void testSetObjectFields5() {
        // Tests the storing an object m1 to a DbObject and getting a new object
        // back from the DbObject with the same field values.
        
        MultiLevelClass m1 = new MultiLevelClass();
        m1.myLong = 100;
        m1.obj.myInt = 200;
        m1.obj.nested.myString = "Alea iacta est";
        
        DbObject to = DbObject.toDbObject(m1);
        MultiLevelClass m2 = new MultiLevelClass();
        to.toJavaObject(m2, new KvToObjectImp());
        
        Assert.assertEquals(100, m2.myLong);
        Assert.assertEquals(200, m2.obj.myInt);
        Assert.assertEquals("Alea iacta est", m2.obj.nested.myString);
    }
    
    @T
    public static void testSetObjectFields6() {
        // Tests the storing an object m1 to a DbObject and getting a new object
        // back from the DbObject with the same field values.
        // This test has a null field.
        
        MultiLevelClass m1 = new MultiLevelClass();
        m1.myLong = 101;
        m1.obj.myInt = 202;
        m1.obj.nested = null;
        
        DbObject dbo = DbObject.toDbObject(m1);
        MultiLevelClass m2 = new MultiLevelClass();
        dbo.toJavaObject(m2, new KvToObjectImp());
        
        Assert.assertEquals(101, m2.myLong);
        Assert.assertEquals(202, m2.obj.myInt);
        Assert.assertNull(m2.obj.nested);
    }
    
    private static class IntArrayClass {
        @SuppressWarnings("unused")
        int[] ints;
    }
    
    @T
    public static void testIntArray1() {
        IntArrayClass object = new IntArrayClass();
        object.ints = new int[]{-1, 1234, Integer.MAX_VALUE};
        DbObject d = DbObject.toDbObject(object);
        Assert.assertEquals('a', d.getType("ints"));
        int[] ints = d.getArray("ints").toJavaObject(int[].class, new KvToObjectImp());
        Assert.assertEquals(3, ints.length);
        Assert.assertEquals(-1, ints[0]);
        Assert.assertEquals(1234, ints[1]);
        Assert.assertEquals(Integer.MAX_VALUE, ints[2]);
    }
    
    @T
    public static void testIntArray2() {
        IntArrayClass object = new IntArrayClass();
        object.ints = new int[0];
        DbObject d = DbObject.toDbObject(object);
        Assert.assertTrue(d.has("ints", 'a'));
        int[] ints = (int[]) d.getArray("ints").toJavaObject(int[].class, new KvToObjectImp());
        Assert.assertEquals(0, ints.length);
    }
    
    @T
    public static void testIntArray3() {
        IntArrayClass object = new IntArrayClass();
        object.ints = null;
        DbObject d = DbObject.toDbObject(object);
        Assert.assertTrue(d.has("ints", 'a'));
        int[] ints = d.getArray("ints").toIntArray();
        Assert.assertNull(ints);
    }
    
    
    
    private static class LongArrayClass {
        long[] array;
    }
    
    private static class DoubleArrayClass {
        double[] array;
    }
    
    @T
    public static void testLongArray1() {
        LongArrayClass object = new LongArrayClass();
        object.array = new long[]{-1, 1234, Long.MAX_VALUE};
        DbObject to = DbObject.toDbObject(object);
        Assert.assertEquals('a', to.getType("array"));
        long[] longs = to.getArray("array").toLongArray();
        Assert.assertEquals(3, longs.length);
        Assert.assertEquals(-1, longs[0]);
        Assert.assertEquals(1234, longs[1]);
        Assert.assertEquals(Long.MAX_VALUE, longs[2]);
    }
    
    @T
    public static void testLongArray2() {
        LongArrayClass object = new LongArrayClass();
        object.array = new long[0];
        DbObject to = DbObject.toDbObject(object);
        Assert.assertEquals('a', to.getType("array"));
        long[] longs = to.getArray("array").toLongArray();
        Assert.assertEquals(0, longs.length);
    }
    
    @T
    public static void testLongArray3() {
        LongArrayClass object = new LongArrayClass();
        object.array = null;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertEquals('a', to.getType("array"));
        long[] longs = to.getArray("array").toLongArray();
        Assert.assertNull(longs);
    }
    
    @T
    public static void testLongArray4() {
        LongArrayClass object = new LongArrayClass();
        object.array = new long[]{-1, 1234, Long.MAX_VALUE};
        DbObject dbo = DbObject.toDbObject(object);
        
        LongArrayClass object2 = new LongArrayClass();
        dbo.toJavaObject(object2, new KvToObjectImp());
        
        Assert.assertArrayEquals(object.array, object2.array);
    }


    @T
    public static void testDoubleArray1() {
        DoubleArrayClass object = new DoubleArrayClass();
        object.array = new double[]{-1.2, 1234.5, 
                Double.MAX_VALUE, Double.NaN, Double.POSITIVE_INFINITY};
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("array", 'a'));
        double[] array = to.getArray("array").toDoubleArray();
        Assert.assertEquals(5, array.length);
        Assert.assertEquals(-1.2, array[0]);
        Assert.assertEquals(1234.5, array[1]);
        Assert.assertEquals(Double.MAX_VALUE, array[2]);
        Assert.assertEquals(Double.NaN, array[3]);
        Assert.assertEquals(Double.POSITIVE_INFINITY, array[4]);
    }
    
    @T
    public static void testDoubleArray2() {
        DoubleArrayClass object = new DoubleArrayClass();
        object.array = new double[0];
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("array", 'a'));
        double[] array = to.getArray("array").toDoubleArray();
        Assert.assertEquals(0, array.length);
    }
    
    @T
    public static void testDoubleArray3() {
        DoubleArrayClass object = new DoubleArrayClass();
        object.array = null;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("array", 'a'));
        double[] array = to.getArray("array").toDoubleArray();
        Assert.assertNull(array);
    }
    
    @T
    public static void testDoubleArray4() {
        DoubleArrayClass object = new DoubleArrayClass();
        object.array = new double[]{1.2, -123.4};
        DbObject dbo = DbObject.toDbObject(object);
        
        DoubleArrayClass object2 = dbo.toJavaObject(DoubleArrayClass.class, new KvToObjectImp());
        Assert.assertArrayEquals(object.array, object2.array);
    }
    
    /**
     * Class with fields that are arrays of primitive types.
     */
    private static class PrimitiveArrays {
        boolean[] booleans;
        byte[] bytes;
        char[] chars;
        short[] shorts;
        int[] ints;
        long[] longs;
        float[] floats;
        double[] doubles;
        
        public PrimitiveArrays() {}
        
        void setThem1() {
            booleans = new boolean[] { true, true, false, true };
            bytes = new byte[] {1, -2};
            chars = new char[] {'a'};
            shorts = new short[] { Short.MIN_VALUE, Short.MAX_VALUE, 1 };
            ints = new int[] { Integer.MIN_VALUE, 111222333 };
            longs = new long[] {Long.MAX_VALUE, -111222333444L, 111125L };
            floats = new float[] { 1.0f, Float.MAX_VALUE, 1234.567f };
            doubles = new double[] {1.0, Double.MAX_VALUE, Double.MIN_VALUE, 1.2e100};
        }
        
        void setThem2() {
            setThem1();
            booleans = new boolean[] {};
            bytes = null;
            chars = new char[] {'a'};
            shorts = null;
            ints = new int[] { Integer.MIN_VALUE, 111222333 };
            longs = null;
            floats = null;
            doubles = new double[] {1.0, Double.MAX_VALUE, Double.MIN_VALUE, 1.2e100};
        }
    }
    
    @T
    public static void testPrimitiveArrays0() {
        PrimitiveArrays p0 = new PrimitiveArrays();
        p0.setThem1();
        
        DbObject dbo = DbObject.toDbObject(p0);
        PrimitiveArrays p1 = dbo.toJavaObject(PrimitiveArrays.class, new KvToObjectImp());
        
        Assert.assertArrayEquals(p0.booleans, p1.booleans);
        Assert.assertArrayEquals(p0.bytes, p1.bytes);
        Assert.assertArrayEquals(p0.chars, p1.chars);
        Assert.assertArrayEquals(p0.shorts, p1.shorts);
        Assert.assertArrayEquals(p0.ints, p1.ints);
        Assert.assertArrayEquals(p0.longs, p1.longs);
        Assert.assertArrayEquals(p0.floats, p1.floats);
        Assert.assertArrayEquals(p0.doubles, p1.doubles);
    }
    
    @T
    public static void testPrimitiveArrays1() {
        PrimitiveArrays p0 = new PrimitiveArrays();
        p0.setThem2();
        
        DbObject dbo = DbObject.toDbObject(p0);
        PrimitiveArrays p1 = dbo.toJavaObject(PrimitiveArrays.class, new KvToObjectImp());
        
        Assert.assertArrayEquals(p0.booleans, p1.booleans);
        Assert.assertArrayEquals(p0.bytes, p1.bytes);
        Assert.assertArrayEquals(p0.chars, p1.chars);
        Assert.assertArrayEquals(p0.shorts, p1.shorts);
        Assert.assertArrayEquals(p0.ints, p1.ints);
        Assert.assertArrayEquals(p0.longs, p1.longs);
        Assert.assertArrayEquals(p0.floats, p1.floats);
        Assert.assertArrayEquals(p0.doubles, p1.doubles);
    }
    
    @T
    public static void testPrimitiveArrays2() {
        // Tests arrays values that are null.
        
        PrimitiveArrays p0 = new PrimitiveArrays();
        
        DbObject dbo = DbObject.toDbObject(p0);
        PrimitiveArrays p1 = new PrimitiveArrays();
        p1.setThem1();
        dbo.toJavaObject(p1, new KvToObjectImp());
        
        Assert.assertArrayEquals(p0.booleans, p1.booleans);
        Assert.assertArrayEquals(p0.bytes, p1.bytes);
        Assert.assertArrayEquals(p0.chars, p1.chars);
        Assert.assertArrayEquals(p0.shorts, p1.shorts);
        Assert.assertArrayEquals(p0.ints, p1.ints);
        Assert.assertArrayEquals(p0.longs, p1.longs);
        Assert.assertArrayEquals(p0.floats, p1.floats);
        Assert.assertArrayEquals(p0.doubles, p1.doubles);
    }
    
    /**
     * String, String[], String[][], String[][][] fields this class.
     */
    @SuppressWarnings("unused")
    private static class Strings {
        String s0a;
        String s0b;
        String[] s1a;
        String[] s1b;
        String[] s1c;
        String[][] s2a;
        String[][] s2b;
        String[][] s2c;
        
        public Strings() {}
        
        void setThem1() {
            s0a = "a";
            s0b = null;
            
            s1a = new String[] { "a", "hello" };
            
            s2a = new String[][] {
                    new String[] { "a", null },
                    new String[] { "We spend our time searching for security and hate it when we get it." }
            };
            
            s2b = null;
            
            s2c = new String[][] {
                    new String[] { "a", null },
                    new String[] { "We spend our time searching for security and hate it when we get it." },
                    null
            };
        }
    }

    public static class StringArrayClass {
        public String[] strings;
    }
    
    @T
    public static void testStrings0() {
        Strings s0 = new Strings();
        s0.setThem1();
        
        DbObject dbo = DbObject.toDbObject(s0);
        Strings s1 = (Strings) dbo.toJavaObject(Strings.class, new KvToObjectImp());
        
        Assert.assertEquals(s0.s0a, s1.s0a);
        Assert.assertNull(s1.s0b);
        Assert.assertArrayEquals(s0.s1a, s1.s1a);
    }
    
    @T
    public static void testStrings1() {
        // Tests storing an array of strings.
        
        String[] myStrings1 = new String[]{"first", "second"};
        StringArrayClass obj1 = new StringArrayClass();
        obj1.strings = myStrings1;
        DbObject dbo1 = DbObject.toDbObject(obj1);
        byte[] bytes = dbo1.getBytes();
        
        // Stored to bytes, lets try to get it back to a String[].
        DbObject dbo2 = new DbObject(bytes);
        StringArrayClass obj2 = (StringArrayClass) dbo2.toJavaObject(
                StringArrayClass.class, new KvToObjectImp());
        String[] myStrings2 = obj2.strings;
        
        // Assert
        
        Assert.assertEquals("first", myStrings2[0]);
        Assert.assertEquals("second", myStrings2[1]);
    }
    
    @T
    public static void testStrings2() {
        // Like previous test, but with null-value.
        
        String[] myStrings1 = new String[]{null, "second"};
        StringArrayClass obj1 = new StringArrayClass();
        obj1.strings = myStrings1;
        DbObject dbo1 = DbObject.toDbObject(obj1);
        byte[] bytes = dbo1.getBytes();
        
        // Stored to bytes, lets try to get it back to a String[].
        DbObject dbo2 = new DbObject(bytes);
        StringArrayClass obj2 = (StringArrayClass) dbo2.toJavaObject(
                StringArrayClass.class, new KvToObjectImp());
        String[] myStrings2 = obj2.strings;
        
        // Assert
        
        Assert.assertNull(myStrings2[0]);
        Assert.assertEquals("second", myStrings2[1]);
    }
    
    private static class IntArray5D implements Serializable {
        private static final long serialVersionUID = 1L;
        
        int[][][][][] array;
        
        public IntArray5D() {}
        
        void set() {
            array = new int[1][2][3][1][2];
            array[0][1][2][0][0] = 1200;
            array[0][0][1][0][0] = 100;
            array[0][0][0] = null;
        }
    }
    
    @T
    public static void test5DIntArray() throws IOException {
        IntArray5D obj0 = new IntArray5D();
        obj0.set();
        
        DbObject dbo = DbObject.toDbObject(obj0);
        IntArray5D obj1 = dbo.toJavaObject(IntArray5D.class, new KvToObjectImp());
        
        byte[] bytes0 = serialize(obj0);
        byte[] bytes1 = serialize(obj1);
        Assert.assertArrayEquals(bytes0, bytes1);
    }
    
    private static class Customer implements Serializable {
        private static final long serialVersionUID = 1L;
        
        String name;
        int id;
        
        public Customer() {}
        public Customer(int id, String name) {
            this.id = id;
            this.name = name;
        }
        public String toString() {
            return id + "-" + name;
        }
    }
    
    private static class CustomerArray implements Serializable {
        private static final long serialVersionUID = 1L;
        
        Customer[][][][] array;
        
        public CustomerArray() {}
        
        void set() {
            array = new Customer[1][2][3][3];
            array[0][0][0][0] = new Customer(20, "Gustav");
            array[0][0][0][1] = null;
            array[0][0][0][2] = new Customer(21, "Anna");
            array[0][0][1] = null;
        }
    }
    
    @T
    public static void test4DCustomerArray() throws IOException {
        CustomerArray obj0 = new CustomerArray();
        obj0.set();
        
        DbObject dbo = DbObject.toDbObject(obj0);
        CustomerArray obj1 = dbo.toJavaObject(CustomerArray.class, new KvToObjectImp());
        byte[] bytes0 = serialize(obj0);
        byte[] bytes1 = serialize(obj1);
        Assert.assertArrayEquals(bytes0, bytes1);
        
        Assert.assertEquals(21, obj1.array[0][0][0][2].id);
        Assert.assertEquals("Anna", obj1.array[0][0][0][2].name);
        Assert.assertNull(obj1.array[0][0][1]);
        
        Assert.assertNull(obj1.array[0][0][0][1]);
    }
    
    @T
    public static void testStrings2D() {
        Strings s0 = new Strings();
        s0.setThem1();
        
        DbObject dbo = DbObject.toDbObject(s0);
        Strings s1 = dbo.toJavaObject(Strings.class, new KvToObjectImp());
        
        Assert.assertNull(s1.s2b);
        Assert.assertEquals(3, s1.s2c.length);
        Assert.assertEquals(2, s1.s2c[0].length);
        Assert.assertEquals("a", s1.s2c[0][0]);
        Assert.assertNull(s1.s2c[0][1]);
        Assert.assertEquals(1, s1.s2c[1].length);
        Assert.assertNull(s1.s2c[2]);
    }
    
    private static class Circular0 {
        Circular1 c;
        public Circular0() {}
    }
    
    private static class Circular1 {
        @SuppressWarnings("unused")
        Circular0 c;
        public Circular1() {}
    }
    
    /** 
     * Circular references will throw StackOverFlowException.
     * This test on my (Frans's) machine (rose) currently (130529) runs in 80 ms
     * and the error condition seem not to disturb the rest of the code.
     * The tests is only run in an ordinary Java environment, not on IKVM, GCJ, Android.
     */
    @T
    public static void testCircularRefs() {
        if (Util.runsIkvm() || Util.runsGcj() || Util.runsAndroid()) {
            return;
        }
        
        Circular0 obj = new Circular0();
        obj.c = new Circular1();
        obj.c.c = obj;
        
        StackOverflowError ex = null;
        try {
            DbObject.toDbObject(obj);
        } catch (StackOverflowError e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    private static class SuperOne {
        int a;
        int b;
        public SuperOne() {}
    }
    
    private static class MyClass extends SuperOne {
        int c;
        public MyClass() {
            super();
        }
    }
    
    @T
    public static void testHierarchy() {
        MyClass obj0 = new MyClass();
        obj0.a = 1;
        obj0.b = 2;
        obj0.c = 3;
        
        DbObject dbo = DbObject.toDbObject(obj0);
        MyClass obj1 = dbo.toJavaObject(MyClass.class, new KvToObjectImp());
        
        Assert.assertEquals(1, obj1.a);
        Assert.assertEquals(2, obj1.b);
        Assert.assertEquals(3, obj1.c);
    }
    
    private static class MyClass2a {
        long a;
    }
    
    @T
    public static void testPrivateConstructor() {
        MyClass2a obj0 = new MyClass2a();
        obj0.a = 123;
        DbObject dbo = DbObject.toDbObject(obj0);
        MyClass2a obj1 = dbo.toJavaObject(MyClass2a.class, new KvToObjectImp());
        Assert.assertEquals(123, obj1.a);
    }
    
    private static class MyClass2b {
        long a;
    }
    
    @T
    public static void testTypeSwitch() {
        MyClass2a obj0 = new MyClass2a();
        obj0.a = -111222333444L;
        DbObject dbo = DbObject.toDbObject(obj0);
        MyClass2b obj1 = dbo.toJavaObject(MyClass2b.class, new KvToObjectImp());
        Assert.assertEquals(obj0.a, obj1.a);
    }
    
    /**
     * Helper method for tests that serializes a Java object with ObjectOutputStream.
     */
    public static byte[] serialize(Serializable object) throws IOException {
        ByteArrayOutputStream b = new ByteArrayOutputStream();
        ObjectOutputStream o = new ObjectOutputStream(b);
        o.writeObject(object);
        return b.toByteArray();
    }
    
    @T
    public static void testNullField0() {
        TestClass1 obj0 = new TestClass1();
        obj0.s = null;
        DbObject dbo = DbObject.toDbObject(obj0);
        TestClass1 obj1 = dbo.toJavaObject(TestClass1.class, new KvToObjectImp());
        
        Assert.assertNull(obj1.s);
    }
    
    private static class A {
        TestClass1 field = new TestClass1();
    }
    
    @T
    public static void testNullField1() {
        A obj0 = new A();
        obj0.field = null;
        DbObject dbo = DbObject.toDbObject(obj0);
        A obj1 = dbo.toJavaObject(A.class, new KvToObjectImp());
        
        Assert.assertNull(obj1.field);
    }
    
    public static class TestClass4 {
        public String[] array;
    }
   
    @T
    public static void testStringArray0() {
        TestClass4 obj1 = new TestClass4();
        obj1.array = new String[]{"1", "2", null, "4"};
        DbObject dbo = DbObject.toDbObject(obj1);
        TestClass4 obj2 = dbo.toJavaObject(TestClass4.class, new KvToObjectImp());
        
        Assert.assertEquals(4, obj2.array.length);
        Assert.assertEquals("1", obj2.array[0]);
        Assert.assertNull(obj2.array[2]);
    }
    
    @T
    public static void testArray0() {
        String[] myStrings1 = new String[]{"first", "second"};
        DbObject dbo = DbObject.toDbObject(myStrings1);
        Assert.assertTrue("assert dbo not null", dbo != null);        
        String[] myStrings2 = dbo.toJavaObject(String[].class, new KvToObjectImp());
        Assert.assertEquals(2, myStrings2.length);
        Assert.assertEquals("first", myStrings2[0]);
        Assert.assertEquals("second", myStrings2[1]);
    }
    
    @T
    public static void testArray1() {
        // Like previous test, but with a null value in array.
        String[] myStrings1 = new String[]{null, "second"};
        DbObject dbo = DbObject.toDbObject(myStrings1);
        
        String[] myStrings2 = dbo.toJavaObject(String[].class, new KvToObjectImp());
        Assert.assertEquals(2, myStrings2.length);
        Assert.assertNull(myStrings2[0]);
        Assert.assertEquals("second", myStrings2[1]);
    }
    
    @T
    public static void testArray2() {
        // Tests with an array using a custom class.
        Customer[] c = new Customer[]{new Customer(), new Customer()};
        c[0].id = 11;
        c[0].name = "A";
        c[1].id = 22;
        c[1].name = "B";
        
        DbObject dbo = DbObject.toDbObject(c);
        
        Customer[] c2 = dbo.toJavaObject(Customer[].class, new KvToObjectImp());
        Assert.assertEquals(2, c2.length);
        Assert.assertEquals(c[0].id, c2[0].id);
        Assert.assertEquals(c[0].name, c2[0].name);
        Assert.assertEquals(c[1].id, c2[1].id);
        Assert.assertEquals(c[1].name, c2[1].name);
    }
    
    @T
    public static void testArray3() {
        // Tests storing an array of primitive values.
        
        int[] ints0 = new int[]{1, 2, -100, Integer.MAX_VALUE};
        DbObject dbo = DbObject.toDbObject(ints0);
        int[] ints1 = dbo.toJavaObject(int[].class, new KvToObjectImp());
        Assert.assertArrayEquals(ints0, ints1);
    }
    
    @T
    public static void testArray4() {
        // Tests storing a multi-dimensional array.
        
        int[][] ints0 = new int[][] {
            new int[] { 1, 10 },
            null,
            new int[] {}
        };
        
        DbObject dbo = DbObject.toDbObject(ints0);
        int[][] ints1 = dbo.toJavaObject(int[][].class, new KvToObjectImp());
        
        Assert.assertEquals(ints0.length, ints1.length);
        for (int i = 0; i < ints0.length; i++) {
            Assert.assertArrayEquals(ints0[i], ints1[i]);
        }
    }
    
    public static void testPrimitive0() {
        DbObject dbo1 = DbObject.toDbObject(1234);
        Integer theInt = dbo1.toJavaObject(Integer.class, new KvToObjectImp());
        Assert.assertEquals(1234, theInt.intValue());
    }
    
    public static void testPrimitive1() {
        // Same as previous, but uses int.class instead of Integer.class.
        DbObject dbo1 = DbObject.toDbObject(1234);
        int theInt = dbo1.toJavaObject(int.class, new KvToObjectImp());
        Assert.assertEquals(1234, theInt);
    }
    
    public static void testPrimitive2() {
        DbObject dbo1 = DbObject.toDbObject(true);
        boolean result = dbo1.toJavaObject(boolean.class, new KvToObjectImp());
        Assert.assertEquals(true, result);
    }
    
    public static void testPrimitive3() {
        DbObject dbo1 = DbObject.toDbObject(123.45);
        double result = dbo1.toJavaObject(double.class, new KvToObjectImp());
        Assert.assertEquals(123.45, result);
    }
    
    public static void testPrimitive4() {
        DbObject dbo1 = DbObject.toDbObject(Double.NaN);
        double result = dbo1.toJavaObject(double.class, new KvToObjectImp());
        Assert.assertTrue(Double.isNaN(result));
    }
    
    public static void main(String[] args) {
    }
}
