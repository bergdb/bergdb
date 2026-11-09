package bergdb.pubimp;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Arrays;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.DbArray;
import bergdb.pub.DbBoolean;
import bergdb.pub.DbByteArray;
import bergdb.pub.DbDouble;
import bergdb.pub.DbLong;
import bergdb.pub.DbObject;
import bergdb.pub.DbString;
import bergdb.pub.DbValue;
import bergdb.pub.util.BadFormatException;

/**
 * Class that tests DbObject and company (DbValue, DbBoolean, DbLong, ...).
 * 
 * @author Frans Lundberg
 */
public class DbObjectTester {
    private DbObjectTester() {}
    
    @Nano
    public static void test0() {
        DbObject obj = new DbObject.Builder().addString("a", "b").build();
        
        Assert.assertEquals(1, obj.getFieldCount());
        Assert.assertEquals("b", obj.getString("a"));
        Assert.assertNull(obj.getString("lastName"));
    }
    
    @Nano
    public static void test1() {
        DbObject obj = new DbObject.Builder().addString("firstName", "Nalia").build();
        
        Assert.assertEquals(1, obj.getFieldCount());
        Assert.assertEquals("Nalia", obj.getString("firstName"));
        Assert.assertNull(obj.getString("lastName"));
    }
    
    @Nano
    public static void test2() {
        DbObject obj = new DbObject.Builder()
            .addString("firstName", "Ron")
            .addString("lastName", "Paul").build();
        
        Assert.assertEquals(2, obj.getFieldCount());
        Assert.assertEquals("Ron", obj.getString("firstName"));
        Assert.assertEquals("Paul", obj.getString("lastName"));
        Assert.assertNull(obj.getString("phone"));
    }
    
    @Nano
    public static void testAssumption1() {
        byte[] b1 = new byte[]{1, 2, 3};
        byte[] b2 = new byte[]{1, 2, 3};
        
        Assert.assertFalse(b1.equals(b2));
        
        b2[1] = 9;
        Assert.assertFalse(b1.equals(b2));
    }
    
    @Nano
    public static void testAssumption2() {
        byte[] b1 = new byte[]{1, 2, 3};
        byte[] b2 = new byte[]{1, 2, 3};
        
        Assert.assertTrue(Arrays.equals(b1, b2));
        
        b2[1] = 9;
        Assert.assertFalse(Arrays.equals(b1, b2));
    }
    
    @Nano
    public static void testLong() {
        DbObject obj = new DbObject.Builder()
        .addString("firstName", "Ron")
        .addLong("birth", 1940L).build();
    
        Assert.assertEquals(2, obj.getFieldCount());
        Assert.assertEquals("Ron", obj.getString("firstName"));
        Assert.assertEquals(1940L, obj.getLong("birth"));
    }
    
    public static class TestClass1 {
        public String s = "a string";
        public long value = 12;
    }
    
    public static class TestClass2 extends TestClass1 {
        public String sub = "Sub!";
    }
    
    @Nano
    public static void testSetObjectFields1() {
        // Simplest possible test for setting object fields.
        DbObject t = new DbObject.Builder().addString("s", "Hello there!").build();
        TestClass1 object = t.toJavaObject(TestClass1.class);
        
        Assert.assertEquals("Hello there!", object.s);
    }
    
    @Nano
    public static void testSetObjectFields2() {
        // Tests multiple fields and field types.
        DbObject t = new DbObject.Builder()
            .addString("s", "Hello there!").addLong("value", 222L).addString("notMatching", "Not").build();
        TestClass1 object = t.toJavaObject(TestClass1.class);
        
        Assert.assertEquals("Hello there!", object.s);
        Assert.assertEquals(222L, object.value);
    }
    
    @Nano
    public static void testSetObjectFields3() {
        // Tests inheritance.
        DbObject t = new DbObject.Builder()
            .addString("s", "Hello there!")
            .addLong("value", 222L)
            .addString("notMatching", "Not")
            .addString("sub", "Nautilus").build();
        TestClass2 object = t.toJavaObject(TestClass2.class);
        
        Assert.assertEquals("Hello there!", object.s);
        Assert.assertEquals(222L, object.value);
        Assert.assertEquals("Nautilus", object.sub);
    }
    
    public static class TestClass3 {
        @SuppressWarnings("unused")
        public String name = "T3";
        public long[] ids = new long[]{123, 444};
    }
    
    @Nano
    public static void tSetObjectFields4() {
        // Tests setting a long array.
        
        TestClass3 object = new TestClass3();
        
        DbObject t = new DbObject.Builder()
            .addString("s", "Hello there!")
            .addArray("ids", new DbArray.Builder().add(new DbLong(1)).add(new DbLong(2)).add(new DbLong(44)).build())
            .build();
        
        Assert.assertArrayEquals(new long[]{123, 444}, object.ids);
        object = t.toJavaObject(TestClass3.class);
        Assert.assertArrayEquals(new long[]{1, 2, 44}, object.ids);
    }
    
    @Nano
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
    
    @Nano
    public static void testString1() {
        TestClass1 object = new TestClass1();
        object.s = null;
        object.value = 123;
        
        DbObject to = DbObject.toDbObject(object);
        Assert.assertFalse(to.has("s", 's'));       // left out (bergdb 020-04's (c))
        Assert.assertEquals('z', to.getType("s"));
        Assert.assertNull(to.getString("s"));
        Assert.assertEquals("a string", to.toJavaObject(TestClass1.class).s);       // the constructor's value
    }
    
    public static class ByteArrayClass {
        @SuppressWarnings("unused")
        public byte[] field;
    }
    
    @Nano
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
    
    @Nano
    public static void testByteArray2() {
        ByteArrayClass object = new ByteArrayClass();
        object.field = new byte[0];
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'b'));
        byte[] array = to.getByteArray("field");
        Assert.assertEquals(0, array.length);
    }
    
    @Nano
    public static void testByteArray3() {
        ByteArrayClass object = new ByteArrayClass();
        object.field = null;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertFalse(to.has("field", 'b'));   // left out (bergdb 020-04's (c))
        byte[] array = to.getByteArray("field");
        Assert.assertNull(array);
    }
    
    public static class BooleanClass {
        public boolean field;
        public BooleanClass() {}
    }
    
    @Nano
    public static void testBoolean1() {
        BooleanClass object = new BooleanClass();
        object.field = true;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'n'));
        Assert.assertEquals('n', to.getType("field"));
        Assert.assertEquals(true, to.getBoolean("field"));
    }
    
    @Nano
    public static void testBoolean2() {
        BooleanClass object = new BooleanClass();
        object.field = false;
        DbObject dbo = DbObject.toDbObject(object);
        Assert.assertTrue(dbo.has("field", 'n'));
        Assert.assertEquals('n', dbo.getType("field"));
        Assert.assertEquals(false, dbo.getBoolean("field"));
        BooleanClass b = dbo.toJavaObject(BooleanClass.class);
        Assert.assertEquals(false, b.field);
    }
    
    
    public static class IntClass {
        public int field;
    }
    
    @Nano
    public static void testInt1() {
        IntClass object = new IntClass();
        object.field = 1234567890;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'i'));
        Assert.assertEquals('l', to.getType("field"));      // one integer (bergdb 020-07)
        Assert.assertEquals(1234567890, to.getInt("field"));
    }
    
    @Nano
    public static void testInt2() {
        IntClass object = new IntClass();
        object.field = -1234567890;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("field", 'i'));
        Assert.assertEquals('l', to.getType("field"));      // one integer (bergdb 020-07)
        Assert.assertEquals(-1234567890, to.getInt("field"));
        
        IntClass o2 = to.toJavaObject(IntClass.class);
        Assert.assertEquals(-1234567890, o2.field);
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
    
    @Nano
    public static void testObject1() {
        // Tests storing an instance of ObjectClass in a DbObject.
        
        ObjectClass obj = new ObjectClass();
        DbObject to = DbObject.toDbObject(obj);
        
        Assert.assertTrue(to.has("myInt", 'i'));
        Assert.assertTrue(to.has("myInt", 'l'));        // one integer (bergdb 020-07)
        Assert.assertEquals('o', to.getType("nested"));
        Assert.assertEquals(12, to.getInt("myInt"));
        
        DbObject nested = to.getObject("nested");
        Assert.assertTrue("assert nested not null", nested != null);
        Assert.assertEquals(11, nested.getInt("myInt"));
        Assert.assertEquals("hello", nested.getString("myString"));
    }
    
    @Nano
    public static void testObject2() {
        // Similar to testObject1, but 'nested' is null.
        
        ObjectClass obj = new ObjectClass();
        obj.nested = null;
        DbObject dbo = DbObject.toDbObject(obj);
        
        Assert.assertEquals('z', dbo.getType("nested"));      // left out (bergdb 020-04)
        Assert.assertEquals(12, dbo.getInt("myInt"));
        
        DbObject nested = dbo.getObject("nested");
        Assert.assertNull(nested);
    }
    
    public static class MultiLevelClass {
        public long myLong = 1234;
        public ObjectClass obj = new ObjectClass();
    }
    
    @Nano
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
    
    @Nano
    public static void testSetObjectFields5() {
        // Tests the storing an object m1 to a DbObject and getting a new object
        // back from the DbObject with the same field values.
        
        MultiLevelClass m1 = new MultiLevelClass();
        m1.myLong = 100;
        m1.obj.myInt = 200;
        m1.obj.nested.myString = "Alea iacta est";
        
        DbObject to = DbObject.toDbObject(m1);
        MultiLevelClass m2 = to.toJavaObject(MultiLevelClass.class);
        
        Assert.assertEquals(100, m2.myLong);
        Assert.assertEquals(200, m2.obj.myInt);
        Assert.assertEquals("Alea iacta est", m2.obj.nested.myString);
    }
    
    @Nano
    public static void testSetObjectFields6() {
        // Tests the storing an object m1 to a DbObject and getting a new object
        // back from the DbObject with the same field values.
        // This test has a null field.
        
        MultiLevelClass m1 = new MultiLevelClass();
        m1.myLong = 101;
        m1.obj.myInt = 202;
        m1.obj.nested = null;
        
        DbObject dbo = DbObject.toDbObject(m1);
        MultiLevelClass m2 = dbo.toJavaObject(MultiLevelClass.class);
        
        Assert.assertEquals(101, m2.myLong);
        Assert.assertEquals(202, m2.obj.myInt);
        // Left out, so the constructor's value (bergdb 020-04's (c)).
        Assert.assertEquals(11, m2.obj.nested.myInt);
    }
    
    public static class IntArrayClass {
        @SuppressWarnings("unused")
        public int[] ints;
    }
    
    @Nano
    public static void testIntArray1() {
        IntArrayClass object = new IntArrayClass();
        object.ints = new int[]{-1, 1234, Integer.MAX_VALUE};
        DbObject d = DbObject.toDbObject(object);
        Assert.assertEquals('a', d.getType("ints"));
        int[] ints = d.getArray("ints").toIntArray();
        Assert.assertEquals(3, ints.length);
        Assert.assertEquals(-1, ints[0]);
        Assert.assertEquals(1234, ints[1]);
        Assert.assertEquals(Integer.MAX_VALUE, ints[2]);
    }
    
    @Nano
    public static void testIntArray2() {
        IntArrayClass object = new IntArrayClass();
        object.ints = new int[0];
        DbObject d = DbObject.toDbObject(object);
        Assert.assertTrue(d.has("ints", 'a'));
        int[] ints = d.getArray("ints").toIntArray();
        Assert.assertEquals(0, ints.length);
    }
    
    @Nano
    public static void testIntArray3() {
        IntArrayClass object = new IntArrayClass();
        object.ints = null;
        DbObject d = DbObject.toDbObject(object);
        Assert.assertFalse(d.has("ints", 'a'));     // left out (bergdb 020-04's (c))
        Assert.assertNull(d.getArray("ints"));
    }
    
    
    
    public static class LongArrayClass {
        public long[] array;
    }
    
    public static class DoubleArrayClass {
        public double[] array;
    }
    
    @Nano
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
    
    @Nano
    public static void testLongArray2() {
        LongArrayClass object = new LongArrayClass();
        object.array = new long[0];
        DbObject to = DbObject.toDbObject(object);
        Assert.assertEquals('a', to.getType("array"));
        long[] longs = to.getArray("array").toLongArray();
        Assert.assertEquals(0, longs.length);
    }
    
    @Nano
    public static void testLongArray3() {
        LongArrayClass object = new LongArrayClass();
        object.array = null;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertEquals('z', to.getType("array"));     // left out (bergdb 020-04's (c))
        Assert.assertNull(to.getArray("array"));
    }
    
    @Nano
    public static void testLongArray4() {
        LongArrayClass object = new LongArrayClass();
        object.array = new long[]{-1, 1234, Long.MAX_VALUE};
        DbObject dbo = DbObject.toDbObject(object);
        
        LongArrayClass object2 = dbo.toJavaObject(LongArrayClass.class);
        
        Assert.assertArrayEquals(object.array, object2.array);
    }


    @Nano
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
    
    @Nano
    public static void testDoubleArray2() {
        DoubleArrayClass object = new DoubleArrayClass();
        object.array = new double[0];
        DbObject to = DbObject.toDbObject(object);
        Assert.assertTrue(to.has("array", 'a'));
        double[] array = to.getArray("array").toDoubleArray();
        Assert.assertEquals(0, array.length);
    }
    
    @Nano
    public static void testDoubleArray3() {
        DoubleArrayClass object = new DoubleArrayClass();
        object.array = null;
        DbObject to = DbObject.toDbObject(object);
        Assert.assertFalse(to.has("array", 'a'));      // left out (bergdb 020-04's (c))
        Assert.assertNull(to.getArray("array"));
    }
    
    @Nano
    public static void testDoubleArray4() {
        DoubleArrayClass object = new DoubleArrayClass();
        object.array = new double[]{1.2, -123.4};
        DbObject dbo = DbObject.toDbObject(object);
        
        DoubleArrayClass object2 = dbo.toJavaObject(DoubleArrayClass.class);
        Assert.assertArrayEquals(object.array, object2.array);
    }
    
    /**
     * Class with fields that are arrays of primitive types.
     */
    public static class PrimitiveArrays {
        public boolean[] booleans;
        public byte[] bytes;
        public char[] chars;
        public short[] shorts;
        public int[] ints;
        public long[] longs;
        public float[] floats;
        public double[] doubles;
        
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
    
    @Nano
    public static void testPrimitiveArrays0() {
        PrimitiveArrays p0 = new PrimitiveArrays();
        p0.setThem1();
        
        DbObject dbo = DbObject.toDbObject(p0);
        PrimitiveArrays p1 = dbo.toJavaObject(PrimitiveArrays.class);
        
        Assert.assertArrayEquals(p0.booleans, p1.booleans);
        Assert.assertArrayEquals(p0.bytes, p1.bytes);
        Assert.assertArrayEquals(p0.chars, p1.chars);
        Assert.assertArrayEquals(p0.shorts, p1.shorts);
        Assert.assertArrayEquals(p0.ints, p1.ints);
        Assert.assertArrayEquals(p0.longs, p1.longs);
        Assert.assertArrayEquals(p0.floats, p1.floats);
        Assert.assertArrayEquals(p0.doubles, p1.doubles);
    }
    
    @Nano
    public static void testPrimitiveArrays1() {
        PrimitiveArrays p0 = new PrimitiveArrays();
        p0.setThem2();
        
        DbObject dbo = DbObject.toDbObject(p0);
        PrimitiveArrays p1 = dbo.toJavaObject(PrimitiveArrays.class);
        
        Assert.assertArrayEquals(p0.booleans, p1.booleans);
        Assert.assertArrayEquals(p0.bytes, p1.bytes);
        Assert.assertArrayEquals(p0.chars, p1.chars);
        Assert.assertArrayEquals(p0.shorts, p1.shorts);
        Assert.assertArrayEquals(p0.ints, p1.ints);
        Assert.assertArrayEquals(p0.longs, p1.longs);
        Assert.assertArrayEquals(p0.floats, p1.floats);
        Assert.assertArrayEquals(p0.doubles, p1.doubles);
    }
    
    @Nano
    public static void testPrimitiveArrays2() {
        // Tests arrays values that are null: left out (bergdb 020-04's (c)), so a read into
        // an object leaves its fields as they are.
        
        PrimitiveArrays p0 = new PrimitiveArrays();
        
        DbObject dbo = DbObject.toDbObject(p0);
        Assert.assertEquals(0, dbo.getFieldCount());
        PrimitiveArrays p1 = dbo.toJavaObject(PrimitiveArrays.class);
        
        // The constructor's values: null (bergdb 020-09, section 5.3).
        Assert.assertTrue(p1.booleans == null && p1.bytes == null && p1.chars == null
                && p1.shorts == null && p1.ints == null && p1.longs == null 
                && p1.floats == null && p1.doubles == null);
    }
    
    /**
     * String, String[], String[][], String[][][] fields this class.
     */
    @SuppressWarnings("unused")
    public static class Strings {
        public String s0a;
        public String s0b;
        public String[] s1a;
        public String[] s1b;
        public String[] s1c;
        public String[][] s2a;
        public String[][] s2b;
        public String[][] s2c;
        
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
        
        /** As setThem1(), with no null array element (bergdb 020-04, section 2.1). */
        void setThem2() {
            s0a = "a";
            s0b = null;
            s1a = new String[] { "a", "hello" };
            s2a = new String[][] {
                    new String[] { "a", "" },
                    new String[] { "We spend our time searching for security and hate it when we get it." }
            };
            s2b = null;
            s2c = new String[][] {
                    new String[] { "a", "b" },
                    new String[] { "We spend our time searching for security and hate it when we get it." },
                    new String[] {}
            };
        }
    }

    public static class StringArrayClass {
        public String[] strings;
    }
    
    @Nano
    public static void testStrings0() {
        Strings s0 = new Strings();
        s0.setThem1();
        assertNullElementRefused(s0, "'s2a[0][1]'");
        s0.setThem2();
        
        DbObject dbo = DbObject.toDbObject(s0);
        Strings s1 = (Strings) dbo.toJavaObject(Strings.class);
        
        Assert.assertEquals(s0.s0a, s1.s0a);
        Assert.assertNull(s1.s0b);
        Assert.assertArrayEquals(s0.s1a, s1.s1a);
    }
    
    @Nano
    public static void testStrings1() {
        // Tests storing an array of strings.
        
        String[] myStrings1 = new String[]{"first", "second"};
        StringArrayClass obj1 = new StringArrayClass();
        obj1.strings = myStrings1;
        DbObject dbo1 = DbObject.toDbObject(obj1);
        byte[] bytes = dbo1.getBytes();
        
        // Stored to bytes, lets try to get it back to a String[].
        DbObject dbo2 = new DbObject(bytes);
        StringArrayClass obj2 = (StringArrayClass) dbo2.toJavaObject(StringArrayClass.class);
        String[] myStrings2 = obj2.strings;
        
        // Assert
        
        Assert.assertEquals("first", myStrings2[0]);
        Assert.assertEquals("second", myStrings2[1]);
    }
    
    @Nano
    public static void testStrings2() {
        // Like previous test, but with null-value: refused (bergdb 020-04, section 2.1).
        
        String[] myStrings1 = new String[]{null, "second"};
        StringArrayClass obj1 = new StringArrayClass();
        obj1.strings = myStrings1;
        assertNullElementRefused(obj1, "'strings[0]'");
    }
    
    public static class IntArray5D implements Serializable {
        private static final long serialVersionUID = 1L;
        
        public int[][][][][] array;
        
        public IntArray5D() {}
        
        void set() {
            array = new int[1][2][3][1][2];
            array[0][1][2][0][0] = 1200;
            array[0][0][1][0][0] = 100;
            array[0][0][0] = null;
        }
    }
    
    @Nano
    public static void test5DIntArray() throws IOException {
        IntArray5D obj0 = new IntArray5D();
        obj0.set();
        assertNullElementRefused(obj0, "'array[0][0][0]'");     // bergdb 020-04
        obj0.array[0][0][0] = new int[0][];
        
        DbObject dbo = DbObject.toDbObject(obj0);
        IntArray5D obj1 = dbo.toJavaObject(IntArray5D.class);
        
        byte[] bytes0 = serialize(obj0);
        byte[] bytes1 = serialize(obj1);
        Assert.assertArrayEquals(bytes0, bytes1);
    }
    
    public static class Customer implements Serializable {
        private static final long serialVersionUID = 1L;
        
        public String name;
        public int id;
        
        public Customer() {}
        public Customer(int id, String name) {
            this.id = id;
            this.name = name;
        }
        public String toString() {
            return id + "-" + name;
        }
    }
    
    public static class CustomerArray implements Serializable {
        private static final long serialVersionUID = 1L;
        
        public Customer[][][][] array;
        
        public CustomerArray() {}
        
        void set() {
            array = new Customer[1][2][3][3];
            array[0][0][0][0] = new Customer(20, "Gustav");
            array[0][0][0][1] = null;
            array[0][0][0][2] = new Customer(21, "Anna");
            array[0][0][1] = null;
        }
    }
    
    @Nano
    public static void test4DCustomerArray() throws IOException {
        CustomerArray obj0 = new CustomerArray();
        obj0.set();
        assertNullElementRefused(obj0, "'array[0][0][0][1]'");      // bergdb 020-04
        obj0.array[0][0][0][1] = new Customer(22, "Bo");
        assertNullElementRefused(obj0, "'array[0][0][1]'");
        obj0.array[0][0][1] = new Customer[0];
        assertNullElementRefused(obj0, "'array[0][0][2][0]'");
        obj0.array[0][0][2] = new Customer[] {new Customer(23, "Cy")};
        assertNullElementRefused(obj0, "'array[0][1][0][0]'");
        obj0.array[0][1] = new Customer[0][];
        
        DbObject dbo = DbObject.toDbObject(obj0);
        CustomerArray obj1 = dbo.toJavaObject(CustomerArray.class);
        byte[] bytes0 = serialize(obj0);
        byte[] bytes1 = serialize(obj1);
        Assert.assertArrayEquals(bytes0, bytes1);
        
        Assert.assertEquals(21, obj1.array[0][0][0][2].id);
        Assert.assertEquals("Anna", obj1.array[0][0][0][2].name);
        Assert.assertEquals(0, obj1.array[0][0][1].length);
        
        Assert.assertEquals("Bo", obj1.array[0][0][0][1].name);
    }
    
    @Nano
    public static void testStrings2D() {
        Strings s0 = new Strings();
        s0.setThem2();
        
        DbObject dbo = DbObject.toDbObject(s0);
        Strings s1 = dbo.toJavaObject(Strings.class);
        
        Assert.assertNull(s1.s2b);
        Assert.assertEquals(3, s1.s2c.length);
        Assert.assertEquals(2, s1.s2c[0].length);
        Assert.assertEquals("a", s1.s2c[0][0]);
        Assert.assertEquals("b", s1.s2c[0][1]);
        Assert.assertEquals(1, s1.s2c[1].length);
        Assert.assertEquals(0, s1.s2c[2].length);
        Assert.assertEquals("", s1.s2a[0][1]);
    }
    
    public static class Circular0 {
        public Circular1 c;
        public Circular0() {}
    }
    
    public static class Circular1 {
        @SuppressWarnings("unused")
        public Circular0 c;
        public Circular1() {}
    }
    
    /** 
     * Circular references throw IllegalArgumentException with the field path (since
     * 2026-10-21, bergdb 005-23; before, StackOverflowError).
     */
    @Nano
    public static void testCircularRefs() {
        Circular0 obj = new Circular0();
        obj.c = new Circular1();
        obj.c.c = obj;
        
        IllegalArgumentException ex = null;
        try {
            DbObject.toDbObject(obj);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
        Assert.assertTrue(ex.getMessage(), ex.getMessage().contains("at c.c is also at the top"));
    }
    
    public static class SuperOne {
        public int a;
        public int b;
        public SuperOne() {}
    }
    
    public static class MyClass extends SuperOne {
        public int c;
        public MyClass() {
            super();
        }
    }
    
    @Nano
    public static void testHierarchy() {
        MyClass obj0 = new MyClass();
        obj0.a = 1;
        obj0.b = 2;
        obj0.c = 3;
        
        DbObject dbo = DbObject.toDbObject(obj0);
        MyClass obj1 = dbo.toJavaObject(MyClass.class);
        
        Assert.assertEquals(1, obj1.a);
        Assert.assertEquals(2, obj1.b);
        Assert.assertEquals(3, obj1.c);
    }
    
    public static class MyClass2a {
        public long a;
    }
    
    public static class PrivateConstructor {
        public long a;
        private PrivateConstructor() {}
        static PrivateConstructor make() {
            return new PrivateConstructor();
        }
    }
    
    /**
     * A class with a private no-argument constructor is not a Data Object (bergdb 020-09,
     * V2 and K2): it was made by setAccessible; a put and a get are refused.
     */
    @Nano
    public static void testPrivateConstructor() {
        PrivateConstructor obj0 = PrivateConstructor.make();
        obj0.a = 123;
        try {
            DbObject.toDbObject(obj0);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("no public no-argument"));
        }
        DbObject dbo = new DbObject.Builder().addLong("a", 123).build();
        try {
            dbo.toJavaObject(PrivateConstructor.class);
            throw new AssertionError("no exception");
        } catch (bergdb.pub.ObjectCreationException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("no public no-argument"));
        }
    }
    
    public static class MyClass2b {
        public long a;
    }
    
    @Nano
    public static void testTypeSwitch() {
        MyClass2a obj0 = new MyClass2a();
        obj0.a = -111222333444L;
        DbObject dbo = DbObject.toDbObject(obj0);
        MyClass2b obj1 = dbo.toJavaObject(MyClass2b.class);
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
    
    @Nano
    public static void testNullField0() {
        TestClass1 obj0 = new TestClass1();
        obj0.s = null;
        DbObject dbo = DbObject.toDbObject(obj0);
        TestClass1 obj1 = dbo.toJavaObject(TestClass1.class);
        
        // Left out, so the constructor's value (bergdb 020-04's (c), 020-09, section 4.3).
        Assert.assertEquals("a string", obj1.s);
    }
    
    public static class A {
        public TestClass1 field = new TestClass1();
    }
    
    @Nano
    public static void testNullField1() {
        A obj0 = new A();
        obj0.field = null;
        DbObject dbo = DbObject.toDbObject(obj0);
        A obj1 = dbo.toJavaObject(A.class);
        
        // Left out, so the constructor's value (bergdb 020-04's (c), 020-09, section 4.3).
        Assert.assertEquals("a string", obj1.field.s);
    }
    
    public static class TestClass4 {
        public String[] array;
    }
   
    @Nano
    public static void testStringArray0() {
        TestClass4 obj1 = new TestClass4();
        obj1.array = new String[]{"1", "2", null, "4"};
        assertNullElementRefused(obj1, "'array[2]'");       // bergdb 020-04
        obj1.array[2] = "3";
        DbObject dbo = DbObject.toDbObject(obj1);
        TestClass4 obj2 = dbo.toJavaObject(TestClass4.class);
        
        Assert.assertEquals(4, obj2.array.length);
        Assert.assertEquals("1", obj2.array[0]);
        Assert.assertEquals("3", obj2.array[2]);
    }
    
    @Nano
    public static void testArray0() {
        String[] myStrings1 = new String[]{"first", "second"};
        DbObject dbo = DbObject.toDbObject(myStrings1);
        Assert.assertTrue("assert dbo not null", dbo != null);        
        String[] myStrings2 = dbo.toJavaObject(String[].class);
        Assert.assertEquals(2, myStrings2.length);
        Assert.assertEquals("first", myStrings2[0]);
        Assert.assertEquals("second", myStrings2[1]);
    }
    
    @Nano
    public static void testArray1() {
        // Like previous test, but with a null value in array: refused (bergdb 020-04).
        String[] myStrings1 = new String[]{null, "second"};
        assertNullElementRefused(myStrings1, "'[0]'");
    }
    
    @Nano
    public static void testArray2() {
        // Tests with an array using a custom class.
        Customer[] c = new Customer[]{new Customer(), new Customer()};
        c[0].id = 11;
        c[0].name = "A";
        c[1].id = 22;
        c[1].name = "B";
        
        DbObject dbo = DbObject.toDbObject(c);
        
        Customer[] c2 = dbo.toJavaObject(Customer[].class);
        Assert.assertEquals(2, c2.length);
        Assert.assertEquals(c[0].id, c2[0].id);
        Assert.assertEquals(c[0].name, c2[0].name);
        Assert.assertEquals(c[1].id, c2[1].id);
        Assert.assertEquals(c[1].name, c2[1].name);
    }
    
    @Nano
    public static void testArray3() {
        // Tests storing an array of primitive values.
        
        int[] ints0 = new int[]{1, 2, -100, Integer.MAX_VALUE};
        DbObject dbo = DbObject.toDbObject(ints0);
        int[] ints1 = dbo.toJavaObject(int[].class);
        Assert.assertArrayEquals(ints0, ints1);
    }
    
    @Nano
    public static void testArray4() {
        // Tests storing a multi-dimensional array.
        
        int[][] ints0 = new int[][] {
            new int[] { 1, 10 },
            null,
            new int[] {}
        };
        assertNullElementRefused(ints0, "'[1]'");       // bergdb 020-04
        ints0[1] = new int[] {7};
        
        DbObject dbo = DbObject.toDbObject(ints0);
        int[][] ints1 = dbo.toJavaObject(int[][].class);
        
        Assert.assertEquals(ints0.length, ints1.length);
        for (int i = 0; i < ints0.length; i++) {
            Assert.assertArrayEquals(ints0[i], ints1[i]);
        }
    }
    
    @Nano
    public static void testPrimitive0() {
        DbObject dbo1 = DbObject.toDbObject(1234);
        Integer theInt = dbo1.toJavaObject(Integer.class);
        Assert.assertEquals(1234, theInt.intValue());
    }
    
    @Nano
    public static void testPrimitive1() {
        // Same as previous, but uses int.class instead of Integer.class.
        DbObject dbo1 = DbObject.toDbObject(1234);
        int theInt = dbo1.toJavaObject(int.class);
        Assert.assertEquals(1234, theInt);
    }
    
    @Nano
    public static void testPrimitive2() {
        DbObject dbo1 = DbObject.toDbObject(true);
        boolean result = dbo1.toJavaObject(boolean.class);
        Assert.assertEquals(true, result);
    }
    
    @Nano
    public static void testPrimitive3() {
        DbObject dbo1 = DbObject.toDbObject(123.45);
        double result = dbo1.toJavaObject(double.class);
        Assert.assertEquals(123.45, result);
    }
    
    @Nano
    public static void testPrimitive4() {
        DbObject dbo1 = DbObject.toDbObject(Double.NaN);
        double result = dbo1.toJavaObject(double.class);
        Assert.assertTrue(Double.isNaN(result));
    }
    
    @Nano
    public static void testNestedField1() {
        DbObject o1 = new DbObject.Builder().addLong("count", 120L).build();
        DbObject o2 = new DbObject.Builder().addObject("obj", o1).build();
        Assert.assertTrue(o2.has(new String[]{"obj", "count"}, DbObject.LONG));
    }
    
    @Nano
    public static void testNestedField2() {
        DbObject o1 = new DbObject.Builder().addLong("count", 120L).build();
        Assert.assertFalse(o1.has(new String[]{"obj", "count"}, DbObject.LONG));
        Assert.assertFalse(o1.has(".count", DbObject.LONG));
        Assert.assertFalse(o1.has("count.", DbObject.LONG));
        Assert.assertTrue(o1.has("count", DbObject.LONG));
    }
    
    @Nano
    public static void testNestedField3() {
        DbObject o1 = new DbObject.Builder().addLong("count", 120L).build();
        DbObject o2 = new DbObject.Builder().addObject("obj", o1).build();
        DbObject o3 = new DbObject.Builder().addObject("o2", o2).build();
        
        Assert.assertTrue(o1.has("count", DbObject.LONG));
        Assert.assertTrue(o2.has(new String[]{"obj", "count"}, DbObject.LONG));
        Assert.assertTrue(o3.has(new String[]{"o2", "obj", "count"}, DbObject.LONG));
        Assert.assertTrue(o2.has("obj", DbObject.OBJECT));
        Assert.assertTrue(o3.has("o2", DbObject.OBJECT));
        Assert.assertTrue(o3.has(new String[]{"o2", "obj"}, DbObject.OBJECT));
    }
    
    @Nano
    public static void testNestedField4() {
        // Tests getLong().
        
        DbObject o1 = new DbObject.Builder().addLong("count", 120L).build();
        DbObject o2 = new DbObject.Builder().addObject("obj", o1).build();
        
        Assert.assertEquals(120L, o2.getLong(new String[]{"obj", "count"}));
    }
    
    @Nano
    public static void testNestedField5() {
        // Tests getLong() with non-existant field.
        
        DbObject o1 = new DbObject.Builder().addLong("count", 120L).build();
        DbObject o2 = new DbObject.Builder().addObject("obj", o1).build();
        DbObject o3 = new DbObject.Builder().addObject("o2", o2).build();
        
        long value = o3.getLong(new String[]{"o2", "obj", "nonExistant"});
        Assert.assertEquals(0, value);
    }
    
    // ---- bergdb 005-22: a value that does not fit its Java field ----
    
    public static class NarrowClass {
        public int i;
        public short s;
        public byte b;
        public char c;
        public long l;
        public float f;
        public int[] ints;
    }
    
    private static NarrowClass narrow(String name, DbValue value) {
        DbObject dbo = new DbObject.Builder().addDbValue(name, value).build();
        return dbo.toJavaObject(NarrowClass.class);
    }
    
    private static DbArray longs(long... values) {
        DbArray.Builder b = new DbArray.Builder();
        for (long v : values) {
            b.add(new DbLong(v));
        }
        return b.build();
    }
    
    /**
     * A value that does not fit its field: DataFormatException since 005-22, clamped since
     * 020-09, section 5.4 (best effort, Frans, 2026-11-08, 21:47): the nearest value, integers
     * saturated, a double beyond a float's range an infinity.
     */
    @Nano
    public static void testNarrowingOutOfRange() {
        Assert.assertEquals(Integer.MAX_VALUE, narrow("i", new DbLong(3000L * 1000 * 1000)).i);
        Assert.assertEquals(Integer.MIN_VALUE, narrow("i", new DbLong(Integer.MIN_VALUE - 1L)).i);
        Assert.assertEquals(Short.MAX_VALUE, narrow("s", new DbLong(444555)).s);
        Assert.assertEquals(Short.MIN_VALUE, narrow("s", new DbLong(-32769)).s);
        Assert.assertEquals(Byte.MAX_VALUE, narrow("b", new DbLong(128)).b);
        Assert.assertEquals(0, narrow("c", new DbLong(-1)).c);
        Assert.assertEquals(65535, narrow("c", new DbLong(65536)).c);
        Assert.assertEquals(Integer.MAX_VALUE, narrow("i", new DbDouble(1e10)).i);
        Assert.assertEquals(0L, narrow("l", new DbDouble(Double.NaN)).l);
        Assert.assertEquals(Long.MAX_VALUE, narrow("l", new DbDouble(1e19)).l);
        Assert.assertTrue(Float.isInfinite(narrow("f", new DbDouble(1e300)).f));
        Assert.assertArrayEquals(new int[] {1, Integer.MAX_VALUE}, 
                narrow("ints", longs(1, 1L << 40)).ints);
    }
    
    @Nano
    public static void testNarrowingInRange() {
        Assert.assertEquals(Integer.MAX_VALUE, narrow("i", new DbLong(Integer.MAX_VALUE)).i);
        Assert.assertEquals(-32768, narrow("s", new DbLong(-32768)).s);
        Assert.assertEquals(-128, narrow("b", new DbLong(-128)).b);
        Assert.assertEquals(65535, narrow("c", new DbLong(65535)).c);
        Assert.assertEquals(2, narrow("i", new DbDouble(2.7)).i);
        Assert.assertEquals(1e30f, narrow("f", new DbDouble(1e30)).f);
        Assert.assertTrue(Float.isInfinite(narrow("f", new DbDouble(Double.POSITIVE_INFINITY)).f));
        Assert.assertArrayEquals(new int[] {1, -5}, narrow("ints", longs(1, -5)).ints);
    }
    
    // ---- bergdb 005-23: cyclic and deeply nested objects ----
    
    public static class Link {
        public int v;
        public Link next;
        public Link[] more;
    }
    
    private static Link list(int length) {
        Link head = null;
        for (int i = 0; i < length; i++) {
            Link n = new Link();
            n.v = i;
            n.next = head;
            head = n;
        }
        return head;
    }
    
    @Nano
    public static void testCycleRefused() {
        Link a = new Link();
        Link b = new Link();
        a.next = b;
        b.next = a;
        try {
            DbObject.toDbObject(a);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("cycle")
                    && e.getMessage().contains("next.next"));
        }
        
        Link c = new Link();            // a cycle through an array
        c.more = new Link[] {new Link(), c};
        try {
            DbObject.toDbObject(c);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("cycle"));
        }
        
        Link shared = new Link();       // twice, but not a cycle: stored as before
        Link d = new Link();
        d.next = shared;
        d.more = new Link[] {shared, shared};
        Link back = DbObject.toDbObject(d).toJavaObject(Link.class);
        Assert.assertEquals(2, back.more.length);
        
        DbObject.toDbObject(list(3));   // the thread's path is empty again
    }
    
    @Nano
    public static void testDeepRefused() {
        try {
            DbObject.toDbObject(list(2000));
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("deeper than"));
        }
    }
    
    /** As deep as allowed, 16 levels (bergdb 020-07, R14): stored and read back. */
    @Nano
    public static void testDeepAtLimit() {
        Link back = DbObject.toDbObject(list(ObjectFormat.MAX_LEVELS))
                .toJavaObject(Link.class);
        int n = 0;
        for (Link l = back; l != null; l = l.next) {
            n++;
        }
        Assert.assertEquals(ObjectFormat.MAX_LEVELS, n);
        try {
            DbObject.toDbObject(list(ObjectFormat.MAX_LEVELS + 1));
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("deeper than 16 levels"));
        }
    }
    
    // ---- bergdb 005-26, 021-04: strings with lone surrogates ----
    
    public static class StringsClass {
        public String[] names;
        public String one;
        public int after;
        public String[][] any;      // an Object until 020-09 (V9: no Object field)
        public StringsClass inner;
        public char[] chars;
    }
    
    /** toDbObject(o) refuses with IllegalArgumentException whose message has 'where'. */
    private static void assertRefused(Object o, String where) {
        try {
            DbObject.toDbObject(o);
            throw new AssertionError("no exception, " + where);
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("lone surrogate"));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains(where));
        }
    }
    
    /**
     * A String with a lone surrogate, anywhere in an object, is refused with the field's path
     * (bergdb 021-04, option 1): BergDB stores every string as well-formed UTF-8. It was
     * stored with '?' in its place (005-26), and the object read back held other strings.
     * A pair is stored; a char[] keeps lone surrogates and reads back exactly.
     */
    @Nano
    public static void testLoneSurrogates() {
        StringsClass o = new StringsClass();
        o.names = new String[] {"y", "x\uD800"};
        assertRefused(o, "'names[1]'");
        
        o = new StringsClass();
        o.one = "a\uD800b";
        assertRefused(o, "'one'");
        
        o = new StringsClass();
        o.inner = new StringsClass();
        o.inner.names = new String[] {"\uD83D\uDE00", "\uD83D"};
        assertRefused(o, "'inner.names[1]'");
        
        o = new StringsClass();
        o.any = new String[][] {{"ok"}, {"z", "\uDE00"}};
        assertRefused(o, "'any[1][1]'");
        
        assertRefused(new String[] {"\uD800"}, "'[0]'");      // an array put as an object
        
        try {
            new DbObject.Builder().addString("s", "a\uD800");
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("A string has"));
        }
        try {
            new DbObject.Builder().addInt("n\uD800", 1);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("A field name has"));
        }
        
        o = new StringsClass();
        o.names = new String[] {"y", "\uD83D\uDE00"};
        o.one = "a\uD83D\uDE00b";
        o.after = 42;
        o.chars = new char[] {'a', '\uD800', 'b', '\uDC00'};
        StringsClass back = DbObject.toDbObject(o).toJavaObject(StringsClass.class);
        Assert.assertArrayEquals(new String[] {"y", "\uD83D\uDE00"}, back.names);
        Assert.assertEquals("a\uD83D\uDE00b", back.one);
        Assert.assertEquals(42, back.after);
        Assert.assertTrue(Arrays.equals(o.chars, back.chars));
        
        DbObject.toDbObject(list(3));   // the thread's path is empty again
    }

    // ---- bergdb 021-07: bytes that are not a well-formed object ----

    /** The reader refuses 'b' with a BadFormatException, not another exception or Error. */
    private static void assertBadFormat(String what, byte[] b) {
        try {
            new DbObject(b);
        } catch (BadFormatException e) {
            return;
        } catch (Throwable e) {
            throw new AssertionError(what + ": not a BadFormatException, " + e, e);
        }
        throw new AssertionError(what + ": read without an exception");
    }

    private static DbObject inner() {
        return new DbObject.Builder().addInt("i", 1).addString("s", "abc").build();
    }

    /**
     * Bytes that end inside a field: every proper prefix of an object's bytes is refused;
     * an array's value cut at its start gave an AssertionError (with -ea), and other cuts
     * an IndexOutOfBoundsException. In format 2 (bergdb 020-07, section 7.1).
     */
    @Nano
    public static void testReaderCutBytes() {
        DbObject o = new DbObject.Builder()
                .addArray("a", new DbArray.Builder().add(new DbLong(5)).add(inner())
                        .add(new DbArray.Builder().add(new DbDouble(1.5)).build()).build())
                .addDbValue("b", new DbByteArray(new byte[] {1, 2}))
                .addDbValue("d", new DbDouble(2.5))
                .addInt("i", 1)
                .addLong("l", 2L)
                .addDbValue("n", new DbBoolean(true))
                .addObject("o", inner())
                .addString("s", "abc")
                .build();
        byte[] all = o.getBytes();
        new DbObject(all);
        for (int length = 0; length < all.length; length++) {
            assertBadFormat("the first " + length + " bytes", Arrays.copyOf(all, length));
        }
    }

    /**
     * Case 5: DbObject.Builder refuses a null name or value    /**
     * Case 5: DbObject.Builder refuses a null name or value with IllegalArgumentException,
     * in each add method; addObject, addArray and addDbValue gave an AssertionError (with
     * -ea) or a NullPointerException, and addString stored a null string.
     */
    @Nano
    public static void testBuilderRefusesNull() {
        Runnable[] adds = {
            () -> new DbObject.Builder().addString("s", null),
            () -> new DbObject.Builder().addObject("o", null),
            () -> new DbObject.Builder().addArray("a", null),
            () -> new DbObject.Builder().addDbValue("v", null),
            () -> new DbObject.Builder().addInt(null, 1),
            () -> new DbObject.Builder().addLong(null, 1L),
            () -> new DbObject.Builder().addString(null, "s"),
            () -> new DbObject.Builder().addObject(null, inner()),
            () -> new DbObject.Builder().addArray(null, new DbArray.Builder().build()),
            () -> new DbObject.Builder().addDbValue(null, new DbLong(1)),
            () -> new DbObject.Builder().addInt("", 1),
            () -> new DbString(null),
            () -> new DbByteArray(null),
            () -> new DbArray.Builder().add(null),
            () -> DbObject.toDbObject(null),
        };
        for (int i = 0; i < adds.length; i++) {
            try {
                adds[i].run();
            } catch (IllegalArgumentException e) {
                continue;
            } catch (Throwable e) {
                throw new AssertionError("add " + i + ": " + e, e);
            }
            throw new AssertionError("add " + i + ": no exception");
        }
    }

    // ---- bergdb 021-08: nesting deeper than the writer writes ----

    /**
     * A stored object whose field "a" holds arrays nested 'n' deep, the innermost empty: the
     * top object level 1, the arrays levels 2 to n + 1 (bergdb 020-07, R14).
     */
    static byte[] nestedArrays(int n) {
        long size = 2 + 2L * n;         // the field: its name's length, "a", the arrays
        int w = ObjectFormat.width(size);
        byte[] b = new byte[(int) (1 + 1 + 2 * w + size)];
        b[0] = DbObject.HEADER;
        ObjectFormat.frame(b, 1, new int[] {(int) size}, 1);
        int p = 2 + 2 * w;
        b[p] = 1;
        b[p + 1] = 'a';
        Arrays.fill(b, p + 2, p + 2 + n, (byte) ObjectFormat.ARRAY_START);
        Arrays.fill(b, p + 2 + n, b.length, (byte) ObjectFormat.ARRAY_END);
        return b;
    }

    /** A stored object of 'n' objects nested through the field "o", the innermost empty. */
    static byte[] nestedObjects(int n) {
        int[] sizes = new int[n];       // sizes[k]: the object at level k + 1
        sizes[n - 1] = 2;               // 48 00
        for (int k = n - 2; k >= 0; k--) {
            int field = 2 + sizes[k + 1];
            sizes[k] = 1 + 2 * ObjectFormat.width(field) + field;
        }
        byte[] b = new byte[1 + sizes[0]];
        b[0] = DbObject.HEADER;
        int p = 1;
        for (int k = 0; k < n - 1; k++) {
            p = ObjectFormat.frame(b, p, new int[] {2 + sizes[k + 1]}, 1);
            b[p] = 1;
            b[p + 1] = 'o';
            p += 2;
        }
        ObjectFormat.frame(b, p, new int[0], 0);
        return b;
    }

    /**
     * The reader refuses bytes nested deeper than 16 levels of objects and arrays, counted
     * alike (bergdb 020-07, R14), before it recurses; it ended in a StackOverflowError, or
     * for objects, which it copied at each level, an OutOfMemoryError (bergdb 021-08).
     */
    @Nano
    public static void testReaderNestingDepth() {
        int levels = ObjectFormat.MAX_LEVELS;
        Assert.assertEquals(1, new DbObject(nestedArrays(levels - 1)).getArray("a").getSize());
        assertBadFormat("arrays at " + (levels + 1) + " levels", nestedArrays(levels));
        assertBadFormat("arrays 100,000 deep", nestedArrays(100 * 1000));

        Assert.assertEquals(1, new DbObject(nestedObjects(levels)).getFieldCount());
        Assert.assertEquals(0, new DbObject(nestedObjects(levels)).getObject("o").getObject("o")
                .getFieldCount() - 1);
        assertBadFormat("objects " + (levels + 1) + " deep", nestedObjects(levels + 1));
        assertBadFormat("objects 100,000 deep", nestedObjects(100 * 1000));
    }

    /** The Builder refuses to build what the reader refuses, with IllegalArgumentException. */
    @Nano
    public static void testBuilderRefusesTooDeep() {
        DbArray a = new DbArray.Builder().build();
        for (int i = 1; i < ObjectFormat.MAX_LEVELS - 1; i++) {
            a = new DbArray.Builder().add(a).build();
        }
        new DbObject.Builder().addArray("a", a).build();      // the most levels read
        final DbArray a15 = a;
        try {
            new DbObject.Builder().addArray("a", new DbArray.Builder().add(a15).build())
                    .build();
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("levels"));
        }
    }

    // ---- bergdb 020-04 and 020-08, step 2: no null in format 2 ----

    public static class Nulls {
        public String s;
        public byte[] bytes;
        public String[] strings;
        public Nested nested;
        public Integer count;
        public int n = 3;
        public Nulls() {}
    }

    public static class OnlyN {
        public int n = 3;
        public OnlyN() {}
    }

    /**
     * N1: a null field is absent (020-04's (c), Frans, 2026-11-08, 21:47): null String,
     * byte[], String[], nested object and Integer fields give no field; read back, each is
     * null. N4: the bytes equal those of an object of a class without the fields.
     */
    @Nano
    public static void testNullFieldsAbsent() {
        DbObject dbo = DbObject.toDbObject(new Nulls());
        for (String name : new String[] {"s", "bytes", "strings", "nested", "count"}) {
            Assert.assertEquals(name, 'z', dbo.getType(name));
            Assert.assertTrue(name, dbo.getDbValue(name) == null);
        }
        Assert.assertEquals(1, dbo.getFieldCount());
        Assert.assertEquals(3, dbo.getInt("n"));
        Assert.assertArrayEquals(DbObject.toDbObject(new OnlyN()).getBytes(), dbo.getBytes());

        Nulls back = dbo.toJavaObject(Nulls.class);
        Assert.assertNull(back.s);
        Assert.assertNull(back.bytes);
        Assert.assertNull(back.strings);
        Assert.assertNull(back.nested);
        Assert.assertNull(back.count);
        Assert.assertEquals(3, back.n);
    }

    public static class Elements {
        public String[] names;
        public Integer[] counts;
        public Customer2[] customers;
        public int[][] rows;
        public Elements inner;
        public Elements() {}
    }

    public static class Customer2 {
        public int id;
        public Customer2() {}
    }

    /** toDbObject(o) refuses with IllegalArgumentException naming "is null" and 'where'. */
    private static void assertNullElementRefused(Object o, String where) {
        try {
            DbObject.toDbObject(o);
            throw new AssertionError("no exception, " + where);
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("is null"));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains(where));
        }
    }

    /**
     * N3: a null array element is refused at every depth and in an array of any element type,
     * naming the element (020-04, section 2.1, rule 3; 020-09, section 4.3): a format 2 array
     * has no absent element. So is an array not filled.
     */
    @Nano
    public static void testNullElementsRefused() {
        Elements e = new Elements();
        e.names = new String[] {"a", null};
        assertNullElementRefused(e, "'names[1]'");
        e = new Elements();
        e.counts = new Integer[] {1, null};
        assertNullElementRefused(e, "'counts[1]'");
        e = new Elements();
        e.customers = new Customer2[] {new Customer2(), null};
        assertNullElementRefused(e, "'customers[1]'");
        e = new Elements();
        e.rows = new int[][] {{1}, null};
        assertNullElementRefused(e, "'rows[1]'");
        e = new Elements();
        e.names = new String[2];
        assertNullElementRefused(e, "'names[0]'");
        e = new Elements();
        e.inner = new Elements();
        e.inner.rows = new int[][] {{1}, {2}, null};
        assertNullElementRefused(e, "'inner.rows[2]'");
        assertNullElementRefused(new String[] {"a", null}, "'[1]'");
        assertNullElementRefused(new String[][] {{"a"}, {null}}, "'[1][0]'");

        DbObject.toDbObject(new int[] {1});     // the thread's path is empty again
    }
}
