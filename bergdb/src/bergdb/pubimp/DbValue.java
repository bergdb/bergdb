package bergdb.pubimp;

import java.lang.reflect.Array;

import bergdb.common.Bug;

/**
 * <p>This is the superclass of all DbObject types: boolean, int, long, double, string, 
 * byteArray, array, object. These types are implemented in subclasses of this class:
 * DbBoolean, DbInt, DbLong, DbDouble, DbString, DbByteArray, DbArray, and DbObject.</p>
 * 
 * <p>All subclasses must implement a static method like this: 
 * <pre>  public static DbBoolean parse(byte[] buffer, int offset) {...</pre>
 * "DbBoolean" is replaced with the subclass name.
 * This method must be able to read bytes written with the write() method.
 * </p>
 * 
 * @author Frans Lundberg
 */
public abstract class DbValue {
    
    /**
     * The special types, type name as returned by Class.getName().
     * The order is important. The first sixteen entries are primitive types and their 
     * corresponding wrapper classes.
     */
    private static final String[] specialTypes = new String[] {
        "boolean",
        "byte",
        "char",
        "short",
        "int",
        "long",
        "float",
        "double",
        "java.lang.Boolean",
        "java.lang.Byte",
        "java.lang.Character",
        "java.lang.Short",
        "java.lang.Integer",
        "java.lang.Long",
        "java.lang.Float",
        "java.lang.Double",
        "java.lang.String",
        byte[].class.getName()
    };
    
    private static final int[] specialHashes = new int[specialTypes.length];
    
    static {
        for (int i = 0; i < specialHashes.length; i++) {
            specialHashes[i] = specialTypes[i].hashCode();
        }
    }
    
    /**
     * Chars based on documentation for method java.lang.Class.getName().
     */
    private static final char[] specialTypeChars = new char[] {
        'Z', 'B', 'C', 'S', 'I', 'J', 'F', 'D',
        'Z', 'B', 'C', 'S', 'I', 'J', 'F', 'D',
        's', 'b'
    };
    
    private static final String stringType = String.class.getName();
    private static final int stringTypeHash = stringType.hashCode();
    
    
    private char type;
    
    public DbValue(char type) {
        switch (type) {
        case 'n':
        case 'i':
        case 'l':
        case 'd':
        case 's':
        case 'b':
        case 'a':
        case 'o':
            break;
        default:
            throw new IllegalArgumentException("Bad type, '" + type + "'.");
        }
        
        this.type = type;
    }
    
    public char getType() {
        return type;
    }
    
    /**
     * Returns the byte size of the serialized form of the DbValue.
     * The method write(ByteBuffer) must write exactly as many bytes to the ByteBuffer.
     */
    public abstract int getByteSize();
    
    /**
     * Serialized the value to a byte array starting from index 'offset'.
     * The number of bytes written must equal getByteSize().
     * Returns the "new offset".
     */
    public abstract int write(byte[] b, int offset);
    
    public boolean toBoolean() {
        return toLong() != 0;
    }
    
    public byte toByte() {
        return (byte) toLong();
    }
    
    public char toChar() {
        return (char) toLong();
    }
    
    public short toShort() {
        return (short) toLong();
    }
    
    public int toInt() {
        return (int) toLong();
    }
    
    public long toLong() {
        return 0;
    }
    
    public float toFloat() {
        return (float) toLong();
    }
    
    public double toDouble() {
        return (double) toLong();
    }
    
    public String toStringValue() {
        return null;
    }
    
    /**
     * Should be overridden. Note, do not use this method for conversion to String value.
     * Use toStringValue() instead.
     */
    public String toString() {
        return type + " " + toStringValue();
    }
    
    /**
     * Converts this db value to a specified Java type, c, and returns the Java value.
     * Primitive types (int.class, boolean.class, ...) result in primitive wrappers
     * objects (Integer, Boolean, ...).
     * The implementation of this method in this class handles primitive types, primitive
     * wrapper classes, and the java.lang.String class. Other Java classes are not handled 
     * by this method, null is returned for all other types.
     */
    @SuppressWarnings("unchecked")
    public <TYPE> TYPE toJavaObject(Class<TYPE> c, ClassToObject c2o) {
        if (c == null) {
            throw new IllegalArgumentException("c == null not allowed");
        }
        
        if (c2o == null) {
            throw new IllegalArgumentException("c2o == null not allowed");
        }
        
        String typeName = c.getName();
        int typeNameHash = typeName.hashCode();
        
        Object result = null;
        char typeChar = getPrimitiveTypeChar(typeName, typeNameHash);
        
        switch (typeChar) {
        case 'Z':
            result = toBoolean();
            break;
        case 'B':
            result = toByte();
            break;
        case 'C':
            result = toChar();
            break;
        case 'S':
            result = toShort();
            break;
        case 'I':
            result = toInt();
            break;
        case 'J':
            result = toLong();
            break;
        case 'F':
            result = toFloat();
            break;
        case 'D':
            result = toDouble();
            break;
        }
        
        if (typeNameHash == stringTypeHash && typeName.equals(stringType)) {
            result = toString();
        }
        
        return (TYPE) result;
    }
    
    /**
     * Returns a char based on what primitive type the class, c, represents, or '.' if it does not
     * represent a primitive type. If it represents a primitive type, or a primitive wrapper 
     * type, one of the characters: 'Z', 'B', 'C', 'S', 'I', 'J', 'F', 'D' is returned.
     */
    private static char getPrimitiveTypeChar(String typeName, int typeHash) {
        // Types:
        // 8 primitive types: boolean, byte, char, short, int, long, float, double.
        // 8 wrappers: java.lang.Boolean, Byte, Character, Short, Integer, Long, Float, Double.
        //
        
        char result = '.';
        
        for (int i = 0; i < 16; i++) {
            if (typeHash == specialHashes[i] && typeName.equals(specialTypes[i])) {
                result = specialTypeChars[i];
                break;
            }
        }
        
        return result;
    }
    
    /**
     * Returns a char based on what special type the class, c, represents, or '.' if it does not
     * represent a "special type". If it represents a primitive type, or a primitive wrapper 
     * type, one of the characters: 'Z', 'B', 'C', 'S', 'I', 'J', 'F', 'D' is returned.
     * If the class equals String.class, it returns 's', and if it equals byte[].class, it 
     * returns 'b'.
     */
    public static char getSpecialTypeChar(String typeName, int typeHash) {
        // Types:
        // 8 primitive types: boolean, byte, char, short, int, long, float, double.
        // 8 wrappers: java.lang.Boolean, Byte, Character, Short, Integer, Long, Float, Double.
        //
        
        char result = '.';
        
        for (int i = 0; i < specialTypes.length; i++) {
            if (typeHash == specialHashes[i] && typeName.equals(specialTypes[i])) {
                result = specialTypeChars[i];
                break;
            }
        }
        
        return result;
    }

    public static DbValue parse(char type, byte[] bytes, int offset) {
        DbValue result = null;
        
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
            throw new IllegalArgumentException("bad type: " + type);
        }
        return result;
    }
    
    /**
     * Returns default value for a specified Java type, c.
     */
    public Object defaultValue(Class<?> c) {
        if (c == null) {
            throw new IllegalArgumentException("c == null not allowed");
        }
        
        String typeName = c.getName();
        int typeNameHash = typeName.hashCode();
        
        Object result = null;
        char typeChar = getPrimitiveTypeChar(typeName, typeNameHash);
        
        switch (typeChar) {
        case 'Z':
            result = false;
            break;
        case 'B':
            result = (byte) 0;
            break;
        case 'C':
            result = (char) 0;
            break;
        case 'S':
            result = (short) 0;
            break;
        case 'I':
            result = 0;
            break;
        case 'J':
            result = 0L;
            break;
        case 'F':
            result = 0.0f;
            break;
        case 'D':
            result = 0.0;
            break;
        }
        
        return result;
    }
    
    private static DbValue toNullDbValue(Class<?> c) {
        DbValue result;
        
        if (c.equals(String.class)) {
            result = new DbString(null);
        } else if (c.equals(byte[].class)) {
            result = new DbByteArray(null);
        } else if (c.isArray()) {
            result = DbArray.Builder.buildNull();
        } else {
            result = DbObject.Builder.buildNull();
        }
        
        return result;
    }
    
    public static DbValue toDbValue(Class<?> dstType, Object object) {
        if (object == null) {
            return toNullDbValue(dstType);
        }
        
        Class<?> c = object.getClass();
        final String typeName = c.getName();
        final int typeHash = typeName.hashCode();
        DbValue result = null;
        
        char specialTypeChar = DbValue.getSpecialTypeChar(typeName, typeHash);
        switch (specialTypeChar) {
        case 'Z':
            result = new DbBoolean((Boolean) object);
            break;
        case 'B':
            result = new DbInt((Byte) object);
            break;
        case 'C':
            result = new DbInt((Character) object);
            break;
        case 'S':
            result = new DbInt((Short) object);
            break;
        case 'I':
            result = new DbInt((Integer) object);
            break;
        case 'J':
            result = new DbLong((Long) object);
            break;
        case 'F':
            result = new DbDouble((Float) object);
            break;
        case 'D':
            result = new DbDouble((Double) object);
            break;
        case 's':
            result = new DbString((String) object);
            break;
        case 'b':
            result = new DbByteArray((byte[]) object);
            break;
        case '.':
            // not a special type...
            break;
        default:
            throw new Bug("Unexpected special type char: " + specialTypeChar + ".");
        }
        
        if (specialTypeChar != '.') {
            assert result != null;
            return result;
        }
        
        if (c.isArray()) {
            Object javaArray = object;
            Class<?> c2 = c.getComponentType();
            DbArray.Builder arrayBuilder = new DbArray.Builder();
            int length = Array.getLength(javaArray);
            for (int i = 0; i < length; i++) {
                Object element = Array.get(javaArray, i);
                DbValue dbValue = DbValue.toDbValue(c2, element);
                arrayBuilder.add(dbValue);
            }
            result = arrayBuilder.build();
        } else {
            result = DbObject.toDbObject(object);
        }
        
        return result;
    }
}
