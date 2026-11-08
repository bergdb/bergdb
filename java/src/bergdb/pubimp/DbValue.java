package bergdb.pubimp;

import java.lang.reflect.Array;

import bergdb.common.Bug;
import bergdb.pub.DataFormatException;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * <p>This is the superclass of the seven DbObject types of format 2 (bergdb 020-07): boolean,
 * integer, double, string, byteArray, array, object. They are implemented in subclasses of
 * this class: DbBoolean, DbLong (the one integer, 64 bits), DbDouble, DbString, DbByteArray,
 * DbArray, and DbObject. No value is null (bergdb 020-02, section 4.1).</p>
 * 
 * <p>Each subclass writes its value in its stored encoding, its type byte included, with
 * write(), and read() reads any value of checked bytes by its type byte.</p>
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
     * Returns the byte size of the serialized form of the DbValue: its encoding in format 2,
     * its type byte included (bergdb 020-07, section 4).
     * The method write() must write exactly as many bytes.
     */
    public abstract int getByteSize();
    
    /**
     * Serialized the value to a byte array starting from index 'offset'.
     * The number of bytes written must equal getByteSize().
     * Returns the "new offset".
     */
    public abstract int write(byte[] b, int offset);
    
    /**
     * The levels of this value (bergdb 020-07, R14): 0 for a scalar; for an object or an
     * array, 1 and the most levels of the values in it. The Builders refuse a value that
     * would put a container above level 16.
     */
    int height() {
        return 0;
    }
    
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
     * Primitive types (int.class, boolean.class, ...) result in primitive wrapper
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
        checkFits(typeChar, c);
        
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
     * Throws DataFormatException if this number does not fit the primitive type 'typeChar'
     * (2026-10-21, bergdb 005-22): toInt() and the other conversions cast, so a stored long of
     * 3,000,000,000 read into an int field was -1,294,967,296. An integral value must be in
     * the type's range; a double must be in the range of an integral type, and not NaN, and
     * a finite double within the range of a float. Fractions and the precision of float
     * and double are converted as before.
     */
    private void checkFits(char typeChar, Class<?> c) {
        final boolean fits;
        final String value;
        if (type == 'l') {
            final long v = toLong();
            value = "" + v;
            switch (typeChar) {
            case 'B': fits = v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE; break;
            case 'C': fits = v >= Character.MIN_VALUE && v <= Character.MAX_VALUE; break;
            case 'S': fits = v >= Short.MIN_VALUE && v <= Short.MAX_VALUE; break;
            case 'I': fits = v >= Integer.MIN_VALUE && v <= Integer.MAX_VALUE; break;
            default: fits = true; break;
            }
        } else if (type == 'd') {
            final double v = toDouble();
            value = "" + v;
            switch (typeChar) {
            case 'B': fits = v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE; break;
            case 'C': fits = v >= Character.MIN_VALUE && v <= Character.MAX_VALUE; break;
            case 'S': fits = v >= Short.MIN_VALUE && v <= Short.MAX_VALUE; break;
            case 'I': fits = v >= Integer.MIN_VALUE && v <= Integer.MAX_VALUE; break;
            case 'J': fits = v >= Long.MIN_VALUE && v <= Long.MAX_VALUE; break;
            case 'F': 
                fits = Double.isNaN(v) || Double.isInfinite(v) || Math.abs(v) <= Float.MAX_VALUE;
                break;
            default: fits = true; break;
            }
        } else {
            return;
        }
        
        if (!fits) {
            throw new DataFormatException("The value " + value + " does not fit the Java type "
                    + c.getName() + ".");
        }
    }
    
    /**
     * Returns true if 'c' represents a primitive type (byte.class, short.class, ...) or a 
     * primitive wrapper class (java.lang.Byte, java.lang.Short, ...).
     */
    public static boolean isPrimitiveOrWrapper(Class<?> c) {
        char result = '.';
        String name = c.getName();
        int typeHash = name.hashCode();
        
        for (int i = 0; i < 16; i++) {
            if (typeHash == specialHashes[i] && c.getName().equals(specialTypes[i])) {
                result = specialTypeChars[i];
                break;
            }
        }
        
        return result != '.';
    }
    
    @Nano
    public static void testIsPrimitiveOrWrapper0() {
        Class<?>[] types = new Class<?>[] {
                String.class, Math.class, Thread.class,
                Integer.class, Double.class, Byte.class,
                byte.class, char.class, double.class};
        
        boolean[] expected = new boolean[] {false, false, false,
                true, true, true,
                true, true, true};
        
        for (int i = 0; i < types.length; i++) {
            Assert.assertEquals("index:" + i, expected[i], isPrimitiveOrWrapper(types[i]));
        }
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

    /**
     * Reads the value at 'p' of checked bytes, by its type byte (bergdb 020-07, section 4): a
     * DbObject is a view on 'b', which must not change; the other values are copies.
     */
    static DbValue read(byte[] b, int p) {
        switch (ObjectFormat.typeAt(b, p)) {
        case 'n':
            return new DbBoolean(ObjectFormat.booleanAt(b, p));
        case 'l':
            return new DbLong(ObjectFormat.integerAt(b, p));
        case 'd':
            return new DbDouble(Double.longBitsToDouble(ObjectFormat.doubleBitsAt(b, p)));
        case 's':
            return DbString.read(b, p);
        case 'b':
            return DbByteArray.read(b, p);
        case 'a':
            return DbArray.read(b, p);
        default:
            return DbObject.view(b, p);
        }
    }
    
    /**
     * Important method that converts a Java object to a DbValue, by the object's class.
     * 
     * @param object  Not null: BergDB stores no null (bergdb 020-04).
     * @return The DbValue created from the input Java Object.
     */
    public static DbValue toDbValue(Object object) {
        if (object == null) {
            throw new IllegalArgumentException("object == null not allowed: BergDB stores no "
                    + "null (bergdb 020-04, section 2.1)");
        }
        
        Class<?> c = object.getClass();
        final String typeName = c.getName();
        final int typeHash = typeName.hashCode();
        DbValue result = null;
        char specialTypeChar = DbValue.getSpecialTypeChar(typeName, typeHash);
        
        if (specialTypeChar == '.') {
            if (c.isArray()) {
                result = createDbArray(c, object);
            } else {
                result = DbObject.toDbObject(object);
            }
        } else {
            result = handleSpecialType(object, specialTypeChar);
        }
        
        return result;
    }

    private static DbValue handleSpecialType(Object object, char specialTypeChar)
            throws Bug {
        DbValue result;
        
        switch (specialTypeChar) {
        case 'Z':
            result = new DbBoolean((Boolean) object);
            break;
        case 'B':
            result = new DbLong((Byte) object);
            break;
        case 'C':
            result = new DbLong((Character) object);
            break;
        case 'S':
            result = new DbLong((Short) object);
            break;
        case 'I':
            result = new DbLong((Integer) object);
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
        default:
            throw new Bug("Unexpected special type char: " + specialTypeChar + ".");
        }
        return result;
    }

    /**
     * The array 'object' as a DbArray. A null element is refused, naming its index: an array
     * has no absent element (bergdb 020-04, section 2.1, rule 3). The array is a level on the
     * thread's path of toDbObject() (bergdb 020-08, section 4.7).
     */
    private static DbValue createDbArray(Class<?> c, Object object) {
        Object javaArray = object;
        DbArray.Builder arrayBuilder = new DbArray.Builder();
        int length = Array.getLength(javaArray);
        DbObject.Path path = DbObject.path();
        path.enter(object);
        try {
            for (int i = 0; i < length; i++) {
                path.step("[" + i + "]");
                Object element = Array.get(javaArray, i);
                DbValue dbValue;
                try {
                    if (element == null) {
                        throw PathException.nullElement();
                    }
                    dbValue = DbValue.toDbValue(element);
                } catch (PathException e) {
                    throw e.in("[" + i + "]");      // the element's index (bergdb 021-04)
                }
                arrayBuilder.add(dbValue);
            }
        } finally {
            path.leave();
        }
        return arrayBuilder.build();
    }
    
    /**
     * A value that has no stored form, refused with the place where it is, from the
     * outermost object: a field's name, and an array element's index, such as
     * "inner.names[3]"; each object and array on the way out adds its step with in()
     * (bergdb 021-04; 020-04, section 2.1). A lone surrogate in a string or a field's name,
     * a null array element, a field's name of more than 255 bytes.
     */
    static final class PathException extends IllegalArgumentException {
        private static final long serialVersionUID = 1L;
        private final String what;      // "string", "field name", "array element"
        private final String rest;      // after the subject and its place
        private final String path;      // "" where not known
        
        private PathException(String what, String rest, String path) {
            super((path.isEmpty() ? "A " + what : "The " + what + " at '" + path + "'") + " " 
                    + rest);
            this.what = what;
            this.rest = rest;
            this.path = path;
        }
        
        /** A string or a field's name ('what') with a lone surrogate (bergdb 021-04). */
        static PathException loneSurrogate(String what) {
            return new PathException(what, "has a lone surrogate, a char of U+D800 to U+DFFF "
                    + "that is not part of a surrogate pair. BergDB stores every string as "
                    + "well-formed UTF-8, which cannot hold one (bergdb 021-04); store such "
                    + "data as a byte[] or a char[].", "");
        }
        
        /** A null array element (bergdb 020-04, section 2.1; 020-09, section 4.3). */
        static PathException nullElement() {
            return new PathException("array element", "is null: BergDB stores no null, and "
                    + "an array has no absent element (bergdb 020-09, section 4.3).", "");
        }
        
        /** A field's name of 'size' bytes in UTF-8, more than 255 (bergdb 020-07, R6). */
        static PathException longName(int size) {
            return new PathException("field name", "has " + size + " bytes in UTF-8; a name "
                    + "has 1 to " + ObjectFormat.MAX_NAME + " bytes (bergdb 020-07, R6).", "");
        }
        
        /** The same, one step further out: a field's name, or "[i]" for an array element. */
        PathException in(String step) {
            String p = path.isEmpty() || path.startsWith("[") ? step + path : step + "." + path;
            return new PathException(what, rest, p);
        }
    }
}
