package bergdb.pubimp;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;

import bergdb.common.Bug;
import bergdb.common.ByteArrayComparator;
import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.pub.util.BadFormatException;

/**
 * <p>An immutable object with a map of named and typed fields.
 * The fields are typed, but the object itself has no particular schema.
 * The set of fields can vary independently between any two DbObjects.
 * The word "field" is not used as the actual Java class fields, but for the conceptual
 * fields that this object contain. The set of types available for a DbObject field does 
 * not correspond directly to Java types, but is a separate small type system with 
 * 8 distinct types.
 * </p>
 * 
 * <p>The DbObject types with their one-character representation, name, and descriptions:</p>
 * 
 * <pre>
 * n - boolean    A type that has a value of either true or false.
 * i - int        A signed 32-bit integer.
 * l - long       A signed 64-bit integer.
 * d - double     A 64-bit floating pointer number (IEEE-754).
 * s - string     A string stored as UTF-8.
 * b - byteArray  An array of bytes.
 * a - array      A heterogeneous array (list) of values. See class DbArray.
 * o - object     A nested DbObject.
 * z - zero       Not a type, character 'z' is reserved for null-capability.
 * </pre>
 * 
 * <p>The types n, i, l, d can have any values permitted by the Java runtime for the primitive 
 * Java types with the same name. The string type can have the value of any Unicode string or
 * null. The object type stores a DbObject, or it can have the value null.
 * The byteArray type stores an array of bytes or have a value of null. The array type stores
 * an array of heterogeneous elements; each element can independently be of any DbObject type. 
 * See class DbArray. The value of an array can be null.</p>
 * 
 * <p>A DbObject can be serialized to a byte array; actually it is stored in memory in 
 * a form that is nearly identical to its serialized byte format.
 * The method write() will serialize the DbObject to bytes, and parse() will parse it back
 * from bytes.</p>
 * 
 * <p>The method Builder.build() defines the byte format of DbObjects, that is, how they 
 * are stored as bytes in the database. The byte format needs to stay stable, since objects 
 * are stored in databases for a long time.</p>
 * 
 * <p>A DbObject can be created from a Java Object with the method DbObject.toDbObject(Object javaObject).
 * The method toJavaObject() converts a DbObject to a Java object.</p>
 * 
 * @author Frans Lundberg
 */
public class DbObject extends DbValue {
    //
    // Special handling of field KEY_FIELD makes this class BergDB specific.
    // Otherwise, it could be used as a general purpose way to serialize/deserialize Java objects.
    //
    // 1304 Frans: Little-endian-first (LE) byte order is used to follow the byte ordering used 
    // in the db stream.
    // 1309 Frans: Added support for Java arrays; they are wrapped field 'v' of a DbObject.
    // 1311 Frans: Changed byte signature to start with "bergo", then byte value 1 for version.
    //
    
    private static final int HEADER_SIZE = 8;
    
    /** The byte signature; the first bytes of the DbObject when serialized. */
    public static final byte[] MAGIC = new byte[]{'b', 'e', 'r', 'g', 'o'};
    
    public static final char BOOLEAN = 'n';
    public static final char INT = 'i';
    public static final char LONG = 'l';
    public static final char DOUBLE = 'd';
    public static final char STRING = 's';
    public static final char BYTE_ARRAY = 'b';
    public static final char ARRAY = 'a';
    public static final char OBJECT = 'o';
    
    private static final int MAGIC_SIZE = MAGIC.length;
    private static final int FIELD_INFO_SIZE = 6;
    private static final String KEY_FIELD = PubUtil.KEY_FIELD;
    private static final short KEY_FIELD_HASH = hash(KEY_FIELD);
    private static final String WRAPPED_ARRAY_FIELD_NAME = "array";
    private static final String WRAPPED_PRIMITIVE_FIELD_NAME = "p";   // p for primitive.
    
    private final byte[] bytes;
    private final short[] hashes;   // cached data from 'bytes'
    private final int fieldCount;   // The number of fields.
    private final boolean isNull;
    private final String key;             
            // If set, represents the database key. Implicitly it is the value of the 'key' field.
            // It may be null.
    
    /**
     * Creates a new DbObject based in its byte array representation.
     * 
     * @param bytes The serialized format of the DbObject.
     * @throws BadFormatException If the bytes are not formatted OK according to the 
     * serialized byte format defined by this class.
     */
    public DbObject(byte[] bytes) throws BadFormatException {
        this(bytes, null);
    }
    
    /**
     * Creates a new DbObject based in its byte array representation.
     * 
     * @param b 
     *      The serialized format of the DbObject. 
     *      Will be copied. 
     * @param key 
     *      The database string key of the DbObject, may be null.
     * @throws BadFormatException 
     *      If the bytes are not formatted OK according to the 
     *      serialized byte format defined by this class.
     */
    public DbObject(byte[] b, String key) throws BadFormatException {
        super('o');
        this.key = key;
        
        if (b == null) {
            throw new IllegalArgumentException("b == null not allowed");
        }
        
        if (b.length < HEADER_SIZE) {
            throw new BadFormatException("bytes too short, " + b.length);
        }
        
        this.bytes = b.clone();
        
        checkSignature(b);
        
        byte version = bytes[MAGIC_SIZE];
        if (version != 1) {
            throw new BadFormatException("Only Version 1 supported, got version " 
                    + ((int) version) + ".");
        }
        
        int fCount = Bytes.bytesToShortLE(bytes, MAGIC_SIZE + 1);
        if (fCount < -1) {
            throw new BadFormatException("Bad fieldCount, " + fCount + ".");
        }
        
        if (fCount == -1) {
            isNull = true;
            fieldCount = 0;
        } else {
            isNull = false;
            fieldCount = fCount;
        }
        
        if (b.length < HEADER_SIZE + fieldCount * FIELD_INFO_SIZE) {
            throw new BadFormatException("bytes.length too small for the fields, " 
                    + b.length + ", fieldCount: " + fieldCount + ".");
        }
        
        this.hashes = new short[fieldCount];
        int offset = HEADER_SIZE;
        
        for (int i = 0; i < fieldCount; i++) {
            hashes[i] = Bytes.bytesToShortLE(bytes, offset);
            int bytePosition = Bytes.bytesToIntLE(bytes, offset + 2);
            if (bytePosition >= b.length) {
                throw new BadFormatException("Bad byte position of field " + i + ", " 
                        + bytePosition + ", bytes not long enough, " + b.length + ".");
            }
            
            int fieldOffset = readFieldOffset(i);
            DbField.parse(b, fieldOffset);
            
            offset += FIELD_INFO_SIZE;
        }
    }
    
    private void checkSignature(byte[] b) {
        for (int i = 0; i < MAGIC.length; i++) {
            if (b[i] != MAGIC[i]) {
                throw new BadFormatException("Bad byte signature of bytes that were expected "
                        + "to be DbObject bytes.");
            }
        }
    }
    
    /**
     * Returns a reference to the internal byte buffer.
     * No value copy is made, the returned reference must not be used to modify the array.
     */
    public byte[] getBytes() {
        return this.bytes;
    }
    
    public final boolean isNull() {
        return isNull;
    }
    
    /**
     * Returns the number of fields of the typeless object.
     */
    public int getFieldCount() {
        int count = Bytes.bytesToShortLE(bytes, MAGIC_SIZE + 1);
        count = key == null ? count : count + 1;
        return count;
    }
    
    /**
     * Returns true iff the typeless object has a field with the given name and type.
     */
    public boolean has(String name, char type) {
        return internalSimpleGet(name, type) != null;
    }
    
    /**
     * Returns true iff the typeless object has a nested field with the 
     * given name parts and the given type.
     */
    public boolean has(String[] nameParts, char type) {
        return internalGet(nameParts, 0, type) != null;
    }
   
    private NameAndType internalGet(String[] parts, int offset, char type) {
        assert offset >= 0;
        assert parts.length - offset > 0;
        
        boolean isNested = (parts.length - offset) > 1;
        if (isNested) {
            return internalNestedGet(parts, offset, type);
        } else {
            return internalSimpleGet(parts[offset], type);
        }
    }
    
    private NameAndType internalNestedGet(String[] parts, int offset, char type) {
        if (parts.length - offset < 2) {
            throw new Bug("parts.length = " + parts.length + ", offset: " + offset);
        }
        
        String firstPart = parts[offset];
        boolean hasFirstPart = (internalSimpleGet(firstPart, DbObject.OBJECT) != null);
        if (!hasFirstPart) {
            return null;
        }
        
        return getObject(firstPart).internalGet(parts, offset + 1, type);
    }
    
    private NameAndType internalSimpleGet(String name, char type) {
        final short hash = hash(name);
        NameAndType n = null;
        boolean gotMatch = false;
        
        if (type == DbObject.STRING 
                && this.key != null 
                && hash == KEY_FIELD_HASH && name.equals(KEY_FIELD)) {
            NameAndType nat = new NameAndType();
            nat.name = KEY_FIELD;
            nat.type = DbObject.STRING;
            nat.valueOffset = -1;
            nat.object = this;
            return nat;
        }
        
        for (int i = 0; i < fieldCount; i++) {
            if (hash == hashes[i]) {
                if (n == null) {
                    n = new NameAndType();
                }
                
                readFieldInfo(i, n);
                
                if (n.name.equals(name) && n.type == type) {
                    gotMatch = true;
                    break;      
                    
                    // Always break here, we matched name, no more match possible.
                    // Multiple fields with same name not allowed.
                }
            }
        }
        
        return gotMatch ? n : null;
    }
    
    private static final int NOT_ELIGIBLE = Modifier.FINAL | Modifier.STATIC | Modifier.TRANSIENT;
    
    /**
     * Returns a list of fields that are eligible to be read or set using methods
     * toJavaObject() and toDbObject().
     * The fields are set to accessible (f.setAccessible(true)).
     */
    private static ArrayList<java.lang.reflect.Field> getEligibleFields(Class<?> c) {
        ArrayList<Field> list = new ArrayList<Field>();
        
        while (!c.equals(Object.class)) {
            Field[] fields = c.getDeclaredFields();
            
            for (Field f : fields) {
                int m = f.getModifiers();
                if ((m & NOT_ELIGIBLE) == 0  && !f.isSynthetic()) {
                    f.setAccessible(true);
                    list.add(f);
                }
            }
            c = c.getSuperclass();
        }
        return list;
    }
    
    /**
     * Creates a DbObject given an ordinary Java object as the source.
     * Copies values of fields that are not transient, not static, and not synthetic (added by 
     * compiler) to the newly created DbObject that is returned.
     * If 'object' is null, Builder.buildNull() is returned (a DbObject representing null).
     */
    public static DbObject toDbObject(Object object) {        
        if (object == null) {
            return Builder.buildNull();
        }
        
        DbObject.Builder b = new DbObject.Builder();
        Class<?> clazz = object.getClass();
        
        if (clazz.isArray()) {
            // If it is an array, wraps it in a DbObject stored in a field.
            
            DbValue array = DbValue.toDbValue(clazz, object);
            if (!(array instanceof DbArray)) {
                throw new Bug("Unexpected type, expected DbArray, got: " + array.getClass());
            }
            b.addArray(WRAPPED_ARRAY_FIELD_NAME, (DbArray) array);            
        
        } else if (DbValue.isPrimitiveOrWrapper(clazz)) {
            // If it is a primitive value, wraps it in a DbObject. Value is stored in a field.  
            
            DbValue value = DbValue.toDbValue(clazz, object);
            b.addDbValue(WRAPPED_PRIMITIVE_FIELD_NAME, value);
            
        } else {
            // An ordinary object.
            
            ArrayList<Field> fields = getEligibleFields(clazz);
            for (Field f : fields) {
                try {
                    DbValue dbValue = fieldToDbValue(object, f);
                    b.addDbValue(f.getName(), dbValue);
                } catch (IllegalArgumentException e) {
                    throw new Bug(e);
                } catch (IllegalAccessException e) {
                    throw new Bug("Should not happen, " + e.toString());
                }
            }
        
        }
        
        DbObject result = b.build();
        return result;
    }
    
    /**
     * Reads the value of a Java object field and adds a corresponding DbField to the 
     * DbObject builder.
     */
    private static DbValue fieldToDbValue(Object object, Field field) 
            throws IllegalArgumentException, IllegalAccessException {
        // See http://docs.oracle.com/javase/1.5.0/docs/api/java/lang/Class.html#getName%28%29
        // for Java type names.
        
        Object fieldValue = field.get(object);
        Class<?> c = field.getType();
        DbValue dbValue = DbValue.toDbValue(c, fieldValue);
        assert dbValue != null;
        return dbValue;
    }
    
    /**
     * Converts this DbObject to a Java object.
     * 
     * @param c     The wanted Class of the Java object that is created and returned.
     * @param c2o   How to create objects from classes.
     * @return      The newly created object of class c.
     */
    @SuppressWarnings("unchecked")
    public <TYPE> TYPE toJavaObject(Class<TYPE> c, ClassToObject c2o) {
        if (isNull()) {
            return null;
        }
        
        TYPE result;
        
        if (c.isArray()) {
            DbArray array = this.getArray(WRAPPED_ARRAY_FIELD_NAME);
            if (array == null) {
                return (TYPE) null;
            }
            
            Class<?> componentType = c.getComponentType();
            int size = array.getSize();
            
            result = (TYPE) Array.newInstance(componentType, size);
            
            int index = 0;
            for (DbValue dbValue : array) {
                Array.set(result, index, dbValue.toJavaObject(componentType, c2o));
                index++;
            }
            
        } else if (DbValue.isPrimitiveOrWrapper(c)) {
            DbValue value = this.getDbValue(WRAPPED_PRIMITIVE_FIELD_NAME);
            if (value == null) {
                return (TYPE) null;
            }
            result = value.toJavaObject(c, c2o);
            
        } else {            
            TYPE object1 = c2o.newObject(c);
            result = (TYPE) toJavaObject(object1, c2o);
        }
        
        return result;
    }
    
    /**
     * Converts this DbObject to a Java object by setting the fields of 'dest'.
     * 
     * @param dest  The object to set the fields of, or null to create a new object.
     * @param c2o   How to create objects from classes.
     * @return      Returns 'dest' or defaultValue(dest.getClass()).
     */
    public Object toJavaObject(Object dest, ClassToObject c2o) {        
        if (dest == null) {
            throw new IllegalArgumentException("dest == null not allowed");
        }
        
        Class<?> c = dest.getClass();
        
        if (isNull()) {
            return defaultValue(c);
        }
        
        ArrayList<Field> fields = getEligibleFields(c);
        for (Field f : fields) {
            final String fieldName = f.getName();
            DbValue dbValue = getDbValue(fieldName);
            if (dbValue != null) {
                Object javaObject = dbValue.toJavaObject(f.getType(), c2o);
                try {
                    f.set(dest, javaObject);
                } catch (IllegalArgumentException e) {
                    throw new Bug(e);
                } catch (IllegalAccessException e) {
                    throw new Bug(e);
                }
            }
        }
        
        return dest;
    }
    
    /**
     * Gets the type of a field, or returns 'z' (think 'zero', nothing) if there is no such field.
     */
    public char getType(String name) {
        final short hash = hash(name);
        char result = 'z';
        
        if (this.key != null && hash == KEY_FIELD_HASH && name.equals(KEY_FIELD)) {
            return 's';
        }
        
        for (int i = 0; i < fieldCount; i++) {
            if (hash == hashes[i]) {
                NameAndType n = new NameAndType();
                readFieldInfo(i, n);
                
                if (n.name.equals(name)) {
                    result = (char) n.type;
                    break;
                }
            }
        }
        
        return result;
    }
    
    /**
     * Returns the DbValue of a field with a specified name.
     */
    public DbValue getDbValue(String name) {
        short hash = hash(name);
        DbValue result = null;
        
        if (this.key != null && hash == KEY_FIELD_HASH && name.equals(KEY_FIELD)) {
            return new DbString(key);
        }
        
        for (int i = 0; i < fieldCount; i++) {
            if (hash == hashes[i]) {
                NameAndType n = new NameAndType();
                readFieldInfo(i, n);
                
                if (n.name.equals(name)) {
                    result = DbValue.parse(n.type, bytes, n.valueOffset);
                    break;
                }
            }
        }
        
        return result;
    }
    
    
    // ======== getType(name) methods ========
    
    public boolean getBoolean(String name) {
        NameAndType n = internalSimpleGet(name, DbObject.BOOLEAN);
        return n == null ? false : DbBoolean.parseToBoolean(n.object.bytes, n.valueOffset);
    }
    
    public int getInt(String name) {
        NameAndType n = internalSimpleGet(name, DbObject.INT);
        return n == null ? 0 : DbInt.parseToInt(n.object.bytes, n.valueOffset);
    }
    
    public int getInt(String[] nameParts) {
        NameAndType n = internalGet(nameParts, 0, DbObject.INT);
        return n == null ? 0 : DbInt.parseToInt(n.object.bytes, n.valueOffset);
    }

    public long getLong(String name) {
        NameAndType n = internalSimpleGet(name, DbObject.LONG);
        return n == null ? 0 : DbLong.parseToLong(n.object.bytes, n.valueOffset);
    }
    
    public long getLong(String[] nameParts) {
        NameAndType n = internalGet(nameParts, 0, DbObject.LONG);
        return n == null ? 0 : DbLong.parseToLong(n.object.bytes, n.valueOffset);
    }
    
    public double getDouble(String name) {
        NameAndType n = internalSimpleGet(name, DbObject.DOUBLE);
        return n == null ? 0.0 : DbDouble.parseToDouble(n.object.bytes, n.valueOffset);
    }
    
    public double getDouble(String[] nameParts) {
        NameAndType n = internalGet(nameParts, 0, DbObject.DOUBLE);
        return n == null ? 0.0 : DbDouble.parseToDouble(n.object.bytes, n.valueOffset);
    }

    /**
     * @throws BadFormatException
     */
    public String getString(String name) {
        short hash = hash(name);
        if (hash == KEY_FIELD_HASH && this.key != null && name.equals(KEY_FIELD)) {
            return this.key;
        }
        
        NameAndType n = internalSimpleGet(name, DbObject.STRING);
        return n == null ? null : DbString.parseToString(n.object.bytes, n.valueOffset);
    }
    
    public String getString(String[] nameParts) {
        NameAndType n = internalGet(nameParts, 0, DbObject.STRING);
        return n == null ? null : DbString.parseToString(n.object.bytes, n.valueOffset);
    }
    
    public byte[] getByteArray(String name) {
        NameAndType n = internalSimpleGet(name, DbObject.BYTE_ARRAY);
        return n == null ? null : DbByteArray.parseToByteArray(n.object.bytes, n.valueOffset);
    }
    
    public DbArray getArray(String name) {
        NameAndType n = internalSimpleGet(name, DbObject.ARRAY);
        return n == null ? null : DbArray.parse(n.object.bytes, n.valueOffset);
    }
    
    public DbObject getObject(String name) {
        NameAndType n = internalSimpleGet(name, DbObject.OBJECT);
        return n == null ? null : DbObject.parse(n.object.bytes, n.valueOffset);
    }
    
    // ====

    /**
     * Reads field name and type.
     */
    private void readFieldInfo(int fieldIndex, NameAndType n) {
        int fieldOffset = readFieldOffset(fieldIndex);
        int offset = fieldOffset;
        n.type = (char) bytes[offset];
        offset += 1;
        short nameSize = Bytes.bytesToShortLE(bytes, offset);
        offset += 2;
        byte[] nameBytes = new byte[nameSize];
        System.arraycopy(bytes, offset, nameBytes, 0, nameSize);
        offset += nameSize;
        n.name = StringUtil.toString(nameBytes);
        n.valueOffset = offset;
        n.object = this;
    }
    
    private int readFieldOffset(int fieldIndex) {
        return Bytes.bytesToIntLE(bytes, HEADER_SIZE + 6 * fieldIndex + 2);
    }
    
    /**
     * Very simple and fast hash value.
     */
    public static short hash(String name) {
        // Note, this computation cannot be changed easily. Part of serialize format.
        assert name != null && name.length() > 0;        
        final int len = name.length();
        short hash = (short) (len + 23 * name.charAt(0) + 43 * name.charAt(len - 1));
        return hash;
    }
    
    public int getByteSize() {
        return 4 + bytes.length;
    }
    
    public int write(byte[] b, int offset) {
        Bytes.intToBytesLE(bytes.length, b, offset);
        offset += 4;
        System.arraycopy(bytes, 0, b, offset, bytes.length);
        offset += bytes.length;
        return offset;
    }
    
    public static DbObject parse(byte[] buffer, int offset) {
        int size = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        
        if (size == -1) {
            return null;
        }
        
        if (size < 0) {
            throw new BadFormatException("size = " + size);
        }
        
        byte[] bytes = new byte[size];
        System.arraycopy(buffer, offset, bytes, 0, bytes.length);
        return new DbObject(bytes);
    }
    
    private static class DbField {
        private final String name;
        private final byte[] nameBytes;
        private final char type;
        private final short hash;
        private final DbValue value;
        
        public DbField(String name, DbValue value) {
            assert name != null;
            assert name.length() > 0;
            assert value != null;
            
            this.name = name;
            this.hash = hash(name);
            this.nameBytes = StringUtil.toBytes(name);
            // The byte length, as stored, since 2026-10-21 (bergdb 005-21); the char length
            // was checked, and a longer UTF-8 name was stored with a wrapped short length.
            if (nameBytes.length > Short.MAX_VALUE) {
                throw new IllegalArgumentException("Name is too large, " + this.nameBytes.length 
                        + " bytes.");
            }
            this.type = value.getType();
            this.value = value;
        }
        
        public int getByteSize() {
            return 1 + 2 + nameBytes.length + value.getByteSize();
        }
        
        /**
         * Serializes the field - type, name, value - to the supplied buffer, 'b'.
         * 
         * @param b  The buffer to serialize to.
         * @param offset  The offset into 'b' to start write to.
         * @return The new offset for 'b'; that is, the original 'offset' plus number of bytes
         * written to.
         */
        public int write(byte[] b, int offset) {
            int offset0 = offset;
            b[offset] = (byte) type;
            offset += 1;
            Bytes.shortToBytesLE((short) nameBytes.length, b, offset);
            offset += 2;
            System.arraycopy(nameBytes, 0, b, offset, nameBytes.length);
            offset += nameBytes.length;
            value.write(b, offset);
            offset += value.getByteSize();
            assert offset == offset0 + getByteSize();
            return offset;
        }
        
        public String toString() {
            return name + ": " + value.toString();
        }
        
        public static DbField parse(byte[] b, int offset) {
            char type = (char) b[offset];
            offset += 1;
            
            int nameSize = Bytes.bytesToShortLE(b, offset);
            offset += 2;
            byte[] nameBytes = new byte[nameSize];
            
            try {
                System.arraycopy(b, offset, nameBytes, 0, nameBytes.length);
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new ArrayIndexOutOfBoundsException("nameSize=" + nameSize + ", offset=" + offset + ", b.length=" + b.length);
            }
            
            offset += nameBytes.length;
            
            String name = StringUtil.toString(nameBytes);
            DbValue value;
            
            switch (type) {
            case 'n':
                value = DbBoolean.parse(b, offset);
                break;
            case 'i':
                value = DbInt.parse(b, offset);
                break;
            case 'l':
                value = DbLong.parse(b, offset);
                break;
            case 'd':
                value = DbDouble.parse(b, offset);
                break;
            case 's':
                value = DbString.parse(b, offset);
                break;
            case 'b':
                value = DbByteArray.parse(b, offset);
                break;
            case 'a':
                value = DbArray.parse(b, offset);
                break;
            case 'o':
                value = DbObject.parse(b, offset);
                break;
            default:
                throw new IllegalArgumentException("Bad type: " + type + ".");
            }
            
            return new DbField(name, value);
        }
    }
    
    private static class NameAndType {
        String name;
        int valueOffset;
        char type;
        
        /** Object in which the matching field was found. */
        DbObject object;
    }
    
    /**
     * A builder object used to create a DbObject.
     */
    public static class Builder {
        private ArrayList<DbField> fields;
        
        public Builder() {
            fields = new ArrayList<DbField>();
        }
        
        public static DbObject buildNull() {
            DbObject result = new Builder().buildInner(true);
            assert result.isNull() : "result is not null";
            return result;
        }
        
        private void addField(DbField field) {
            int index = -1;
            final byte[] fieldName = field.nameBytes;
            final int size = fields.size();
            
            if (size >= Short.MAX_VALUE) {
                throw new IllegalStateException("More than " + Short.MAX_VALUE 
                        + " fields is not allowed.");
            }
            
            for (int i = 0; i < size; i++) {
                DbField f = fields.get(i);
                if (Arrays.equals(f.nameBytes, fieldName)) {
                    index = i;
                    break;
                }
            }
            
            if (index == -1) {
                fields.add(field);
            } else {
                fields.set(index, field);
            }
        }
        
        public Builder addDbValue(String name, DbValue value) {
            addField(new DbField(name, value));
            return this;
        }
        
        public Builder addInt(String name, int value) {
            addField(new DbField(name, new DbInt(value)));
            return this;
        }
        
        public Builder addLong(String name, long value) {
            addField(new DbField(name, new DbLong(value)));
            return this;
        }

        public Builder addString(String name, String value) {
            addField(new DbField(name, new DbString(value)));
            return this;
        }
        
        public Builder addObject(String name, DbObject value) {
            addField(new DbField(name, value));
            return this;
        }
        
        public Builder addArray(String name, DbArray value) {
            addField(new DbField(name, value));
            return this;
        }
        
        /**
         * Builds a DbObject with its fields in order sorted alphabetically according
         * to their names.
         */
        public DbObject build() {
            return buildInner(false);
        }
        
        /**
         * Builds a DbObject with its fields in order sorted alphabetically according
         * to their names.
         * This method currently (2013-11) defines the byte format of a DbObject.
         */
        private DbObject buildInner(boolean isNull) {            
            int size = 0;
            
            assert fields.size() <= Short.MAX_VALUE;
            
            if (isNull && fields.size() != 0) {
                throw new IllegalStateException("fields.size() = " + fields.size());
            }
            
            Collections.sort(fields, new Comparator<DbField>() {
                public int compare(DbField f1, DbField f2) {
                    return ByteArrayComparator.compareArrays(f1.nameBytes, f2.nameBytes);
                }
            });
            
            for (DbField f : fields) {
                size += f.getByteSize();
            }
            
            size += HEADER_SIZE;
            size += FIELD_INFO_SIZE * fields.size();  // for fast linear search, hash of name + offset
            
            int offset = 0;
            byte[] bytes = new byte[size];
            //Bytes.intToBytesLE(MAGIC, bytes, offset);
            //offset += 4;
            //bytes[offset] = 0;      // Version 0 of byte format.
            //offset++;
            
            System.arraycopy(MAGIC, 0, bytes, 0, MAGIC.length);
            offset += MAGIC.length;
            bytes[offset] = 1;        // Version 1 of byte format.
            offset++;
            short fieldSize = isNull ? -1 : (short) fields.size();
            Bytes.shortToBytesLE(fieldSize, bytes, offset);
            offset += 2;
            
            int fieldOffset = HEADER_SIZE + FIELD_INFO_SIZE * fields.size();
            
            for (DbField f : fields) {
                Bytes.shortToBytesLE(f.hash, bytes, offset);
                offset += 2;
                Bytes.intToBytesLE(fieldOffset, bytes, offset);
                offset += 4;
                fieldOffset += f.getByteSize();
            }
            
            for (DbField f : fields) {
                offset = f.write(bytes, offset);
            }
            
            return new DbObject(bytes, null);
                // Note, we could have a special constructor or static method that does not
                // do format checking since it is not required when DbObject is created
                // with its Builder.
        }
    }
    
    public static void main(String[] args) {
        DbObject t = new DbObject.Builder().build();
        System.out.println("size: " + t.getBytes().length);
        System.out.println("t buffer to string: " + StringUtil.toString(t.getBytes()));
    }
    
    /** bergdb 005-21: a name too long in UTF-8 bytes is refused (the chars were checked). */
    @bergdb.nanotest.Nano
    private static void testLongFieldName() {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < 20000; i++) {
            b.append('\u00e9');      // two bytes in UTF-8
        }
        try {
            new Builder().addInt(b.toString(), 1).build();
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
    }
}

/*

Overhead for a single int
=========================

2013-09-01. Considering support for single numeric values
(Byte, Character, Short, Int, Long, Float, Double). Example code:

    c.set("noOfCores.obj", 8).execute();
    int noOfCores = c.get("noOfCores.obj", Integer.class);
    
The size of the value (if stored in field "v") would be 8 + 6 + 1 + 2 + 1 + 4
= 18 + 4 = 22. 18 bytes overhead. Not super much waste, but not super efficient either.
We could have 8 + 4 = 12 instead and still keep the 4-byte signature and version.
Special type byte used for byte at index 5 - currently 0 and not used. Or we could
reduce header size with 4 bytes and have: ['B' VERSION(1) SIZE(2)] as header.

However, this optimization may not be worth it. Could be done with code storing
primitive as byte[]. This allows zero overhead for the stored value.


Types to support, notes
=======================

Supporting as many field types as possible is not be the best approach. Not all languages
will support all types, obviously. We want a subset of types inspired by Java and C#.
We want to keep complexity as low as possible. Serialization of existing objects is not the goal; 
we assume specially crafted classes for data storage.

More important than supporting many types, is portability to vast number of platforms
and languages. Therefore, a small set of types, supported on almost all systems has been
chosen.

== Java ==

Primitive (8): boolean, byte, char, short, int, long, float, double.
String, Object. 1D, 2D arrays of these. Generic types.

== Json ==

Supports arrays, objects and the following values: string, number, true, false, null.
No exact definition of max size of number. JavaScript works the same.
To convert Json->DbObject, we would need to choose byte/int/long for integers
and float/double for floating point numbers. Could be chosen based on size needed to encode
the value, but often, we might need a more "stable" type for the number.
We could choose to always represent integers as long and floating point numbers as double.

== BSON ==

"Binary JSON"; used internally in MongoDB. I think the definition of it is MongoDB-specific 
rather then created as a general document-serialization format.

== C# ==

All types in Java plus unsigned (byte, uint, ulong...), and 128-bit "precise fraction / integral type".

== SOAP ==

"Built-in types". See http://www.w3.org/TR/xmlschema-2/#built-in-datatypes  
Lots of ugly complexity. All Java primitive types and more.

== C ==

All Java primitive types and more. Primitive types can be made nullable (int?), references
are always nullable, like in Java.

== MySQL ==

Integers: TINYINT (1), SMALLINT (2), MEDIUMINT (3), INT (4), BIGINT (8). Both signed and unsigned.
DECIMAL - fixed point.
FLOAT, DOUBLE - floating point types.
BIT - bitfields
String: VARCHAR, CHAR, NVARCHAR, NCHAR.
BLOB, TEXT, LONGBLOB.

*/