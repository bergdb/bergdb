package bergdb.pub;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import bergdb.common.StringUtil;
import bergdb.pub.util.BadFormatException;
import bergdb.pubimp.DataObjects;
import bergdb.pubimp.ObjectFormat;

/**
 * <p>A stored object: an immutable set of named, typed fields, as BergDB stores an object
 * at a key, in the stored object format, format 2 (bergdb 020-07). A get as DbObject.class
 * gives the stored object exactly, whatever class put it; a put of a DbObject stores its
 * bytes as they are. An object has no schema: the fields of two objects are independent.
 * The format is the same in every language that reads or writes a database, not a detail
 * of Java.</p>
 *
 * <p><b>The model.</b> A field has a name, 1 to 255 bytes of well-formed UTF-8, unique in
 * its object, and a value of one of seven types, each with its type char:</p>
 *
 * <pre>
 * n - boolean    true or false.
 * l - integer    A signed 64-bit integer, the one integer type: Java's byte, short, char,
 *                int and long are each stored as an integer, in the fewest bytes.
 * d - double     A 64-bit floating point number (IEEE 754); every NaN is one value, and
 *                -0.0 is kept.
 * s - string     Unicode text, stored as well-formed UTF-8.
 * b - byteArray  Bytes, any.
 * a - array      A list of values, each of any type (DbArray).
 * o - object     A nested object, with fields of its own.
 * </pre>
 *
 * <p>The char 'z' is not a type: getType() gives it for a field that the object does not
 * have. INT, 'i', is not a stored type either: has(name, INT) is true, and getInt() gives
 * the value, for an integer within int's range. An object has at most 32,767 fields, at
 * most 16 levels of objects and arrays (the top object is level 1, a scalar is no level),
 * and its stored bytes at most 2^31 - 1 bytes by the format; in Java at most 2^31 - 9, the
 * most that an array holds.</p>
 *
 * <p><b>No null.</b> No value is null: a field without a value is absent, and an array has
 * no absent element (the package's {@linkplain bergdb.pub##null Null and absent fields}).
 * The Builder and the value classes refuse null, and toDbObject() leaves a null field
 * out.</p>
 *
 * <p><b>The bytes.</b> getBytes() gives the stored bytes, the bytes of the value at a key:
 * the header, HEADER (0x82), then the object. One object has one byte string: the fields
 * in the order of their names' unsigned bytes, every number in its fewest bytes, so two
 * objects with the same fields and values have equal bytes, and comparing getBytes() with
 * java.util.Arrays.equals() compares the objects. new DbObject(bytes) checks every rule
 * of the format and refuses any other bytes with BadFormatException, also an object of
 * BergDB 2026.3 and before (format 1). No UTF-8 string starts with the byte 0x82, so a
 * String value is never taken for an object.</p>
 *
 * <p><b>The lookups.</b> A field is found by its name with a binary search on the object's
 * table of fields, so a lookup takes a time logarithmic in the number of fields, with no
 * parse of the object. The typed getters, getBoolean(), getInt(), getLong(), getDouble(),
 * getString(), getByteArray(), getArray() and getObject(), give the field's value if the
 * field is there and of the getter's type, and otherwise false, 0, 0.0 or null: for a field
 * that is absent and for one of another type alike, never a throw for the data (bergdb
 * 020-04, Q6; 020-09). has(name, type) and getType(name) tell the cases apart. A name that
 * no field can have (empty, longer than 255 bytes in UTF-8, or with a lone surrogate) is
 * absent; a null name is refused with IllegalArgumentException. The getters that take
 * String[] follow a path of nested objects, one name per level; a part that is absent or
 * not an object makes the field absent.</p>
 *
 * <p><b>Views.</b> getObject() gives a view on this object's bytes: no copy is made, and the
 * nested object's getBytes() gives its own stored bytes with the header, a new array. The
 * other getters give copies: a byte[] from getByteArray() is the caller's, and a DbArray
 * holds its own bytes.</p>
 *
 * <p><b>Immutable and thread-safe.</b> A DbObject never changes, and any number of threads
 * may read one at the same time without synchronization: new DbObject(bytes) copies the
 * bytes, and getBytes() gives a copy. No class outside BergDB extends DbValue: its
 * constructor is not public, and the package is sealed in BergDB's jars. A put of a
 * DbObject checks its bytes by the format's full check and stores a copy. The Builders
 * are not thread-safe: use one from one thread.</p>
 *
 * <p><b>Strings.</b> A string, and a field's name, is Unicode text stored as well-formed
 * UTF-8, as every string BergDB stores (the package's
 * {@linkplain bergdb.pub##strings Strings}). A Java String with a lone surrogate, a char
 * of U+D800 to U+DFFF that is not part of a surrogate pair, cannot be stored so:
 * toDbObject(), the Builder and DbString refuse it with IllegalArgumentException; the
 * message of toDbObject() names its place, the field and an array element's index
 * ("inner.names[3]"). A char[] field keeps any chars, as an array of integers; a byte[]
 * field keeps any bytes.</p>
 *
 * <p><b>Data Objects.</b> toDbObject() makes a DbObject from an object of a Data Object
 * class, exactly, as a put stores it; toJavaObject() makes an object of a Data Object class
 * from a DbObject, best effort, as a get does (the package's
 * {@linkplain bergdb.pub##objects Objects}; bergdb 020-09).</p>
 *
 * @author Frans Lundberg
 */
public final class DbObject extends DbValue {
    //
    // 1304 Frans: Little-endian-first (LE) byte order is used to follow the byte ordering used 
    // in the db stream.
    // 1309 Frans: Added support for Java arrays; they are wrapped field 'v' of a DbObject.
    // 1311 Frans: Changed byte signature to start with "bergo", then byte value 1 for version.
    // 2026-11 (bergdb 020-08, step 2): format 2, bergdb 020-07; "bergo" is format 1.
    // 2026-11 (bergdb 020-08, step 7): no key field; a field named "key" is an ordinary field
    // (Frans, 2026-11-08, 19:21; bergdb 020-02, section 5.1b).
    //
    
    /** The header of a stored object, format 2: its first byte, 0x82 (bergdb 020-07, R1). */
    public static final byte HEADER = (byte) ObjectFormat.HEADER;
    
    /** The type char of a boolean. */
    public static final char BOOLEAN = 'n';
    
    /** Not a stored type: an integer within int's range, for has() (bergdb 020-08, section 3). */
    public static final char INT = 'i';
    
    /** The type char of an integer, 64 bits: getType() of every integer. */
    public static final char LONG = 'l';
    
    /** The type char of a double. */
    public static final char DOUBLE = 'd';
    
    /** The type char of a string. */
    public static final char STRING = 's';
    
    /** The type char of bytes. */
    public static final char BYTE_ARRAY = 'b';
    
    /** The type char of an array. */
    public static final char ARRAY = 'a';
    
    /** The type char of an object. */
    public static final char OBJECT = 'o';
    
    
    private final byte[] bytes;     // the stored value, header first; or a parent's bytes
    private final int start;        // the object's type byte in 'bytes'
    private final int end;          // after its last field
    private final boolean whole;    // 'bytes' is the stored value of this object
    private int height;             // its levels, 1 or more; 0 until computed (a benign
                                    // race: every thread computes the same value)
    
    /**
     * Reads a stored object from its bytes, as getBytes() gives them: checked by every rule of
     * the format (bergdb 020-07, section 7.1), so that no later lookup meets bytes it cannot
     * read.
     * 
     * @param b 
     *      The stored bytes, the header first. They are copied: a later change of 'b' does
     *      not change the object.
     * @throws BadFormatException 
     *      If the bytes are not a stored object of format 2; the message starts with the
     *      condition's code (bergdb 020-07, section 7.2), "format-1" for an object of
     *      BergDB 2026.3 and before.
     * @throws IllegalArgumentException  If 'b' is null.
     */
    public DbObject(byte[] b) throws BadFormatException {
        super('o');
        if (b == null) {
            throw new IllegalArgumentException("b == null not allowed");
        }
        byte[] copy = b.clone();
        ObjectFormat.checkStored(copy);
        this.bytes = copy;
        this.start = 1;
        this.end = copy.length;
        this.whole = true;
    }
    
    /** The object in [start, end) of checked 'bytes'. */
    private DbObject(byte[] bytes, int start, int end, boolean whole, int height) {
        super('o');
        this.bytes = bytes;
        this.start = start;
        this.end = end;
        this.whole = whole;
        this.height = height;
    }
    
    /** The object at 'p' of checked bytes, a view on them; 'b' must not change. */
    static DbObject view(byte[] b, int p) {
        return new DbObject(b, p, ObjectFormat.objectEnd(b, p), false, 0);
    }
    
    /**
     * Returns the stored bytes, the header first: the bytes that a put of this object stores
     * and that new DbObject(bytes) reads back. A new array each time, the caller's: a change
     * of it changes neither this object nor what a put of it stored (2026-11-09, the review
     * of bergdb 020-10, B3: the object's own array, so a change after a put changed the
     * committed value in memory).
     *
     * @return A copy of the stored bytes.
     */
    public byte[] getBytes() {
        if (whole) {
            return this.bytes.clone();
        }
        byte[] b = new byte[1 + end - start];
        b[0] = HEADER;
        System.arraycopy(bytes, start, b, 1, end - start);
        return b;
    }
    
    /**
     * Returns the number of fields of the object, 0 to 32,767.
     *
     * @return The number of fields.
     */
    public int getFieldCount() {
        return ObjectFormat.countAt(bytes, start);
    }
    
    /**
     * Returns true if the object has a field with the given name and type: tells a field
     * that is absent from one of another type, which the typed getters do not. For INT, a
     * field of an integer within int's range.
     *
     * @param name  The field's name.
     * @param type  A type char, such as LONG; or INT.
     * @return True if the field is there and of the type.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public boolean has(String name, char type) {
        return is(find(name), type);
    }
    
    /**
     * Returns true if the object has a nested field with the given name parts, one name per
     * level of nested objects, and the given type.
     *
     * @param nameParts  The names, the top object's field first.
     * @param type  A type char, such as LONG; or INT.
     * @return True if the field is there and of the type.
     * @throws IllegalArgumentException  If 'nameParts' is null, empty or holds a null,
     *      checked first, also when an earlier part is absent.
     */
    public boolean has(String[] nameParts, char type) {
        checkParts(nameParts);
        if (nameParts.length == 1) {
            return has(nameParts[0], type);
        }
        return is(find(nameParts), type);
    }
    
    /** Whether the value at 'p' is of 'type': false if p is -1, absent. */
    private boolean is(int p, char type) {
        if (p < 0) {
            return false;
        }
        char t = ObjectFormat.typeAt(bytes, p);
        if (type == INT) {
            return t == LONG && ObjectFormat.integerAt(bytes, p) == (int) ObjectFormat.integerAt(
                    bytes, p);
        }
        return t == type;
    }
    
    /** The start of the value of the field 'name', or -1 if absent (bergdb 020-07, section 8). */
    private int find(String name) {
        byte[] b = nameBytes(name);
        return b == null ? -1 : ObjectFormat.find(bytes, start, end, b);
    }
    
    /**
     * Refuses name parts that are null, empty or hold a null, before any lookup, so that the
     * answer does not depend on the data (2026-11-09, the review of bergdb 020-10, B3: a null
     * after an absent part gave 0 or null, a null array a NullPointerException).
     */
    private static void checkParts(String[] parts) {
        if (parts == null || parts.length == 0) {
            throw new IllegalArgumentException("nameParts: null or empty; a nested field "
                    + "has one name per level");
        }
        for (String part : parts) {
            if (part == null) {
                throw new IllegalArgumentException("nameParts: a part is null");
            }
        }
    }
    
    /** The start of the value of a nested field, or -1 if absent. */
    private int find(String[] parts) {
        if (parts.length == 0) {
            throw new IllegalArgumentException("no name parts");
        }
        int p = start;
        int e = end;
        for (int k = 0; ; k++) {
            byte[] b = nameBytes(parts[k]);
            int q = b == null ? -1 : ObjectFormat.find(bytes, p, e, b);
            if (q < 0 || k == parts.length - 1) {
                return q;
            }
            if (!ObjectFormat.isObjectAt(bytes, q)) {
                return -1;
            }
            p = q;
            e = ObjectFormat.objectEnd(bytes, q);
        }
    }
    
    /**
     * A field's name in UTF-8, or null if no field has it: an empty name, one with a lone
     * surrogate, which has no UTF-8 form (a replacing encoder would give '?' and find a field
     * named so), or one longer than 255 bytes.
     */
    private static byte[] nameBytes(String name) {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        if (name.isEmpty() || StringUtil.hasLoneSurrogate(name)) {
            return null;
        }
        byte[] b = name.getBytes(StandardCharsets.UTF_8);
        return b.length > ObjectFormat.MAX_NAME ? null : b;
    }
    
    /**
     * Converts a Data Object to a DbObject, exactly (bergdb 020-09, section 4): a Data Object
     * class stores its public, non-static, non-transient fields, each by its declared type; a
     * null field is left out (absent); an array put at the top is wrapped in the field
     * "array", a primitive or a wrapper in the field "p". A DbObject is returned as it is.
     *
     * @throws IllegalArgumentException  If 'object' is null, or is not a Data Object, or a
     *      class it reaches is not (bergdb 020-09, section 3); if an array in it has a null
     *      element (bergdb 020-04, section 2.1); if a value's class is not its field's type;
     *      if a String in the object, at any depth, has a lone surrogate (see "Strings" above;
     *      bergdb 021-04); if the object has a reference cycle (bergdb 005-23), or is nested
     *      deeper than 16 levels of objects and arrays (bergdb 020-07, R14). The message
     *      names the class or the place: the field, and an array element's index.
     */
    public static DbObject toDbObject(Object object) {
        return DataObjects.toDbObject(object);
    }
    
    /**
     * Converts this DbObject to an object of the class 'c', best effort (bergdb 020-09,
     * section 5): each stored field with a matching field of the class is converted to the
     * field's type, the nearest value where it does not fit, the type's zero where no
     * sensible conversion exists; a field of the class that is not stored keeps the value its
     * constructor gives. A primitive class or a wrapper reads the field "p", an array class
     * the field "array"; null if it is absent.
     * 
     * @param c     The wanted Class of the Java object that is created and returned: a Data
     *              Object class, a primitive or a wrapper, or an array class.
     * @return      The newly created object of class c.
     * @throws bergdb.pub.ObjectCreationException  If 'c', or a class it reaches through its
     *              fields' types, is not a Data Object class (bergdb 020-09, section 3), or
     *              a constructor throws (the cause).
     */
    public <TYPE> TYPE toJavaObject(Class<TYPE> c) {
        return DataObjects.toJavaObject(bytes, start, c);       // reads, no copy
    }
    
    /**
     * Returns the type char of a field, or 'z' (think 'zero', nothing) if the object has no
     * field of that name: absent. LONG, 'l', for every integer.
     *
     * @param name  The field's name.
     * @return The type char, or 'z'.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public char getType(String name) {
        int p = find(name);
        return p < 0 ? 'z' : ObjectFormat.typeAt(bytes, p);
    }
    
    /**
     * Returns the value of a field as a DbValue of its type (DbBoolean, DbLong, DbDouble,
     * DbString, DbByteArray, DbArray or DbObject), or null if the field is absent. A DbObject
     * is a view on this object's bytes; the other values are copies.
     *
     * @param name  The field's name.
     * @return The value, or null.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public DbValue getDbValue(String name) {
        int p = find(name);
        return p < 0 ? null : DbValue.read(bytes, p);
    }
    
    
    // ======== getType(name) methods ========
    //
    // Each gives the value of a field of its type: 0, false or null if the field is absent
    // or of another type (bergdb 020-04, Q6, decided 2026-11-09 under Frans's delegation).
    
    /**
     * The value of a boolean field; false if the field is absent or not a boolean.
     *
     * @param name  The field's name.
     * @return The value, or false.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public boolean getBoolean(String name) {
        int p = find(name);
        return is(p, BOOLEAN) && ObjectFormat.booleanAt(bytes, p);
    }
    
    /**
     * The value of an integer field within int's range; 0 if the field is absent, not an
     * integer, or an integer outside int's range (has(name, INT) tells).
     *
     * @param name  The field's name.
     * @return The value, or 0.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public int getInt(String name) {
        int p = find(name);
        return is(p, INT) ? (int) ObjectFormat.integerAt(bytes, p) : 0;
    }
    
    /**
     * As getInt(String), for a nested field: one name per level of nested objects.
     *
     * @param nameParts  The names, the top object's field first.
     * @return The value, or 0.
     * @throws IllegalArgumentException  If 'nameParts' is null, empty or holds a null,
     *      checked first, also when an earlier part is absent.
     */
    public int getInt(String[] nameParts) {
        checkParts(nameParts);
        if (nameParts.length == 1) {
            return getInt(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, INT) ? (int) ObjectFormat.integerAt(bytes, p) : 0;
    }

    /**
     * The value of an integer field; 0 if the field is absent or not an integer.
     *
     * @param name  The field's name.
     * @return The value, or 0.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public long getLong(String name) {
        int p = find(name);
        return is(p, LONG) ? ObjectFormat.integerAt(bytes, p) : 0;
    }
    
    /**
     * As getLong(String), for a nested field: one name per level of nested objects.
     *
     * @param nameParts  The names, the top object's field first.
     * @return The value, or 0.
     * @throws IllegalArgumentException  If 'nameParts' is null, empty or holds a null,
     *      checked first, also when an earlier part is absent.
     */
    public long getLong(String[] nameParts) {
        checkParts(nameParts);
        if (nameParts.length == 1) {
            return getLong(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, LONG) ? ObjectFormat.integerAt(bytes, p) : 0;
    }
    
    /**
     * The value of a double field; 0.0 if the field is absent or not a double. An integer
     * field is not a double: getLong() reads it.
     *
     * @param name  The field's name.
     * @return The value, or 0.0.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public double getDouble(String name) {
        int p = find(name);
        return is(p, DOUBLE) ? Double.longBitsToDouble(ObjectFormat.doubleBitsAt(bytes, p)) 
                : 0.0;
    }
    
    /**
     * As getDouble(String), for a nested field: one name per level of nested objects.
     *
     * @param nameParts  The names, the top object's field first.
     * @return The value, or 0.0.
     * @throws IllegalArgumentException  If 'nameParts' is null, empty or holds a null,
     *      checked first, also when an earlier part is absent.
     */
    public double getDouble(String[] nameParts) {
        checkParts(nameParts);
        if (nameParts.length == 1) {
            return getDouble(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, DOUBLE) ? Double.longBitsToDouble(ObjectFormat.doubleBitsAt(bytes, p)) 
                : 0.0;
    }

    /**
     * The value of a string field; null if the field is absent or not a string.
     *
     * @param name  The field's name.
     * @return The value, or null.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public String getString(String name) {
        int p = find(name);
        return is(p, STRING) ? ObjectFormat.stringAt(bytes, p) : null;
    }
    
    /**
     * As getString(String), for a nested field: one name per level of nested objects.
     *
     * @param nameParts  The names, the top object's field first.
     * @return The value, or null.
     * @throws IllegalArgumentException  If 'nameParts' is null, empty or holds a null,
     *      checked first, also when an earlier part is absent.
     */
    public String getString(String[] nameParts) {
        checkParts(nameParts);
        if (nameParts.length == 1) {
            return getString(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, STRING) ? ObjectFormat.stringAt(bytes, p) : null;
    }
    
    /**
     * The value of a bytes field, a new array; null if the field is absent or not bytes.
     *
     * @param name  The field's name.
     * @return The value, or null.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public byte[] getByteArray(String name) {
        int p = find(name);
        return is(p, BYTE_ARRAY) ? ObjectFormat.bytesAt(bytes, p) : null;
    }
    
    /**
     * The value of an array field; null if the field is absent or not an array.
     *
     * @param name  The field's name.
     * @return The value, or null.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public DbArray getArray(String name) {
        int p = find(name);
        return is(p, ARRAY) ? DbArray.read(bytes, p) : null;
    }
    
    /**
     * The value of an object field, a view on this object's bytes; null if the field is
     * absent or not an object.
     *
     * @param name  The field's name.
     * @return The value, or null.
     * @throws IllegalArgumentException  If 'name' is null.
     */
    public DbObject getObject(String name) {
        int p = find(name);
        return is(p, OBJECT) ? view(bytes, p) : null;
    }
    
    // ====
    
    /**
     * The size of the object's encoding as a value, without the header: its type byte,
     * count, ends and fields, as it is nested in another object (bergdb 020-07, section 4).
     */
    public int getByteSize() {
        return end - start;
    }
    
    /** Writes the encoding that getByteSize() counts. */
    public int write(byte[] b, int offset) {
        System.arraycopy(bytes, start, b, offset, end - start);
        return offset + end - start;
    }
    
    int height() {
        if (height == 0) {
            height = ObjectFormat.heightAt(bytes, start);
        }
        return height;
    }
    
    private static class DbField {
        private final String name;
        private final byte[] nameBytes;
        private final DbValue value;
        
        public DbField(String name, DbValue value) {
            // Refused, not asserted (bergdb 021-07): an AssertionError in rw() fails the
            // database (019-10).
            if (name == null || name.isEmpty()) {
                throw new IllegalArgumentException("A field's name must not be null or empty.");
            }
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, field '" + name
                        + "': BergDB stores no null, leave the field out (bergdb 020-04).");
            }
            
            // A name is a string too: well-formed UTF-8 (bergdb 021-04). javac refuses a
            // lone surrogate in a field's name, but a generated class or the Builder may not.
            if (StringUtil.hasLoneSurrogate(name)) {
                throw PathException.loneSurrogate("field name");
            }
            this.name = name;
            this.nameBytes = name.getBytes(StandardCharsets.UTF_8);
            // 1 to 255 bytes (bergdb 020-07, R6); 32,767 until 2026.3 (bergdb 005-21).
            if (nameBytes.length > ObjectFormat.MAX_NAME) {
                throw PathException.longName(nameBytes.length);
            }
            this.value = value;
        }
        
        public String toString() {
            return name + ": " + value.toString();
        }
    }
    
    /**
     * A builder of a DbObject: fields are added in any order, and build() writes the
     * object's bytes, its fields sorted by their names. A field added with the name of one
     * added before replaces it. The builder may build again, with the fields it has. It is
     * not thread-safe: use it from one thread.
     *
     * <p>Each add refuses, with IllegalArgumentException, a name that is null, empty, longer
     * than 255 bytes in UTF-8 or that has a lone surrogate; a null value; a 32,768th field.
     * build() refuses an object of more than 16 levels, or of more than 2^31 - 9 bytes, the
     * most that a Java array holds (the format allows 2^31 - 1).</p>
     */
    public static final class Builder {
        private final ArrayList<DbField> fields = new ArrayList<DbField>();
        private final HashMap<String, Integer> indexes = new HashMap<String, Integer>();
        
        /** A builder with no fields. */
        public Builder() {
        }
        
        /** Adds a field, or replaces the field of its name. */
        private void addField(DbField field) {
            Integer index = indexes.get(field.name);
            if (index != null) {
                fields.set(index, field);
                return;
            }
            if (fields.size() >= ObjectFormat.MAX_FIELDS) {
                throw new IllegalArgumentException("More than " + ObjectFormat.MAX_FIELDS 
                        + " fields is not allowed (bergdb 020-07, R3).");
            }
            indexes.put(field.name, fields.size());
            fields.add(field);
        }
        
        /**
         * Adds a field of any type: a DbBoolean, DbLong, DbDouble, DbString, DbByteArray,
         * DbArray or DbObject.
         *
         * @param name  The field's name.
         * @param value  The value.
         * @return This builder.
         */
        public Builder addDbValue(String name, DbValue value) {
            addField(new DbField(name, value));
            return this;
        }
        
        /**
         * Adds an integer: format 2 has one integer type, 'l' (bergdb 020-07, R9).
         *
         * @param name  The field's name.
         * @param value  The value.
         * @return This builder.
         */
        public Builder addInt(String name, int value) {
            addField(new DbField(name, new DbLong(value)));
            return this;
        }
        
        /**
         * Adds an integer.
         *
         * @param name  The field's name.
         * @param value  The value.
         * @return This builder.
         */
        public Builder addLong(String name, long value) {
            addField(new DbField(name, new DbLong(value)));
            return this;
        }

        /**
         * Adds a string.
         *
         * @param name  The field's name.
         * @param value  The value: not null, and with no lone surrogate.
         * @return This builder.
         */
        public Builder addString(String name, String value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed (bergdb 021-07)");
            }
            addField(new DbField(name, new DbString(value)));
            return this;
        }
        
        /**
         * Adds a nested object: its bytes are copied in at build().
         *
         * @param name  The field's name.
         * @param value  The value.
         * @return This builder.
         */
        public Builder addObject(String name, DbObject value) {
            addField(new DbField(name, value));
            return this;
        }
        
        /**
         * Adds an array.
         *
         * @param name  The field's name.
         * @param value  The value.
         * @return This builder.
         */
        public Builder addArray(String name, DbArray value) {
            addField(new DbField(name, value));
            return this;
        }
        
        /**
         * Builds a DbObject with its fields in order sorted by their names' unsigned bytes:
         * a stored object of format 2 (bergdb 020-07, sections 4 to 6), written bottom up,
         * each nested value copied in (bergdb 020-08, section 4.4).
         * 
         * @throws IllegalArgumentException  If the object would have more than 16 levels of
         *      objects and arrays (bergdb 020-07, R14), or more than 2^31 - 9 bytes, the most
         *      that a Java array holds (R15 allows 2^31 - 1).
         */
        public DbObject build() {
            DbField[] f = fields.toArray(new DbField[0]);
            Arrays.sort(f, (x, y) -> Arrays.compareUnsigned(x.nameBytes, y.nameBytes));
            int n = f.length;
            int[] ends = new int[n];
            long size = 0;
            int height = 1;
            for (int i = 0; i < n; i++) {
                size += 1 + f[i].nameBytes.length + (long) f[i].value.getByteSize();
                ObjectFormat.checkStoredSize(size);
                ends[i] = (int) size;
                height = Math.max(height, 1 + f[i].value.height());
            }
            if (height > ObjectFormat.MAX_LEVELS) {
                throw new IllegalArgumentException("The object has " + height + " levels of "
                        + "objects and arrays; at most " + ObjectFormat.MAX_LEVELS 
                        + " (bergdb 020-07, R14).");
            }
            long total = 1 + ObjectFormat.headSize(n, size) + size;
            ObjectFormat.checkStoredSize(total);
            if (total > ObjectFormat.MAX_ARRAY) {
                throw new IllegalArgumentException("size: a stored value of " + total 
                        + " bytes, more than the " + ObjectFormat.MAX_ARRAY + " of Java's "
                        + "largest array (bergdb 020-07, R15)");
            }
            
            byte[] b = new byte[(int) total];
            b[0] = HEADER;
            int p = ObjectFormat.frame(b, 1, ends, n);
            for (DbField field : f) {
                p = ObjectFormat.writeName(b, p, field.nameBytes);
                p = field.value.write(b, p);
            }
            assert p == b.length;
            return new DbObject(b, 1, b.length, true, height);
        }
    }
    
    /** Names of 1 to 255 bytes (bergdb 020-07, R6); 32,767 until 2026.3 (bergdb 005-21). */
    @bergdb.nanotest.Nano
    private static void testLongFieldName() {
        new Builder().addInt("\u00e9".repeat(127) + "a", 1).build();      // 255 bytes
        for (String name : new String[] {"\u00e9".repeat(128), "a".repeat(256), 
                "\u00e9".repeat(20000)}) {
            try {
                new Builder().addInt(name, 1).build();
                throw new AssertionError("no exception");
            } catch (IllegalArgumentException e) {
                bergdb.nanotest.Assert.assertTrue(e.getMessage(), 
                        e.getMessage().contains("has " + name.getBytes(StandardCharsets.UTF_8)
                        .length + " bytes"));
            }
        }
    }
    
    /**
     * Immutable (the review of B3, F1): getBytes() gives a copy, so a change of it changes
     * neither the object nor what a put of it stored.
     */
    @bergdb.nanotest.Nano
    private static void testGetBytesGivesACopy() {
        DbObject o = new Builder().addInt("a", 1).build();
        byte[] b = o.getBytes();
        b[b.length - 1] = 9;
        bergdb.nanotest.Assert.assertEquals(1, o.getInt("a"));
        bergdb.nanotest.Assert.assertTrue(o.getBytes() != o.getBytes());
    }
    
    /**
     * A put of a DbObject checks its bytes by the full check (the review of B3, F2): one whose
     * bytes break a rule, here made by this class's own constructor, is refused with
     * IllegalArgumentException naming the condition, and nothing is written.
     */
    @bergdb.nanotest.Nano
    private static void testPutChecksTheBytes() {
        byte[] bad = new Builder().addInt("a", 1).build().getBytes();
        bad[bad.length - 2] = 0x7f;     // the integer's type byte: no type
        final DbObject o = new DbObject(bad, 1, bad.length, true, 0);
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            try {
                c.put("/k", o);
                throw new AssertionError("a DbObject that breaks a rule was put");
            } catch (IllegalArgumentException e) {
                bergdb.nanotest.Assert.assertTrue(e.getMessage(), e.getMessage().contains("type"));
            }
            bergdb.nanotest.Assert.assertTrue(c.get("/k", byte[].class) == null);
        } finally {
            d.close();
        }
    }
    
    /**
     * The getters of a nested field check the parts first (the review of B3, F5): a null
     * array, an empty one, or one with a null part is refused, also after a part that is
     * absent.
     */
    @bergdb.nanotest.Nano
    private static void testNamePartsCheckedFirst() {
        final DbObject o = new Builder().addInt("a", 1).build();
        Runnable[] calls = {
            () -> o.getInt(new String[] {"absent", null}),
            () -> o.getLong(new String[] {"absent", null}),
            () -> o.getDouble(new String[] {"absent", null}),
            () -> o.getString(new String[] {"absent", null}),
            () -> o.has(new String[] {"absent", null}, LONG),
            () -> o.getInt((String[]) null),
            () -> o.has((String[]) null, LONG),
            () -> o.getString(new String[0]),
            () -> o.getLong(new String[] {null}),
        };
        for (int k = 0; k < calls.length; k++) {
            try {
                calls[k].run();
                throw new AssertionError("call " + k + ": not refused");
            } catch (IllegalArgumentException e) {
                // refused
            }
        }
        bergdb.nanotest.Assert.assertEquals(1, o.getInt(new String[] {"a"}));
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