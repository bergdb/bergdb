package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import bergdb.common.StringUtil;
import bergdb.pub.util.BadFormatException;

/**
 * <p>An immutable object with a map of named and typed fields.
 * The fields are typed, but the object itself has no particular schema.
 * The set of fields can vary independently between any two DbObjects.
 * The word "field" is not used as the actual Java class fields, but for the conceptual
 * fields that this object contain. The set of types available for a DbObject field does 
 * not correspond directly to Java types, but is a separate small type system with 
 * 7 distinct types, Binson's.
 * </p>
 *
 * <p>Experimental in 2026.3, with known faults; it may change in a later release (bergdb
 * 018-01, D6).</p>
 * 
 * <p>The DbObject types with their one-character representation, name, and descriptions:</p>
 * 
 * <pre>
 * n - boolean    A type that has a value of either true or false.
 * l - integer    A signed 64-bit integer, the one integer type: Java's byte, short, char,
 *                int and long are each stored as an integer, in the fewest bytes.
 * d - double     A 64-bit floating pointer number (IEEE-754); every NaN is one value.
 * s - string     A string stored as well-formed UTF-8.
 * b - byteArray  An array of bytes.
 * a - array      A heterogeneous array (list) of values. See class DbArray.
 * o - object     A nested DbObject.
 * z - absent     Not a type: getType() of a field that the object does not have.
 * </pre>
 * 
 * <p>INT, 'i', is not a stored type: has(name, INT) is true, and getInt() gives the value,
 * for an integer within int's range (bergdb 020-08, section 3).</p>
 * 
 * <p>No value is null (bergdb 020-02, section 4.1): a field without a value is absent, an
 * array has no absent element, and toDbObject() leaves a null field out. The bytes are format
 * 2 of stored objects, bergdb 020-07: the header byte 0x82, then the object, its fields
 * found by a binary search on their names; names of 1 to 255 bytes; at most 16 levels of
 * objects and arrays.</p>
 *
 * <p>Strings. A string, and a field's name, is Unicode text: a sequence of Unicode scalar
 * values, stored as well-formed UTF-8 (RFC 3629), as every string BergDB stores, keys and
 * values too (the Pub API's package bergdb.pub, "Strings"; bergdb 021-04). A Java String
 * with a lone surrogate, a char of U+D800 to U+DFFF that is not part of a surrogate pair,
 * cannot be stored so: toDbObject(), the Builder and DbString refuse it with
 * IllegalArgumentException, whose message names the field and an array element's index
 * ("inner.names[3]"). A char[] field keeps any chars, as an array of ints, and reads back
 * exactly; a byte[] field keeps any bytes.</p>
 * 
 * <p>A DbObject is held in memory as its stored bytes, checked by every rule of the format
 * when it is made from bytes, and read by lookups. getBytes() gives the stored bytes, and
 * new DbObject(bytes) reads them back.</p>
 * 
 * <p>A DbObject can be created from a Data Object with the method toDbObject(), and
 * toJavaObject() converts a DbObject to a Data Object: bergdb 020-09's rules, layer 2 of
 * bergdb 020-02, section 5.1b, over this class, layer 1.</p>
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
    
    /** The header of a stored object, format 2: its first byte (bergdb 020-07, R1). */
    public static final byte HEADER = (byte) ObjectFormat.HEADER;
    
    public static final char BOOLEAN = 'n';
    
    /** Not a stored type: an integer within int's range, for has() (bergdb 020-08, section 3). */
    public static final char INT = 'i';
    
    /** The integer, 64 bits; getType() of every integer. */
    public static final char LONG = 'l';
    public static final char DOUBLE = 'd';
    public static final char STRING = 's';
    public static final char BYTE_ARRAY = 'b';
    public static final char ARRAY = 'a';
    public static final char OBJECT = 'o';
    
    
    private final byte[] bytes;     // the stored value, header first; or a parent's bytes
    private final int start;        // the object's type byte in 'bytes'
    private final int end;          // after its last field
    private final boolean whole;    // 'bytes' is the stored value of this object
    private int height;             // its levels, 1 or more; 0 until computed
    
    /**
     * Creates a new DbObject based in its byte array representation: a stored object of
     * format 2, checked by every rule (bergdb 020-07, section 7.1).
     * 
     * @param b 
     *      The serialized format of the DbObject. 
     *      Will be copied. 
     * @throws BadFormatException 
     *      If the bytes are not a stored object of format 2; the message starts with the
     *      condition's code (bergdb 020-07, section 7.2), "format-1" for an object of
     *      BergDB 2026.3 and before.
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
     * Returns the stored bytes, the header first. For an object made from bytes or by the
     * Builder, a reference to the internal byte buffer: no value copy is made, and the
     * returned reference must not be used to modify the array. For an object nested in
     * another, a new array.
     */
    public byte[] getBytes() {
        if (whole) {
            return this.bytes;
        }
        byte[] b = new byte[1 + end - start];
        b[0] = HEADER;
        System.arraycopy(bytes, start, b, 1, end - start);
        return b;
    }
    
    /**
     * Returns the number of fields of the typeless object.
     */
    public int getFieldCount() {
        return ObjectFormat.countAt(bytes, start);
    }
    
    /**
     * Returns true iff the typeless object has a field with the given name and type. For
     * INT, a field of an integer within int's range.
     */
    public boolean has(String name, char type) {
        return is(find(name), type);
    }
    
    /**
     * Returns true iff the typeless object has a nested field with the 
     * given name parts and the given type.
     */
    public boolean has(String[] nameParts, char type) {
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
        return DataObjects.toJavaObject(this, c);
    }
    
    /** The bytes of the object this one is in, for DataObjects; they must not change. */
    byte[] bytesInternal() {
        return bytes;
    }
    
    /** The object's type byte in bytesInternal(). */
    int startInternal() {
        return start;
    }
    
    /** The end of the object in bytesInternal(). */
    int endInternal() {
        return end;
    }
    
    /**
     * Gets the type of a field, or returns 'z' (think 'zero', nothing) if there is no such
     * field: absent. 'l' for every integer.
     */
    public char getType(String name) {
        int p = find(name);
        return p < 0 ? 'z' : ObjectFormat.typeAt(bytes, p);
    }
    
    /**
     * Returns the DbValue of a field with a specified name, or null if absent.
     */
    public DbValue getDbValue(String name) {
        int p = find(name);
        return p < 0 ? null : DbValue.read(bytes, p);
    }
    
    
    // ======== getType(name) methods ========
    //
    // Each gives the value of a field of its type: 0, false or null if the field is absent
    // or of another type.
    
    public boolean getBoolean(String name) {
        int p = find(name);
        return is(p, BOOLEAN) && ObjectFormat.booleanAt(bytes, p);
    }
    
    /** An integer within int's range; 0 for another value. */
    public int getInt(String name) {
        int p = find(name);
        return is(p, INT) ? (int) ObjectFormat.integerAt(bytes, p) : 0;
    }
    
    public int getInt(String[] nameParts) {
        if (nameParts.length == 1) {
            return getInt(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, INT) ? (int) ObjectFormat.integerAt(bytes, p) : 0;
    }

    public long getLong(String name) {
        int p = find(name);
        return is(p, LONG) ? ObjectFormat.integerAt(bytes, p) : 0;
    }
    
    public long getLong(String[] nameParts) {
        if (nameParts.length == 1) {
            return getLong(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, LONG) ? ObjectFormat.integerAt(bytes, p) : 0;
    }
    
    public double getDouble(String name) {
        int p = find(name);
        return is(p, DOUBLE) ? Double.longBitsToDouble(ObjectFormat.doubleBitsAt(bytes, p)) 
                : 0.0;
    }
    
    public double getDouble(String[] nameParts) {
        if (nameParts.length == 1) {
            return getDouble(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, DOUBLE) ? Double.longBitsToDouble(ObjectFormat.doubleBitsAt(bytes, p)) 
                : 0.0;
    }

    public String getString(String name) {
        int p = find(name);
        return is(p, STRING) ? ObjectFormat.stringAt(bytes, p) : null;
    }
    
    public String getString(String[] nameParts) {
        if (nameParts.length == 1) {
            return getString(nameParts[0]);
        }
        int p = find(nameParts);
        return is(p, STRING) ? ObjectFormat.stringAt(bytes, p) : null;
    }
    
    public byte[] getByteArray(String name) {
        int p = find(name);
        return is(p, BYTE_ARRAY) ? ObjectFormat.bytesAt(bytes, p) : null;
    }
    
    public DbArray getArray(String name) {
        int p = find(name);
        return is(p, ARRAY) ? DbArray.read(bytes, p) : null;
    }
    
    public DbObject getObject(String name) {
        int p = find(name);
        return is(p, OBJECT) ? view(bytes, p) : null;
    }
    
    // ====
    
    /** The bytes of the object, without the header: its type byte, count, ends, fields. */
    public int getByteSize() {
        return end - start;
    }
    
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
            if (PubKeys.hasLoneSurrogate(name)) {
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
     * A builder object used to create a DbObject.
     */
    public static class Builder {
        private final ArrayList<DbField> fields = new ArrayList<DbField>();
        private final HashMap<String, Integer> indexes = new HashMap<String, Integer>();
        
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
        
        public Builder addDbValue(String name, DbValue value) {
            addField(new DbField(name, value));
            return this;
        }
        
        /** Adds an integer: format 2 has one integer type, 'l' (bergdb 020-07, R9). */
        public Builder addInt(String name, int value) {
            addField(new DbField(name, new DbLong(value)));
            return this;
        }
        
        public Builder addLong(String name, long value) {
            addField(new DbField(name, new DbLong(value)));
            return this;
        }

        public Builder addString(String name, String value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed (bergdb 021-07)");
            }
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
         * Builds a DbObject with its fields in order sorted by their names' unsigned bytes:
         * a stored object of format 2 (bergdb 020-07, sections 4 to 6), written bottom up,
         * each nested value copied in (bergdb 020-08, section 4.4).
         * 
         * @throws IllegalArgumentException  If the object would have more than 16 levels of
         *      objects and arrays, or more than 2^31 - 1 bytes (bergdb 020-07, R14, R15).
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