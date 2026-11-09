package bergdb.pub;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pubimp.ObjectFormat;

/**
 * <p>A value in a stored object: a field's value or an array's element, of one of the seven
 * types of the stored object format (bergdb 020-07), each a final class of this package:
 * DbBoolean, DbLong (the one integer, 64 bits), DbDouble, DbString, DbByteArray, DbArray
 * and DbObject. getType() gives its type char, one of DbObject's BOOLEAN to OBJECT. No value
 * is null (bergdb 020-02, section 4.1).</p>
 * 
 * <p>Each class gives its own value: DbBoolean.toBoolean(), DbLong.toLong(),
 * DbDouble.toDouble(), DbString.toStringValue(), DbByteArray.getByteArray(); DbArray its
 * elements, DbObject its fields. A value is immutable and may be read by any number of
 * threads at the same time. No class outside this package extends DbValue (its constructor
 * is not public, and BergDB's jars seal the package), so every value is one of the seven,
 * and writes only bytes that a reader of the format takes. getByteSize() and write() give its encoding in the format, its type
 * byte included (bergdb 020-07, section 4).</p>
 * 
 * @author Frans Lundberg
 */
public abstract class DbValue {
    private final char type;
    
    /** For the value classes of this package only: no other writes stored bytes. */
    DbValue(char type) {
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
    
    /**
     * The value's type char: one of DbObject's BOOLEAN, LONG, DOUBLE, STRING, BYTE_ARRAY,
     * ARRAY and OBJECT.
     *
     * @return The type char.
     */
    public char getType() {
        return type;
    }
    
    /**
     * Returns the size of the value's encoding in the stored object format, its type byte
     * included (bergdb 020-07, section 4): the bytes that write() writes.
     *
     * @return The size in bytes.
     */
    public abstract int getByteSize();
    
    /**
     * Writes the value's encoding, getByteSize() bytes, into 'b' at 'offset'.
     *
     * @param b  The array to write into.
     * @param offset  Where the encoding starts in 'b'.
     * @return The offset after the encoding: offset + getByteSize().
     * @throws IndexOutOfBoundsException  If 'b' has fewer than getByteSize() bytes from
     *      'offset'.
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
    
    /**
     * A short tag of the value, for a log or a debugger, not the value in full: "o" for an
     * object, whatever its fields; "a:" and the size for an array, "a:2"; "b:" and the
     * length for bytes; "d:" and the number for a double; the value for a boolean, an
     * integer and a string (bergdb 020-24-05, U5-10). The value classes do not override
     * equals() and hashCode(): see DbObject, "The bytes".
     */
    public String toString() {
        return String.valueOf(type);
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
     * A value that has no stored form, refused by the Builder or a value class (bergdb
     * 021-04; 020-07, section 6.1): a lone surrogate in a string or a field's name, a field's
     * name of more than 255 bytes. A put of a Data Object refuses them first, naming the
     * place (DataObjects).
     */
    static final class PathException extends IllegalArgumentException {
        private static final long serialVersionUID = 1L;
        
        private PathException(String message) {
            super(message);
        }
        
        /** A string or a field's name ('what') with a lone surrogate (bergdb 021-04). */
        static PathException loneSurrogate(String what) {
            return new PathException("A " + what + " has a lone surrogate, a char of U+D800 to "
                    + "U+DFFF that is not part of a surrogate pair. BergDB stores every string "
                    + "as well-formed UTF-8, which cannot hold one (bergdb 021-04); store such "
                    + "data as a byte[] or a char[].");
        }
        
        /** A field's name of 'size' bytes in UTF-8, more than 255 (bergdb 020-07, R6). */
        static PathException longName(int size) {
            return new PathException("A field name has " + size + " bytes in UTF-8; a name has "
                    + "1 to " + ObjectFormat.MAX_NAME + " bytes (bergdb 020-07, R6).");
        }
    }

    // ======== Tests ========

    /** A value of 'size' bytes that is never written: the size checks come first. */
    private static DbValue sized(final int size) {
        return new DbValue('b') {
            public int getByteSize() {
                return size;
            }

            public int write(byte[] b, int offset) {
                throw new AssertionError("written");
            }
        };
    }

    /** r throws IllegalArgumentException whose message has 'part'. */
    private static void assertArgRefused(String what, String part, Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(what + ": " + e.getMessage(), e.getMessage().contains(part));
            return;
        }
        throw new AssertionError(what + ": not refused");
    }

    /**
     * 020-07, R15 (020-09, section 4.7, item 7): a value too large for a stored value is
     * refused with IllegalArgumentException "size", before anything is allocated; an int
     * size overflowed, and the Builders gave an OutOfMemoryError or a
     * NegativeArraySizeException. (From DbObjectFormatTester, bergdb 020-10, B3: a value of
     * a size of its own needs DbValue's constructor, this package's.)
     */
    @Nano
    private static void testSizesRefused() {
        int big = Integer.MAX_VALUE - 3;
        assertArgRefused("an element of 2^31 - 4 bytes", "size:",
                () -> new DbArray.Builder().add(sized(big)));
        assertArgRefused("a field of 2^31 - 4 bytes", "size:",
                () -> new DbObject.Builder().addDbValue("v", sized(big)).build());
        final DbObject.Builder two = new DbObject.Builder().addDbValue("a", sized(1 << 30))
                .addDbValue("b", sized(1 << 30));
        assertArgRefused("two fields of 2^30 bytes", "size:", () -> two.build());
        assertArgRefused("a field near Java's largest array", "size:",
                () -> new DbObject.Builder().addDbValue("v", sized(Integer.MAX_VALUE - 12))
                .build());
        ObjectFormat.checkValueSize(ObjectFormat.MAX_VALUE);
        assertArgRefused("a value above MAX_VALUE", "size:",
                () -> ObjectFormat.checkValueSize(ObjectFormat.MAX_VALUE + 1L));
        assertArgRefused("a bytes value of 2^31 - 5 bytes", "size:",
                () -> ObjectFormat.checkValueSize(5L + Integer.MAX_VALUE - 5));
    }
}
