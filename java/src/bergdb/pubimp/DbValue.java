package bergdb.pubimp;

/**
 * <p>This is the superclass of the seven DbObject types of format 2 (bergdb 020-07): boolean,
 * integer, double, string, byteArray, array, object. They are implemented in subclasses of
 * this class: DbBoolean, DbLong (the one integer, 64 bits), DbDouble, DbString, DbByteArray,
 * DbArray, and DbObject. No value is null (bergdb 020-02, section 4.1).</p>
 * 
 * <p>Each subclass writes its value in its stored encoding, its type byte included, with
 * write(), and read() reads any value of checked bytes by its type byte. Each gives its own
 * value: DbBoolean.toBoolean(), DbLong.toLong(), DbDouble.toDouble(),
 * DbString.toStringValue(), DbByteArray.getByteArray(). The conversions to other Java types
 * are DataObjects', by bergdb 020-09 (layer 2 of bergdb 020-02, section 5.1b).</p>
 * 
 * @author Frans Lundberg
 */
public abstract class DbValue {
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
}
