package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;

import bergdb.common.StringUtil;
import bergdb.core.DbConstants;
import bergdb.core.InternalDataException;
import bergdb.dag.Keys;

/**
 * The keys of the user indexes and the encodings of their levels: bergdb 020-10, sections 4.1
 * and 4.4 (the indexes of 2026.4). The reserved keys under the IKP are part of the stream's
 * format (bergdb 018-01, section 2). Static methods; nothing is cached but constants.
 *
 * <p><b>The keys</b> (020-10, section 4.1), ikeys under the IKP /#i/, made bkeys by
 * key-encoding.md's rule (each byte + 2, '/' as 1); G is the index's generation, above 0:</p>
 * <ul>
 * <li>/#i/didef/-NAME: the index's definition, a stored object of format 2
 *     (IndexDefinition);</li>
 * <li>bkey(/#i/dient/dNAME/) G8 LEVELS K: an entry, with an empty value; G8 is G as 8 bytes,
 *     big-endian; K is the bkey of the file part of the value's ikey, "-" and its name (first
 *     byte 0x2f, no byte below 2);</li>
 * <li>/#i/didel/dNAME/-G16: the marker of a deleted generation, until its cleanup ends; G16
 *     is G as 16 lowercase hexadecimal digits;</li>
 * <li>/#i/dii/: the definitions of format 1 (2026.3 and before), which a start refuses.</li>
 * </ul>
 *
 * <p><b>The levels</b> (020-10, section 4.4): each level's value is a byte string whose
 * unsigned lexicographic order is the values' order, and which no other value's string of
 * the level is a proper prefix of, so that the levels, then K, sort as tuples:</p>
 * <ul>
 * <li>long: 8 bytes, big-endian, of v + 2^63;</li>
 * <li>double, not NaN: x its bits; s = x if x &gt;= 0, else -(x AND 0x7fffffffffffffff); s as
 *     a long. So -0.0 and 0.0 are one key, -infinity the least, +infinity the greatest;</li>
 * <li>string and bytes, one encoding E of the bytes (a string's are its UTF-8): each byte 00
 *     written 01 01, each 01 written 01 02, every other byte as it is; then 00. A string's
 *     order is its code points', a bytes value's its unsigned bytes'; E' (E without its 00)
 *     of a prefix p is a prefix of E(v) exactly when v starts with p.</li>
 * </ul>
 *
 * <p>An index's name (020-10, section 3.1) is 1 to 255 UTF-8 bytes, without '/', whitespace
 * (Character.isWhitespace) or a lone surrogate.</p>
 *
 * @author Frans Lundberg
 */
final class IndexKeys {
    private IndexKeys() {}

    // ======== Types and limits ========

    /** The level types (020-10, section 3.1), as ObjectFormat.typeAt() gives their kinds. */
    static final char LONG = 'l';
    static final char DOUBLE = 'd';
    static final char STRING = 's';
    static final char BYTES = 'b';

    /** The four types, in the order of 020-10, section 3.1. */
    static final char[] TYPES = {LONG, DOUBLE, STRING, BYTES};

    /** The longest index name, in UTF-8 bytes (020-10, section 3.1). */
    static final int MAX_NAME = 255;

    /** The most bytes of an entry's levels; above it a value has no entry (020-10, 3.3). */
    static final int MAX_LEVEL_BYTES = 4096;

    /**
     * The type of a type string: "long", "double", "string" or "bytes".
     *
     * @throws IllegalArgumentException  If 'typeName' is another string, or null.
     */
    static char type(String typeName) {
        if (typeName != null) {
            switch (typeName) {
            case "long":
                return LONG;
            case "double":
                return DOUBLE;
            case "string":
                return STRING;
            case "bytes":
                return BYTES;
            default:
                break;
            }
        }
        throw new IllegalArgumentException("The type " + (typeName == null ? "null"
                : "\"" + typeName + "\"") + " is not a level's type; a level is of type "
                + "\"long\", \"double\", \"string\" or \"bytes\" (bergdb 020-10, section 3.1).");
    }

    /** The type string of a type. */
    static String typeName(char type) {
        switch (type) {
        case LONG:
            return "long";
        case DOUBLE:
            return "double";
        case STRING:
            return "string";
        case BYTES:
            return "bytes";
        default:
            throw new IllegalArgumentException("not a level's type: " + type);
        }
    }

    // ======== Names (020-10, section 3.1) ========

    /**
     * Why 'name' is not an index's name, or null if it is one: 1 to 255 UTF-8 bytes, without
     * '/', whitespace (Character.isWhitespace) or a lone surrogate (020-10, section 3.1).
     */
    static String nameFault(String name) {
        if (name == null) {
            return "null is not an index name";
        }
        if (StringUtil.hasLoneSurrogate(name)) {
            return "an index name has no lone surrogate, a char of U+D800 to U+DFFF that is "
                    + "not part of a surrogate pair";
        }
        for (int i = 0; i < name.length(); ) {
            int c = name.codePointAt(i);
            if (c == '/') {
                return "an index name has no '/'";
            }
            if (Character.isWhitespace(c)) {
                return "an index name has no whitespace (Character.isWhitespace), such as "
                        + "U+" + String.format("%04X", c);
            }
            i += Character.charCount(c);
        }
        int n = name.getBytes(StandardCharsets.UTF_8).length;
        if (n == 0 || n > MAX_NAME) {
            return "an index name has 1 to " + MAX_NAME + " UTF-8 bytes, not " + n;
        }
        return null;
    }

    /**
     * Checks an index's name (020-10, section 3.1).
     *
     * @throws IllegalArgumentException  If it is not one; the message says why.
     */
    static void checkName(String name) {
        String fault = nameFault(name);
        if (fault != null) {
            throw new IllegalArgumentException("Bad index name " + quote(name) + ": " + fault
                    + " (bergdb 020-10, section 3.1).");
        }
    }

    // ======== The keys (020-10, section 4.1) ========

    private static final String DEFINITIONS = DbConstants.INTERNAL_PREFIX + "didef/";
    private static final String ENTRIES = DbConstants.INTERNAL_PREFIX + "dient/";
    private static final String MARKERS = DbConstants.INTERNAL_PREFIX + "didel/";
    private static final String FORMAT_1 = DbConstants.INTERNAL_PREFIX + "dii/";

    private static final byte[] DEFINITIONS_BYTES = Keys.toBytes(DEFINITIONS);
    private static final byte[] DEFINITION_HEAD = Keys.toBytes(DEFINITIONS + "-");
    private static final byte[] ENTRIES_BYTES = Keys.toBytes(ENTRIES);
    private static final byte[] MARKERS_BYTES = Keys.toBytes(MARKERS);
    private static final byte[] MARKER_HEAD = Keys.toBytes(MARKERS + "d");
    private static final byte[] FORMAT_1_BYTES = Keys.toBytes(FORMAT_1);

    /** The bkey of '/', which ends a directory's name. */
    private static final int SLASH = 1;

    /** The bkey of '-', the first byte of a file's name, and of K. */
    private static final int FILE = '-' + 2;

    /**
     * The key of an index's definition: bkey(/#i/didef/-NAME).
     *
     * @throws IllegalArgumentException  If the name is not valid (020-10, section 3.1).
     */
    static byte[] definitionKey(String name) {
        checkName(name);
        return Keys.toBytes(DEFINITIONS + "-" + name);
    }

    /** The prefix of every definition's key: bkey(/#i/didef/). */
    static byte[] definitionsPrefix() {
        return DEFINITIONS_BYTES.clone();
    }

    /**
     * The index's name in a definition's key.
     *
     * @throws InternalDataException  If 'key' is not bkey(/#i/didef/-NAME) with a valid name.
     */
    static String nameOfDefinitionKey(byte[] key) {
        if (!startsWith(key, DEFINITION_HEAD)) {
            throw badKey("an index definition's key", key, "it does not start with "
                    + DEFINITIONS + "-");
        }
        String name = keyName(key, DEFINITION_HEAD.length, key.length);
        if (name == null || nameFault(name) != null) {
            throw badKey("an index definition's key", key, "no index name follows "
                    + DEFINITIONS + "- (" + (name == null ? "not UTF-8" : nameFault(name))
                    + ")");
        }
        return name;
    }

    /** The prefix of every entry's key: bkey(/#i/dient/). */
    static byte[] entriesPrefix() {
        return ENTRIES_BYTES.clone();
    }

    /**
     * The prefix of the entries of an index's generation: bkey(/#i/dient/dNAME/) and G8 (020-10,
     * section 4.1). No generation's prefix starts with another's: the name ends at '/', which
     * no name has, and G8 has 8 bytes.
     *
     * @throws IllegalArgumentException  If the name is not valid (3.1), or gen is not above 0.
     */
    static byte[] generationPrefix(String name, long gen) {
        checkName(name);
        checkGen(gen);
        byte[] dir = Keys.toBytes(ENTRIES + "d" + name + "/");
        byte[] b = Arrays.copyOf(dir, dir.length + 8);
        writeLongBE(b, dir.length, gen);
        return b;
    }

    /**
     * The marker of a deleted generation: bkey(/#i/didel/dNAME/-G16) (020-10, section 4.1).
     *
     * @throws IllegalArgumentException  If the name is not valid (3.1), or gen is not above 0.
     */
    static byte[] markerKey(String name, long gen) {
        checkName(name);
        checkGen(gen);
        return Keys.toBytes(MARKERS + "d" + name + "/-" + String.format("%016x", gen));
    }

    /** The prefix of every marker's key: bkey(/#i/didel/). */
    static byte[] markersPrefix() {
        return MARKERS_BYTES.clone();
    }

    /** The prefix of the definitions of format 1, which a start refuses: bkey(/#i/dii/). */
    static byte[] format1Prefix() {
        return FORMAT_1_BYTES.clone();
    }

    /** A marker's index name and generation. */
    static final class Marker {
        final String name;
        final long gen;

        Marker(String name, long gen) {
            this.name = name;
            this.gen = gen;
        }

        public String toString() {
            return "marker " + quote(name) + ", generation " + gen;
        }
    }

    /**
     * Parses a marker's key, bkey(/#i/didel/dNAME/-G16).
     *
     * @throws InternalDataException  If 'key' is not one: another prefix, a bad name, G16 not
     *      16 lowercase hexadecimal digits, or G not above 0.
     */
    static Marker parseMarker(byte[] key) {
        String what = "an index deletion's marker";
        if (!startsWith(key, MARKER_HEAD)) {
            throw badKey(what, key, "it does not start with " + MARKERS + "d");
        }
        int slash = indexOf(key, SLASH, MARKER_HEAD.length);
        if (slash < 0) {
            throw badKey(what, key, "no '/' after the name");
        }
        String name = keyName(key, MARKER_HEAD.length, slash);
        if (name == null || nameFault(name) != null) {
            throw badKey(what, key, "no index name after " + MARKERS + "d ("
                    + (name == null ? "not UTF-8" : nameFault(name)) + ")");
        }
        int g = slash + 1;
        if (key.length != g + 17 || (key[g] & 0xff) != FILE) {
            throw badKey(what, key, "the name is not followed by '/-' and 16 digits");
        }
        long gen = 0;
        for (int i = g + 1; i < key.length; i++) {
            int c = (key[i] & 0xff) - 2;
            int digit = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : -1;
            if (digit < 0) {
                throw badKey(what, key, "the generation is not 16 lowercase hexadecimal digits");
            }
            gen = gen << 4 | digit;
        }
        if (gen <= 0) {
            throw badKey(what, key, "the generation is not above 0");
        }
        return new Marker(name, gen);
    }

    /**
     * K of a value's ikey: the bkey of its file part, '-' and the name after the last '/'
     * (020-10, section 4.1). The value's directory is the ikey before it.
     *
     * @throws IllegalArgumentException  If 'ikey' has no file part: no '/', or no '-' after
     *      the last one.
     */
    static byte[] fileKey(String ikey) {
        int slash = ikey.lastIndexOf('/');
        if (slash < 0 || slash + 1 >= ikey.length() || ikey.charAt(slash + 1) != '-') {
            throw new IllegalArgumentException("Not the ikey of a value in a directory, "
                    + "with '/-' before its name: " + quote(ikey));
        }
        return Keys.toBytes(ikey.substring(slash + 1));
    }

    // ======== The levels (020-10, section 4.4) ========

    private static final long SIGN = 0x8000000000000000L;

    /** The greatest sort long of a double, +infinity's: its bits. */
    private static final long INFINITY_BITS = 0x7ff0000000000000L;

    /** A long's level: 8 bytes, big-endian, of v + 2^63. */
    static byte[] encodeLong(long v) {
        byte[] b = new byte[8];
        writeLong(b, 0, v);
        return b;
    }

    /** Writes a long's level, 8 bytes, at 'p'; returns p + 8. */
    static int writeLong(byte[] b, int p, long v) {
        writeLongBE(b, p, v ^ SIGN);
        return p + 8;
    }

    /** The long of a long's level at 'p'. */
    static long decodeLong(byte[] b, int p) {
        long u = 0;
        for (int i = 0; i < 8; i++) {
            u = u << 8 | (b[p + i] & 0xff);
        }
        return u ^ SIGN;
    }

    /**
     * A double's level: its sort long's (doubleSortLong) level. -0.0 and 0.0 have one.
     *
     * @throws IllegalArgumentException  If 'v' is NaN, which has no level (020-10, 3.3).
     */
    static byte[] encodeDouble(double v) {
        if (v != v) {
            throw new IllegalArgumentException("NaN has no index entry (bergdb 020-10, "
                    + "section 3.3).");
        }
        return encodeLong(doubleSortLong(Double.doubleToRawLongBits(v)));
    }

    /**
     * The sort long of a double's bits, which must not be a NaN: the bits if the sign is 0,
     * else minus the bits without the sign (020-10, section 4.4); so -0.0 is 0.
     */
    static long doubleSortLong(long bits) {
        return bits >= 0 ? bits : -(bits & ~SIGN);
    }

    /**
     * The double of a double's level at 'p'; 0.0 for -0.0's.
     *
     * @throws IllegalArgumentException  If the 8 bytes are no double's level (a NaN's).
     */
    static double decodeDouble(byte[] b, int p) {
        long s = decodeLong(b, p);
        if (s > INFINITY_BITS || s < -INFINITY_BITS) {
            throw new IllegalArgumentException("not the level of a double: its sort long 0x"
                    + Long.toHexString(s) + " is a NaN's");
        }
        return Double.longBitsToDouble(s >= 0 ? s : -s | SIGN);
    }

    /**
     * A string's level: E of its UTF-8.
     *
     * @throws IllegalArgumentException  If 's' has a lone surrogate (020-07, R11).
     */
    static byte[] encodeString(String s) {
        return encodeBytes(ObjectFormat.utf8(s));
    }

    /** A bytes value's level: E of its bytes. */
    static byte[] encodeBytes(byte[] v) {
        byte[] b = new byte[escapedLength(v, 0, v.length) + 1];
        int p = writeEscaped(b, 0, v, 0, v.length);
        b[p] = 0;
        return b;
    }

    /**
     * E' of a string prefix: E of its UTF-8 without the final 00; a prefix of the level of
     * every string that starts with it, by code points, and of no other.
     *
     * @throws IllegalArgumentException  If 'p' has a lone surrogate.
     */
    static byte[] encodeStringPrefix(String p) {
        return encodeBytesPrefix(ObjectFormat.utf8(p));
    }

    /** E' of a bytes prefix: E without the final 00. */
    static byte[] encodeBytesPrefix(byte[] p) {
        byte[] b = new byte[escapedLength(p, 0, p.length)];
        writeEscaped(b, 0, p, 0, p.length);
        return b;
    }

    /** The bytes of E' of [start, start + length) of 'v': E's without the final 00. */
    static int escapedLength(byte[] v, int start, int length) {
        int n = length;
        for (int i = start; i < start + length; i++) {
            if ((v[i] & 0xfe) == 0) {
                n++;
            }
        }
        return n;
    }

    /** Writes E' of [start, start + length) of 'v' at 'p' of 'b'; returns its end. */
    static int writeEscaped(byte[] b, int p, byte[] v, int start, int length) {
        for (int i = start; i < start + length; i++) {
            byte x = v[i];
            if ((x & 0xfe) == 0) {
                b[p++] = 1;
                b[p++] = (byte) (x + 1);
            } else {
                b[p++] = x;
            }
        }
        return p;
    }

    /**
     * The bytes of E' in [p, end) of 'b', escaped as E writes them: the value of an E level
     * without its final 00.
     *
     * @throws IllegalArgumentException  If [p, end) has a 00, or a 01 not followed by 01 or 02.
     */
    static byte[] decodeEscaped(byte[] b, int p, int end) {
        byte[] v = new byte[end - p];
        int n = 0;
        for (int i = p; i < end; i++) {
            int x = b[i] & 0xff;
            if (x == 0) {
                throw new IllegalArgumentException("a 00 inside an escaped value, at " + i);
            } else if (x == 1) {
                int y = i + 1 < end ? b[i + 1] & 0xff : -1;
                if (y != 1 && y != 2) {
                    throw new IllegalArgumentException("01 not followed by 01 or 02, at " + i);
                }
                v[n++] = (byte) (y - 1);
                i++;
            } else {
                v[n++] = (byte) x;
            }
        }
        return Arrays.copyOf(v, n);
    }

    /**
     * succ(x), the least byte string above every string that starts with x (020-10, section
     * 4.4): x without its trailing ff bytes, its last byte then + 1. Null if there is none (x
     * empty, or all ff): every string above x starts with it.
     */
    static byte[] succ(byte[] x) {
        int n = x.length;
        while (n > 0 && x[n - 1] == (byte) 0xff) {
            n--;
        }
        if (n == 0) {
            return null;
        }
        byte[] s = Arrays.copyOf(x, n);
        s[n - 1]++;
        return s;
    }

    // ======== Entries (020-10, sections 4.1 and 4.4) ========

    /** An entry's key: the generation's prefix, the levels, K. */
    static byte[] entryKey(byte[] generationPrefix, byte[] levels, byte[] k) {
        byte[] b = new byte[generationPrefix.length + levels.length + k.length];
        System.arraycopy(generationPrefix, 0, b, 0, generationPrefix.length);
        System.arraycopy(levels, 0, b, generationPrefix.length, levels.length);
        System.arraycopy(k, 0, b, generationPrefix.length + levels.length, k.length);
        return b;
    }

    /** An entry's key, parsed: where each level and K start. */
    static final class Entry {
        final byte[] key;
        private final char[] types;

        /** starts[i] is where level i starts; starts[n], where K starts. */
        private final int[] starts;

        private Entry(byte[] key, char[] types, int[] starts) {
            this.key = key;
            this.types = types;
            this.starts = starts;
        }

        int levelCount() {
            return types.length;
        }

        /** The levels, L_1 to L_n, as the index function makes them. */
        byte[] levels() {
            return Arrays.copyOfRange(key, starts[0], starts[types.length]);
        }

        /** K: the bkey of the value's file part, '-' and its name. */
        byte[] k() {
            return Arrays.copyOfRange(key, starts[types.length], key.length);
        }

        /** The file part of the value's ikey, '-' and its name. */
        String fileName() {
            return Keys.bkey2ikey(k());
        }

        /**
         * The value of level i: a Long, a Double (0.0 for -0.0), a String or a byte[].
         *
         * @throws InternalDataException  If the level is no value's: a double's 8 bytes that
         *      are a NaN's, or a string's bytes that are not well-formed UTF-8.
         */
        Object value(int i) {
            int p = starts[i];
            switch (types[i]) {
            case LONG:
                return decodeLong(key, p);
            case DOUBLE:
                try {
                    return decodeDouble(key, p);
                } catch (IllegalArgumentException e) {
                    throw badKey("an index entry", key, "level " + (i + 1) + ": "
                            + e.getMessage());
                }
            case STRING: {
                byte[] b = decodeEscaped(key, p, starts[i + 1] - 1);
                if (ObjectFormat.utf8Fault(b, 0, b.length) >= 0) {
                    throw badKey("an index entry", key, "level " + (i + 1) + ", a string, is "
                            + "not well-formed UTF-8");
                }
                return new String(b, StandardCharsets.UTF_8);
            }
            default:
                return decodeEscaped(key, p, starts[i + 1] - 1);
            }
        }
    }

    /**
     * Parses an entry's key from its start (020-10, section 4.4): the generation's prefix,
     * then each level by its type (8 bytes; or up to the 00 that ends E, every 01 followed by
     * 01 or 02), then K (not empty, its first byte 0x2f, no byte below 2, the bkey of an
     * ikey's file part: Keys.bkey2ikeyOrNull gives its ikey, so fileName() does not throw).
     *
     * @throws InternalDataException  If the key does not parse; the message names it.
     */
    static Entry parseEntry(byte[] key, byte[] generationPrefix, char[] types) {
        String what = "an index entry";
        if (!startsWith(key, generationPrefix)) {
            throw badKey(what, key, "it does not start with its generation's prefix "
                    + show(generationPrefix));
        }
        int[] starts = new int[types.length + 1];
        int p = generationPrefix.length;
        for (int i = 0; i < types.length; i++) {
            starts[i] = p;
            if (types[i] == LONG || types[i] == DOUBLE) {
                if (key.length - p < 8) {
                    throw badKey(what, key, "level " + (i + 1) + " has less than 8 bytes");
                }
                p += 8;
            } else {
                while (true) {
                    if (p >= key.length) {
                        throw badKey(what, key, "level " + (i + 1) + " is not ended by 00");
                    }
                    int x = key[p] & 0xff;
                    if (x == 0) {
                        p++;
                        break;
                    } else if (x == 1) {
                        int y = p + 1 < key.length ? key[p + 1] & 0xff : -1;
                        if (y != 1 && y != 2) {
                            throw badKey(what, key, "level " + (i + 1) + " has 01 not followed "
                                    + "by 01 or 02, at byte " + p);
                        }
                        p += 2;
                    } else {
                        p++;
                    }
                }
            }
        }
        starts[types.length] = p;
        if (p >= key.length) {
            throw badKey(what, key, "no K after the levels");
        }
        if ((key[p] & 0xff) != FILE) {
            throw badKey(what, key, "K does not start with 0x2f, '-'");
        }
        for (int i = p; i < key.length; i++) {
            if ((key[i] & 0xff) < 2) {
                throw badKey(what, key, "K has a byte below 2, at byte " + i);
            }
        }
        if (Keys.bkey2ikeyOrNull(Arrays.copyOfRange(key, p, key.length)) == null) {
            // Else fileName() throws IllegalArgumentException in a scan (bergdb 020-16, F16-1).
            throw badKey(what, key, "K is no ikey's bkey: it has the byte 0x31, or its bytes "
                    + "less 2 are not well-formed UTF-8");
        }
        return new Entry(key, types.clone(), starts);
    }

    // ======== Helpers ========

    private static void checkGen(long gen) {
        if (gen <= 0) {
            throw new IllegalArgumentException("An index's generation is above 0, not " + gen
                    + " (bergdb 020-10, section 4.3).");
        }
    }

    /**
     * The name in [start, end) of a bkey, its bytes - 2, or null if a byte is below 2 (00, or
     * 01 for '/') or the bytes are not well-formed UTF-8.
     */
    private static String keyName(byte[] key, int start, int end) {
        byte[] b = new byte[end - start];
        for (int i = start; i < end; i++) {
            int x = key[i] & 0xff;
            if (x < 2) {
                return null;
            }
            b[i - start] = (byte) (x - 2);
        }
        if (ObjectFormat.utf8Fault(b, 0, b.length) >= 0) {
            return null;
        }
        return new String(b, StandardCharsets.UTF_8);
    }

    private static int indexOf(byte[] b, int x, int from) {
        for (int i = from; i < b.length; i++) {
            if ((b[i] & 0xff) == x) {
                return i;
            }
        }
        return -1;
    }

    private static void writeLongBE(byte[] b, int p, long v) {
        for (int i = 0; i < 8; i++) {
            b[p + i] = (byte) (v >>> (56 - 8 * i));
        }
    }

    static boolean startsWith(byte[] b, byte[] prefix) {
        return b.length >= prefix.length
                && Arrays.equals(b, 0, prefix.length, prefix, 0, prefix.length);
    }

    /** A key in a message: its bytes in hexadecimal, and as an ikey would show it. */
    static String show(byte[] key) {
        return StringUtil.toHex(key) + " (" + Keys.toDisplayString(key) + ")";
    }

    static String quote(String s) {
        return s == null ? "null" : "\"" + s + "\"";
    }

    private static InternalDataException badKey(String what, byte[] key, String why) {
        return new InternalDataException("The key " + show(key) + " is not " + what + ": "
                + why + " (bergdb 020-10, section 4).");
    }
}
