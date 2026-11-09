package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;

import bergdb.common.StringUtil;
import bergdb.pub.util.BadFormatException;

/**
 * The bytes of a stored object, format 2: the codec of bergdb 020-07 ("Stored objects, format
 * 2: the spec"), as Frans decided the format on 2026-11-08 (bergdb 020-02, section 4).
 *
 * <p>A stored object is the header byte 0x82 and an object. An object is a type byte (0x48,
 * 0x49 or 0x4a) that gives the width w of its numbers (1, 2 or 4 bytes), the count of its
 * fields in w bytes, the end of each field in w bytes, and the fields in the order of their
 * names' unsigned bytes; a field is a name length L (1 to 255), L bytes of well-formed UTF-8
 * and a value. Every value but the object is Binson's (BINSON-SPEC-1.1): integers of 1, 2, 4
 * and 8 bytes, strings, bytes, booleans, doubles and arrays (0x42, the elements, 0x43). A
 * nested object has the same framing and no header. One object has one byte string: every
 * width, integer and length in the fewest bytes, one NaN (020-07, sections 4 and 5).</p>
 *
 * <p>Static methods on byte arrays, with no allocation but for their results:</p>
 * <ul>
 * <li>the full check, checkStored(): every rule of 020-07, section 5, each limit checked
 *     before the reader recurses or reads for it (section 7.1); a refusal is a
 *     BadFormatException whose message starts with the condition's code of 020-07, section
 *     7.2, as "past-end: ...", and no other exception leaves it;</li>
 * <li>the lookup, find(): the binary search of 020-07, section 8.2, checking what it touches
 *     (section 7.4);</li>
 * <li>the readers of checked bytes: typeAt(), integerAt(), stringAt(), the object's head and
 *     fields, valueEnd();</li>
 * <li>the writer's encodings and checks: writeInteger(), writeDouble(), frame() and more,
 *     refusing with IllegalArgumentException, whose message starts with the condition's code,
 *     what has no stored form (020-07, section 6.1). The writer adds the place.</li>
 * </ul>
 *
 * <p>Levels (020-07, R14): the top object is level 1, a container that is a field's value or
 * an array's element is its parent's level + 1, and a scalar has no level; no level is above
 * MAX_LEVELS (Frans, 2026-11-08, 19:43: a scalar is not a level).</p>
 *
 * @author Frans Lundberg
 */
final class ObjectFormat {
    private ObjectFormat() {}

    /** The header of format 2, before the top object (020-07, section 9). */
    static final int HEADER = 0x82;

    // The type bytes (020-07, section 4.3).
    static final int INT8 = 0x10;
    static final int INT16 = 0x11;
    static final int INT32 = 0x12;
    static final int INT64 = 0x13;
    static final int STRING1 = 0x14;
    static final int STRING2 = 0x15;
    static final int STRING4 = 0x16;
    static final int BYTES1 = 0x18;
    static final int BYTES2 = 0x19;
    static final int BYTES4 = 0x1a;
    static final int ARRAY_START = 0x42;
    static final int ARRAY_END = 0x43;
    static final int TRUE = 0x44;
    static final int FALSE = 0x45;
    static final int DOUBLE = 0x46;
    static final int OBJECT1 = 0x48;
    static final int OBJECT2 = 0x49;
    static final int OBJECT4 = 0x4a;

    /** The most fields of an object (020-07, R3). */
    static final int MAX_FIELDS = 32767;

    /** The most levels: the top object 1, and objects and arrays below it (020-07, R14). */
    static final int MAX_LEVELS = 16;

    /** The longest name, in bytes (020-07, R6). */
    static final int MAX_NAME = 255;

    /** The largest stored value, header included: 2^31 - 1 bytes (020-07, R15). */
    static final long MAX_STORED = Integer.MAX_VALUE;

    /**
     * The largest value in a stored object: MAX_STORED less the smallest object that holds
     * one field, its header, type byte, count and end of 4 bytes, and a name of 1 byte.
     */
    static final long MAX_VALUE = MAX_STORED - 12;

    /**
     * The largest stored value Java can hold in one array, below R15's limit: an array of
     * more than this many bytes may not be allocated (Java's soft maximum array length).
     */
    static final int MAX_ARRAY = Integer.MAX_VALUE - 8;

    /** The one NaN (020-07, R12). */
    static final long NAN = 0x7ff8000000000000L;

    /** The bytes of a double: its type byte and 8 bytes. */
    static final int DOUBLE_SIZE = 9;

    /** The first bytes of format 1, BergDB 2026.3's and before (020-07, section 9). */
    private static final byte[] FORMAT_1 = {'b', 'e', 'r', 'g', 'o'};

    private static final long EXPONENT = 0x7ff0000000000000L;
    private static final long FRACTION = 0x000fffffffffffffL;

    // ======== Format 1, BergDB 2026.3's (020-08, section 3) ========

    /** Format 1's type bytes: boolean, int, long, double, string, bytes, array, object. */
    private static final String FORMAT_1_TYPES = "nildsbao";

    /**
     * True if 'b' is a whole object of format 1, BergDB 2026.3's and before, by its structure,
     * as 2026.3's writer wrote it (DbObject.Builder at release-2026.3; 020-07, section 9),
     * each field checked as its reader checked it. It is "bergo", the version 1 and a field
     * count n, a little-endian short: -1 (a null object) or 0 with nothing after it, or 1 to
     * 32,767 and a table of n entries of 6 bytes (a hash of the name, not checked, and the
     * field's offset, an int) and the n fields in order, the first right after the table and
     * the last ending at the end of 'b'. A field is a type byte of FORMAT_1_TYPES, the name's
     * size (a short, at least 1), the name, and a value that fills the field: a boolean 1
     * byte, 0 or 1; an int 4; a long and a double 8; a string, bytes and an object a size
     * (an int) and that many bytes, or -1 and nothing (null), an object's starting with
     * "bergo" and the version 1; an array ends with 'z' or 'Z'. A nested object's and an
     * array's elements are not checked: no recursion, so no depth to bound.
     *
     * <p>The stored value has no type of its own, so this is a guess (bergdb 020-08, section
     * 3): a value that only starts with "bergo" and the version 1, such as the String "bergo"
     * + U+0001 + " text", is not taken for format 1, but one whose bytes happen to be a whole
     * object of it, such as "bergo" + U+0001 + U+0000 + U+0000, is.</p>
     */
    static boolean isFormat1(byte[] b) {
        if (b.length < 8 || !startsWith(b, FORMAT_1) || b[5] != 1) {
            return false;
        }
        int n = (int) signed(b, 6, 2);
        if (n <= 0) {
            return n >= -1 && b.length == 8;
        }
        int at = 8 + 6 * n;
        if (b.length < at) {
            return false;
        }
        for (int i = 0; i < n; i++) {
            int offset = (int) signed(b, 8 + 6 * i + 2, 4);
            int end = i + 1 < n ? (int) signed(b, 8 + 6 * (i + 1) + 2, 4) : b.length;
            if (offset != at || end <= offset || end > b.length 
                    || !isFormat1Field(b, offset, end)) {
                return false;
            }
            at = end;
        }
        return true;
    }

    /** True if b[p..end) is a field of format 1, by isFormat1()'s rules. */
    private static boolean isFormat1Field(byte[] b, int p, int end) {
        if (end - p < 4 || FORMAT_1_TYPES.indexOf(b[p] & 0xff) < 0) {
            return false;
        }
        int nameSize = (int) signed(b, p + 1, 2);
        if (nameSize < 1 || nameSize > end - p - 4) {
            return false;
        }
        int v = p + 3 + nameSize;
        int size = end - v;
        switch (b[p]) {
        case 'n':
            return size == 1 && (b[v] == 0 || b[v] == 1);
        case 'i':
            return size == 4;
        case 'l':
        case 'd':
            return size == 8;
        case 'a':
            return b[end - 1] == 'z' || b[end - 1] == 'Z';
        default:        // 's', 'b', 'o': a size and its bytes, or -1 for null
            if (size < 4) {
                return false;
            }
            long length = signed(b, v, 4);
            if (length == -1) {
                return size == 4;
            }
            return length == size - 4 && (b[p] != 'o' || (length >= 8 
                    && Arrays.equals(b, v + 4, v + 9, FORMAT_1, 0, 5) && b[v + 9] == 1));
        }
    }

    // ======== The full check (020-07, section 7.1) ========

    /**
     * The full check of a stored value: every rule of 020-07, section 5. It recurses at most
     * MAX_LEVELS deep, checks each count before the table and each end and length before the
     * bytes it gives, and allocates nothing. (A Java array is never above R15's limit.)
     *
     * @throws BadFormatException  If 'b' is not a stored object of format 2. The message
     *      starts with the condition's code (020-07, section 7.2), "format-1" for an object
     *      of BergDB 2026.3 and before, and says where.
     */
    static void checkStored(byte[] b) {
        if (b.length == 0) {
            throw bad("past-end", "no bytes, not even the header");
        }
        int first = b[0] & 0xff;
        if (first != HEADER) {
            if (startsWith(b, FORMAT_1)) {
                throw bad("format-1", "the object is in format 1, written by BergDB 2026.3 or "
                        + "before, which this version does not read (bergdb 020-02, section 4.11)");
            } else if (first > HEADER && first <= 0xbf) {
                throw bad("header", "a stored object of format " + (first - 0x80)
                        + ", which this version does not read; it reads format 2");
            }
            throw bad("header", "the first byte is " + hex(first) + ", not the header "
                    + hex(HEADER));
        }
        if (b.length < 2) {
            throw bad("past-end", "no object after the header");
        }
        if (!isObjectType(b[1] & 0xff)) {
            throw bad("type", "the top value starts with " + hex(b[1] & 0xff)
                    + ", not an object");
        }
        int end = checkObject(b, 1, b.length, 1);
        if (end != b.length) {
            throw bad("trailing", (b.length - end) + " bytes after the top object, from byte "
                    + end);
        }
    }

    /** The full check, true or false: whether 'b' is a stored object of format 2. */
    static boolean isStoredObject(byte[] b) {
        try {
            checkStored(b);
            return true;
        } catch (BadFormatException e) {
            return false;
        }
    }

    /**
     * The full check of the value at 'p', which must lie in [p, limit), in a container at
     * 'level' (0 for none): its type, its bytes, its nested values and their levels. Reads
     * nothing outside [p, limit).
     *
     * @return  The value's end.
     * @throws BadFormatException  If the value breaks a rule of 020-07, section 5.
     */
    static int checkValue(byte[] b, int p, int limit, int level) {
        if (p >= limit) {
            throw bad("past-end", "a value expected at byte " + p + ", at the end of its extent");
        }
        int t = b[p] & 0xff;
        switch (t) {
        case INT8: case INT16: case INT32: case INT64: {
            int size = 1 << (t - INT8);
            if (size > limit - p - 1) {
                throw bad("past-end", "the integer at byte " + p + " ends past its extent");
            }
            long v = signed(b, p + 1, size);
            if (integerSize(v) != 1 + size) {
                throw bad("integer-size", "the integer " + v + " at byte " + p + " is in "
                        + size + " bytes, not the fewest");
            }
            return p + 1 + size;
        }
        case STRING1: case STRING2: case STRING4: case BYTES1: case BYTES2: case BYTES4: {
            int size = 1 << (t & 3);
            String what = t <= STRING4 ? "the string" : "the bytes";
            if (size > limit - p - 1) {
                throw bad("past-end", "the length of " + what + " at byte " + p
                        + " ends past its extent");
            }
            long length = signed(b, p + 1, size);
            if (length < 0) {
                throw bad("length", "the length of " + what + " at byte " + p + " is " + length);
            }
            if (lengthSize((int) length) != 1 + size) {
                throw bad("integer-size", "the length of " + what + " at byte " + p + ", "
                        + length + ", is in " + size + " bytes, not the fewest");
            }
            int start = p + 1 + size;
            if (length > limit - start) {
                throw bad("past-end", what + " at byte " + p + ", " + length
                        + " bytes, end past the extent");
            }
            if (t <= STRING4) {
                int fault = utf8Fault(b, start, (int) length);
                if (fault >= 0) {
                    throw bad("utf8", "the string at byte " + p
                            + " is not well-formed UTF-8, at byte " + fault);
                }
            }
            return start + (int) length;
        }
        case TRUE: case FALSE:
            return p + 1;
        case DOUBLE: {
            if (8 > limit - p - 1) {
                throw bad("past-end", "the double at byte " + p + " ends past its extent");
            }
            long bits = signed(b, p + 1, 8);
            if (isNaN(bits) && bits != NAN) {
                throw bad("nan", "the double at byte " + p + " is the NaN 0x"
                        + Long.toHexString(bits) + ", not the one NaN 0x7ff8000000000000");
            }
            return p + DOUBLE_SIZE;
        }
        case ARRAY_START: {
            if (level >= MAX_LEVELS) {
                throw bad("depth", "the array at byte " + p + " is at level " + (level + 1)
                        + ", above " + MAX_LEVELS);
            }
            int q = p + 1;
            while (true) {
                if (q >= limit) {
                    throw bad("past-end", "the array at byte " + p + " is not ended in its "
                            + "extent");
                }
                if ((b[q] & 0xff) == ARRAY_END) {
                    return q + 1;
                }
                q = checkValue(b, q, limit, level + 1);
            }
        }
        case OBJECT1: case OBJECT2: case OBJECT4:
            if (level >= MAX_LEVELS) {
                throw bad("depth", "the object at byte " + p + " is at level " + (level + 1)
                        + ", above " + MAX_LEVELS);
            }
            return checkObject(b, p, limit, level + 1);
        default:
            throw bad("type", "the byte " + hex(t) + " at byte " + p + " is not a type byte");
        }
    }

    /** The full check of the object at 'p' in [p, limit), at 'level'; returns its end. */
    private static int checkObject(byte[] b, int p, int limit, int level) {
        int w = 1 << ((b[p] & 0xff) - OBJECT1);
        if (w > limit - p - 1) {
            throw bad("past-end", "the count of the object at byte " + p
                    + " ends past its extent");
        }
        long count = unsigned(b, p + 1, w);
        if (count > MAX_FIELDS) {
            throw bad("fields", "the object at byte " + p + " has " + count
                    + " fields, more than " + MAX_FIELDS);
        }
        int n = (int) count;
        int table = p + 1 + w;
        if (n * w > limit - table) {
            throw bad("past-end", "the table of the object at byte " + p
                    + " ends past its extent");
        }
        int f0 = table + n * w;
        long size = n == 0 ? 0 : unsigned(b, f0 - w, w);
        if (size > limit - f0) {
            throw bad("past-end", "the fields of the object at byte " + p + ", " + size
                    + " bytes, end past its extent");
        }
        if (width(size) != w) {
            throw bad("width", "the object at byte " + p + " has numbers of " + w
                    + " bytes for fields of " + size + " bytes, not the smallest width");
        }

        int previousEnd = 0;
        int previousName = -1;
        int previousLength = 0;
        for (int i = 0; i < n; i++) {
            long end = unsigned(b, table + i * w, w);
            if (end <= previousEnd || end > size) {
                throw bad("ends", "the end of field " + i + " of the object at byte " + p
                        + ", " + end + ", does not lie after the end before it, "
                        + previousEnd + ", and up to the last end, " + size);
            }
            int fe = f0 + (int) end;
            int f = f0 + previousEnd;
            int length = b[f] & 0xff;
            if (length == 0) {
                throw bad("name-length", "the name of field " + i + " of the object at byte "
                        + p + " has 0 bytes");
            }
            int name = f + 1;
            if (length > fe - name) {
                throw bad("past-end", "the name of field " + i + " of the object at byte " + p
                        + " ends past its field");
            }
            int fault = utf8Fault(b, name, length);
            if (fault >= 0) {
                throw bad("utf8", "the name of field " + i + " of the object at byte " + p
                        + " is not well-formed UTF-8, at byte " + fault);
            }
            if (previousName >= 0) {
                int c = Arrays.compareUnsigned(b, previousName, previousName + previousLength,
                        b, name, name + length);
                if (c == 0) {
                    throw bad("duplicate", "the name of field " + i + " of the object at byte "
                            + p + " is the name before it");
                } else if (c > 0) {
                    throw bad("order", "the name of field " + i + " of the object at byte " + p
                            + " comes before the name before it");
                }
            }
            int valueEnd = checkValue(b, name + length, fe, level);
            if (valueEnd != fe) {
                throw bad("field-size", "the value of field " + i + " of the object at byte "
                        + p + " ends at byte " + valueEnd + ", before its field's end, " + fe);
            }
            previousEnd = (int) end;
            previousName = name;
            previousLength = length;
        }
        return f0 + (int) size;
    }

    /**
     * The first byte of a fault in the UTF-8 of [p, p + length), or -1 if it is well-formed:
     * no surrogate, no overlong form, nothing above U+10FFFF, no cut sequence (020-07, R11;
     * the Unicode Standard, table 3-7). Java's decoder replaces; it is not used to check.
     */
    static int utf8Fault(byte[] b, int p, int length) {
        int end = p + length;
        int i = p;
        while (i < end) {
            int c = b[i];
            if (c >= 0) {
                i++;
                continue;
            }
            c &= 0xff;
            int n;
            int low = 0x80, high = 0xbf;        // the second byte's range
            if (c >= 0xc2 && c <= 0xdf) {
                n = 1;
            } else if (c >= 0xe0 && c <= 0xef) {
                n = 2;
                if (c == 0xe0) {
                    low = 0xa0;                 // not overlong
                } else if (c == 0xed) {
                    high = 0x9f;                // no surrogate
                }
            } else if (c >= 0xf0 && c <= 0xf4) {
                n = 3;
                if (c == 0xf0) {
                    low = 0x90;                 // not overlong
                } else if (c == 0xf4) {
                    high = 0x8f;                // not above U+10FFFF
                }
            } else {
                return i;
            }
            if (n > end - i - 1) {
                return i;
            }
            int c1 = b[i + 1] & 0xff;
            if (c1 < low || c1 > high) {
                return i;
            }
            for (int k = 2; k <= n; k++) {
                int ck = b[i + k] & 0xff;
                if (ck < 0x80 || ck > 0xbf) {
                    return i;
                }
            }
            i += n + 1;
        }
        return -1;
    }

    // ======== The lookup (020-07, section 8) ========

    /**
     * Finds the field 'name' (UTF-8 bytes) of the object at 'start', which fills [start, end),
     * by the binary search of 020-07, section 8.2: it reads the object's head and, for at
     * most about log2(n + 1) fields, their ends and names, and no other byte. On bytes that
     * have not passed the full check, it checks what it touches (020-07, section 7.4) and
     * reads nothing outside [start, end), where end &lt;= b.length; on such bytes it may answer
     * absent for a field that is there, or give another field's value.
     *
     * @return  The start of the value of the field, its type byte, or -1 if absent.
     * @throws BadFormatException  If what it reads breaks a rule.
     */
    static int find(byte[] b, int start, int end, byte[] name) {
        if (start >= end) {
            throw bad("past-end", "an object expected at byte " + start
                    + ", at the end of its extent");
        }
        int t = b[start] & 0xff;
        if (!isObjectType(t)) {
            throw bad("type", "the byte " + hex(t) + " at byte " + start + " is not an object");
        }
        int w = 1 << (t - OBJECT1);
        if (w > end - start - 1) {
            throw bad("past-end", "the count of the object at byte " + start
                    + " ends past its extent");
        }
        long count = unsigned(b, start + 1, w);
        if (count > MAX_FIELDS) {
            throw bad("fields", "the object at byte " + start + " has " + count
                    + " fields, more than " + MAX_FIELDS);
        }
        int n = (int) count;
        int table = start + 1 + w;
        if (n * w > end - table) {
            throw bad("past-end", "the table of the object at byte " + start
                    + " ends past its extent");
        }
        int f0 = table + n * w;

        int low = 0, high = n - 1;
        while (low <= high) {
            int m = (low + high) >>> 1;
            long fieldStart = m == 0 ? 0 : unsigned(b, table + (m - 1) * w, w);
            long fieldEnd = unsigned(b, table + m * w, w);
            if (fieldStart >= fieldEnd) {
                throw bad("ends", "the ends of field " + m + " of the object at byte " + start
                        + " do not increase");
            }
            if (fieldEnd > end - f0) {
                throw bad("past-end", "field " + m + " of the object at byte " + start
                        + " ends past its extent");
            }
            int f = f0 + (int) fieldStart;
            int length = b[f] & 0xff;
            if (length == 0) {
                throw bad("name-length", "the name of field " + m + " of the object at byte "
                        + start + " has 0 bytes");
            }
            int value = f + 1 + length;
            if (value >= f0 + fieldEnd) {
                throw bad("past-end", "the name of field " + m + " of the object at byte "
                        + start + " leaves no value in its field");
            }
            int c = Arrays.compareUnsigned(b, f + 1, value, name, 0, name.length);
            if (c == 0) {
                return value;
            } else if (c < 0) {
                low = m + 1;
            } else {
                high = m - 1;
            }
        }
        return -1;
    }

    // ======== Readers of checked bytes ========
    //
    // Each reads the value or object at 'p' of bytes that passed the full check (or of a value
    // that passed checkValue). On other bytes, it may give anything or throw any exception.

    static boolean isObjectType(int t) {
        return t >= OBJECT1 && t <= OBJECT4;
    }

    static boolean isObjectAt(byte[] b, int p) {
        return isObjectType(b[p] & 0xff);
    }

    /**
     * The type of the value at 'p', as DbObject's type chars: 'n' boolean, 'l' integer, 'd'
     * double, 's' string, 'b' bytes, 'a' array, 'o' object.
     *
     * @throws BadFormatException  If the byte at 'p' is not a type byte.
     */
    static char typeAt(byte[] b, int p) {
        int t = b[p] & 0xff;
        switch (t) {
        case INT8: case INT16: case INT32: case INT64:
            return 'l';
        case STRING1: case STRING2: case STRING4:
            return 's';
        case BYTES1: case BYTES2: case BYTES4:
            return 'b';
        case ARRAY_START:
            return 'a';
        case TRUE: case FALSE:
            return 'n';
        case DOUBLE:
            return 'd';
        case OBJECT1: case OBJECT2: case OBJECT4:
            return 'o';
        default:
            throw bad("type", "the byte " + hex(t) + " at byte " + p + " is not a type byte");
        }
    }

    static boolean booleanAt(byte[] b, int p) {
        return (b[p] & 0xff) == TRUE;
    }

    static long integerAt(byte[] b, int p) {
        return signed(b, p + 1, 1 << ((b[p] & 0xff) - INT8));
    }

    /** The 64 bits of the double at 'p'. */
    static long doubleBitsAt(byte[] b, int p) {
        return signed(b, p + 1, 8);
    }

    /** The length in bytes of the string or bytes at 'p'. */
    static int lengthAt(byte[] b, int p) {
        return (int) signed(b, p + 1, 1 << (b[p] & 3));
    }

    /** Where the bytes of the string or bytes at 'p' start, after the type byte and length. */
    static int contentAt(byte[] b, int p) {
        return p + 1 + (1 << (b[p] & 3));
    }

    /** The string at 'p'; its UTF-8 is well-formed, so the String holds it exactly. */
    static String stringAt(byte[] b, int p) {
        return new String(b, contentAt(b, p), lengthAt(b, p), StandardCharsets.UTF_8);
    }

    /** A copy of the bytes at 'p'. */
    static byte[] bytesAt(byte[] b, int p) {
        int start = contentAt(b, p);
        return Arrays.copyOfRange(b, start, start + lengthAt(b, p));
    }

    /** The end of the value at 'p': an object's from its head, an array's by its elements. */
    static int valueEnd(byte[] b, int p) {
        int t = b[p] & 0xff;
        switch (t) {
        case INT8: case INT16: case INT32: case INT64:
            return p + 1 + (1 << (t - INT8));
        case STRING1: case STRING2: case STRING4: case BYTES1: case BYTES2: case BYTES4:
            return contentAt(b, p) + lengthAt(b, p);
        case TRUE: case FALSE:
            return p + 1;
        case DOUBLE:
            return p + DOUBLE_SIZE;
        case ARRAY_START: {
            int q = p + 1;
            while ((b[q] & 0xff) != ARRAY_END) {
                q = valueEnd(b, q);
            }
            return q + 1;
        }
        case OBJECT1: case OBJECT2: case OBJECT4:
            return objectEnd(b, p);
        default:
            throw bad("type", "the byte " + hex(t) + " at byte " + p + " is not a type byte");
        }
    }

    /**
     * The levels of the value at 'p': 0 for a scalar, 1 for a container that holds no
     * container, and one more for each level of containers below it (020-07, R14). A walk of
     * the value; at most MAX_LEVELS deep on checked bytes.
     */
    static int heightAt(byte[] b, int p) {
        int t = b[p] & 0xff;
        int height = 0;
        if (t == ARRAY_START) {
            for (int q = p + 1; (b[q] & 0xff) != ARRAY_END; q = valueEnd(b, q)) {
                height = Math.max(height, heightAt(b, q));
            }
            return 1 + height;
        } else if (isObjectType(t)) {
            int n = countAt(b, p);
            for (int i = 0; i < n; i++) {
                int f = fieldAt(b, p, i);
                height = Math.max(height, heightAt(b, f + 1 + (b[f] & 0xff)));
            }
            return 1 + height;
        }
        return 0;
    }

    /** The width w of the object at 'p': its count and ends take w bytes each. */
    static int widthAt(byte[] b, int p) {
        return 1 << ((b[p] & 0xff) - OBJECT1);
    }

    /** The count of fields of the object at 'p'. */
    static int countAt(byte[] b, int p) {
        return (int) unsigned(b, p + 1, widthAt(b, p));
    }

    /** The start of the fields of the object at 'p', after its table. */
    static int fieldsAt(byte[] b, int p) {
        int w = widthAt(b, p);
        return p + 1 + w + countAt(b, p) * w;
    }

    /** end[i] of the object at 'p': where field i ends, from the start of the fields. */
    static int endAt(byte[] b, int p, int i) {
        int w = widthAt(b, p);
        return (int) unsigned(b, p + 1 + w + i * w, w);
    }

    /** The start of field i of the object at 'p': its name's length, then the name. */
    static int fieldAt(byte[] b, int p, int i) {
        return fieldsAt(b, p) + (i == 0 ? 0 : endAt(b, p, i - 1));
    }

    /** The end of the object at 'p', from its head. */
    static int objectEnd(byte[] b, int p) {
        int n = countAt(b, p);
        return fieldsAt(b, p) + (n == 0 ? 0 : endAt(b, p, n - 1));
    }

    // ======== The writer's encodings (020-07, sections 4 and 6) ========
    //
    // Each write method writes at 'p' and returns the position after what it wrote. A writer
    // computes sizes in 64 bits and checks them with checkStoredSize() before it writes, so
    // that no number wraps (020-07, section 6.2).

    /** The bytes of an integer, its type byte included: 2, 3, 5 or 9 (020-07, R9). */
    static int integerSize(long v) {
        if (v == (byte) v) {
            return 2;
        } else if (v == (short) v) {
            return 3;
        } else if (v == (int) v) {
            return 5;
        }
        return 9;
    }

    /** Writes an integer in the fewest bytes (020-07, R9). */
    static int writeInteger(byte[] b, int p, long v) {
        int size = integerSize(v) - 1;
        b[p] = (byte) (INT8 + Integer.numberOfTrailingZeros(size));
        writeLE(b, p + 1, v, size);
        return p + 1 + size;
    }

    /** A double's 64 bits as stored: every NaN as NAN; -0.0 and the rest kept (020-07, R12). */
    static long doubleBits(long bits) {
        return isNaN(bits) ? NAN : bits;
    }

    /** Writes a double given by its bits, a NaN as NAN (020-07, R12): DOUBLE_SIZE bytes. */
    static int writeDouble(byte[] b, int p, long bits) {
        b[p] = (byte) DOUBLE;
        writeLE(b, p + 1, doubleBits(bits), 8);
        return p + DOUBLE_SIZE;
    }

    /**
     * The bytes of a string's or bytes' type byte and length: 2, 3 or 5 (020-07, R10).
     *
     * @throws IllegalArgumentException  If 'length' is below 0.
     */
    static int lengthSize(int length) {
        if (length < 0) {
            throw new IllegalArgumentException("length: a length of " + length
                    + " (bergdb 020-07, R10)");
        }
        return length <= Byte.MAX_VALUE ? 2 : length <= Short.MAX_VALUE ? 3 : 5;
    }

    /** Writes a string's type byte and length; its UTF-8 bytes follow. */
    static int writeStringHead(byte[] b, int p, int length) {
        return writeLength(b, p, STRING1, length);
    }

    /** Writes a bytes value's type byte and length; its bytes follow. */
    static int writeBytesHead(byte[] b, int p, int length) {
        return writeLength(b, p, BYTES1, length);
    }

    private static int writeLength(byte[] b, int p, int base, int length) {
        int size = lengthSize(length) - 1;
        b[p] = (byte) (base + Integer.numberOfTrailingZeros(size));
        writeLE(b, p + 1, length, size);
        return p + 1 + size;
    }

    static int writeBoolean(byte[] b, int p, boolean v) {
        b[p] = (byte) (v ? TRUE : FALSE);
        return p + 1;
    }

    /**
     * The width w of an object whose fields take 'fieldsSize' bytes: the smallest of 1, 2 and
     * 4 that holds it (020-07, R2).
     */
    static int width(long fieldsSize) {
        return fieldsSize <= 0xff ? 1 : fieldsSize <= 0xffff ? 2 : 4;
    }

    /** The bytes of an object's frame: its type byte, count and ends (020-07, section 4.2). */
    static int headSize(int count, long fieldsSize) {
        int w = width(fieldsSize);
        return 1 + w + count * w;
    }

    /**
     * Writes an object's frame, its type byte, count and ends, in front of its fields
     * (020-07, section 4.2): ends[i] is where field i ends, from the start of the fields.
     * Returns where the fields start.
     *
     * @throws IllegalArgumentException  If 'count' is above MAX_FIELDS, or a field has less
     *      than 3 bytes (020-07, R4 and R5).
     */
    static int frame(byte[] b, int p, int[] ends, int count) {
        checkCount(count);
        int w = width(count == 0 ? 0 : ends[count - 1]);
        b[p] = (byte) (OBJECT1 + (w >> 1));
        writeLE(b, p + 1, count, w);
        int q = p + 1 + w;
        int previous = 0;
        for (int i = 0; i < count; i++) {
            if (ends[i] - previous < 3) {
                throw new IllegalArgumentException("ends: field " + i + " ends at " + ends[i]
                        + ", " + (ends[i] - previous) + " bytes, less than a field's 3");
            }
            previous = ends[i];
            writeLE(b, q, ends[i], w);
            q += w;
        }
        return q;
    }

    /** Writes a field's name length and its name, checked by checkName(). */
    static int writeName(byte[] b, int p, byte[] name) {
        b[p] = (byte) name.length;
        System.arraycopy(name, 0, b, p + 1, name.length);
        return p + 1 + name.length;
    }

    // ======== The writer's checks (020-07, section 6.1) ========
    //
    // Each refuses with an IllegalArgumentException whose message starts with the condition's
    // code; the writer adds the place, as "inner.names[3]".

    /**
     * The well-formed UTF-8 of 's'.
     *
     * @throws IllegalArgumentException  If 's' has a lone surrogate, a char of U+D800 to U+DFFF
     *      that is not part of a surrogate pair: UTF-8 cannot hold it (020-07, R11; 021-04).
     */
    static byte[] utf8(String s) {
        if (StringUtil.hasLoneSurrogate(s)) {
            throw new IllegalArgumentException("utf8: a string with a lone surrogate, a char "
                    + "of U+D800 to U+DFFF that is not part of a surrogate pair, has no UTF-8 "
                    + "form (bergdb 020-07, R11)");
        }
        return s.getBytes(StandardCharsets.UTF_8);
    }

    /** The UTF-8 of a field's name, checked by checkName(). */
    static byte[] nameBytes(String name) {
        byte[] b = utf8(name);
        checkName(b);
        return b;
    }

    /**
     * Checks a name: 1 to 255 bytes of well-formed UTF-8 (020-07, R6).
     *
     * @throws IllegalArgumentException  If not.
     */
    static void checkName(byte[] name) {
        if (name.length == 0 || name.length > MAX_NAME) {
            throw new IllegalArgumentException("name-length: a name of " + name.length
                    + " bytes; a name has 1 to " + MAX_NAME + " bytes (bergdb 020-07, R6)");
        }
        checkUtf8(name, "a name");
    }

    /**
     * Checks that 'b' is well-formed UTF-8 (020-07, R11).
     *
     * @throws IllegalArgumentException  If not; 'what' names it in the message.
     */
    static void checkUtf8(byte[] b, String what) {
        int fault = utf8Fault(b, 0, b.length);
        if (fault >= 0) {
            throw new IllegalArgumentException("utf8: " + what + " that is not well-formed "
                    + "UTF-8, at byte " + fault + " (bergdb 020-07, R11)");
        }
    }

    /** @throws IllegalArgumentException  If 'count' is above MAX_FIELDS (020-07, R3). */
    static void checkCount(int count) {
        if (count > MAX_FIELDS) {
            throw new IllegalArgumentException("fields: an object of " + count
                    + " fields; at most " + MAX_FIELDS + " (bergdb 020-07, R3)");
        }
    }

    /**
     * @throws IllegalArgumentException  If a container at 'level' is too deep: above
     *      MAX_LEVELS, the top object at level 1 (020-07, R14).
     */
    static void checkLevel(int level) {
        if (level > MAX_LEVELS) {
            throw new IllegalArgumentException("depth: a container at level " + level
                    + ", deeper than " + MAX_LEVELS + " levels of objects and arrays (bergdb "
                    + "020-07, R14)");
        }
    }

    /**
     * @throws IllegalArgumentException  If a stored value, or a part of it, of 'size' bytes is
     *      above MAX_STORED (020-07, R15).
     */
    static void checkStoredSize(long size) {
        if (size > MAX_STORED) {
            throw new IllegalArgumentException("size: a stored value of " + size
                    + " bytes or more; at most 2^31 - 1 (bergdb 020-07, R15)");
        }
    }

    /**
     * @throws IllegalArgumentException  If a value of 'size' bytes, its type byte and length
     *      included, cannot be in a stored value: above MAX_VALUE (020-07, R15). A writer
     *      checks it in 64 bits before it allocates or writes, so that no size wraps.
     */
    static void checkValueSize(long size) {
        if (size > MAX_VALUE) {
            throw new IllegalArgumentException("size: a value of " + size + " bytes; a stored "
                    + "value has at most 2^31 - 1 bytes, and an object's frame some of them "
                    + "(bergdb 020-07, R15)");
        }
    }

    // ======== Bytes ========

    /** An unsigned little-endian number of 'size' bytes, 1 to 4. */
    private static long unsigned(byte[] b, int p, int size) {
        long x = 0;
        for (int k = size - 1; k >= 0; k--) {
            x = (x << 8) | (b[p + k] & 0xff);
        }
        return x;
    }

    /** A signed little-endian number of 'size' bytes, 1, 2, 4 or 8. */
    private static long signed(byte[] b, int p, int size) {
        long x = 0;
        for (int k = size - 1; k >= 0; k--) {
            x = (x << 8) | (b[p + k] & 0xff);
        }
        int shift = 64 - 8 * size;
        return (x << shift) >> shift;
    }

    private static void writeLE(byte[] b, int p, long x, int size) {
        for (int k = 0; k < size; k++) {
            b[p + k] = (byte) (x >>> (8 * k));
        }
    }

    private static boolean isNaN(long bits) {
        return (bits & EXPONENT) == EXPONENT && (bits & FRACTION) != 0;
    }

    private static boolean startsWith(byte[] b, byte[] prefix) {
        return b.length >= prefix.length
                && Arrays.equals(b, 0, prefix.length, prefix, 0, prefix.length);
    }

    private static String hex(int t) {
        return String.format("%02x", t);
    }

    private static BadFormatException bad(String code, String what) {
        return new BadFormatException(code + ": " + what + " (bergdb 020-07, section 7.2)");
    }
}
