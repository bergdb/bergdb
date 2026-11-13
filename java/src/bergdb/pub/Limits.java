package bergdb.pub;

import bergdb.pubimp.PubKeys;

/**
 * The limits of keys, values and transactions, and a check of a key before a call (bergdb
 * 026-02). The limits are the same for every database (the package's
 * {@linkplain bergdb.pub##limits Limits}; bergdb 024-17, section 6): a call over one throws
 * and writes nothing, and the database goes on. They are constants of the release, not
 * settings: a later release may raise them, never lower them, so a key that fits now fits
 * in later releases too.
 *
 * <p><b>Check a key first.</b> A put() or delete() of a {@link WBuilder} that is refused
 * spoils the builder, and an {@link RwEnvironment}'s action that catches a refusal and
 * returns commits its other writes ("Refused calls"). A key that a program makes, from a
 * user's input or a file's name, is checked before the call with keyBytes(), which also
 * tells how far over the limit it is, or checkKey(), which throws what the put would:</p>
 *
 * <pre>
 * String key = "/files/" + name;
 * if (Limits.keyBytes(key) &gt; Limits.MAX_KEY_BYTES) {
 *     key = "/files/#" + sha256Hex(name);     // a key that always fits
 * }
 * c.put(key, data);
 * </pre>
 *
 * <p>Both depend on the key alone, not on a database or a connection, and give the answer
 * of a put() and a delete() of every database of this release: they and the puts and
 * deletes of {@link Connection}, {@link WBuilder} and {@link RwEnvironment} run one check.
 * They check the key's form and its length (L2), not the rest of a put: a put may still
 * refuse its value (L4, or a null), an object at a key with a suffix other than ".obj"
 * (the package's {@linkplain bergdb.pub##objects Objects}), or, while key replace is on
 * (Connection.setEnableKeyReplace()), a key without a suffix or with ".obj" whose directory
 * holds "${transactionTime}". get() and exists() do not refuse a key over L2: they find no
 * value for it.</p>
 *
 * <p><b>An index entry's levels</b> (L6, {@link #MAX_LEVEL_BYTES}) are counted by the
 * user, who knows the levels of the indexes he defined: a "long" or a "double" level is 8
 * bytes; a "string" level the UTF-8 of the field's string and one byte, and one byte more
 * for each character U+0000 and U+0001; a "bytes" level its bytes and one byte, and one
 * byte more for each byte 0x00 and 0x01. The levels of an index together are at most
 * MAX_LEVEL_BYTES, for each index of the object's directory; so a "bytes" level alone
 * holds at most 110 bytes, or 55 zero bytes, and a "string" level alone 110 ASCII
 * characters. A put of an object over it is refused at the commit with
 * IllegalArgumentException; index such a value by a hash of it, or by a prefix as a level
 * of its own. An index built over objects put before it gives such an object no entry.</p>
 *
 * <p><b>A transaction</b> (L1, L3, L5) is checked at its commit, after BergDB has added the
 * index entries of the objects it puts: an object put at a key of a directory with k
 * indexes is up to 1 + 2k operations. The package's Limits gives the count.</p>
 *
 * <p>The constants are the Core's, by reference, and compile-time constants: code compiled
 * against them keeps the numbers of its release, which is safe, as a later release only
 * raises a limit.</p>
 *
 * @author Frans Lundberg
 */
public final class Limits {

    private Limits() {}

    /**
     * L1: the most operations of a transaction, 500: the keys it puts or deletes, one a key
     * (the last call on a key counts), and the index entries that BergDB puts and deletes for
     * its objects. A delete counts whether its key has a value or not. A transaction over it
     * is refused at its commit with DbException (bergdb 024-17, L1).
     */
    public static final int MAX_OPERATIONS = PubKeys.MAX_OPERATIONS;

    /**
     * L2: the most bytes of a key as stored, 111: its UTF-8, and one byte more for each part,
     * so each '/' counts two ("/customers/12345678" is 21 bytes). keyBytes() counts them, and
     * a put() or delete() of a longer key throws IllegalArgumentException, as checkKey() does
     * (bergdb 024-17, L2).
     */
    public static final int MAX_KEY_BYTES = PubKeys.MAX_KEY_BYTES;

    /**
     * L3: the most bytes of the keys of a transaction, 56 KiB, 57,344 bytes, the keys of its
     * index entries included. 500 keys of 111 bytes are 55,500 bytes, so it binds only on
     * BergDB's own longer keys. A transaction over it is refused at its commit with
     * DbException (bergdb 024-17, L3).
     */
    public static final int MAX_TRANS_KEY_BYTES = PubKeys.MAX_TRANS_KEY_BYTES;

    /**
     * L4: the most bytes of a value as stored, 8 MiB, 8,388,608 bytes: a byte[]'s bytes, a
     * String's UTF-8, an object's stored value. A put of a larger one throws
     * IllegalArgumentException; a larger file is put in chunks, under keys of their own
     * (bergdb 024-17, L4).
     */
    public static final int MAX_VALUE_BYTES = PubKeys.MAX_VALUE_BYTES;

    /**
     * L5: the most bytes of the keys and values of a transaction, 32 MiB. A transaction over
     * it is refused at its commit with DbException (bergdb 024-17, L5).
     */
    public static final long MAX_TRANS_BYTES = PubKeys.MAX_TRANS_BYTES;

    /**
     * L6: the most bytes of an object's levels in an entry of an index, 111, as a key's. The
     * class Javadoc says how a level is counted. A put of an object whose levels for an index
     * of its directory are longer is refused at its commit with IllegalArgumentException
     * (bergdb 024-17, L6; 024-26, U26-3).
     */
    public static final int MAX_LEVEL_BYTES = PubKeys.MAX_LEVEL_BYTES;

    /**
     * The bytes of a key as stored, to compare with MAX_KEY_BYTES: its UTF-8, and one byte
     * more for each part, so each '/' counts two. ASCII letters and digits are one byte each,
     * letters such as å, ä and ö two (U+0080 to U+07FF), the other characters of the Basic
     * Multilingual Plane, such as Chinese, three, and a character outside it, such as an
     * emoji, four; U+0000 is one byte. Also for a key over the
     * limit, so that the caller knows how far over it is. "${transactionTime}" counts as
     * written: key replace puts a time of as many digits in its place.
     *
     * @param key  A key: it starts with '/', has at least one more character, does not end
     *     with '/', and has no "//" and no lone surrogate (Connection, "Keys").
     * @return  The key's bytes as stored; a put() or delete() of the key throws if it is more
     *     than MAX_KEY_BYTES.
     * @throws IllegalArgumentException  If the key is null or of a bad form, with the message
     *     that a put() of it gives, whatever its length.
     */
    public static long keyBytes(String key) {
        return PubKeys.keyBytes(key);
    }

    /**
     * Throws the IllegalArgumentException that a put() or a delete() throws for the key, with
     * the same message, or returns if they take it: if it is null or of a bad form, or has
     * more than MAX_KEY_BYTES bytes as stored (keyBytes()). The rest of a put is not checked
     * (the class Javadoc).
     *
     * @param key  The key.
     * @throws IllegalArgumentException  If a put() or delete() refuses the key.
     */
    public static void checkKey(String key) {
        PubKeys.checkedIkey(key);
    }
}
