package bergdb.pub;

import bergdb.pub.util.Job;

/**
 * A builder of a user index: an index of the values of one directory, ordered by 1 to 8
 * levels, each a field of the objects (bergdb 020-10, section 3.1). Get one with
 * Database.indexBuilder(name); call dir() once, then type() and field() (or nestedField())
 * for each level, then start():
 *
 * <pre>
 *     database.indexBuilder("by-salary").dir("/employees/").type("long").field("salary")
 *             .start().join();
 * </pre>
 *
 * <p>Each call is checked at once, in the order given. The builder is spent after start(),
 * whatever it threw.</p>
 *
 * <p><b>The index function.</b> The index is a function of the data: each value v at a key of
 * the directory (its own keys, not its subdirectories') has one entry or none, by these
 * rules (bergdb 020-10, section 3.3):</p>
 * <ol>
 * <li>If the key has a suffix other than ".obj", or v is not a stored object (a value whose
 *     first byte is the header of the object format, 0x82, and that passes the format's full
 *     check), v has no entry. A String value never is an object; a byte[] value that passes
 *     the check is taken as one. An object of the format of BergDB 2026.3 and before is
 *     refused: a write of it in an indexed directory throws DataFormatException, and a build
 *     over it fails. It is told by its structure, "bergo", the version 1, a field count and
 *     a field table that fits the value, so a value that only starts with "bergo" and the
 *     version 1 is not one. A String put is never taken for one, but a write over a stored
 *     value, a delete of it and a build read its bytes alone: a String or a byte[] whose
 *     bytes happen to be a whole object of format 1, such as "bergo" and the chars U+0001,
 *     U+0000 and U+0000, is refused as one (bergdb 020-08, section 3).</li>
 * <li>Each level's field is followed in the stored object; each part of a nested path but
 *     the last must name a field that holds an object. The value found must be of the
 *     level's stored kind: an integer for "long" (Java's long, int, short, byte and char
 *     fields), a double but NaN for "double" (Java's double and float), a string for
 *     "string", bytes for "bytes" (byte[]). No kind is converted to another; a boolean, an
 *     array or an object gives no entry; an absent field gives no entry.</li>
 * <li>If the levels' encodings take more than 4,096 bytes in all, v has no entry.</li>
 * </ol>
 *
 * <p>The order of a level: "long" by the numbers; "double" by the numbers, -0.0 as 0.0 (one
 * key), -infinity the least, +infinity the greatest; "string" by the strings' Unicode code
 * points; "bytes" by unsigned bytes. An application that needs a language's order stores its
 * own collation key, such as java.text.Collator.getCollationKey(s).toByteArray(), in a byte[]
 * field and indexes it as "bytes".</p>
 *
 * <p>Every put and delete at an object key of the directory, of any value, keeps the index:
 * a String or a byte[] put over an object deletes its entry.</p>
 *
 * @author Frans Lundberg
 */
public interface IndexBuilder {
    /**
     * The directory whose values are indexed, such as "/persons/": its own values, not its
     * subdirectories'. Called once, first.
     *
     * @param dir  The directory: it starts and ends with '/', and has no "//" and no lone
     *     surrogate.
     * @throws IllegalArgumentException  If dir is null or not a directory.
     * @throws IllegalStateException  If dir() was called before, or the builder is spent.
     */
    public IndexBuilder dir(String dir);

    /**
     * Starts the next level, of type "long", "double", "string" or "bytes"; at most 8 levels.
     *
     * @throws IllegalArgumentException  If the type is another string, or null.
     * @throws IllegalStateException  If dir() was not called yet, the level before has no
     *     field, there are 8 levels already, or the builder is spent.
     */
    public IndexBuilder type(String type);

    /**
     * The level's field: a top-level field name, one part (a '.' in it is part of the name).
     * Once per level, after type().
     *
     * @throws IllegalArgumentException  If the name is null, empty, has more than 255 UTF-8
     *     bytes, or has a lone surrogate.
     * @throws IllegalStateException  If type() was not called for the level, the level has its
     *     field, or the builder is spent.
     */
    public IndexBuilder field(String name);

    /**
     * The level's field as a nested path: "car.size.length" split at '.', each part a name as
     * for field(); 1 to 16 parts, no empty part.
     *
     * @throws IllegalArgumentException  If the path is null, or a part breaks field()'s rules,
     *     or there are more than 16 parts.
     * @throws IllegalStateException  As field().
     */
    public IndexBuilder nestedField(String path);

    /**
     * As nestedField(String), with the parts given; a part may hold '.'.
     *
     * @throws IllegalArgumentException  If 'parts' is null or empty, has more than 16 parts,
     *     or a part breaks field()'s rules.
     * @throws IllegalStateException  As field().
     */
    public IndexBuilder nestedField(String[] parts);

    /**
     * Creates the index: writes its definition, in state building, in one transaction, and
     * starts its build in a background thread. From its return, every write of the directory
     * keeps the index. Returns the build's job: start().join() waits until the index is
     * active, at once for an empty directory. If the database stops before the build ends,
     * the next start takes it again, from the first key of the directory.
     *
     * @throws IllegalStateException  If dir() was not called, no level was given, a level has
     *     no field, or start() was called before.
     * @throws IndexAlreadyExistsException  If an index of the name exists, building or active.
     * @throws bergdb.pub.util.DbException  If the creation's transaction is refused; then
     *     nothing changed.
     */
    public Job start();
}
