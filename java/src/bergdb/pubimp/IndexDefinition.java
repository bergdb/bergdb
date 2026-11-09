package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.InternalDataException;
import bergdb.dag.Keys;
import bergdb.pub.DataFormatException;
import bergdb.pub.util.BadFormatException;

/**
 * The definition of a user index and its function: bergdb 020-10, sections 4.2 and 3.3 (the
 * indexes of 2026.4). Immutable.
 *
 * <p><b>The definition</b> (020-10, section 4.2) is stored at /#i/didef/-NAME as a stored
 * object of format 2 (bergdb 020-07), written field by field with ObjectFormat's encodings
 * and read with its full check and readers, with exactly these fields:</p>
 * <ul>
 * <li>version: the integer 1;</li>
 * <li>dir: the directory as the user gave it, such as "/p/q/", valid by PubKeys.udir2idir's
 *     rules;</li>
 * <li>gen: the generation G, an integer above 0 (020-10, section 4.3);</li>
 * <li>state: the string "building" or "active";</li>
 * <li>levels: an array of 1 to 8 objects, each exactly {type: a string, path: an array of
 *     strings}; type "long", "double", "string" or "bytes"; path 1 to 16 strings, each a name
 *     of 1 to 255 bytes (020-07's names).</li>
 * </ul>
 * The index's name is not in the object: it is its key's, by 020-10, section 3.1's rule. A
 * reader that meets bytes that break any of this throws an InternalDataException that names
 * the key and the rule.
 *
 * <p><b>The function</b> (020-10, section 3.3): a value v at an object key of the index's
 * directory has zero or one entry. None if v is not a stored object of format 2 (the header
 * 0x82 and 020-07's full check); none if a level's path is absent, passes through a value that
 * is not an object, or ends at a value of another stored kind than the level's type (long: an
 * integer; double: a double but NaN; string: a string; bytes: bytes; no kind is converted);
 * none if the levels take more than 4,096 bytes. Else its levels are L_1 to L_n, encoded by
 * IndexKeys (020-10, section 4.4). An object of format 1 is refused (DataFormatException).</p>
 *
 * @author Frans Lundberg
 */
final class IndexDefinition {

    /** The version of the definition's fields, its field 'version'. */
    static final int VERSION = 1;

    /** The most levels of an index (020-10, section 3.1). */
    static final int MAX_LEVELS = 8;

    /** The most parts of a level's path (020-10, section 3.1). */
    static final int MAX_PARTS = 16;

    private static final String BUILDING = "building";
    private static final String ACTIVE = "active";

    /** The fields of a definition, in their stored order: by their names' bytes. */
    private static final String[] FIELDS = {"dir", "gen", "levels", "state", "version"};
    private static final int DIR = 0, GEN = 1, LEVELS = 2, STATE = 3, VERSION_FIELD = 4;

    /** The fields of a level, in their stored order. */
    private static final String[] LEVEL_FIELDS = {"path", "type"};
    private static final int PATH = 0, TYPE = 1;

    private static final byte[][] FIELD_BYTES = utf8(FIELDS);
    private static final byte[][] LEVEL_FIELD_BYTES = utf8(LEVEL_FIELDS);

    private final String name;
    private final String dir;
    private final String idir;
    private final long gen;
    private final boolean active;
    private final char[] types;
    private final String[][] paths;
    private final byte[][][] pathBytes;
    private final byte[] key;
    private final byte[] generationPrefix;

    /**
     * A definition from its values; the arrays are copied.
     *
     * @param name  The index's name (020-10, section 3.1).
     * @param dir  The directory, as the user gave it, such as "/p/q/".
     * @param gen  The generation, above 0 (020-10, section 4.3).
     * @param active  True if active, false if building.
     * @param typeNames  Each level's type: "long", "double", "string" or "bytes".
     * @param paths  Each level's path: 1 to 16 names of 1 to 255 UTF-8 bytes.
     * @throws IllegalArgumentException  If a value breaks a rule of 020-10, section 4.2 or 3.1;
     *      the message names the field.
     */
    IndexDefinition(String name, String dir, long gen, boolean active, String[] typeNames,
            String[][] paths) {
        IndexKeys.checkName(name);
        this.name = name;
        this.idir = checkDir(dir);
        this.dir = dir;
        if (gen <= 0) {
            throw new IllegalArgumentException("'gen' is above 0, not " + gen + " (bergdb "
                    + "020-10, section 4.2).");
        }
        this.gen = gen;
        this.active = active;
        if (typeNames == null || paths == null || typeNames.length != paths.length) {
            throw new IllegalArgumentException("'levels': a type and a path for each level");
        }
        int n = typeNames.length;
        if (n < 1 || n > MAX_LEVELS) {
            throw new IllegalArgumentException("'levels': " + n + " levels; an index has 1 to "
                    + MAX_LEVELS + " (bergdb 020-10, section 4.2).");
        }
        this.types = new char[n];
        this.paths = new String[n][];
        this.pathBytes = new byte[n][][];
        for (int i = 0; i < n; i++) {
            String level = "'levels': level " + (i + 1) + "'s ";
            try {
                types[i] = IndexKeys.type(typeNames[i]);
            } catch (IllegalArgumentException e) {
                throw new IllegalArgumentException(level + "'type': " + e.getMessage(), e);
            }
            String[] path = paths[i];
            if (path == null || path.length < 1 || path.length > MAX_PARTS) {
                throw new IllegalArgumentException(level + "'path' has " + (path == null
                        ? "no" : path.length) + " parts; a path has 1 to " + MAX_PARTS
                        + " (bergdb 020-10, section 4.2).");
            }
            this.paths[i] = path.clone();
            this.pathBytes[i] = new byte[path.length][];
            for (int k = 0; k < path.length; k++) {
                if (path[k] == null) {
                    throw new IllegalArgumentException(level + "'path', part " + (k + 1)
                            + ": null is not a name");
                }
                try {
                    pathBytes[i][k] = ObjectFormat.nameBytes(path[k]);
                } catch (IllegalArgumentException e) {
                    throw new IllegalArgumentException(level + "'path', part " + (k + 1)
                            + ": " + e.getMessage(), e);
                }
            }
        }
        this.key = IndexKeys.definitionKey(name);
        this.generationPrefix = IndexKeys.generationPrefix(name, gen);
    }

    /** The idir of a definition's directory, by PubKeys.udir2idir's rules (bergdb 021-09). */
    private static String checkDir(String dir) {
        try {
            return PubKeys.udir2idir(dir);
        } catch (IllegalArgumentException e) {
            throw new IllegalArgumentException("'dir' " + IndexKeys.quote(dir) + " is not a "
                    + "directory: " + e.getMessage(), e);
        }
    }

    // ======== Getters ========

    String name() {
        return name;
    }

    /** The directory as the user gave it. */
    String dir() {
        return dir;
    }

    /** The directory's idir, PubKeys.udir2idir(dir()). */
    String idir() {
        return idir;
    }

    long gen() {
        return gen;
    }

    boolean isActive() {
        return active;
    }

    int levelCount() {
        return types.length;
    }

    /** The type of level i (from 0): IndexKeys.LONG, DOUBLE, STRING or BYTES. */
    char type(int i) {
        return types[i];
    }

    /** The types of the levels, a copy. */
    char[] types() {
        return types.clone();
    }

    String typeName(int i) {
        return IndexKeys.typeName(types[i]);
    }

    /** The path of level i (from 0), a copy. */
    String[] path(int i) {
        return paths[i].clone();
    }

    /** The key of the definition, bkey(/#i/didef/-NAME). */
    byte[] key() {
        return key.clone();
    }

    /** The prefix of the entries of this generation (020-10, section 4.1). */
    byte[] generationPrefix() {
        return generationPrefix.clone();
    }

    /** The same definition in state active. */
    IndexDefinition activated() {
        return new IndexDefinition(name, dir, gen, true, typeNames(), paths);
    }

    private String[] typeNames() {
        String[] t = new String[types.length];
        for (int i = 0; i < t.length; i++) {
            t[i] = IndexKeys.typeName(types[i]);
        }
        return t;
    }

    // ======== The bytes (020-10, section 4.2) ========

    /** The definition's stored value: a stored object of format 2 (020-07). */
    byte[] toBytes() {
        int n = types.length;
        byte[][] levels = new byte[n][];
        for (int i = 0; i < n; i++) {
            byte[][] parts = new byte[paths[i].length][];
            for (int k = 0; k < parts.length; k++) {
                parts[k] = string(paths[i][k]);
            }
            levels[i] = object(LEVEL_FIELD_BYTES, new byte[][] {array(parts),
                    string(typeName(i))});
        }
        byte[][] values = new byte[FIELDS.length][];
        values[DIR] = string(dir);
        values[GEN] = integer(gen);
        values[LEVELS] = array(levels);
        values[STATE] = string(active ? ACTIVE : BUILDING);
        values[VERSION_FIELD] = integer(VERSION);
        byte[] top = object(FIELD_BYTES, values);
        byte[] b = new byte[1 + top.length];
        b[0] = (byte) ObjectFormat.HEADER;
        System.arraycopy(top, 0, b, 1, top.length);
        return b;
    }

    /**
     * The definition in a stored value, read from the index's definition key: 020-07's full
     * check, then every rule of 020-10, section 4.2, and the name by 3.1's rule.
     *
     * @param name  The index's name, from the key.
     * @throws InternalDataException  If a rule is broken; the message names the key and the
     *      rule.
     */
    static IndexDefinition fromBytes(String name, byte[] b) {
        String where = "/#i/didef/-" + name;
        String nameFault = IndexKeys.nameFault(name);
        if (nameFault != null) {
            throw bad(where, "the name from the key: " + nameFault + " (020-10, section 3.1)");
        }
        try {
            ObjectFormat.checkStored(b);
        } catch (BadFormatException e) {
            throw bad(where, "it is not a stored object of format 2 (bergdb 020-07): "
                    + e.getMessage());
        }

        int version = ObjectFormat.find(b, 1, b.length, FIELD_BYTES[VERSION_FIELD]);
        if (version >= 0 && (ObjectFormat.typeAt(b, version) != 'l'
                || ObjectFormat.integerAt(b, version) != VERSION)) {
            throw bad(where, "'version' is not the integer " + VERSION + "; this BergDB reads "
                    + "version " + VERSION);
        }
        int[] at = fields(b, 1, FIELDS, FIELD_BYTES, where, "the definition");

        if (ObjectFormat.typeAt(b, at[DIR]) != 's') {
            throw bad(where, "'dir' is not a string");
        }
        String dir = ObjectFormat.stringAt(b, at[DIR]);
        if (ObjectFormat.typeAt(b, at[GEN]) != 'l') {
            throw bad(where, "'gen' is not an integer");
        }
        long gen = ObjectFormat.integerAt(b, at[GEN]);
        if (ObjectFormat.typeAt(b, at[STATE]) != 's') {
            throw bad(where, "'state' is not a string");
        }
        String state = ObjectFormat.stringAt(b, at[STATE]);
        if (!state.equals(BUILDING) && !state.equals(ACTIVE)) {
            throw bad(where, "'state' is " + IndexKeys.quote(state) + ", not \"" + BUILDING
                    + "\" or \"" + ACTIVE + "\"");
        }

        if (ObjectFormat.typeAt(b, at[LEVELS]) != 'a') {
            throw bad(where, "'levels' is not an array");
        }
        List<String> typeNames = new ArrayList<>();
        List<String[]> paths = new ArrayList<>();
        int p = at[LEVELS] + 1;
        while ((b[p] & 0xff) != ObjectFormat.ARRAY_END) {
            int i = typeNames.size();
            String level = "'levels': level " + (i + 1);
            if (i == MAX_LEVELS) {
                throw bad(where, "'levels' has more than " + MAX_LEVELS + " levels");
            }
            if (ObjectFormat.typeAt(b, p) != 'o') {
                throw bad(where, level + " is not an object");
            }
            int[] lat = fields(b, p, LEVEL_FIELDS, LEVEL_FIELD_BYTES, where, level);
            if (ObjectFormat.typeAt(b, lat[TYPE]) != 's') {
                throw bad(where, level + "'s 'type' is not a string");
            }
            typeNames.add(ObjectFormat.stringAt(b, lat[TYPE]));
            if (ObjectFormat.typeAt(b, lat[PATH]) != 'a') {
                throw bad(where, level + "'s 'path' is not an array");
            }
            List<String> parts = new ArrayList<>();
            int q = lat[PATH] + 1;
            while ((b[q] & 0xff) != ObjectFormat.ARRAY_END) {
                if (parts.size() == MAX_PARTS) {
                    throw bad(where, level + "'s 'path' has more than " + MAX_PARTS + " parts");
                }
                if (ObjectFormat.typeAt(b, q) != 's') {
                    throw bad(where, level + "'s 'path', part " + (parts.size() + 1)
                            + ", is not a string");
                }
                parts.add(ObjectFormat.stringAt(b, q));
                q = ObjectFormat.valueEnd(b, q);
            }
            paths.add(parts.toArray(new String[0]));
            p = ObjectFormat.valueEnd(b, p);
        }

        try {
            return new IndexDefinition(name, dir, gen, state.equals(ACTIVE),
                    typeNames.toArray(new String[0]), paths.toArray(new String[0][]));
        } catch (IllegalArgumentException e) {
            throw bad(where, e.getMessage());
        }
    }

    /**
     * The value positions of exactly the fields 'names' of the object at 'p' of checked
     * bytes, in the names' stored order.
     *
     * @throws InternalDataException  If the object has another field, or lacks one.
     */
    private static int[] fields(byte[] b, int p, String[] names, byte[][] nameBytes,
            String where, String what) {
        int n = ObjectFormat.countAt(b, p);
        int[] at = new int[names.length];
        Arrays.fill(at, -1);
        for (int i = 0; i < n; i++) {
            int f = ObjectFormat.fieldAt(b, p, i);
            int length = b[f] & 0xff;
            int k = names.length - 1;
            while (k >= 0 && !Arrays.equals(b, f + 1, f + 1 + length, nameBytes[k], 0,
                    nameBytes[k].length)) {
                k--;
            }
            if (k < 0) {
                throw bad(where, what + " has a field '" + new String(b, f + 1, length,
                        StandardCharsets.UTF_8) + "'; its fields are exactly "
                        + String.join(", ", names));
            }
            at[k] = f + 1 + length;
        }
        for (int k = 0; k < names.length; k++) {
            if (at[k] < 0) {
                throw bad(where, what + " has no field '" + names[k] + "'");
            }
        }
        return at;
    }

    /**
     * The definition of the index 'name' at a lookup time: read from /#i/didef/-NAME with
     * Db.getOne at 'lookupTime' (Long.MAX_VALUE for the latest), or null if there is none. A
     * name that breaks 020-10, section 3.1's rule has none.
     *
     * @throws InternalDataException  If the stored definition breaks a rule of 4.2.
     * @throws IllegalArgumentException  If 'name' is null.
     * @throws bergdb.pub.util.LookupTimeNotAvailableException  As Db.getOne.
     */
    static IndexDefinition read(Db db, String name, long lookupTime) {
        if (name == null) {
            throw new IllegalArgumentException("null is not an index name");
        }
        if (IndexKeys.nameFault(name) != null) {
            return null;
        }
        byte[] value = db.getOne(lookupTime, Keys.toSegments(IndexKeys.definitionKey(name)),
                db.newGetData());
        return value == null ? null : fromBytes(name, value);
    }

    // ======== The function (020-10, section 3.3) ========

    /**
     * The levels of the entry of the value at 'ikey', L_1 to L_n, or null if it has none
     * (020-10, section 3.3). The caller gives a key of this index's directory, its own
     * values; a key with a suffix that is not ".obj" (Entries.isObjectKey) has no entry. The
     * value is its stored bytes; an object's must pass 020-07's full check. Null, no value
     * (the old value of a new key, the new value of a delete), has no entry.
     *
     * @throws DataFormatException  If the value is an object of format 1, of BergDB 2026.3
     *      and before, at an object key, by its structure (ObjectFormat.isFormat1; 020-08,
     *      section 3): a byte[] put of it is refused, and a build fails (020-10, sections
     *      3.3, 5.1 and 6.1). RwEnvironmentImp gives a previous value of format 1 no entries
     *      without calling this, so a put over it and a delete of it work (2026-11-09).
     */
    byte[] entryLevels(String ikey, byte[] value) {
        if (value == null || !Entries.isObjectKey(ikey)) {
            return null;
        }
        if (ObjectFormat.isFormat1(value)) {
            throw new DataFormatException("The value at " + ukeyOf(ikey) + " is an object in "
                    + "format 1, written by BergDB 2026.3 or before, which this version does "
                    + "not read; the index " + IndexKeys.quote(name) + " cannot take it (bergdb "
                    + "020-02, section 4.11; 020-10, section 3.3).");
        }
        if (value.length < 2 || (value[0] & 0xff) != ObjectFormat.HEADER
                || !ObjectFormat.isStoredObject(value)) {
            return null;
        }

        int n = types.length;
        int[] at = new int[n];
        int size = 0;
        for (int i = 0; i < n; i++) {
            int p = find(value, pathBytes[i]);
            if (p < 0 || ObjectFormat.typeAt(value, p) != types[i]) {
                return null;
            }
            switch (types[i]) {
            case IndexKeys.DOUBLE:
                if (ObjectFormat.doubleBitsAt(value, p) == ObjectFormat.NAN) {
                    return null;
                }
                size += 8;
                break;
            case IndexKeys.LONG:
                size += 8;
                break;
            default: {
                int length = ObjectFormat.lengthAt(value, p);
                if (length >= IndexKeys.MAX_LEVEL_BYTES - size) {
                    return null;        // E has at least length + 1 bytes
                }
                size += IndexKeys.escapedLength(value, ObjectFormat.contentAt(value, p),
                        length) + 1;
                break;
            }
            }
            if (size > IndexKeys.MAX_LEVEL_BYTES) {
                return null;
            }
            at[i] = p;
        }

        byte[] levels = new byte[size];
        int q = 0;
        for (int i = 0; i < n; i++) {
            int p = at[i];
            switch (types[i]) {
            case IndexKeys.LONG:
                q = IndexKeys.writeLong(levels, q, ObjectFormat.integerAt(value, p));
                break;
            case IndexKeys.DOUBLE:
                q = IndexKeys.writeLong(levels, q, IndexKeys.doubleSortLong(
                        ObjectFormat.doubleBitsAt(value, p)));
                break;
            default:
                q = IndexKeys.writeEscaped(levels, q, value, ObjectFormat.contentAt(value, p),
                        ObjectFormat.lengthAt(value, p));
                levels[q++] = 0;
                break;
            }
        }
        assert q == size;
        return levels;
    }

    /** A key as the user gave it, and its ikey: "/p/b (/dp/-b)"; the ikey if it has no ukey. */
    private static String ukeyOf(String ikey) {
        try {
            return PubKeys.i2u(ikey) + " (" + ikey + ")";
        } catch (IllegalArgumentException e) {
            return ikey;
        }
    }
    
    /**
     * The entry's key of the value at 'ikey' (020-10, section 4.1): the generation's prefix,
     * the levels (entryLevels) and K of the ikey; or null if the value has no entry.
     *
     * @throws DataFormatException  As entryLevels().
     * @throws IllegalArgumentException  If 'ikey' has no file part ('/-' and a name).
     */
    byte[] entry(String ikey, byte[] value) {
        byte[] levels = entryLevels(ikey, value);
        return levels == null ? null
                : IndexKeys.entryKey(generationPrefix, levels, IndexKeys.fileKey(ikey));
    }

    /**
     * The value at a path of names in checked bytes of a stored object, from its top object:
     * the start of the value, or -1 if a part is absent, or a part but the last is not an
     * object (020-07, section 8.1).
     */
    private static int find(byte[] b, byte[][] parts) {
        int start = 1;
        int end = b.length;
        for (int k = 0; ; k++) {
            int q = ObjectFormat.find(b, start, end, parts[k]);
            if (q < 0 || k == parts.length - 1) {
                return q;
            }
            if (!ObjectFormat.isObjectAt(b, q)) {
                return -1;
            }
            start = q;
            end = ObjectFormat.objectEnd(b, q);
        }
    }

    // ======== Writing (020-07, section 6) ========

    private static byte[] string(String s) {
        byte[] u = ObjectFormat.utf8(s);
        byte[] b = new byte[ObjectFormat.lengthSize(u.length) + u.length];
        int p = ObjectFormat.writeStringHead(b, 0, u.length);
        System.arraycopy(u, 0, b, p, u.length);
        return b;
    }

    private static byte[] integer(long v) {
        byte[] b = new byte[ObjectFormat.integerSize(v)];
        ObjectFormat.writeInteger(b, 0, v);
        return b;
    }

    private static byte[] array(byte[][] elements) {
        int size = 2;
        for (byte[] e : elements) {
            size += e.length;
        }
        byte[] b = new byte[size];
        b[0] = (byte) ObjectFormat.ARRAY_START;
        int p = 1;
        for (byte[] e : elements) {
            System.arraycopy(e, 0, b, p, e.length);
            p += e.length;
        }
        b[p] = (byte) ObjectFormat.ARRAY_END;
        return b;
    }

    /** An object of the fields 'names' (in their stored order) and their values. */
    private static byte[] object(byte[][] names, byte[][] values) {
        int n = names.length;
        int[] ends = new int[n];
        int size = 0;
        for (int i = 0; i < n; i++) {
            size += 1 + names[i].length + values[i].length;
            ends[i] = size;
        }
        byte[] b = new byte[ObjectFormat.headSize(n, size) + size];
        int p = ObjectFormat.frame(b, 0, ends, n);
        for (int i = 0; i < n; i++) {
            p = ObjectFormat.writeName(b, p, names[i]);
            System.arraycopy(values[i], 0, b, p, values[i].length);
            p += values[i].length;
        }
        return b;
    }

    private static byte[][] utf8(String[] names) {
        byte[][] b = new byte[names.length][];
        for (int i = 0; i < names.length; i++) {
            b[i] = ObjectFormat.nameBytes(names[i]);
        }
        return b;
    }

    private static InternalDataException bad(String where, String why) {
        return new InternalDataException("The index definition at " + where + " breaks bergdb "
                + "020-10, section 4.2: " + why + ".");
    }

    // ======== Object ========

    public boolean equals(Object o) {
        if (!(o instanceof IndexDefinition)) {
            return false;
        }
        IndexDefinition d = (IndexDefinition) o;
        return name.equals(d.name) && dir.equals(d.dir) && gen == d.gen && active == d.active
                && Arrays.equals(types, d.types) && Arrays.deepEquals(paths, d.paths);
    }

    public int hashCode() {
        return name.hashCode() * 31 + Long.hashCode(gen);
    }

    public String toString() {
        StringBuilder s = new StringBuilder("index " + IndexKeys.quote(name) + " of "
                + IndexKeys.quote(dir) + ", generation " + gen + ", "
                + (active ? ACTIVE : BUILDING) + ", levels");
        for (int i = 0; i < types.length; i++) {
            s.append(i == 0 ? " " : ", ").append(typeName(i)).append(' ')
                    .append(Arrays.toString(paths[i]));
        }
        return s.toString();
    }
}
