package bergdb.pubimp;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

import bergdb.common.MyLongSet;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.KeyTransformation;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.DataFormatException;
import bergdb.pub.RwEnvironment;
import bergdb.pub.util.BadFormatException;

/**
 * Environment for a transaction.
 * 
 * @author Frans Lundberg
 */
public class RwEnvironmentImp implements RwEnvironment {
    // For now, we assume one object of this class per transaction.
    // If needed for performance, this could change. Initialization is 
    // relatively heavy.
    
    private static final byte[] emptyByteArray = new byte[0];
    private HashMap<String, Object> output;
    private boolean firstRead;
    private long readTime;
    private MyLongSet readHashes;
    private GetData readData;       // The reads' own (bergdb 015-42); made at the first read.
    
    // The writes, one operation a key in each map (bergdb 015-40): a value, or null for a
    // delete. Every put and delete at an object key (no suffix, or ".obj"), of any value, is
    // in objectOps, and keeps the directory's indexes (bergdb 020-10, section 5.1; 015-46: a
    // String or byte[] put was in kvOps, and left the previous object's index entries);
    // every other key's is in kvOps. So the last call on a key wins in its one map (bergdb
    // 015-41). In indexOps a put of an index entry stays over a delete of it
    // (deleteIndexEntry).
    private HashMap<MapKey, byte[]> kvOps;
    private HashMap<String, ObjectInfo> objectOps;
    private HashMap<MapKey, byte[]> indexOps;
    private MyLongSet vkeyWriteHashes;                  // Writes of virtual KVs.
    private final ConnectionImp connection;
    private final boolean enableKeyReplace;
    private boolean closed;                             // Set by close().
    
    public RwEnvironmentImp(ConnectionImp connection) {
        readHashes = new MyLongSet();
        kvOps = new HashMap<MapKey, byte[]>();
        objectOps = new HashMap<String, ObjectInfo>();
        indexOps = new HashMap<MapKey, byte[]>();
        firstRead = true;
        readTime = -1;
        this.connection = connection;
        output = null;
        this.enableKeyReplace = connection.getEnableKeyReplace();
    }
    
    public boolean exists(String ukey) {
        return get(ukey, byte[].class) != null;
    }
    
    /**
     * @throws IllegalArgumentException
     */
    public <TYPE> TYPE get(String ukey, Class<TYPE> clazz) {
        checkOpen();
        String ikey = PubKeys.u2i(ukey);
        
        long[] keySegments = Keys.toSegments(ikey);
        addReadHash(Keys.hash(keySegments));
        long lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
        
        TYPE result = connection.getInTransaction(readData(), lookupTime, ikey, clazz);
        
        if (firstRead) {
            readTime = readData.actualLookupTime;
            firstRead = false;
        }
        
        return result;
    }
    
    private <TYPE> TYPE getInternal(String ikey, Class<TYPE> clazz) {
        long[] keySegments = Keys.toSegments(ikey);
        addReadHash(Keys.hash(keySegments));
        long lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
        
        TYPE result = connection.getInTransaction(readData(), lookupTime, ikey, clazz);
        
        if (firstRead) {
            readTime = readData.actualLookupTime;
            firstRead = false;
        }
        
        return result;
    }
    
    /**
     * The GetData of this transaction's reads, its own, not the connection's: a read here
     * leaves the connection's frozen lookup time and its transactionInfo() as they were
     * (bergdb 015-42).
     */
    private GetData readData() {
        if (readData == null) {
            readData = connection.getDb().newGetData();
        }
        return readData;
    }
    
    /**
     * Ends the environment of an rw-transaction once its action has run for the last time:
     * a call of a method of RwEnvironment then throws IllegalStateException (bergdb 005-12).
     * Before, a put() or delete() made then was lost silently, and a setOutput() changed the
     * outputs of the committed transaction.
     */
    public void close() {
        closed = true;
    }
    
    private void checkOpen() {
        if (closed) {
            throw new IllegalStateException("The RwEnvironment is used after the action has "
                    + "run; it is valid only while Action.run() runs.");
        }
    }
    
    /**
     * Checks the name of an output, for setOutput() and Transaction.getOutput().
     * 
     * @throws IllegalArgumentException if name is null or empty.
     */
    static void checkOutputName(String name) {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        if (name.length() == 0) {
            throw new IllegalArgumentException("The empty string is not allowed for 'name'.");
        }
    }
    
    public void clearOutput() {
        if (this.output != null) {
            output.clear();
        }
    }
    
    public void setOutput(String name, Object value) {
        checkOpen();
        checkOutputName(name);
        
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed");
        }
        
        if (output == null) {
            output = new HashMap<String, Object>();
        }
        
        output.put(name, value);
    }
    
    public HashMap<String, Object> getOutputMap() {
        // NOTE If we would start to reuse RwEnvironmentImp objects, we must copy 'output' before
        // returning it. Alternatively, it can be copied when this object is reset for reuse.
        return output;
    }
    
    void addReadHash(long hash) {
        this.readHashes.add(hash);
    }
    
    public final int getObjectOpsSize() {
        return objectOps.size();
    }
    
    /**
     * Prepares internal data structures for rerunning a W-transaction.
     */
    public void prepareForWRerun() {
        // No user reads for a w-transaction.
        // Set operations not done again (kvOps, objectOps).
        // Index lookup is done again.
        
        firstRead = true;
        readTime = -1;
        readHashes.clear();
        
        if (objectOps.size() > 0) {
            for (ObjectInfo info : objectOps.values()) {
                info.indexes = null;
            }
            
            indexOps.clear();
        }
    }
    
    /**
     * Prepares internal data structures for rerunning an RW-transaction.
     */
    public void prepareForRWRerun() {
        // Everything done again, reset everything.
        
        firstRead = true;
        readTime = -1;
        readHashes.clear();
        kvOps.clear();
        objectOps.clear();
        indexOps.clear();
    }
    
    private static KeyTransformation getKeyTransformation(String key) {
        return key.contains("${transactionTime}") ? replaceTransformation : null;
    }
    
    private static final byte[] TRANSACTION_TIME_BYTES = Keys.toBytes("${transactionTime}");
    
    /**
     * A put of a String's or a byte[]'s bytes: at an object key in objectOps, which keeps the
     * indexes (bergdb 020-10, section 5.1; 015-46), else in kvOps.
     */
    private void setBytes(String ikey, byte[] value) {        
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed.");
        }
        
        KeyTransformation kt = enableKeyReplace ? getKeyTransformation(ikey) : null;
        if (Entries.isObjectKey(ikey)) {
            objectOps.put(ikey, ObjectInfo.ofBytes(ikey, value, kt));
        } else {
            setKv(new MapKey(Keys.toSegments(ikey), kt), value);
        }
    }
    
    // Used internally, no checking
    void set(byte[] key, byte[] value, KeyTransformation kt) {
        setKv(new MapKey(Keys.toSegments(key), kt), value);
    }
    
    /**
     * Sets the operation of a key in kvOps, a put, or a delete if value is null: it replaces
     * the key's earlier one, so the last call on a key wins (bergdb 015-40). The key is
     * removed first, as a HashMap keeps its first key object when a put replaces an entry,
     * and the key transformation of the MapKey must be the last call's (a delete has none).
     */
    private void setKv(MapKey key, byte[] value) {
        kvOps.remove(key);
        kvOps.put(key, value);
    }

    /**
     * @throws IllegalArgumentException if 'ukey' is null or invalid.
     */
    public void delete(String ukey) {
        // Null values allowed in a HashMap.
        
        checkOpen();
        String ikey = PubKeys.u2i(ukey);

        if (Entries.isObjectKey(ikey)) {
            objectOps.put(ikey, new ObjectInfo(ikey, null, null));
        } else {
            setKv(new MapKey(Keys.toSegments(ikey), null), null);   
        }
    }
    
    /**
     * @throws IllegalArgumentException
     */
    public void put(String ukey, Object object) {
        // Implementation here must match the Java object creation. Currently (June 2013) this
        // is made in pubimp.KvToObjectImp.createObject().
        
        checkOpen();
        if (object == null) {
            throw new IllegalArgumentException("object == null not allowed");
        }
        
        String ikey = PubKeys.u2i(ukey);
        Class<?> clazz = object.getClass();
        
        if (clazz.equals(byte[].class)) {
            // NOTE, No check here, but we could force suffix != EMPTY.
            // A copy: the value in memory must not be the caller's array, which the caller
            // may change after the put (bergdb 015-47).
            setBytes(ikey, ((byte[]) object).clone());
        } else if (clazz.equals(String.class)) {
            // A lone surrogate is refused, as in a key (bergdb 015-49): its UTF-8 bytes would
            // have '?' in its place, and a get would return another string (bergdb 019-44).
            if (PubKeys.hasLoneSurrogate((String) object)) {
                throw new IllegalArgumentException("String value has a lone surrogate, a "
                        + "char of U+D800 to U+DFFF that is not part of a surrogate pair "
                        + "(bergdb 019-44).");
            }
            setBytes(ikey, StringUtil.toBytes((String) object));
        } else {
            if (!Entries.isObjectKey(ikey)) {
                throw new IllegalArgumentException(
                        "Bad key, expected no suffix (or possibly the obsolete '.obj' suffix), "
                        + "key was: '" + ikey + "'.");
            }
            objectOps.put(ikey, new ObjectInfo(ikey, object, 
                    enableKeyReplace ? getKeyTransformation(ikey) : null));
        }
    }
    
    /**
     * Deletes an index entry of an object's previous value, unless this transaction puts it
     * (bergdb 015-40): when the indexed fields of an object are unchanged, the entry deleted
     * for its previous value and the one put for its new value are one key, and the entry
     * must stay, whatever the order of the two calls. indexEntries() deletes first, so the
     * put replaces the delete; before 015-40, when MapKey.equals was never true and indexOps
     * held both, Trans.Builder.build's rule (a put over a delete) kept the entry.
     */
    private void deleteIndexEntry(byte[] indexKey) {
        indexOps.putIfAbsent(new MapKey(Keys.toSegments(indexKey), null), null);
            // null marks "delete op"; putIfAbsent replaces a delete, not a put
    }
    
    /**
     * Sets and deletes the index entries of this transaction's writes at object keys, after
     * the user's action has run (or at once for a w()), by bergdb 020-10, section 5.1, for
     * every put and delete at an object key, of any value:
     * <ol>
     * <li>The read time R is fixed first: if nothing was read yet, R is the latest
     *     transaction's time, as a read at Long.MAX_VALUE resolves it (fixReadTime), before
     *     anything below. Until 2026-11-08 the index set was read before R existed (015-28,
     *     015-43, S2-F12): an index created or deleted meanwhile was missed.</li>
     * <li>The hash of each directory's virtual key goes into the read set, whether the
     *     directory has an index or not: a creation or deletion of an index of the directory
     *     writes it, so this transaction runs again if one commits after R.</li>
     * <li>The index set of each directory is read from the manager, under its lock, after
     *     R (IndexManager.getActiveIndexesForDir): a change of the set at or before R is in
     *     it (020-10, section 5.2).</li>
     * <li>If the set is not empty, the previous value is read at R (its key's hash in the
     *     read set), the entries of the previous value are deleted and those of the new one
     *     put. A value that is not a stored object of format 2 (a String's bytes, a byte[]
     *     that fails 020-07's full check) has no entries, so a String or a byte[] put over an
     *     object deletes its entries (015-46); a byte[] that passes the check is an object
     *     (020-10, section 3.3).</li>
     * <li>The index definitions' keys are not in the read set: an activation does not change
     *     the set.</li>
     * </ol>
     * 
     * @throws DataFormatException  If, in a directory with an index, the previous value or
     *      the new one is an object of format 1 (BergDB 2026.3's, "bergo" and the version 1):
     *      such a write is refused, a byte[] put of such bytes included; in a directory
     *      without an index they are stored as they are (bergdb 020-08, step 3; 020-10,
     *      section 5.1).
     */
    public void indexEntries(IndexManager m) throws DataFormatException {
        assert m != null : "m is null";
        assert objectOps != null;
        
        if (objectOps.size() == 0) {
            return;
        }
        
        fixReadTime();
        for (ObjectInfo info : objectOps.values()) {
            addReadHash(IndexManager.vhashOfDir(info.dir));
        }
        m.hook(IndexManager.WRITE_BEFORE_SET);
        for (ObjectInfo info : objectOps.values()) {
            info.indexes = m.getActiveIndexesForDir(info.dir);
        }
        m.hook(IndexManager.WRITE_AFTER_SET);
        
        RwEnvironmentImp.IndexSetter setter = new RwEnvironmentImp.IndexSetter() {
            public void setIndexKey(byte[] indexKey, KeyTransformation kt) {
                // Removed first, so that the MapKey kept is the put's, with its kt (setKv).
                MapKey key = new MapKey(Keys.toSegments(indexKey), kt);
                indexOps.remove(key);
                indexOps.put(key, emptyByteArray);
            }
        };
        IndexSetter deleteSetter = new IndexSetter() {
            public void setIndexKey(byte[] indexKey, KeyTransformation kt) {
                deleteIndexEntry(indexKey);
            }
        };
        
        for (Map.Entry<String, ObjectInfo> entry : objectOps.entrySet()) {
            final ObjectInfo info = entry.getValue();
            final String ikey = entry.getKey();
            
            if (info.indexes == null || info.indexes.length == 0) {
                continue;
            }
            
            // The previous value, read at R, to delete its entries.
            DbObject previousDbo = indexedObject(ikey, getInternal(ikey, byte[].class));
            DbObject newDbo = info.dbo != null ? info.dbo : indexedObject(ikey, info.value);
            
            for (IndexManager.IndexForDir indexForDir : info.indexes) {
                final IndexManager.Index index = indexForDir.index;
                if (previousDbo != null) {
                    RwEnvironmentImp.setIndexEntry(previousDbo, info.name, index,
                            indexForDir.dirId, deleteSetter, enableKeyReplace);
                }
                if (newDbo != null) {
                    RwEnvironmentImp.setIndexEntry(newDbo, info.name, index,
                            indexForDir.dirId, setter, enableKeyReplace);
                }
            }
        }
    }
    
    /**
     * Fixes the read time R if nothing was read yet: the latest transaction's time, as a read
     * at Long.MAX_VALUE resolves it (bergdb 020-10, section 5.1, step 1). Every later read of
     * the transaction is at R, and its Core transaction's read set is checked against R.
     */
    private void fixReadTime() {
        if (firstRead) {
            readTime = connection.getDb().lookupTime(Long.MAX_VALUE);
            firstRead = false;
        }
    }
    
    /** The first bytes of an object of format 1, BergDB 2026.3's: "bergo" and the version 1. */
    private static final byte[] FORMAT_1 = {'b', 'e', 'r', 'g', 'o', 1};
    
    /**
     * The value at an object key as an object to index: a DbObject if it is a stored object
     * of format 2 (the header and 020-07's full check), else null (bergdb 020-10, section
     * 3.3, rule 1): no value, a String's bytes, a byte[] that fails the check.
     * 
     * @throws DataFormatException  If the value is an object of format 1.
     */
    static DbObject indexedObject(String ikey, byte[] value) {
        if (value == null) {
            return null;
        }
        if (value.length >= FORMAT_1.length
                && Arrays.equals(value, 0, FORMAT_1.length, FORMAT_1, 0, FORMAT_1.length)) {
            throw new DataFormatException("The value at " + ikey + " is an object in format 1, "
                    + "written by BergDB 2026.3 or before, which this version does not read: a "
                    + "write of the key in a directory with an index is refused (bergdb 020-02, "
                    + "section 4.11; 020-10, section 5.1).");
        }
        if (value.length < 3 || value[0] != DbObject.HEADER) {
            return null;
        }
        try {
            return new DbObject(value);
        } catch (BadFormatException e) {
            return null;
        }
    }
    
    /**
     * Internal method for using GetMany in an RW transaction.
     * g.lookupTime is set by this method and should not be set by the caller.
     */
    void getMany(GetMany g) {
        g.lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
        
        connection.getDb().getMany(g);
        if (firstRead) {
            this.readTime = g.actualLookupTime;
            firstRead = false;
            
            //System.out.println("RwEnvironmentImp, firstRead, readTime: " + readTime + ", " + g.result.size());
        }
        
        for (Kvt kvt : g.result) {
            this.readHashes.add(Keys.hash(kvt.key));
        }
    }
    
    /**
     * This method creates the transaction (core.Trans) based on the values set to readHashes, 
     * kvOps, objectOps, indexOps, vkeyWriteHashes. If this transaction is an RW transaction
     * (Connection.rw()), the Action.run() method has been run already.
     */
    public Trans createTrans(Db db) {
        Trans.Builder b = db.trans();
        
        b.lookupTime(readTime == -1 ? Long.MAX_VALUE : this.readTime);
        
        if (readHashes.isArray()) {
            b.addReadHashes(readHashes.getArray(), readHashes.size());
        } else {
            for (long hash : readHashes) {
                b.addReadHash(hash);
            }
        }
        
        for (Map.Entry<MapKey, byte[]> entry : kvOps.entrySet()) {
            final long[] key = entry.getKey().getArray();
            final byte[] value = entry.getValue();
            final KeyTransformation kt = entry.getKey().getKeyTransformation();
            
            if (value == null) {
                b.delete(key);
            } else {
                b.put(key, kt, value, null);
            }
        }
        
        for (Map.Entry<String, ObjectInfo> entry : objectOps.entrySet()) {
            final String key = entry.getKey();
            final ObjectInfo info = entry.getValue();
            
            if (info.value == null) {
                b.delete(key);
            } else {
                b.put(Keys.toSegments(key), info.kt, info.value, null);
            }
        }
        
        for (Map.Entry<MapKey, byte[]> entry : indexOps.entrySet()) {
            final MapKey mkey = entry.getKey();
            final long[] key = mkey.getArray();
            final byte[] value = entry.getValue();
            final KeyTransformation kt = mkey.getKeyTransformation();
            
            if (value == null) {
                b.delete(key);
            } else {
                b.put(key, kt, value, null);
            }
        }
        
        if (this.vkeyWriteHashes != null) {
            for (long hash : vkeyWriteHashes) {
                b.addVirtualWriteHash(hash);
            }
        }
        
        Trans trans = b.build();
        return trans;
    }
    
    private static final String REPLACE_ME = Util.identity("${transactionTime}");
    private static final byte[] REPLACE_ME_BYTES = Keys.toBytes(REPLACE_ME);
    private static final int REPLACE_ME_LENGTH = REPLACE_ME_BYTES.length;
    
    private static final KeyTransformation replaceTransformation = new KeyTransformation() {
        
        public void transform(Trans trans, int index) {
            byte[] bytes = Keys.toBytes(trans.kvs[index].getKey());
            byte[] timeBytes = Keys.toBytes(transTimeToString(trans.tt));
            assert timeBytes.length == REPLACE_ME_LENGTH;
            boolean found = false;
            
            // Every occurrence is replaced, from the end of the key (bergdb 015-64; until
            // 015-64 only the last). The time's digits cannot form a new occurrence.
            if (bytes.length >= REPLACE_ME_BYTES.length) {
                int startIndex = bytes.length - REPLACE_ME_LENGTH;
                while (startIndex >= 0) {
                    boolean match = true;
                    for (int i = 0; i < REPLACE_ME_LENGTH; i++) {
                        if (bytes[startIndex + i] != REPLACE_ME_BYTES[i]) {
                            match = false;
                            break;
                        }
                    }
                    
                    if (match) {
                        System.arraycopy(timeBytes, 0, bytes, startIndex, REPLACE_ME_LENGTH);
                        found = true;
                        startIndex -= REPLACE_ME_LENGTH;
                    } else {
                        startIndex--;
                    }
                }
            }
            
            if (!found) {
                return;
            }
            
            long[] newKey = Keys.toSegments(bytes);
            trans.kvs[index].setKey(newKey);
            trans.writeKeyHashes[index] = Keys.hash(newKey);
        }
    };
    
    private static final String transTimeToString(long transTime) {
        assert transTime >= Klong.MIN_TIME && transTime <= Klong.MAX_TIME;
        return String.format(Locale.US, "%018d", transTime);
    }
    
    /**
     * The core code for creating one or more index entries in the database for a 
     * given DbObject and a given Index.
     * 
     * @param dbo  The object to index.
     * @param keyname  Database key name of the object.
     * @param index  The index.
     * @param dirId  The dirId of the directory where the object is located.
     * @param setter  Used for output.
     * @param useKeyReplace  True to use key replace.
     */
    public static void setIndexEntry(DbObject dbo, String keyname, IndexManager.Index index,
            int dirId, RwEnvironmentImp.IndexSetter setter, boolean useKeyReplace) {
        assert index != null : "index == null";
        assert dirId < 127;
        
        KeyTransformation kt = useKeyReplace ? getKeyTransformation(keyname) : null;
        byte[] firstPart = IndexManager.getIndexDbDirAsBytes(index.getName());
        byte[] keynameBytes = Keys.toBytes(keyname);
        
        byte[] lastPart = new byte[1 + 1 + keynameBytes.length];
        lastPart[0] = 0;
        lastPart[1] = (byte) (dirId + 1);
        System.arraycopy(keynameBytes, 0, lastPart, 2, keynameBytes.length);
        
        // We have first part (dir) and last part (dirId + keyname).
        // Lets iterate field combinations and add one entry for each combination for which all
        // fields exist in 'to'.
        
        IndexEntryBuilder b = new IndexEntryBuilder();
        index.function.createIndexEntries(dbo, b);
        byte[][] sortByteEntries = b.done();
        
        for (int i = 0; i < sortByteEntries.length; i++) {
            byte[] middlePart = sortByteEntries[i];            
            byte[] indexKeyBytes = concat(firstPart, middlePart, lastPart);
            setter.setIndexKey(indexKeyBytes, kt);
        }
    }
    
    private static byte[] concat(byte[] arr1, byte[] arr2, byte[] arr3) {
        assert arr1 != null;
        assert arr2 != null;
        assert arr3 != null;
        
        int totalSize = arr1.length + arr2.length + arr3.length;
        byte[] result = new byte[totalSize];
        
        int offset = 0;
        System.arraycopy(arr1, 0, result, offset, arr1.length);
        offset += arr1.length;
        System.arraycopy(arr2, 0, result, offset, arr2.length);
        offset += arr2.length;
        System.arraycopy(arr3, 0, result, offset, arr3.length);
        
        return result;
    }

    /**
     * A put or a delete at an object key: the stored value, or null for a delete; for an
     * object put, its DbObject too (bergdb 020-10, section 5.1).
     */
    private static class ObjectInfo {
        String dir;              // The directory where object is stored.
        String name;             // short object name
        DbObject dbo;            // The object of an object put, else null
        byte[] value;            // The value to store, null for a delete
        IndexManager.IndexForDir[] indexes;
        KeyTransformation kt;    // If non-null, the key transformation to use.
        
        /**
         * Creates the object.
         * 
         * @param key
         * @param object 'null' used to mark a deletion.
         */
        ObjectInfo(String ikey, Object object, KeyTransformation kt) {
            assert ikey != null;
            int charIndex = ikey.lastIndexOf('/');
            assert charIndex != -1 : "An object must be stored in a directory, missing '/' in key.";
            assert Entries.isObjectKey(ikey);
            
            dir = ikey.substring(0, charIndex + 1);
            name = ikey.substring(charIndex + 1);
            
            if (object == null) {
                dbo = null;
            } else if (object instanceof DbObject) {
                dbo = (DbObject) object;
            } else {
                dbo = DbObject.toDbObject(object);
            }
            value = dbo == null ? null : dbo.getBytes();
            
            this.kt = kt;
        }
        
        /** A put of a String's or a byte[]'s bytes at an object key. */
        static ObjectInfo ofBytes(String ikey, byte[] value, KeyTransformation kt) {
            ObjectInfo info = new ObjectInfo(ikey, null, kt);
            info.value = value;
            return info;
        }
    }

    public static interface IndexSetter {
        public void setIndexKey(byte[] indexKey, KeyTransformation kt);
    }
    
    /**
     * Internal class that bounds a key transformation with a database key.
     * Two MapKeys are equal when their keys are, whatever their transformations.
     * Until 2026-11-03 (bergdb 015-40) equals() tested for a long[] and so was never true:
     * a map held each call on a key, and the order of the calls was lost.
     */
    private static final class MapKey {
        private long[] array;
        private KeyTransformation kt;
        
        public MapKey(long[] array, KeyTransformation kt) {
            assert array != null;
            this.array = array;
            this.kt = kt;
        }
        
        public KeyTransformation getKeyTransformation() {
            return kt;
        }

        public boolean equals(Object key) {
            if (key == null) {
                return false;
            }
            
            if (!(key instanceof MapKey)) {
                return false;
            }
            
            MapKey key2 = (MapKey) key;
            long[] array2 = key2.array;
            
            if (array.length != array2.length) {
                return false;
            }
            
            for (int i = 0; i < array.length; i++) {
                if (array[i] != array2[i]) {
                    return false;
                }
            }
            
            return true;
        }
        
        /**
         * See http://stackoverflow.com/questions/2827612/effective-java-hashcode-implementation.
         */
        public int hashCode() {
            long prime = 37;
            long value = prime;
            for (int i = 0; i < array.length; i++) {
                value = value * prime + array[i];
            }
            
            int result = (int) value;
            result = (int) (result * prime + value >>> 32);
            return result;
        }
        
        public final long[] getArray() {
            return array;
        }
    }
    
    private static boolean assertionsEnabled() {
        boolean enabled = false;
        try {
            assert false;                                                                                                                                                                                                                                           
        } catch (AssertionError e) {
            enabled = true;
        }
        return enabled;
    }
    
    @Nano
    public static void testTransactionTimeString1() {
        long[] times = {0, 200, 17000000000000000L};
        String[] expected = {
                "000000000000000000", 
                "000000000000000200", 
                "017000000000000000"
        };  
        
        for (int i = 0; i < times.length; i++) {
            Assert.assertEquals(expected[i], transTimeToString(times[i]));
        }
    }
    
    @Nano
    public static void testTransactionTimeString2() {
        // Assertions must be enabled to test this. (-ea). Otherwise, nothing is tested.
        Throwable ex = null;
        try {
            transTimeToString(210000000000000000L);
        } catch (AssertionError e) {
            ex = e;
        }
        
        if (assertionsEnabled()) {
            Assert.assertTrue(ex != null);
        }
    }
    
    public static void main(String[] args) {
        System.out.println("transTimeToString, 1, 111222333444L");
        System.out.println(transTimeToString(1));
        System.out.println(transTimeToString(111222333444L));
        System.out.println(transTimeToString(Klong.MAX_TIME));
        
        // -->
        // 000000000000000001
        // 000000111222333444
        // 072057594037927935
        // 18 chars.
    }
}
