package bergdb.pubimp;

import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

import bergdb.common.Bug;
import bergdb.common.MyLongSet;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.KeyTransformation;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadFormatException;
import bergdb.pub.DataFormatException;
import bergdb.pub.MissingKeyFieldException;
import bergdb.pub.RwEnvironment;
import bergdb.pubimp.IndexManager.Index;

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
    private HashMap<MapKey, byte[]> kvOps;
    private HashMap<String, ObjectInfo> objectOps;
    private HashMap<MapKey, byte[]> indexOps;
    private MyLongSet vkeyWriteHashes;                  // Writes of virtual KVs.
    private final ConnectionImp connection;
    private final boolean enableKeyReplace;
    
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
        String ikey = PubKeys.u2i(ukey);
        
        long[] keySegments = Keys.toSegments(ikey);
        addReadHash(Keys.hash(keySegments));
        long lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
        
        TYPE result = connection.getInternal(lookupTime, ikey, clazz);
        
        if (firstRead) {
            readTime = connection.getActualLookupTime();
            firstRead = false;
        }
        
        return result;
    }
    
    private <TYPE> TYPE getInternal(String ikey, Class<TYPE> clazz) {
        long[] keySegments = Keys.toSegments(ikey);
        addReadHash(Keys.hash(keySegments));
        long lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
        
        TYPE result = connection.getInternal(lookupTime, ikey, clazz);
        
        if (firstRead) {
            readTime = connection.getActualLookupTime();
            firstRead = false;
        }
        
        return result;
    }
    
    public void clearOutput() {
        if (this.output != null) {
            output.clear();
        }
    }
    
    public void setOutput(String name, Object value) {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed");
        }
        
        if (name.length() == 0) {
            throw new IllegalArgumentException("The empty is not allowed for 'name'.");
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
    
    private void addReadHash(long hash) {
        this.readHashes.add(hash);
    }
    
    public void vkeyRead(long[] vkey) {
        this.readHashes.add(Keys.hash(vkey));
    }
    
    public void vkeyRead(long hash) {
        this.readHashes.add(hash);
    }
    
    public void vkeyWrite(long[] vkey) {
        vkeyWrite(Keys.hash(vkey));
    }
    
    public void vkeyWrite(long hash) {
        if (this.vkeyWriteHashes == null) {
            this.vkeyWriteHashes = new MyLongSet();
        }
        this.vkeyWriteHashes.add(hash);
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
    
    @SuppressWarnings("unused")
    private static KeyTransformation getKeyTransformation(byte[] key) {
        return Util.contains(TRANSACTION_TIME_BYTES, key) ? replaceTransformation : null;
    }
    
    private void setBytes(String ikey, byte[] value) {        
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed.");
        }

        kvOps.put(new MapKey(Keys.toSegments(ikey), 
                enableKeyReplace ? getKeyTransformation(ikey) : null), value);
    }
    
    // Used internally, no checking
    void set(byte[] key, byte[] value, KeyTransformation kt) {
        kvOps.put(new MapKey(Keys.toSegments(key), kt), value);
    }

    /**
     * @throws IllegalArgumentException if 'ukey' is null or invalid.
     */
    public void delete(String ukey) {
        // Null values allowed in a HashMap.
        
        String ikey = PubKeys.u2i(ukey);

        if (Entries.isObjectKey(ikey)) {
            objectOps.put(ikey, new ObjectInfo(ikey, null, null));
        } else {
            kvOps.put(new MapKey(Keys.toSegments(ikey), null), null);   
        }
    }
    
    /**
     * @throws MissingKeyFieldException
     * @throws IllegalArgumentException if object is null or if the key field is null or 
     * of an invalid format.
     */
    public void put(Object object) throws MissingKeyFieldException {
        if (object == null) {
            throw new IllegalArgumentException("object == null not allowed");
        }
        
        String ukey;
        
        if (object instanceof DbObject) {
            ukey = ((DbObject)object).getString(PubUtil.KEY_FIELD);
            if (ukey == null) {
                throw new MissingKeyFieldException("No field named " + PubUtil.KEY_FIELD + " in DbObject.");
            }
        } else {
            ukey = PubUtil.readExistingKeyField(object);
        }
        
        put(ukey, object);
    }
    
    /**
     * @throws IllegalArgumentException
     */
    public void put(String ukey, Object object) {
        // Implementation here must match the Java object creation. Currently (June 2013) this
        // is made in pubimp.KvToObjectImp.createObject().
        
        if (object == null) {
            throw new IllegalArgumentException("object == null not allowed");
        }
        
        String ikey = PubKeys.u2i(ukey);
        Class<?> clazz = object.getClass();
        
        if (clazz.equals(byte[].class)) {
            // NOTE, No check here, but we could force suffix != EMPTY.
            setBytes(ikey, (byte[]) object);
        } else if (clazz.equals(String.class)) {
            setBytes(ikey, Util.toBytes((String) object));
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
    
    private void deleteIndexEntry(byte[] indexKey) {
        indexOps.put(new MapKey(Keys.toSegments(indexKey), null), null);
            // null marks "delete op"
    }
    
    /**
     * Sets/deletes index entries as appropriate.
     * Called after user Action has run.
     * 
     * @throws DataFormatException
     */
    public void indexEntries(IndexManager m) throws DataFormatException {
        assert m != null : "m is null";
        assert objectOps != null;
        
        if (objectOps.size() == 0) {
            return;
        }
        
        // We should not need to synch over all calls to getIndexes. If index was modified
        // since read time, we will notice. Would cause a transaction rerun.
        // We also add virtual read hash values for all directories of the objects.
        // This is to make sure that the set of indexes for a directory is not changed while
        // this transaction is running.
        
        for (ObjectInfo info : objectOps.values()) {
            assert info != null : "info is null";
            info.indexes = m.getActiveIndexesForDir(info.dir);
            addReadHash(IndexManager.vhashOfDir(info.dir));
        }
        
        RwEnvironmentImp.IndexSetter setter = new RwEnvironmentImp.IndexSetter() {
            public void setIndexKey(byte[] indexKey, KeyTransformation kt) {
                indexOps.put(new MapKey(Keys.toSegments(indexKey), kt), emptyByteArray);
            }
        };
        
        for (Map.Entry<String, ObjectInfo> entry : objectOps.entrySet()) {
            final ObjectInfo info = entry.getValue();
            final String ikey = entry.getKey();
            
            if (info.indexes != null) {
                // We need to know previous object value to delete index entries if needed.
                byte[] previousBytes = getInternal(ikey, byte[].class);
                DbObject previousDbo = null;
                
                if (previousBytes != null) {
                    try {
                        previousDbo = new DbObject(previousBytes, null);
                    } catch (BadFormatException e) {
                        throw new DataFormatException(e.getMessage() + " For ikey: '" + ikey + "'.");
                    }
                }
                
                for (IndexManager.IndexForDir indexForDir : info.indexes) {
                    final IndexManager.Index index = indexForDir.index;
                    
                    addReadHash(index.keyHash);
                    
                    if (previousDbo != null) {
                        IndexSetter deleteSetter = new IndexSetter() {
                            public void setIndexKey(byte[] indexKey, KeyTransformation kt) {
                                deleteIndexEntry(indexKey);
                            }
                        };
                        
                        RwEnvironmentImp.setIndexEntry(previousDbo, info.name, index, indexForDir.dirId, 
                                deleteSetter, enableKeyReplace);
                    }
                    
                    if (info.dbo == null) {    // if delete op
                        // Empty, we already deleted index entries for previous value.
                    } else {
                        RwEnvironmentImp.setIndexEntry(info.dbo, info.name, index, indexForDir.dirId, 
                                setter, enableKeyReplace);
                    }
                }
            }
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
            
            if (info.dbo == null) {
                b.delete(key);
            } else {
                b.put(Keys.toSegments(key), info.kt, info.dbo.getBytes(), null);
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
            byte[] timeBytes = Keys.toBytes(transTimeToString(trans.time));
            assert timeBytes.length == REPLACE_ME_LENGTH;
            boolean found = false;
            
            if (bytes.length >= REPLACE_ME_BYTES.length) {
                for (int startIndex = bytes.length - REPLACE_ME_LENGTH; startIndex >= 0; startIndex--) {
                    found = true;
                    for (int i = 0; i < REPLACE_ME_LENGTH; i++) {
                        if (bytes[startIndex + i] != REPLACE_ME_BYTES[i]) {
                            found = false;
                            break;
                        }
                    }
                    
                    if (found) {
                        System.arraycopy(timeBytes, 0, bytes, startIndex, REPLACE_ME_LENGTH);
                        break;
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
     * The core code for creating one (or more) index entries in the database for a 
     * given DbObject and a given index.
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
        assert index.fields != null : "index.index.fields == null";
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
        
        for (int i = 0; i < index.fieldCombinations.length; i++) {
            byte[] middlePart = indexKeyMiddlePart(index, i, dbo);
        
            if (middlePart != null) {
                byte[] indexKey = concat(firstPart, middlePart, lastPart);
                setter.setIndexKey(indexKey, kt);
            }
        }
    }
    
    /**
     * Returns the middle part of the compound index key name.
     * This method determines what index entries an object should have when written to the database.
     */
    private static byte[] indexKeyMiddlePart(IndexManager.Index index, int combinationIndex, 
            DbObject dbo) {
        // Both long and int fields are indexed in a "long" index.
        // Both double and float fields are indexed in a "double" index.

        byte[] result = null;
        byte[][] parts = new byte[index.parts][];
        final String[] fieldCombination = index.fieldCombinations[combinationIndex];

        for (int j = 0; j < index.parts; j++) {
            String field = fieldCombination[j];
            char type = index.types[j];

            // Switch will set parts[j] if field exist.

            parts[j] = null;

            switch (type) {
            case Index.TYPE_LONG:
                if (dbo.has(field, 'l')) {
                    parts[j] = IndexManager.indexKeyPartFromLong(dbo.getLong(field));
                } else if (dbo.has(field, 'i')) {
                    parts[j] = IndexManager.indexKeyPartFromLong(dbo.getInt(field));
                }
                break;

            case Index.TYPE_DOUBLE:
                if (dbo.has(field, 'd')) {
                    parts[j] = IndexManager.indexKeyPartFromDouble(dbo.getDouble(field));
                }
                break;

            case Index.TYPE_STRING:
                if (dbo.has(field, 's')) {
                    String stringValue = dbo.getString(field);
                    parts[j] = IndexManager
                            .indexKeyPartFromString(index.kcollators[j], stringValue);
                }
                break;

            default:
                throw new Bug("Bad index type: " + type + ".");

            }

            if (parts[j] == null) {
                break;
            }

            if (j == index.parts - 1) {
                // Last part, create complete indexKey.
                result = concat(parts);
            }
        }

        return result;
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
    
    private static byte[] concat(byte[][] arrays) {
        assert arrays != null;
        assert arrays.length > 0;
        
        int totalSize = 0;
        for (int i = 0; i < arrays.length; i++) {
            assert arrays[i] != null;
            assert arrays[i].length > 0;
            totalSize += arrays[i].length;
        }
        
        byte[] total = new byte[totalSize];
        int offset = 0;
        for (int i = 0; i < arrays.length; i++) {
            System.arraycopy(arrays[i], 0, total, offset, arrays[i].length);
            offset += arrays[i].length;
        }
        return total;
    }

    private static class ObjectInfo {
        String dir;              // The directory where object is stored.
        String name;             // short object name
        DbObject dbo;       // null use to mark delete operation
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
            
            this.kt = kt;
        }
    }

    public static interface IndexSetter {
        public void setIndexKey(byte[] indexKey, KeyTransformation kt);
    }
    
    /**
     * Internal class that bounds a key transformation with a database key.
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
            
            if (!(key instanceof long[])) {
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
    
    @T
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
    
    @T
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
