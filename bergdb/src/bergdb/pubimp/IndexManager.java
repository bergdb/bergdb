package bergdb.pubimp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.InternalDataException;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.BadFormatException;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pubimp.IndexBuilderImp.IndexCreateState;

/**
 * <p>An object of this class manages secondary indexes.
 * A single IndexManager object is used for one database (DatabaseImp.indeXManager). 
 * It is used to add and delete indexes,
 * to add/delete index entries (IKP/i/[indexName]). The index information is stored in the database
 * and survives a database restart.
 * All index info from IKP/ii/ is read from database at startup time and kept in memory for
 * fast cached access. We expect not to have more than in the order of 10,000 indexes.<p>
 * 
 * <p><i>Composite indexes</i> are supported. A composite index consists of more than one ordered 
 * <i>composite parts</i>. Each part has a type and one or more field names.</p>
 */
public class IndexManager {
    //
    // The info about indexes are assumed to fit into memory and be fast to read at startup.
    // This information is fully cached in memory.
    // A suppose 1000's of indexes are fine, 100*1000 too possibly. But probably not millions?
    // Well, we need to do it in memory, we do not want a db lookup for method getIndexes.
    // It should be really fast. Possibly, we could even have a Bloom filter to very quickly 
    // determine that a directory has no index.
    //
    
    /**
     * Name of the primary index.
     */
    public static final String PRIMARY = Util.identity("primary");
    
    /** 
     * ikey for where to store index entries, constant database directory. 
     */
    private static final byte[] INDEX_DIR_BYTES = Keys.toBytes(Db.INTERNAL_KEY_PREFIX + "di/");

    private static final String INDEX_INFO_DIR = Util.identity(Db.INTERNAL_KEY_PREFIX + "dii/");
    
    /** 
     * bkey for where to store index info entries (Data.Index objects).
     */
    private static final byte[] INDEX_INFO_DIR_BYTES = Keys.toBytes(Db.INTERNAL_KEY_PREFIX + "dii/");
    
    /** 
     * ikey for a virtual key directory. 
     * Just a prefix. Nothing actually stored here.
     */
    private static final String INDEX_VDIR = Util.identity(Db.INTERNAL_KEY_PREFIX + "div/");
    
    /**
     * Map from database directory to array of active/creating indexes for the directory.
     * Only indexes in STATE_ACTIVE or STATE_CREATING are included.
     * Sync note: protected by 'lock'.
     */
    private DirToIndexesMap dirToActiveIndexes;
    
    /**
     * Map from index name to Index object. 
     * Sync note: protected by 'lock'.
     */
    private Map<String, Index> nameToIndex;
    
    /**
     * Lock object used to synchronize index creation (index info KV), index deletion (index info
     * KV) and dir-to-Index lookups. It protects the fields: dirToIndex and nameToIndex.
     * Locking is also used to ensure that the in-memory maps dirToIndex and nameToIndex matches the 
     * latest data in the database.
     * Write access to internal db directory 'indexInfoDir' is only allowed through threads 
     * holding 'lock'.
     */
    private final Object lock = new Object();
    private final CollatorFactory collatorFactory;
    
    /**
     * Creates a new object.
     */
    public IndexManager(CollatorFactory collatorFactory) {
        if (collatorFactory == null) {
            throw new IllegalArgumentException("collationFactory == null not allowed");
        }
        
        this.collatorFactory = collatorFactory;
        dirToActiveIndexes = new DirToIndexesMap();        
        nameToIndex = new HashMap<String, Index>();
        
        Index primaryIndex = new Index(IndexManager.PRIMARY, new String[]{"DUMMY"}, 
                new String[][] {new String[0]}, 
                new String[]{"string"}, this);
        assert primaryIndex.kcollators.length == 1;
        
        synchronized (lock) {
            nameToIndex.put(primaryIndex.getName(), primaryIndex);
        }
    }
    
    public Index getIndex(String indexName) {
        synchronized (lock) {
            return nameToIndex.get(indexName);
        }
    }
    
    /**
     * Reads the index info objects from database to the in-memory data structures.
     * 
     * @throws InternalDataException If internal data in the database is not valid.
     */
    public void initFromDatabase(ConnectionImp connection) throws InternalDataException {        
        UsePrimaryBuilderImp<Data.Index> b = (UsePrimaryBuilderImp<Data.Index>) connection.usePrimary(Data.Index.class);
        Iterable<Kv<Data.Index>> kvs = b.dirInternal(INDEX_INFO_DIR).kvs();
        
        for (Kv<Data.Index> kv : kvs) {
            Data.Index indexDo = kv.value();
            indexDo.check(this);
            
            String ikey = kv.ikey();
            
            int index1 = ikey.lastIndexOf('/');
            if (index1 == -1) {
                throw new InternalDataException("Bad ikey in dir " + INDEX_INFO_DIR + ", '" + ikey + "'.");
            }
            
            String indexName = ikey.substring(index1 + 2);
                // Does not include the '-', that is why we do "+ 2".
            IndexManager.Index index = Data.createIndex(indexName, indexDo, this);            
            nameToIndex.put(indexName, index);
            if (index.getState() == Index.STATE_ACTIVE || index.getState() == Index.STATE_CREATING) {
                dirToActiveIndexes.add(index);
            }
        }
    }
    
    /**
     * Starts new Jobs to complete index creation for indexes in state STATE_CREATING,
     * and to complete index deletion for indexes in state STATE_DELETING.
     * The previously started index operations where stopped when the database was
     * stopped.
     */
    public List<Job> finishOngoingJobs(DatabaseImp database) {
        // Assumption: method run before any other operations.
        
        List<Job> startedJobs = new ArrayList<Job>();
        List<Index> indexes = new ArrayList<Index>();
        ConnectionImp connection = new ConnectionImp(database);
        
        synchronized (lock) {
            for (Index index : nameToIndex.values()) {
                int state = index.getState();
                if (state == Index.STATE_CREATING || state == Index.STATE_DELETING) {
                    indexes.add(index);
                }
            }
        }
        
        for (final Index index : indexes) {
            int state = index.getState();
            
            if (state == Index.STATE_CREATING) {
                startedJobs.add(createJob(connection, index));
            } else if (state == Index.STATE_DELETING) {
                startedJobs.add(deleteJob(connection, index));
            }
        }
        
        return startedJobs;
    }

    /** Creates a Job for finishing creating the index. */
    private Job createJob(ConnectionImp connection, final Index index) {
        IndexBuilderImp creator = new IndexBuilderImp(index.name, connection.getDatabaseImp());
        IndexCreateState createState = new IndexCreateState(index);
        final Thread thread = creator.createInThread(createState);
        
        Job job = new Job() {
            public JobStatus getStatus() {
                return thread.isAlive() ? new WorkingJobStatus(index) : new DoneJobStatus(index);
            }

            public JobStatus join() {
                join(0);
                return getStatus();
            }

            public JobStatus join(int millis) {
                try {
                    thread.join(millis);
                } catch (InterruptedException e) {
                    throw new Error("Unexpected interruption of internal thread.");
                }
                return getStatus();
            }
        };
        
        return job;
    }

    private Job deleteJob(ConnectionImp connection, final Index index) {
        Job job = connection.getDatabaseImp().deleteIndexInternal(index.name);
        return job;
    }
    
    /**
     * Throws IllegalArgumentException if the indexName is illegal.
     */
    public static void checkIndexName(String indexName) {
        if (indexName == null) {
            throw new IllegalArgumentException("indexName cannot be null");
        }
        
        if (indexName.length() == 0) {
            throw new IllegalArgumentException("The empty string is not allowed as 'indexName'.");
        }
        
        int len = indexName.length();
        for (int i = 0; i < len; i++) {
            char c = indexName.charAt(i);
            if (Character.isWhitespace(c)) {
                throw new IllegalArgumentException("Illegal indexName: '" + indexName + "'.");
            }
            
            if (c == '/') {
                throw new IllegalArgumentException("Illegal indexName: '" + indexName + "'.");
            }
        }
    }
    
    /**
     * Check of index type string.
     */
    public boolean typeSupported(String type) {
        if (type == null || type.length() == 0) {
            return false;
        }
        
        char first = type.charAt(0);
        boolean result = false;
        
        switch (first) {
        case 'l':
            if (type.equals("long")) {
                result = true;
            }
            break;
            
        case 'd':
            if (type.equals("double")) {
                result = true;
            }
            break;
            
        case 's':
            result = checkStringIndexType(type);
            break;
        }
        
        return result;
    }
    
    private final boolean checkStringIndexType(String type) {
        return collatorFactory.typeSupported(type);
    }
    
    /**
     * Adds an index info entry and modifies the in-memory data structures accordingly.
     * The actual index KVs are not added.
     * 
     * @param indexName  Name of the index.
     * @param dirs  Directories to use the index on.
     * @param fields  Field names to use the index for.
     * @param types  The index types.
     * @throws IndexAlreadyExistsException  If an index with the name 'indexName' already exists.
     * @throws IllegalArgumentException  If type not supported, or...
     */
    public IndexManager.Index addIndex(ConnectionImp connection, String indexName, String[] dirs, 
            String[][] fields, String[] types) throws IndexAlreadyExistsException {
        assert indexName != null;
        assert indexName.length() > 0;
        assert dirs != null;
        assert dirs.length > 0;
        assert fields != null;
        assert fields.length > 0;
        assert types != null;
        assert types.length > 0;
        
        final int levels = types.length;
        
        assert fields.length == levels;
        
        for (int i = 0; i < levels; i++) {
            String[] levelFields = fields[i];
            
            for (String field : levelFields) {
                assert field != null;
                assert field.length() > 0;
            }
            
            assert types[i] != null;
            assert types[i].length() > 0;
        }
        
        for (int i = 0; i < dirs.length; i++) {
            String dir = dirs[i];
            assert dir != null;
            assert dir.length() > 0;
        }
        
        // Defensive copy, "call by value".
        dirs = dirs.clone();
        fields = fields.clone();
        
        Index index;
        
        synchronized (lock) {
            if (nameToIndex.get(indexName) != null) {
                throw new IndexAlreadyExistsException("Index '" + indexName + "' already exists.");
            }
            
            index = new Index(indexName, dirs.clone(), fields.clone(), types, this);
            assert index.name.equals(indexName);
            assert index.getState() == Index.STATE_CREATING;
            
            nameToIndex.put(indexName, index);
            dirToActiveIndexes.add(index);            
            storeIndex(connection, index);
        }
        
        return index;
    }
    
    /**
     * @throws DbException
     */
    public void storeIndex(ConnectionImp connection, IndexManager.Index index) {
        Data.Index indexDo = Data.createIndexDo(index);
        try {
            indexDo.check(this);
        } catch (InternalDataException e) {
            throw new Bug(e);   // Should never happen
        }
        
        byte[] key = getIndexInfoKeyAsBytes(index.name);
        Db db = connection.getDb();
        Trans.Builder b = db.trans();
        for (String dir : index.dirs) {
            b.addVirtualWriteHash(vhashOfDir(dir));
        }
        DbObject dbo = DbObject.toDbObject(indexDo);
        b.put(key, dbo.getBytes());
        db.execute(b.build());
    }
    
    public static long vhashOfDir(String dir) {
        String s = INDEX_VDIR + dir;
        long[] segments = Keys.toSegments(s);
        long hash = Keys.hash(segments);
        assert hash > 0;
        return hash;
    }
    
    private final byte[] getIndexInfoKeyAsBytes(String indexName) {
        return Util.concat(INDEX_INFO_DIR_BYTES, Keys.toBytes("-" + indexName));
    }

    /**
     * Removes index entries for a an index specified by its name.
     * 
     * @param indexName  Index name.
     * @param db         DB object.
     * @param deletedCounter
     *                   A long array of length 1. Number of elements removed so far is written
     *                   to removedCounter[0]. 
     *                   Sync note: the counter value is protected by synchronized on removedCounter.
     *                   The parameter functions as an updating output parameter.
     */
    void deleteIndexEntries(String indexName, Db db, long[] deletedCounter) {
        byte[] indexDbDir = IndexManager.getIndexDbDirAsBytes(indexName);
        long[] startKey = Keys.toSegments(indexDbDir);
        final long[] dirKey = Keys.toSegments(indexDbDir);
        final boolean[] isDone = new boolean[] { false };
        
        while (!isDone[0]) {
            GetMany g = new GetMany();
            g.inclusive = false;
            g.startKey = startKey;
            g.lookupTime = Long.MAX_VALUE;
            g.stopCondition = new GetMany.StopCondition() {
                private int count = 0;
                private static final int maxCount = 100;
                
                public int handleKvt(Kvt kvt) {
                    int result = GetMany.StopCondition.ADD;
                    
                    count++;
                    if (count == maxCount) {
                        result = GetMany.StopCondition.ADD_AND_STOP;
                    }
                    
                    if (!Keys.isPrefix(dirKey, kvt.key)) {
                        result = GetMany.StopCondition.STOP;
                        isDone[0] = true;
                    }
                
                    return result;
                }
                
                public void eod() {
                    isDone[0] = true;
                }
            };
            
            db.getMany(g);
            Trans.Builder b = db.trans();

            if (g.result.size() > 0) {
                for (Kvt kvt : g.result) {
                    b.delete(kvt.key);
                }
                db.execute(b.build());
            }
            
            synchronized (deletedCounter) {
                deletedCounter[0] += g.result.size();
            }
            
            if (!isDone[0]) {
                assert g.result.size() > 0 : "g.result.size() is 0";
                startKey = g.result.get(g.result.size() - 1).key;
            }
        }
    }
    
    void deleteIndexInfo(ConnectionImp connection, IndexManager.Index index) {
        /*String key = getIndexInfoKey(index.name);
        WTransactionBuilderImp b = (WTransactionBuilderImp) connection.w();
        b.internal();   // Allows access to index data.
        b.delete(key);
        
        synchronized (lock) {
            b.execute();
            this.nameToIndex.remove(index.name);
        }*/
        
        byte[] key = getIndexInfoKeyAsBytes(index.name);
        Db db = connection.getDb();
        Trans trans = db.trans().delete(key).build();
        
        synchronized (lock) {
            db.execute(trans);
            nameToIndex.remove(index.name);
        }
    }
    
    public boolean hasIndex(String indexName) {
        if (indexName == null) {
            throw new IllegalArgumentException("indexName == null not allowed");
        }
        
        Index index;
        
        synchronized (lock) {
            index = nameToIndex.get(indexName);
        }
        
        return index != null;
    }
    
    /**
     * Returns an Index object read from the database, or null if it does not exist, or did not 
     * exist at the given lookup time, or is not active (STATE_ACTIVE).
     * 
     * @param connection
     * @param indexName
     * @param wantedLookupTime
     */
    public Index getActiveIndex(ConnectionImp connection, String indexName, long wantedLookupTime) 
            throws InternalDataException {
        //
        // Note, we are careful to treat internal DB data as any data external to the 
        // application. It could have been modified with other software.
        // We must check that it follows the correct format, or throw DBInternalDataException.
        //
        
        assert indexName != null;
        
        if (indexName.equals(PRIMARY)) {
            Index primary;
            
            synchronized (lock) {
                primary = nameToIndex.get(PRIMARY);
            }
            
            if (primary == null) {
                throw new Bug("Missing 'primary' index, should not happen.");
            }
            return primary;
        }
        
        Data.Index indexDo;
        byte[] key = getIndexInfoKeyAsBytes(indexName);
        
        long[] segmentKey = Keys.toSegments(key);
        byte[] value = connection.getBytesAtLookupTime(wantedLookupTime, segmentKey);
        if (value == null) {
            return null;
        }
        
        DbObject dbo;
        try {
            dbo = new DbObject(value);
        } catch (BadFormatException e) {
            throw new InternalDataException("Bad index info object: '" + key + "', " + e.getMessage());
        }
        
        indexDo = dbo.toJavaObject(Data.Index.class, connection.getDatabaseImp().getClassToObject());
        indexDo.check(this);
        
        Index index = Data.createIndex(indexName, indexDo, this);
        return index.getState() == IndexManager.Index.STATE_ACTIVE ? index : null;
    }
    
    public static final byte[] getIndexDbDirAsBytes(String indexName) {
        return Util.concat(INDEX_DIR_BYTES, Keys.toBytes(PubKeys.DIR_PREFIX + indexName + "/"));
    }
    
    /**
     * Returns active (STATE_ACTIVE or STATE_CREATING) indexes for the directory. 
     * 'dirname' should end with a "/".
     */
    public IndexForDir[] getActiveIndexesForDir(String dirname) {
        IndexForDir[] result;
        
        synchronized (lock) {
            result = dirToActiveIndexes.get(dirname);
        }
        
        return result;
    }
    
    private static final long LONGMAX = 9223372036854775807L;   // 2^63-1
    
    /**
     * Returns a long composite index part to an index entry key.
     */
    public static byte[] indexKeyPartFromLong(long longValue) {
        //
        // 'longValue' is converted. Range of Java's "long" is: 
        // [-9,223,372,036,854,775,808 to +9,223,372,036,854,775,807]
        // That is: [-2^63 to 2^63-1].
        // To add 2^63 (mod 2^64), we add 2^63-1 first and then we add 1.
        // This converts like this:
        // Long.MIN_VALUE (-2^63)  -> 0.
        // 0                       -> 2^63
        // Long.MAX_VALUE (2^63-1) -> 2^64 (if considered unsigned).
        // Seems correct :-)
        //
        
        long sortValue = (longValue + LONGMAX) + 1;
        byte[] bytes = new byte[8];
        Bytes.longToBytesBE(sortValue, bytes, 0);
        return bytes;
    }
    
    private static final long signBit = 0x8000000000000000L;
    
    public static byte[] indexKeyPartFromDouble(double doubleValue) {
        //
        // From http://www.cygnus-software.com/papers/comparingfloats/comparingfloats.htm:
        // The IEEE float and double formats were designed so that the numbers are lexicographically
        // ordered, which – in the words of IEEE architect William Kahan means 
        // "if two floating-point numbers in the same format are ordered ( say x < y ), then they 
        // are ordered the same way when their bits are reinterpreted as Sign-Magnitude integers."
        //
        // Note, we do not store a long "Sign-Magnitude", but in two's-complement representation.
        // So, we *cannot* simply do:
        //     return createIndexKey(index, keyname, Double.doubleToLongBits(doubleValue));
        // 
        // See http://stackoverflow.com/questions/7534230/converting-from-sign-magnitude-to-twos-complement.
        //
        // Note, this will not sort -0.0 before 0.0. They are considered the same.
        // Sorting Double.POSITIVE_INFINITY and Double.NEGATIVE_INFINITY works as expected.
        //
        
        long x = Double.doubleToLongBits(doubleValue);
        long twosComplement = (x & signBit) == 0 ? x : -(x & ~signBit);
        return indexKeyPartFromLong(twosComplement);
    }
    
    public static byte[] indexKeyPartFromString(KCollator collator, String stringValue) {
        assert collator != null : "collator is null";
        assert stringValue != null: "stringValue is null";
        
        byte[] sortBytes = collator.getSortBytes(stringValue);
        return sortBytes;
    }
    
    /**
     * Given the full index key, this method returns the corresponding
     * object key (the key to the indexed object).
     */
    public static byte[] getObjectKey(Index index, long[] key) {
        assert key != null;
        assert index != null;
        assert key.length > 0;
        
        int separatorIndex = -1;
        
        byte[] keyBytes = Keys.toBytes(key);
        for (int i = keyBytes.length - 1; i >= 0; i--) {
            if (keyBytes[i] == 0) {
                separatorIndex = i;
                break;
            }
        }
        
        if (separatorIndex == -1) {
            throw new InternalDataException("Bad index key: " + Util.toString(keyBytes) + ", " 
                    + Util.toHexString(keyBytes));
        }
        
        if (separatorIndex == 0 || separatorIndex == keyBytes.length - 1) {
            throw new InternalDataException("Bad index key (separatorIndex): " 
                    + Util.toString(keyBytes) + ", " + Util.toHexString(keyBytes));
        }
        
        int dirId = keyBytes[separatorIndex + 1] - 1;
        if (dirId < 0) {
            throw new InternalDataException("Bad index key (bad dirId): " 
                    + Util.toString(keyBytes) + ", " + Util.toHexString(keyBytes));
        }
        if (dirId >= index.dirs.length) {
            throw new InternalDataException("Bad index key (bad dirId, too big): " 
                    + Util.toString(keyBytes) + ", " + Util.toHexString(keyBytes));
        }
        
        int length = keyBytes.length - (separatorIndex + 2);
        assert length >= 0 : "Neg length: " + length;
        
        byte[] dirBytes = index.dirBytes[dirId];
        byte[] result = Util.concat(dirBytes, 0, dirBytes.length, keyBytes, separatorIndex + 2, length);        
        return result;
    }
    
    public void setIndexStateToActive(ConnectionImp connection, Index index) {
        assert connection != null;
        assert index != null : "index was null";
        
        synchronized (lock) {
            int state = index.getState();
            if (index.getState() != Index.STATE_CREATING) {
                throw new IllegalStateException("State not STATE_CREATING, but " + state 
                        + ", cannot set state to STATE_ACTIVE.");
            }
            index.setState(Index.STATE_ACTIVE);
            assert dirToActiveIndexes.assertHasIndexMappings(index);
            storeIndex(connection, index);
        }
    }
    
    /**
     * Ensures that an index is in a deleting state.
     * 
     * @throws NoSuchIndexException  If no index exists with the given name.
     * @throws DbException
     */
    public Index ensureDeletingState(ConnectionImp connection, String indexName) {
        assert indexName != null;
        Index index;
        
        synchronized (lock) {
            index = nameToIndex.get(indexName);
            if (index == null) {
                throw new NoSuchIndexException("No index named '" + indexName + "' exists.");
            }
            
            int state = index.getState();
            if (state != Index.STATE_DELETING) {
                index.state = Index.STATE_DELETING;
                dirToActiveIndexes.remove(index);
                storeIndex(connection, index);
            }
        }
        
        return index;
    }
    
    /**
     * Immutable index class.
     */
    public static class Index {
        static final int STATE_CREATING = 10;
        static final int STATE_ACTIVE = 20;
        static final int STATE_DELETING = 30;
        
        public static final char TYPE_STRING = 's';
        public static final char TYPE_DOUBLE = 'd';
        public static final char TYPE_LONG = 'l';
        
        private final String name;     // Unique name of the index.
        final String[] dirs;
        private final byte[][] dirBytes;  // 'dirs' as bytes, for performance.
        final String[][] fields;
        final String[] typeStrings;
        final char[] types;              // TYPE_x
        final KCollator[] kcollators;    // Non-null when type == TYPE_STRING;
        private int state;
        final long keyHash;
        final int parts;       // Number of user-specified composite parts 
        final String[][] fieldCombinations;
        final int combinationCount;
        private final Object lock;
        
        /**
         * Created an Index object.
         * Parameters should have been checked already. 
         * Only asserts (not IllegalArgumentException) used in this constructor.
         */
        public Index(String name, String[] dirs, String[][] fields, String[] typeStrings, 
                IndexManager indexManager) {
            KCollator kc = null;      // local variable
            this.name = name;
            this.dirs = dirs.clone();
            this.fields = fields.clone();
            this.typeStrings = typeStrings.clone();
            this.state = STATE_CREATING;
            this.keyHash = Keys.hash(Keys.toSegments(indexManager.getIndexInfoKeyAsBytes(name)));
            this.parts = typeStrings.length;
            this.lock = indexManager.lock;
            typeStrings = typeStrings.clone();
            
            assert parts >= 1;
            assert dirs != null;
            assert fields.length == parts;
            assert typeStrings != null;
            
            for (int i = 0; i < typeStrings.length; i++) {
                assert indexManager.typeSupported(typeStrings[i]);
            }
            
            this.combinationCount = computeCombinationCount();
            this.fieldCombinations = computeFieldCombinations(fields);
            this.types = new char[parts];
            this.kcollators = new KCollator[parts];
            this.dirBytes = new byte[dirs.length][];
            
            handleIndexLevels(indexManager, kc);
            
            if (name.equals(PRIMARY)) {
                // The primary index is a special case. 
                this.kcollators[0] = new PrimaryKeyCollator();
                this.state = Index.STATE_ACTIVE;
            }
        }

        private void handleIndexLevels(IndexManager indexManager, KCollator kc) {
            
            for (int i = 0; i < dirs.length; i++) {
                dirBytes[i] = Keys.toBytes(dirs[i]);
            }
            
            for (int level = 0; level < parts; level++) {
                String typeString = typeStrings[level];
                char type = 'X';
            
                char first = typeString.charAt(0);
                switch (first) {
                case 'l':
                    if (!typeString.equals("long")) {
                        throw new IllegalArgumentException("Unsupported index type: " + typeString);
                    }
                    
                    type = TYPE_LONG;
                    break;
                    
                case 'd':
                    if (!typeString.equals("double")) {
                        throw new IllegalArgumentException("Unsupported index type: " + typeString);
                    }
                    
                    type = TYPE_DOUBLE;
                    break;
                    
                case 's':   
                    kc = indexManager.collatorFactory.createCollator(typeString);
                    if (kc == null) {
                        throw new IllegalArgumentException("Unsupported index type: " + typeString);
                    }
                    type = TYPE_STRING;
                    break;
                    
                default:
                    throw new IllegalArgumentException("Unsupported index type: " + typeString);
                }
                
                assert type != 'X';
                this.types[level] = type;
                this.kcollators[level] = kc;
            }
        }
        
        private int computeCombinationCount() {
            int cCount = 1;
            for (int i = 0; i < parts; i++) {
                cCount = cCount * fields[i].length;
            }
            return cCount;
        }

        private String[][] computeFieldCombinations(String[][] fields) {
            String[][] fieldComb = new String[combinationCount][];
            int[] indexArray = new int[parts];
            int[] sizeArray = new int[parts];
            for (int i = 0; i < parts; i++) {
                sizeArray[i] = fields[i].length;
            }
            int combinationIndex = 0;
            
            for (int i = 0; i < combinationCount; i++) {
                String[] combination = new String[parts];
                for (int j = 0; j < parts; j++) {
                    combination[j] = fields[j][indexArray[j]];
                }
                
                fieldComb[combinationIndex++] = combination;
                
                boolean increased = nextIndexArray(indexArray, sizeArray);
                if (i < combinationCount - 1) {
                    assert increased : "'increased' was false, levels=" + parts + ", i=" + i;
                }
            }
            
            return fieldComb;
        }
        
        private boolean nextIndexArray(int[] indexArray, int[] sizeArray) {
            int levels = indexArray.length;
            assert sizeArray.length == levels;
            boolean increased = false;
            
            for (int i = levels - 1; i >= 0; i--) {
                if (indexArray[i] == sizeArray[i] - 1) {
                    continue;
                } else {
                    indexArray[i]++;
                    for (int j = i + 1; j < levels; j++) {
                        indexArray[j] = 0;
                    }
                    
                    increased = true;
                    break;
                }
            }
            return increased;
        }
        
        /**
         * Returns the number of user composite index levels.
         */
        public final int getLevels() {
            return this.parts;
        }
        
        public final String getName() {
            return this.name;
        }
        
        public final int getState() {
            synchronized (lock) {
                return state;
            }
        }
        
        public final void setState(int state) {
            this.state = state;
        }
        
        public String getStateString() {
            String result;
            
            switch (state) {
            case STATE_CREATING:
                result = "creating";
                break;
            case STATE_ACTIVE:
                result = "active";
                break;
            case STATE_DELETING:
                result = "deleting";
                break;
            default:
                throw new IllegalStateException("Bad state: " + state);
            }
            return result;
        }
        
        public String toString() {
            StringBuilder b = new StringBuilder();
            
            b.append("name: " + this.name + ". ");
            
            b.append("levels: " + this.parts + ". ");
            
            b.append("dirs: ");
            for (int i = 0; i < dirs.length; i++) {
                b.append(dirs[i]);
                if (i != dirs.length - 1) {
                    b.append(", ");
                } else {
                    b.append(". ");
                }
            }
            
            b.append("types: ");
            for (int i = 0; i < typeStrings.length; i++) {
                b.append(typeStrings[i]);
                if (i != typeStrings.length - 1) {
                    b.append("-");
                } else {
                    b.append(". ");
                }
            }
            
            b.append("status:" + getStateString());
            
            return b.toString();
        }
    }
    
    /**
     * Used in map dir -> IndexForDir map.
     */
    static class IndexForDir {
        /** The Index. */
        final Index index;
        
        /** 
         * The directory ID used to identify the directory within all directories the index
         * applies to.
         */
        final int dirId;
        
        public IndexForDir(Index index, int dirId) {
            this.index = index;
            this.dirId = dirId;
        }
    }
    
    
    private static class WorkingJobStatus implements JobStatus {
        private Index index;
        
        WorkingJobStatus(Index index) {
            this.index = index;
        }
        
        public int progress() {
            return -1;
        }

        public String note() {
            return "Working on creating index '" + index.name + "'.";
        }
    }
    
    private static class DoneJobStatus implements JobStatus {
        private Index index;
        
        DoneJobStatus(Index index) {
            this.index = index;
        }
        
        public int progress() {
            return 100;
        }

        public String note() {
            return "Done, created index '" + index.name + "'.";
        }
    }
    
    /**
     * Specialized map implementation for string-to-array-of-IndexForDir mapping.
     */
    static class DirToIndexesMap extends HashMap<String, IndexForDir[]> {
        private static final long serialVersionUID = 1L;
        
        /**
         * Adds indexForDir to array for 'dir' key. If no array exists a one-long array
         * of IndexForDir is created and put to the Map.
         */
        void add(String dir, IndexForDir indexForDir) {
            IndexForDir[] array = get(dir);
            IndexForDir[] newArray;
            
            if (array == null) {
                newArray = new IndexForDir[] { indexForDir };
            } else {
                newArray = new IndexForDir[1 + array.length];
                newArray[0] = indexForDir;
                System.arraycopy(array, 0, newArray, 1, array.length);
            }
            put(dir, newArray);
        }
        
        public boolean assertHasIndexMappings(Index index) {
            for (int i = 0; i < index.dirs.length; i++) {
                String dir = index.dirs[i];
                IndexForDir[] array = this.get(dir);
                assert array != null;
                assert array.length > 0;
                
                boolean found = false;
                for (IndexForDir indexForDir : array) {
                    if (index.name.equals(indexForDir.index.name)) {
                        found = true;
                        break;
                    }
                }
                
                assert found : "index " + index.name + " not found.";
            }
            
            return true;
        }

        /**
         * Add all dir-to-Index mappings for 'index'.
         */
        void add(Index index) {
            for (int i = 0; i < index.dirs.length; i++) {
                IndexForDir indexForDir = new IndexForDir(index, i);
                add(index.dirs[i], indexForDir);
            }
        }
        
        /**
         * Removes dir-to-index mapping. If mapping does not exist, throws Bug.
         */
        void remove(String dir, String indexName) {
            IndexForDir[] array = get(dir);
            if (array == null) {
                throw new Bug("Map dirToIndex did not have mapping dir:'" 
                        + dir + "' -> index:'" + indexName + "'.");
            }
            
            if (array.length == 0) {
                throw new Bug("array.length == 0, index:'" + indexName + "'.");
            }
            
            int deleteIndex = -1;
            for (int i = 0; i < array.length; i++) {
                if (array[i].index.name.equals(indexName)) {
                    deleteIndex = i;
                    break;
                }
            }
            
            if (deleteIndex == -1) {
                throw new Bug("Bad state, dir = " + dir 
                        + ", but not fould in 'array'. Index name: " + indexName + ".");
            }
            
            if (array.length == 1) {
                remove(dir);
            } else {
                IndexForDir[] newArray = new IndexForDir[array.length - 1];
                int newIndex = 0;
                
                for (int i = 0; i < array.length; i++) {
                    if (i != deleteIndex) {
                        newArray[newIndex++] = array[i];
                    }
                }
                
                if (newIndex != newArray.length) {
                    throw new Bug("newIndex = " + newIndex + ", " + newArray.length);
                }
                
                put(dir, newArray);
            }
        }
        
        void remove(Index index) {
            for (String dir : index.dirs) {
                remove(dir, index.name);
            }
        }
    }
    
    public static class Tester {
        private Tester() {}
        
        @Nano
        public static void testIndexConstructor1() {
            IndexManager m = new IndexManager(new BergCollatorFactory());
            IndexManager.Index index = new Index("index1", new String[] {"d/testGetKey/"}, 
                    new String[][] {{"account"}, {"time"}}, new String[] {"long", "long"}, m);
            
            Assert.assertEquals(1, index.combinationCount);
        }
        
        @Nano
        public static void testIndexConstructor2() {
            IndexManager m = new IndexManager(new BergCollatorFactory());
            IndexManager.Index index = new Index("index1", new String[] {"d/testGetKey/"}, 
                    new String[][] {{"from", "to"}, {"time", "rTime"}}, new String[] {"long", "long"}, m);
            
            Assert.assertEquals(4, index.combinationCount);
            Assert.assertEquals(4, index.fieldCombinations.length);
            
            Assert.assertEquals("from", index.fieldCombinations[0][0]);
            Assert.assertEquals("time", index.fieldCombinations[0][1]);
            
            Assert.assertEquals("from", index.fieldCombinations[1][0]);
            Assert.assertEquals("rTime", index.fieldCombinations[1][1]);
            
            Assert.assertEquals("to", index.fieldCombinations[2][0]);
            Assert.assertEquals("time", index.fieldCombinations[2][1]);
            
            Assert.assertEquals("to", index.fieldCombinations[3][0]);
            Assert.assertEquals("rTime", index.fieldCombinations[3][1]);
        }
        
        @Nano
        public static void testCheckType1() {
            String[] types =     {"long", "double", "string", "a", "", "longs", "doublex", "string/"};
            boolean[] expected = {true,   true,     true,     false, false, false, false,  false};
            
            IndexManager m = new IndexManager(new BergCollatorFactory());
            
            for (int i = 0; i < types.length; i++) {
                Assert.assertEquals(expected[i], m.typeSupported(types[i]));
            }
        }
    }
    
    public static void main(String[] args) {
        Tester.testIndexConstructor2();
    }
}

/*

---- Virtual keys ----

Concept of "virtual" keys. KVs that does not really exist, but used for synch.
Corresponding data for the key can exist directly in memory as a Java object, not in the database.

Needed for indexing. Works like this for the indexing case.
- When index is added, the index info entry is added to the database in IKP/ii/.
- Virtual keys are also included in the add-index transaction for each directory the index applies to:
  vkey = IKP/iv/<dir>. This is not a real KV. Only hash(vkey) is added to Trans.writeKeyHashes.
  This is done in one atomic transaction.
- When an object is stored/deleted, IndexManager.getActiveIndexesForDir() is used to lookup the indexes for
  the directory. For this transaction, we will add hash(vkey) of the directory of the object
  to Trans.readKeyHashes.
- Note that this works even when directory has no indexes. We still have a readKeyHash for the 
  directory and can get transaction rerun in case an index is added while Connection.set(String, Object)
  is being executed.

*/