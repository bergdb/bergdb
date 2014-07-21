package bergdb.pubimp;

import java.util.Iterator;
import java.util.NoSuchElementException;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.GetMany.StopCondition;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.UseIndexBuilder;

/**
 * Creates an iterator to iterate indexed objects in the database.
 * 
 * @author Frans Lundberg
 */
public class UseIndexBuilderImp<TYPE> implements UseIndexBuilder<TYPE> {
    private static final byte[] emptyByteArray = new byte[0];
    private boolean builderDone;
    private final ConnectionImp connection;
    private byte[] startValue;
    private byte[] eqValue;
    private final long actualLookupTime;
    private final byte[] dir;
    private final boolean isPrimary;
    private final IndexManager.Index index;
    private final IndexManager indexManager;
    private boolean forward;
    private boolean inclusive;
    private boolean startAtCalled;
    private int level;              // The composite level we are at.
    private String prefixString;    // The prefix string set with prefix(String) method.
    private final boolean excludeNonObj;  // If true, non-object KVs are excluded from the result.
    private final Class<TYPE> type;
    
    // Level info for builder
    
    private boolean levelStartAtCalled = false;
    private boolean levelEqCalled = false;
    private boolean levelPrefixCalled = false;
    
    // Below fields used only after prepare()
    
    private long[] startKeySegments;
    private long[] prefixKeySegments;           // directory or index dir + EQ value.
    
    /**
     * @throws NoSuchIndexException if no index with the name exists.
     */
    public UseIndexBuilderImp(ConnectionImp connection, String indexName, Class<TYPE> type, 
            long wantedLookupTime) {
        assert connection != null;
        
        if (indexName == null) {
            throw new IllegalArgumentException("indexName == null not allowed");
        }
        
        this.type = type;
        this.connection = connection;
        this.builderDone = false;
        this.indexManager = connection.getDatabaseImp().getIndexManager();
        this.isPrimary = indexName.equals(IndexManager.PRIMARY);
        
        this.index = indexManager.getActiveIndex(connection, indexName, wantedLookupTime);
        if (isPrimary) {
            this.actualLookupTime = connection.getDb().getTimeForGet(wantedLookupTime);
        } else {
            this.actualLookupTime = connection.getActualLookupTime();
                // Returns the actual lookup time used in indexManager.getActiveIndex.
        }
        
        if (index == null) {
            throw new NoSuchIndexException("No index named: '" + indexName 
                    + "' at the given lookup time.");
        }
        
        if (index.getState() != IndexManager.Index.STATE_ACTIVE) {
            throw new NoSuchIndexException("Index is not active, but in state: " 
                    + index.getStateString() + ".");
        }
        
        final int typeOfType = Entries.classify(type);
        this.excludeNonObj = isPrimary && 
                (typeOfType == Entries.TYPE_ORDINARY || typeOfType == Entries.TYPE_DB_OBJECT);
        this.dir = isPrimary ? new byte[0] : IndexManager.getIndexDbDirAsBytes(indexName);
        
        this.forward = true;
        this.inclusive = true;
        this.level = 0;
        this.startAtCalled = false;
        this.startValue = emptyByteArray;
        this.eqValue = emptyByteArray;
    }
    
    public UseIndexBuilder<TYPE> inclusive(boolean inclusive) {
        this.inclusive = inclusive;
        return this;
    }
    
    /**
     * First index part EQ condition. Iterator will only return objects with 
     * <code>indexValue.equals(string)</code>.
     * 
     * @throws IllegalArgumentException if 'string' is null.
     * @throws IllegalStateException
     */
    public UseIndexBuilder<TYPE> eq(String string) {
        
        if (string == null) {
            throw new IllegalArgumentException("'string' == null not allowed");
        }
        
        if (startAtCalled) {
            throw new IllegalStateException("Cannot call eq() after startAt() has been called.");
        }
        
        if (levelEqCalled) {
            throw new IllegalStateException("Cannot call eq() more than once per composite level.");
        }
        
        if (levelPrefixCalled) {
            throw new IllegalStateException("Cannot call eq() after call to prefix() for " +
            		"same composite level.");
        }
        
        if (level > index.getLevels() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (index.types[level] != IndexManager.Index.TYPE_STRING) {
            throw new IllegalStateException("Index is not a string index, index type is: " 
                    + index.typeStrings[0] + ". Cannot call eq(String).");
        }
        
        byte[] toAdd = IndexManager.indexKeyPartFromString(index.kcollators[level], string);
        eqValue = Util.concat(eqValue, toAdd);
        
        levelEqCalled = true;
        return this;
    }

    public UseIndexBuilder<TYPE> eq(long value) {
        if (startAtCalled) {
            throw new IllegalStateException("Cannot call eq() after startAt() has been called.");
        }
        
        if (levelEqCalled) {
            throw new IllegalStateException("Cannot call eq() more than once per composite level.");
        }
        
        if (levelPrefixCalled) {
            throw new IllegalStateException("Cannot call eq() after call to prefix() for " +
                    "same composite level.");
        }
        
        if (level > index.getLevels() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (index.types[level] != IndexManager.Index.TYPE_LONG) {
            throw new IllegalStateException("Index is not a long index, index type is: " 
                    + index.typeStrings[0] + ". Cannot call eq(long).");
        }
        
        byte[] toAdd = IndexManager.indexKeyPartFromLong(value);
        eqValue = Util.concat(eqValue, toAdd);
        
        levelEqCalled = true;
        return this;
    }
    
    public UseIndexBuilder<TYPE> eq(double value) {
        if (startAtCalled) {
            throw new IllegalStateException("Cannot call eq() after startAt() has been called.");
        }
        
        if (levelEqCalled) {
            throw new IllegalStateException("Cannot call eq() more than once per composite level.");
        }
        
        if (levelPrefixCalled) {
            throw new IllegalStateException("Cannot call eq() after call to prefix() for " +
                    "same composite level.");
        }
        
        if (level > index.getLevels() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (index.types[level] != IndexManager.Index.TYPE_DOUBLE) {
            throw new IllegalStateException("Index is not a double index, index type is: " 
                    + index.typeStrings[0] + ". Cannot call eq(double).");
        }
        
        byte[] toAdd = IndexManager.indexKeyPartFromDouble(value);
        eqValue = Util.concat(eqValue, toAdd);
        
        levelEqCalled = true;
        return this;
    }
    
    public UseIndexBuilder<TYPE> startAt(String string) {
        // Appends bytes to startValue.
        
        if (string == null) {
            throw new IllegalArgumentException("'string' == null not allowed");
        }
        
        if (levelStartAtCalled) {
            throw new IllegalStateException("Cannot call startAt() more than once per composite level.");
        }
        
        if (levelEqCalled) {
            throw new IllegalStateException("Cannot call eq() more than once per composite level.");
        }
        
        if (level > index.getLevels() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (index.types[level] != IndexManager.Index.TYPE_STRING) {
            throw new IllegalStateException("Index is not a string index, index type is: " 
                    + index.typeStrings[0] + ". Cannot call startAt(String).");
        }
        
        if (prefixString != null) {
            // If prefixString set, 'string' is a suffix to prefixString.
            string = prefixString + string;
        }
        
        startValue = Util.concat(startValue, 
                IndexManager.indexKeyPartFromString(index.kcollators[level], string));        
        startAtCalled = true;
        levelStartAtCalled = true;
        return this;
    }
    
    public UseIndexBuilder<TYPE> startAt(long value) {
        // Appends bytes to startValue.
        
        if (levelStartAtCalled) {
            throw new IllegalStateException("Cannot call startAt() more than once per composite level.");
        }
        
        if (levelEqCalled) {
            throw new IllegalStateException("Cannot call eq() more than once per composite level.");
        }
        
        if (level > index.getLevels() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (index.types[level] != IndexManager.Index.TYPE_LONG) {
            throw new IllegalStateException("Index is not a long index, index type is: " 
                    + index.typeStrings[0] + ". Cannot call startAt(long).");
        }
        
        startValue = Util.concat(startValue, IndexManager.indexKeyPartFromLong(value));        
        startAtCalled = true;
        levelStartAtCalled = true;
        
        return this;
    }
    
    public UseIndexBuilder<TYPE> startAt(double value) {
        // Appends bytes to startValue.
        
        if (levelStartAtCalled) {
            throw new IllegalStateException("Cannot call startAt() more than once per composite level.");
        }
        
        if (levelEqCalled) {
            throw new IllegalStateException("Cannot call eq() more than once per composite level.");
        }
        
        if (level > index.getLevels() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (index.types[level] != IndexManager.Index.TYPE_DOUBLE) {
            throw new IllegalStateException("Index is not a double index, index type is: " 
                    + index.typeStrings[0] + ". Cannot call startAt(double).");
        }
        
        startValue = Util.concat(startValue, IndexManager.indexKeyPartFromDouble(value));        
        startAtCalled = true;
        levelStartAtCalled = true;
        
        return this;
    }
    
    public UseIndexBuilderImp<TYPE> nextLevel() {
        int newLevel = level + 1;
        if (newLevel >= index.getLevels()) {
            throw new IllegalStateException("Cannot increase composite level to " + newLevel
                    + ", number of levels: " + index.getLevels() + ".");
        }
        
        if (this.prefixString != null) {
            throw new IllegalStateException("Cannot go to next composite level, " +
            		"prefix() has been called.");
        }
        
        this.levelEqCalled = false;
        this.levelStartAtCalled = false;
        this.levelPrefixCalled = false;
        level = newLevel;
        
        return this;
    }
    
    public UseIndexBuilder<TYPE> prefix(String prefix) {
        if (prefix == null) {
            throw new IllegalArgumentException("'prefix' == null not allowed");
        }
        
        if (prefix.length() == 0) {
            throw new IllegalArgumentException("empty string for 'prefix' not allowed");
        }
        
        if (levelEqCalled) {
            throw new IllegalStateException("Cannot call eq() and prefix() for same composite level.");
        }
        
        if (levelPrefixCalled) {
            throw new IllegalStateException("Cannot call prefix() more than once.");
        }
        
        if (prefixString != null) {
            throw new IllegalStateException("Cannot call prefix() method more than once.");
        }
        
        if (level >= index.getLevels()) {
            throw new IllegalStateException("Cannot call prefix() at composite level " + level 
                    + ".");
        }
        
        if (index.types[level] != IndexManager.Index.TYPE_STRING) {
            throw new IllegalStateException("Index is not a string index, index type is: " 
                    + index.typeStrings[0] + ". Cannot call prefix(String).");
        }
        
        this.prefixString = prefix;
        
        return this;
    }
    
    public UseIndexBuilder<TYPE> backward() {
        this.forward = false;
        return this;
    }
    
    /**
     * Prepares builder object for returning iterator.
     */
    private void prepare() {
        // Dev note: note that non-primary index entries contains object key name, not only 
        // indexed value. So exact matches (GetData.includeEQ = true) with startValue do not 
        // make sense for this case.
        
        byte[] dirBytes = dir;
        byte[] eqBytes = Util.concat(dirBytes, eqValue);
        byte[] startBytes = Util.concat(eqBytes, startValue);
        byte[] prefixBytes;
        
        if (this.prefixString == null) {
            prefixBytes = eqBytes;
        } else {
            prefixBytes = Util.concat(eqBytes, index.kcollators[level].getSortBytes(prefixString));
        }
        
        prefixKeySegments = Keys.toSegments(prefixBytes);
        
        if (isPrimary) {
            // include = true allowed for this case.
            // If we have no start value but a prefix string, we set startValue according to 
            // prefix.
            
            if (prefixString != null && startValue.length == 0) {
                startBytes = prefixBytes.clone();
                
                if (forward == false) {
                    plusOne(startBytes);
                }
            }
            
            
        } else {
            if (forward) {
                if (inclusive) {
                    // empty
                } else {
                    plusOne(startBytes);
                }
            } else {
                if (inclusive) {
                    plusOne(startBytes);
                } else {
                    // empty
                }
            }
            
            inclusive = true;    // We never work with exact matches for secondary indexes.
        }
        
        startKeySegments = Keys.toSegments(startBytes);
    }
    
    private static void plusOneArray(byte[] bytes) {
        assert bytes != null;
        
        for (int i = bytes.length - 1; i >= 0; i--) {
            int value = 0xff & bytes[i];
            if (value < 255) {
                bytes[i] = (byte) (value + 1);
                for (int j = i + 1; j < bytes.length; j++) {
                    bytes[j] = 0;
                }
                break;
            }
            
            if (i == 0) {
                // No solution!
                // Should never happen for key with directory. Always contains '/'.
                throw new IllegalArgumentException("Cannot do plusOneArray on array than only " +
                		"contains ff bytes, " + bytes.length + ".");
            }
        }
    }
    
    /**
     * Changes 'bytes' in-place so it is the smallest key that is greater than all keys that 
     * has input 'bytes' as a prefix.
     */
    private static void plusOne(byte[] bytes) {
        assert bytes != null;
        assert bytes.length > 0;
        
        boolean handled = false;
        
        for (int i = bytes.length - 1; i >= 0; i--) {
            int value = 0xff & bytes[i];
            if (value != 0xff) {
                bytes[i] = (byte) (value + 1);
                handled = true;
                break;
            }
        }
        
        if (!handled) {
            if (bytes.length == 0) {
                throw new IllegalArgumentException("Array 'bytes' is empty.");
            } else {
                throw new IllegalArgumentException("Array 'bytes' consists of only byte values 255.");
            }
        }
    }
    
    /**
     * @see bergdb.pub.UseIndexBuilder#objects()
     */
    public Iterable<TYPE> objects() {
        if (builderDone) {
            throw new IllegalStateException("This object should not be used again.");
        }
        builderDone = true;
        
        prepare();
        
        return new Iterable<TYPE>() {
            public Iterator<TYPE> iterator() {
                return new Iterator<TYPE>() {
                    private final Iterator<Kv<TYPE>> iter = new IndexIterator(actualLookupTime, excludeNonObj);
                    
                    public final boolean hasNext() {
                        return iter.hasNext();
                    }

                    public final TYPE next() throws NoSuchElementException {
                        assert iter != null;
                        final Kv<TYPE> next = iter.next();
                        assert next != null : "next is null";
                            // 'next' should never be null, if no more elements, next() throws 
                            // NoSuchElementException.
                        return (TYPE) next.value();
                    }

                    public void remove() {
                        throw new UnsupportedOperationException();
                    }
                };
            }
        };
    }
    
    public Iterable<Kv<TYPE>> kvs() {
        if (builderDone) {
            throw new IllegalStateException("This object should not be used again.");
        }
        builderDone = true;
        
        prepare();
        
        return new Iterable<Kv<TYPE>>() {
            public Iterator<Kv<TYPE>> iterator() {
                final Iterator<Kv<TYPE>> iter = new IndexIterator(actualLookupTime, excludeNonObj);
                
                return new Iterator<Kv<TYPE>>() {
                    public boolean hasNext() {
                        return iter.hasNext();
                    }

                    public Kv<TYPE> next() {
                        Kv<TYPE> result = (Kv<TYPE>) iter.next();
                        assert result != null : "result is null";
                        return result;
                    }

                    public void remove() {
                        throw new UnsupportedOperationException();
                    }
                };
            }
        };
    }

    private class IndexIterator implements Iterator<Kv<TYPE>> {
        private GetMany g;
        private boolean gotEod = false;
        private int resultIndex = -1;
        private long[] startKey;
        private boolean done = false;
        private boolean firstBatch = true;
        private final IndexManager.Index index;
        private final long wantedLookupTime;
        private long actualLookupTime = -1;
        private final boolean forward;
        private final boolean inclusive2;
        private final boolean excludeNonObj;
        
        public IndexIterator(long wantedLookupTime, boolean excludeNonObj) {
            this.startKey = UseIndexBuilderImp.this.startKeySegments;            
            this.index = UseIndexBuilderImp.this.index;
            assert this.index != null;
            this.wantedLookupTime = wantedLookupTime;
            this.forward = UseIndexBuilderImp.this.forward;
            this.inclusive2 = UseIndexBuilderImp.this.inclusive;
            this.excludeNonObj = excludeNonObj;
        }
        
        private void getMany() {
            assert connection != null : "connection is null";
            assert connection.getDb() != null : "DB is null";
            
            IterStopCondition stopCondition = new IterStopCondition(excludeNonObj);
            
            g = new GetMany();
            g.startKey = this.startKey;
            g.forward = forward;
            g.inclusive = firstBatch ? inclusive2 : false;
            g.stopCondition = stopCondition;
            g.lookupTime = firstBatch ? wantedLookupTime : actualLookupTime;
            
            assert g.lookupTime >= 0;
            connection.getDb().getMany(g);
            this.gotEod = stopCondition.gotEod();
            
            if (g.result.size() > 0) {
                this.startKey = g.result.get(g.result.size() - 1).key;
            }
            
            if (firstBatch) {
                actualLookupTime = g.actualLookupTime;
                firstBatch = false;
            }
        }

        public boolean hasNext() {
            if (done) {
                return false;
            }
            
            if (resultIndex == -1) {
                getMany();
                if (g.result.size() == 0) {
                    done = true;
                } else {
                    resultIndex = 0;
                }
            }
            return !done;
        }

        /**
         * @throws NoSuchElementException if there are no more elements to iterate.
         */
        public Kv<TYPE> next() {
            byte[] value;
            byte[] objectKey;
            
            A: while (true) {           // Used for "continue A;"
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                
                final Kvt kvt = g.result.get(resultIndex);
                if (isPrimary) {
                    objectKey = Keys.toBytes(kvt.key);
                    value = kvt.value;
                } else {
                    objectKey = IndexManager.getObjectKey(index, kvt.key);
                    assert actualLookupTime >= 0;
                    value = connection.getBytesAtLookupTime(actualLookupTime, Keys.toSegments(objectKey));
                }
                
                resultIndex++;
                if (resultIndex == g.result.size()) {
                    if (gotEod) {
                        done = true;
                    } else {
                        resultIndex = -1;
                    }
                }
                
                if (value == null) {        
                    // We have a stale index entry, ignore it. It should be removed.
                    continue A;
                }
                
                break;
            }
            
            final String ikey = Keys.toString(objectKey);
            
            String ukey;
            try {
                ukey = PubKeys.i2u(ikey);
            } catch (IllegalArgumentException e) {
                ukey = null;
            }
            final String finalUkey = ukey;
            
            final TYPE finalObject = connection.getDatabaseImp()
                    .getKvToObject().createObject(type, ikey, value);
            
            assert finalObject != null : "finalObject is null";
            
            return new Kv<TYPE>() {
                public String key() {
                    return finalUkey;
                }
                
                public String ikey() {
                    return ikey;
                }
                
                public TYPE value() {
                    return finalObject;
                }
            };
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
    
    /**
     * Max 100 KVs, max 1.0 sec, max 50M total data, within prefix.
     */
    private class IterStopCondition implements GetMany.StopCondition {
        private final long[] stopConditionPrefix = UseIndexBuilderImp.this.prefixKeySegments;
        private static final int maxCount = 100;
        private static final int maxData = 50*1000000;
        private static final long maxNanos = 1 * 1000000000L;
        private boolean isFirst;
        private long t0;
        private int count = 0;
        private boolean gotEod = false;
        private long data = 0;
        private final boolean excludeNonObj;
        
        public IterStopCondition(boolean excludeNonObj) {
            isFirst = true;
            gotEod = false;
            this.excludeNonObj = excludeNonObj;
        }
        
        public int handleKvt(Kvt kvt) {
            if (isFirst) {
                t0 = System.nanoTime();
                isFirst = false;
            }
            
            int result = StopCondition.ADD;     // default result
            count++;
            data += kvt.key.length * 8 + (kvt.value == null ? 0 : kvt.value.length);
            long nanos = System.nanoTime() - t0;
            
            if (!Keys.isPrefix(stopConditionPrefix, kvt.key)) {
                result = GetMany.StopCondition.STOP;
                return result;
            }
            
            if (count >= maxCount || data > maxData || nanos > maxNanos) {
                result = GetMany.StopCondition.ADD_AND_STOP;
            }
            
            if (excludeNonObj) {
                boolean isObject = Entries.isProbablyDbObject(Keys.toString(kvt.key), kvt.value);
                
                if (!isObject) {
                    if (result == GetMany.StopCondition.ADD) {
                        result = GetMany.StopCondition.CONTINUE;
                    } else if (result == GetMany.StopCondition.ADD_AND_STOP) {
                        result = GetMany.StopCondition.STOP;
                    } else {
                        throw new Bug("Unexpected state, " + result);
                    }
                }
            }
        
            return result;
        }

        public void eod() {
            gotEod = true;
        }
        
        public final boolean gotEod() {
            return gotEod;
        }
    }
    
    // ============== Tests =============
    
    @T
    public static void testPlusOne1() {
        byte[] bytes = {1, 2, '/'};
        plusOne(bytes);
        Assert.assertArrayEquals(new byte[]{1, 2, '/' + 1}, bytes);
    }
    
    @T
    public static void testPlusOneArray1() {
        byte[] bytes = {1, 2, 3};
        plusOneArray(bytes);
        Assert.assertArrayEquals(new byte[]{1, 2, 4}, bytes);
    }
    
    @T
    public static void testPlusOneArray2() {
        byte[] bytes = {1, 2, (byte) 0xff};
        plusOneArray(bytes);
        Assert.assertArrayEquals(new byte[]{1, 3, 0}, bytes);
    }
    
    @T
    public static void testPlusOneArray3() {
        byte[] bytes = {1, (byte) 0xff, (byte) 0xff};
        plusOneArray(bytes);
        Assert.assertArrayEquals(new byte[]{2, 0, 0}, bytes);
    }
    
    @T
    public static void testPlusOneArray4() {
        byte[] bytes = {(byte) 0xff, (byte) 0xff, (byte) 0xff};
        Throwable ex = null;
        try {
            plusOneArray(bytes);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        Assert.assertTrue(ex != null);
    }
}
