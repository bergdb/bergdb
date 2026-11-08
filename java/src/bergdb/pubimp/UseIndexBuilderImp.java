package bergdb.pubimp;

import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.GetMany.StopCondition;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.Time;
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
    private final byte[] dir;               // The prefix of the generation's entries
    private final IndexDefinition def;
    private boolean forward;
    private boolean inclusive;
    private boolean startAtCalled;
    private int level;              // The composite level we are at.
    private String prefixString;    // The prefix string set with prefix(String) method.
    private final Class<TYPE> type;
    
    // Level info for builder
    
    private boolean levelStartAtCalled = false;
    private boolean levelEqCalled = false;
    private boolean levelPrefixCalled = false;
    
    // Below fields used only after prepare()
    
    private long[] startKeySegments;
    private long[] prefixKeySegments;           // directory or index dir + EQ value.
    
    /**
     * The definition is read at the lookup time, resolved at this call (bergdb 020-10, section
     * 3.6), with IndexDefinition.read; the keys are IndexKeys' (section 4.4). The grammar is
     * 2026.3's, which step I3 replaces.
     * 
     * @throws NoSuchIndexException  If there is no index of the name at the lookup time, or it
     *      is building then.
     * @throws ObjectCreationException  If 'type' is not a class a get takes (bergdb 020-09,
     *      section 3.3), whatever the data.
     */
    public UseIndexBuilderImp(ConnectionImp connection, String indexName, Class<TYPE> type, 
            long wantedLookupTime) {
        assert connection != null;
        
        if (indexName == null) {
            throw new IllegalArgumentException("indexName == null not allowed");
        }
        if (!type.equals(String.class) && !type.equals(byte[].class)
                && !type.equals(DbObject.class) && !type.equals(Object.class)) {
            DataObjects.checkGet(type);
        }
        
        this.type = type;
        this.connection = connection;
        this.builderDone = false;
        this.actualLookupTime = connection.scanLookupTime(wantedLookupTime);
        this.def = IndexDefinition.read(connection.getDb(), indexName, actualLookupTime);
        if (def == null) {
            throw new NoSuchIndexException("No index named '" + indexName + "' at the lookup "
                    + "time.");
        }
        if (!def.isActive()) {
            throw new NoSuchIndexException("The index '" + indexName + "' is building at the "
                    + "lookup time.");
        }
        this.dir = def.generationPrefix();
        
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
        
        if (level > def.levelCount() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (def.type(level) != IndexKeys.STRING) {
            throw new IllegalStateException("Index is not a string index, index type is: " 
                    + def.typeName(level) + ". Cannot call eq(String).");
        }
        
        byte[] toAdd = IndexKeys.encodeString(string);
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
        
        if (level > def.levelCount() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (def.type(level) != IndexKeys.LONG) {
            throw new IllegalStateException("Index is not a long index, index type is: " 
                    + def.typeName(level) + ". Cannot call eq(long).");
        }
        
        byte[] toAdd = IndexKeys.encodeLong(value);
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
        
        if (level > def.levelCount() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (def.type(level) != IndexKeys.DOUBLE) {
            throw new IllegalStateException("Index is not a double index, index type is: " 
                    + def.typeName(level) + ". Cannot call eq(double).");
        }
        
        byte[] toAdd = IndexKeys.encodeDouble(value);
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
        
        if (level > def.levelCount() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (def.type(level) != IndexKeys.STRING) {
            throw new IllegalStateException("Index is not a string index, index type is: " 
                    + def.typeName(level) + ". Cannot call startAt(String).");
        }
        
        if (prefixString != null) {
            // If prefixString set, 'string' is a suffix to prefixString.
            string = prefixString + string;
        }
        
        startValue = Util.concat(startValue, 
                IndexKeys.encodeString(string));        
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
        
        if (level > def.levelCount() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (def.type(level) != IndexKeys.LONG) {
            throw new IllegalStateException("Index is not a long index, index type is: " 
                    + def.typeName(level) + ". Cannot call startAt(long).");
        }
        
        startValue = Util.concat(startValue, IndexKeys.encodeLong(value));        
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
        
        if (level > def.levelCount() - 1) {
            throw new IllegalStateException("Illegal composite level " + level 
                    + ".");
        }
        
        if (def.type(level) != IndexKeys.DOUBLE) {
            throw new IllegalStateException("Index is not a double index, index type is: " 
                    + def.typeName(level) + ". Cannot call startAt(double).");
        }
        
        startValue = Util.concat(startValue, IndexKeys.encodeDouble(value));        
        startAtCalled = true;
        levelStartAtCalled = true;
        
        return this;
    }
    
    public UseIndexBuilderImp<TYPE> nextLevel() {
        int newLevel = level + 1;
        if (newLevel >= def.levelCount()) {
            throw new IllegalStateException("Cannot increase composite level to " + newLevel
                    + ", number of levels: " + def.levelCount() + ".");
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
        
        if (level >= def.levelCount()) {
            throw new IllegalStateException("Cannot call prefix() at composite level " + level 
                    + ".");
        }
        
        if (def.type(level) != IndexKeys.STRING) {
            throw new IllegalStateException("Index is not a string index, index type is: " 
                    + def.typeName(level) + ". Cannot call prefix(String).");
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
            prefixBytes = Util.concat(eqBytes, IndexKeys.encodeStringPrefix(prefixString));
        }
        
        prefixKeySegments = Keys.toSegments(prefixBytes);
        
        {
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
                // 2026-10-21 (bergdb 005-15): the 0xff bytes carried past become 0. They
                // were kept, so {.., 0x00, 0xff} became {.., 0x01, 0xff}, not {.., 0x01,
                // 0x00}: a long index skipped entries after startAt(255) exclusive.
                for (int j = i + 1; j < bytes.length; j++) {
                    bytes[j] = 0;
                }
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
                    private final Iterator<Kv<TYPE>> iter = new IndexIterator(actualLookupTime);
                    
                    public final boolean hasNext() {
                        return iter.hasNext();
                    }

                    public final TYPE next() throws NoSuchElementException {
                        assert iter != null;
                        final Kv<TYPE> next = iter.next();
                        assert next != null : "next is null";
                            // 'next' should never be null, if no more elements, next() throws 
                            // NoSuchElementException.
                        return next.value();
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
                final Iterator<Kv<TYPE>> iter = new IndexIterator(actualLookupTime);
                
                return new Iterator<Kv<TYPE>>() {
                    public boolean hasNext() {
                        return iter.hasNext();
                    }

                    public Kv<TYPE> next() {
                        Kv<TYPE> result = iter.next();
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
        private boolean endedAtLimit = false;
        private int resultIndex = -1;
        private long[] startKey;
        private boolean done = false;
        private boolean firstBatch = true;
        private final long wantedLookupTime;
        private long actualLookupTime = -1;
        private final boolean forward;
        private final boolean inclusive2;
        
        public IndexIterator(long wantedLookupTime) {
            this.startKey = UseIndexBuilderImp.this.startKeySegments;            
            this.wantedLookupTime = wantedLookupTime;
            this.forward = UseIndexBuilderImp.this.forward;
            this.inclusive2 = UseIndexBuilderImp.this.inclusive;
        }
        
        private void getMany() {
            assert connection != null : "connection is null";
            assert connection.getDb() != null : "DB is null";
            
            IterStopCondition stopCondition = new IterStopCondition();
            
            g = connection.getDb().newGetMany();
            g.startKey = this.startKey;
            g.forward = forward;
            g.inclusive = firstBatch ? inclusive2 : false;
            g.stopCondition = stopCondition;
            g.lookupTime = firstBatch ? wantedLookupTime : actualLookupTime;
            
            assert g.lookupTime >= 0;
            connection.getDb().getMany(g);
            this.gotEod = stopCondition.gotEod();
            this.endedAtLimit = stopCondition.endedAtLimit();
            
            if (stopCondition.lastKey() != null) {
                this.startKey = stopCondition.lastKey();
                    // The last entry visited, returned or filtered out (bergdb 015-20).
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
            
            while (resultIndex == -1) {
                getMany();
                if (g.result.size() > 0) {
                    resultIndex = 0;
                } else if (!endedAtLimit) {
                    done = true;
                    break;
                }
                // Else a limit ended the page on entries filtered out, not the end of the
                // range: the next page starts after them (bergdb 015-20).
            }
            return !done;
        }

        /**
         * @throws NoSuchElementException if there are no more elements to iterate.
         */
        public Kv<TYPE> next() {
            byte[] value;
            String ikey;
            
            A: while (true) {           // Used for "continue A;"
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                
                // The entry's key: its generation's prefix, its levels, K (020-10, 4.4).
                final Kvt kvt = g.result.get(resultIndex);
                IndexKeys.Entry entry = IndexKeys.parseEntry(Keys.toBytes(kvt.key), dir,
                        def.types());
                ikey = def.idir() + entry.fileName();
                assert actualLookupTime >= 0;
                value = connection.getBytesAtLookupTime(actualLookupTime, Keys.toSegments(ikey));
                
                resultIndex++;
                if (resultIndex == g.result.size()) {
                    if (gotEod) {
                        done = true;
                    } else {
                        resultIndex = -1;
                    }
                }
                
                // A stale entry gives no result: the value at its key must have it as its
                // entry (020-10, section 3.4).
                byte[] levels = value == null ? null : def.entryLevels(ikey, value);
                if (levels == null || !Arrays.equals(levels, entry.levels())) {
                    continue A;
                }
                
                break;
            }
            
            final String finalIkey = ikey;
            
            String ukey;
            try {
                ukey = PubKeys.i2u(ikey);
            } catch (IllegalArgumentException e) {
                ukey = null;
            }
            final String finalUkey = ukey;
            
            // Null for a type whose get gives null for this value, as a get of a primitive's
            // wrapper over an object without the field p (bergdb 020-09, section 5.9).
            final TYPE finalObject = connection.getDatabaseImp()
                    .getKvToObjectConverter().createObject(type, ikey, value);
            
            return new Kv<TYPE>() {
                public String key() {
                    return finalUkey;
                }
                
                public String ikey() {
                    return finalIkey;
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
        private long[] lastKey = null;      // The last entry visited within the prefix.
        private boolean endedAtLimit = false;
        
        public IterStopCondition() {
            isFirst = true;
            gotEod = false;
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
            
            lastKey = kvt.key;
            
            if (count >= maxCount || data > maxData || nanos > maxNanos) {
                result = GetMany.StopCondition.ADD_AND_STOP;
                endedAtLimit = true;
            }
            
            return result;
        }

        public void eod() {
            gotEod = true;
        }
        
        public final boolean gotEod() {
            return gotEod;
        }
        
        /**
         * True if a limit ended the page, false if the end of the prefix or of the
         * database did. A page that a limit ended can be empty, all its entries filtered
         * out (bergdb 015-20).
         */
        public final boolean endedAtLimit() {
            return endedAtLimit;
        }
        
        /** The key of the last entry visited within the prefix, or null. */
        public final long[] lastKey() {
            return lastKey;
        }
    }
    
    // ============== Tests =============
    
    @Nano
    public static void testPlusOne1() {
        byte[] bytes = {1, 2, '/'};
        plusOne(bytes);
        Assert.assertArrayEquals(new byte[]{1, 2, '/' + 1}, bytes);
    }
    
    /** Regression test for 005-15: the 0xff bytes carried past become 0. */
    @Nano
    public static void testPlusOneCarry() {
        byte[] bytes = {1, 0, (byte) 0xff};
        plusOne(bytes);
        Assert.assertArrayEquals(new byte[]{1, 1, 0}, bytes);
        
        bytes = new byte[]{0x7f, (byte) 0xff, (byte) 0xff};
        plusOne(bytes);
        Assert.assertArrayEquals(new byte[]{(byte) 0x80, 0, 0}, bytes);
    }
    
    @Nano
    public static void testPlusOneArray1() {
        byte[] bytes = {1, 2, 3};
        plusOneArray(bytes);
        Assert.assertArrayEquals(new byte[]{1, 2, 4}, bytes);
    }
    
    @Nano
    public static void testPlusOneArray2() {
        byte[] bytes = {1, 2, (byte) 0xff};
        plusOneArray(bytes);
        Assert.assertArrayEquals(new byte[]{1, 3, 0}, bytes);
    }
    
    @Nano
    public static void testPlusOneArray3() {
        byte[] bytes = {1, (byte) 0xff, (byte) 0xff};
        plusOneArray(bytes);
        Assert.assertArrayEquals(new byte[]{2, 0, 0}, bytes);
    }
    
    @Nano
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
