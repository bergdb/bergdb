package bergdb.core;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.TreeMap;

import bergdb.common.StringUtil;
import bergdb.core.Db.ExecuteData;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.dag.Spos;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Data for executing a transaction. Input, output and some working data.
 * The KVs of the transaction are defined in this class; the transaction description.
 * This class is defined in the most preferred, most efficient form for the Db class, 
 * not for the client using Db; it is not especially user-friendly.
 * 
 * To save memory allocation costs, a Trans object may be reused for multiple 
 * transactions run by the same thread. This is however only recommended when 
 * there is a significant performance benefit of doing so.
 * 
 * @author Frans Lundberg
 */
public class Trans {
    //
    // We might want to add a size limitation to the transactions.
    // It can easily be enforced in the Builder.
    //
    // Note. It would be good for memory reuse possibilities to use array+size approach.
    // For example; have long[] readKeyHashes *and* int readKeyHashesLength.
    // We would be able to reuse Trans object memory.
    // 
    // Startup transaction rerun does not use this class.
    //
    
    private static final Kv[] EMPTY_KV_ARRAY = new Kv[0];
    private static final Comparator<long[]> ARRAY_COMPARATOR = new Comparator<long[]>() {
        public int compare(long[] a1, long[] a2) {
            return Keys.compareArrays(a1, a2);
        }
    };
    
    // -- Input --
    
    public Kv[] kvs;
    public long[] writeKeyHashes;   // Precomputed hashes of keys to set. May be longer than 
                                    // kvs.length due to virtual KVs.
    public long readTime;           // Time when keys were read.
    public long[] readKeyHashes;    // Hashes of keys read. May include hashes of virtual KVs.
    
    // -- Output --
    
    /**
     * The transaction's time, set by Db.execute(): a database time (clock units), later than
     * every transaction's before it; a read at it or later sees the transaction (Db,
     * "Threads"). The only way to learn the time of a transaction that a Db executes.
     */
    public long tt;
    
    /**
     * The stream position of the transaction's first byte, set by Db.execute():
     * Db.getTrans(tpos) reads the transaction back.
     */
    public long tpos;
    
    /**
     * The stream position of the transaction's last byte, its commit byte, set by
     * Db.execute(): Db.sync(lastPos, level) waits until the transaction is durable.
     */
    public long lastPos;
    
    /**
     * The stream position after the transaction, lastPos + 1, set by Db.execute(): the
     * stream's length when it was committed.
     */
    public long nextPos;
    
    public int nodeCount;           // Number of nodes written to stream. Useful for testing/debug.
    public Listener listener;       // Low-level listener, for development/debugging typically.

    // -- Other --
    
    /** True if transaction is executed on behalf of the database itself. */
    boolean isInternal;
    
    /**
     * For internal transactions of reclaim, its steps (2026-10-13): before the puts, the
     * writer visits the index nodes on the path of each of the transaction's keys at the
     * transaction time, as the put of the key will, so that each of them gets dirty and is
     * counted (dirtiedNodes, dirtiedBytes) before the step's row is put, and stays dirty also
     * if the puts then replace it (Db.touchPaths, Db.endOfTrans). Until bergdb 024-07 the
     * touch visited a key range, touchFrom to touchTo.
     * Not stored: startup rebuilds D from the stored got-dirty ids.
     */
    boolean touch;
    
    /**
     * For a transaction with touch (2026-10-13, bergdb 011-04, "Level 3 cost"):
     * the index nodes it makes dirty, by the puts and the touch, and their size in the
     * stream when they got dirty, so far; a value transformation can store them.
     */
    long dirtiedNodes;
    long dirtiedBytes;

    /**
     * Statistics of the touch, or null (2026-10-13, measurements of reclaim): the
     * index nodes it visits and makes dirty, and of those, the ones stored before
     * touchOldBefore and their ancestors. See Reclaim.Stats.
     */
    Reclaim.TouchCount touchCount;
    long touchOldBefore;

    /** startupPos stored in stream with transaction. */
    public long startupPos = Spos.NULL;
    
    /** GetData for Db.warmup() method. */
    WarmupGetData warmupGetData;
    
    /**
     * The GetData of a transaction's warmup (Db.warmup), a class of its own so that the load
     * listener tells a warmup's load from a reader's by its type (bergdb 005-52, option B: a
     * warmup's load does not wait for eviction; Eviction.afterLoad).
     */
    static final class WarmupGetData extends GetData {}
    
    /**
     * Private constructor, use the builder: new Trans.Builder().
     */
    private Trans() {
        readKeyHashes = new long[0];
        listener = Listener.DO_NOTHING;
    }
    
    public boolean isInternal() {
        return isInternal;
    }
    
    public String toString() {
        String s = "tt:" + tt + ", pos:" + tpos;
        s = isInternal ? s + ", internal" : s;
        return s;
    }
    
    
    
    /**
     * Listens to what happens to a transaction; suitable for testing.
     */
    public static interface Listener {
        /**
         * The default trans listener that does nothing. 
         * The object can be shared freely, it is thread-safe.
         */
        public static final Listener DO_NOTHING = new Listener() {
            public final void transExecuted(ExecuteData x) {}
            public final void valueNodeCreated(ValueNode node, long[] key) {}
        };
        
        /**
         * Reports that a transaction was executed.
         * The x object is owned by the caller; it must not
         * be modified by the callee. Also, it is mutable.
         */
        public void transExecuted(Db.ExecuteData x);

        public void valueNodeCreated(ValueNode node, long[] key);
    }
    
    /**
     * Used to create a transaction.
     * A value's array is not copied: once put, it is the database's, and the caller must not
     * change it; the value in memory is that array. The Pub API copies a byte[] value at
     * its put (bergdb 015-47).
     * 
     * <p>A Builder is for one thread at a time. Of the calls on one key, the transaction
     * keeps one operation, the last one, a put or a delete (build()): a delete after a put
     * deletes, a put after a delete puts, as a batch of most embedded stores. Until release
     * 2026.4 a delete never replaced a put, whatever their order (bergdb 015-40; 020-24-09,
     * U9-12; changed by 024-10). The keys and values: Db's "Keys and values"; the read time
     * and the keys read: Db's "Optimistic transactions".</p>
     * <p>A null key, value, read key or hash array is refused with IllegalArgumentException,
     * and nothing is added (bergdb 020-27, Q2: a null key threw NullPointerException, or
     * AssertionError with -ea, and delete((long[]) null) was taken, so that build() threw);
     * delete() removes a key's value.</p>
     */
    public static class Builder {
        // Note This class does not enforce uniqueness of elements in keyReadSet, kvs, vkeyHashes.
        
        private long builderLookupTime;
        private ArrayList<Kv> kvs;
        private ArrayList<Long> readHashes;    // hashes of keys read.
        private ArrayList<Long> virtualWriteHashes;    // virtual key hashes for virtual writes
        private WarmupGetData warmupGetData;
        
        public Builder() {
            kvs = new ArrayList<Kv>();
            readHashes = new ArrayList<Long>();
            virtualWriteHashes = new ArrayList<Long>();
            builderLookupTime = Long.MAX_VALUE;

            warmupGetData = new WarmupGetData();
            warmupGetData.pointerListener = Dag.DO_NOTHING_POINTER_LISTENER;        
            // As a get's: a value over 1 MiB is not kept (Eviction's admission). Until bergdb
            // 019-22, CACHE_ALL: the warmup put a key's old large value into its leaf.
            warmupGetData.cachePolicy = Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES;
        }
        
        /**
         * Puts the value at the key, both arrays of bytes; the empty array is a value, and
         * so is an empty key (Db, "Keys and values").
         * 
         * @throws IllegalArgumentException  If key or value is null; for a null value, delete()
         *      deletes.
         */
        public Builder put(byte[] key, byte[] value) {
            checkKey(key);
            checkValue(value);
            kvs.add(new Kv(Keys.toSegments(key), value));
            return this;
        }
        
        /**
         * As put(byte[], byte[]) with the key as segments (Keys.toSegments()).
         * 
         * @throws IllegalArgumentException  If key or value is null, or the key has no segment;
         *      for a null value, delete() deletes.
         */
        public Builder put(long[] key, byte[] value) {
            checkSegments(key);
            checkValue(value);
            kvs.add(new Kv(key, value));
            return this;
        }
        
        /**
         * Puts the value at the key, with a key transformation and a value transformation,
         * each null for none.
         * 
         * @throws IllegalArgumentException  If key or value is null, or the key has no segment.
         */
        public Builder put(long[] key, KeyTransformation kt, byte[] value, ValueTransformation vt) {
            checkSegments(key);
            checkValue(value);
            Kv kv = new Kv(key, value, kt, vt);
            kvs.add(kv);
            return this;
        }
        
        /**
         * Puts the value's UTF-8 bytes at the key's bkey (Keys.toBytes()). The key and the
         * value are Unicode text, stored as well-formed UTF-8 (bergdb 021-04, 021-05).
         *
         * @throws IllegalArgumentException  If the key or the value has a lone surrogate, a
         *      char of U+D800 to U+DFFF that is not part of a surrogate pair: UTF-8 cannot
         *      hold it, and its encoding would write '?' (bergdb 021-05). If key or value is
         *      null, or the key is empty (Keys.toBytes()).
         */
        public Builder put(String key, String value) {
            checkKey(key);
            checkValue(value);
            if (StringUtil.hasLoneSurrogate(value)) {
                throw new IllegalArgumentException("The value has a lone surrogate, a char "
                        + "of U+D800 to U+DFFF that is not part of a surrogate pair. BergDB "
                        + "stores every string as well-formed UTF-8, which cannot hold one "
                        + "(bergdb 021-04, 021-05).");
            }
            put(Keys.toBytes(key), StringUtil.toBytes(value));
            return this;
        }
        
        /**
         * Puts the value at the key's bkey (Keys.toBytes()).
         * 
         * @throws IllegalArgumentException  If key or value is null, or the key is empty or has
         *      a lone surrogate, as for put(String, String).
         */
        public Builder put(String key, byte[] value) {
            checkKey(key);
            checkValue(value);
            put(Keys.toBytes(key), value);
            return this;
        }
        
        /**
         * Sets the transaction's read time, the time at which it read the keys that keyRead()
         * and addReadHash() give: Db.execute() refuses it with RerunException if a
         * transaction with a later time wrote one of them (Db, "Optimistic transactions").
         * Long.MAX_VALUE by default, which checks nothing; a time that Db.currentTime() or a
         * read's actual lookup time gave.
         * 
         * @throws IllegalArgumentException  If lookupTime is negative.
         */
        public Builder lookupTime(long lookupTime) {
            if (lookupTime < 0) {
                throw new IllegalArgumentException("lookupTime = " + lookupTime);
            }
            
            this.builderLookupTime = lookupTime;
            return this;
        }
        
        /**
         * Adds a key that the transaction read, as segments (Keys.toSegments()), with a value
         * or without: a put or a delete of it by a transaction after the read time
         * (lookupTime()) is a conflict. Kept as its hash, Keys.hash().
         * 
         * @throws IllegalArgumentException  If key is null or has no segment.
         */
        public Builder keyRead(long[] key) {
            checkSegments(key);
            long[] segments = key;
            long hash = Keys.hash(segments);
            readHashes.add(hash);
            return this;
        }
        
        /**
         * As keyRead(long[]) of the key's segments (Keys.toSegments()).
         * 
         * @throws IllegalArgumentException  If key is null, empty or has a lone surrogate
         *      (Keys.toBytes()).
         */
        public Builder keyRead(String key) {
            checkKey(key);
            long[] segments = Keys.toSegments(key);
            return keyRead(segments);
        }
        
        /**
         * Adds a hash that the transaction read: a key's, Keys.hash(), as keyRead() adds, or a
         * virtual one, that a transaction writes with addVirtualWriteHash().
         * 
         * @throws IllegalArgumentException  If hash is negative.
         */
        public final Builder addReadHash(long hash) {
            checkHash(hash);
            readHashes.add(hash);
            return this;
        }
        
        /**
         * As addReadHash() for each of the first 'length' hashes.
         * 
         * @throws IllegalArgumentException  If hashes is null, length is outside 0 to
         *      hashes.length, or one of the hashes is negative; nothing is added then.
         */
        public final Builder addReadHashes(long[] hashes, final int length) {
            if (hashes == null) {
                throw new IllegalArgumentException("hashes == null not allowed");
            }
            if (length < 0 || length > hashes.length) {
                // An assert until bergdb 020-27, Q2: without -ea, an
                // ArrayIndexOutOfBoundsException after some hashes were added.
                throw new IllegalArgumentException("Bad length, " + length + ", for "
                        + "hashes.length " + hashes.length + ".");
            }
            for (int i = 0; i < length; i++) {
                checkHash(hashes[i]);       // All checked before any is added.
            }
            
            for (int i = 0; i < length; i++) {
                readHashes.add(hashes[i]);
            }
            return this;
        }
        
        /**
         * Deletes the key's value; the key is the String's bkey (Keys.toBytes()).
         * 
         * @throws IllegalArgumentException  If key is null, empty or has a lone surrogate.
         */
        public Builder delete(String key) {
            checkKey(key);
            return delete(Keys.toBytes(key));
        }

        /**
         * Deletes the key's value. A delete of a key without a value stores nothing
         * (Db.getTrans()). Of this builder's calls on the key the last one counts: the
         * delete replaces a put made before it, and a put made after it replaces the delete
         * (build()).
         * 
         * @throws IllegalArgumentException  If key is null.
         */
        public Builder delete(byte[] key) {
            checkKey(key);
            kvs.add(new Kv(Keys.toSegments(key), null));
            return this;
        }
        
        /**
         * As delete(byte[]) with the key as segments (Keys.toSegments()).
         * 
         * @throws IllegalArgumentException  If key is null or has no segment.
         */
        public Builder delete(long[] key) {
            checkSegments(key);
            kvs.add(new Kv(key, null));
            return this;
        }

        /**
         * Adds a virtual write hash to the list of hashes: a hash that the transaction counts
         * as written, with no key. A transaction that read it (addReadHash()) at an earlier
         * read time then gets RerunException, so that transactions that share no key can
         * conflict (Db, "Optimistic transactions").
         * 
         * @throws IllegalArgumentException  If hash is negative.
         */
        public Builder addVirtualWriteHash(long hash) {
            checkHash(hash);
            virtualWriteHashes.add(hash);
            return this;
        }
        
        /** A null key refused (bergdb 020-27, Q2). */
        private static void checkKey(Object key) {
            if (key == null) {
                throw new IllegalArgumentException("key == null not allowed");
            }
        }
        
        /**
         * A key of no segments refused (bergdb 020-27, Q2): with -ea a put or a delete of one
         * failed the database (Dag.putKv's assert, after the go point); without it, it was
         * written. Keys.toSegments() gives one segment at least.
         */
        private static void checkSegments(long[] key) {
            checkKey(key);
            if (key.length == 0) {
                throw new IllegalArgumentException("key.length == 0 not allowed: a key has one "
                        + "segment at least (Keys.toSegments()).");
            }
        }
        
        private static void checkValue(Object value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, use delete() "
                        + "to delete a key-value pair.");
            }
        }
        
        /**
         * A key hash is never negative (Keys.hash); KeyModSet uses it as an index
         * (2026-10-21, bergdb 005-21: a negative write hash threw after the go point).
         */
        private static void checkHash(long hash) {
            if (hash < 0) {
                throw new IllegalArgumentException("Negative key hash, " + hash + ".");
            }
        }
        
        private long[] computeWriteHashes(Kv[] kvs) {
            long[] keyHashes = new long[kvs.length + this.virtualWriteHashes.size()];
            for (int i = 0; i < kvs.length; i++) {
                keyHashes[i] = Keys.hash(kvs[i].getKey());
            }
            for (int i = 0; i < virtualWriteHashes.size(); i++) {
                keyHashes[kvs.length + i] = virtualWriteHashes.get(i);
            }
            
            return keyHashes;
        }
        
        /**
         * Finishes building the transaction by creating a Trans
         * instance and returning it.
         * 
         * One operation a key, in key order: of the calls on a key, the last one, a put or a
         * delete (bergdb 024-10, section 3, R1: the last operation wins; Frans, 2026-11-10). The
         * key is the key as written, before any key transformation: of the KVs that key
         * transformations make one key, Db.putKvs keeps the one called last (R2), which each
         * KV's call number tells it (Kv.call). Until release 2026.4 the last put was kept, or a
         * delete if there was no put (bergdb 015-40).
         */
        public Trans build() {
            // We use a TreeMap to sort and to avoid duplicates.
            // Could be done while we add KVs too.
            
            Trans t = new Trans();
            t.readTime = builderLookupTime;
            t.warmupGetData = warmupGetData;
            
            TreeMap<long[], Kv> map = new TreeMap<long[], Kv>(ARRAY_COMPARATOR);
            
            for (int i = 0; i < kvs.size(); i++) {
                Kv kv = kvs.get(i);
                kv.call = i;
                map.put(kv.getKey(), kv);       // the last call on a key replaces the others
            }
            
            t.kvs = map.values().toArray(EMPTY_KV_ARRAY);
            
            t.readKeyHashes = new long[readHashes.size()];
            for (int i = 0; i < t.readKeyHashes.length; i++) {
                t.readKeyHashes[i] = readHashes.get(i);
            }
            
            t.writeKeyHashes = computeWriteHashes(t.kvs);
            
            return t;
        }
        
        /**
         * Special access for Db; methods must only be called from Db or from
         * test code.
         */
        static class ForDb {
            static Builder create() {
                return new Trans.Builder();
            }
        }
    }
    
    /** bergdb 021-05: a lone surrogate in a String key or value is refused; it was '?'. */
    @Nano
    static void testLoneSurrogateRefused() {
        String[][] kvs = {{"k", "a\uD800"}, {"k\uDC00", "v"}};
        for (String[] kv : kvs) {
            try {
                new Trans.Builder().put(kv[0], kv[1]);
                throw new AssertionError("no exception");
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("lone surrogate"));
            }
        }
        new Trans.Builder().put("k?\uD83D\uDE00", "v?\uD83D\uDE00");     // pairs are text
    }
    
    /** bergdb 005-21: a negative key hash is refused when the transaction is built. */
    @Nano
    static void testNegativeHash() {
        try {
            new Trans.Builder().addVirtualWriteHash(-1);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
        try {
            new Trans.Builder().addReadHash(Long.MIN_VALUE);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
    }
    
    @Nano
    static void testTransReuse() {
        Trans t;
        Db db;
        
        db = Db.builder().testSetup().start();
        t = db.trans().put("k", "v").build();
        
        for (int i0 = 0; i0 < 2; i0++) {
            db.execute(t);
        }
        
        db.close();
        db = Db.builder().testSetup().start();
        for (int i0 = 0; i0 < 1; i0++) {
            db.execute(t);
        }
        db.close();
    }
}
