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
    
    public long tt;                 // Transaction time, used internally and as output.
    public int splitCount;          // Number of node splits made during execute().
    public long tpos;               // Stream position of the first byte of the transaction. Available after execute().
    public long lastPos;            // Stream position of the last byte of the transaction. Available after execute().
    public long nextPos;            // Stream position of the first byte of the next transaction. Available after execute().
    public int nodeCount;           // Number of nodes written to stream. Useful for testing/debug.
    public Listener listener;       // Low-level listener, for development/debugging typically.

    // -- Other --
    
    /** True if transaction is executed on behalf of the database itself. */
    boolean isInternal;
    
    /**
     * For internal transactions of reclaim (2026-10-13): before the puts, the
     * writer visits every node reachable at the transaction time for the keys
     * after touchFrom (exclusive; null: from the first key) up to touchTo (inclusive; null:
     * to the last key), as a put visits its path, so that each of them gets dirty and is
     * written again.
     * Not stored: startup rebuilds D from the stored got-dirty ids.
     */
    boolean touch;
    long[] touchFrom;
    long[] touchTo;
    
    /**
     * For a transaction with touch (2026-10-13, docs/levels.md, "Level 3 cost"):
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
    GetData warmupGetData;
    
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
     * Returns a multi-line string representing this object for debug purpose.
     */
    public String print() {
        StringBuilder b = new StringBuilder();
        b.append("pos: " + tpos + "\n");
        b.append("storedNewStartupPos: " + startupPos + "\n");
        b.append("readKeyHashes: ");
        for (int i = 0; i < this.readKeyHashes.length; i++) {
            b.append(readKeyHashes[i] + " ");
        }
        b.append("\n");
        
        b.append("kv keys:\n");
        for (int i = 0; i < this.kvs.length; i++) {
            Kv kv =  kvs[i];
            b.append("  " + Keys.toStringWithSubstitute(kv.getKey())
                    + " -> size:" + kv.getValue().length
                    + ", key hash: " + Keys.hash(kv.getKey()) + "\n");
        }
        
        return b.toString();
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
     */
    public static class Builder {
        // Note This class does not enforce uniqueness of elements in keyReadSet, kvs, vkeyHashes.
        
        private long builderLookupTime;
        private ArrayList<Kv> kvs;
        private ArrayList<Long> readHashes;    // hashes of keys read.
        private ArrayList<Long> virtualWriteHashes;    // virtual key hashes for virtual writes
        private GetData warmupGetData;
        
        public Builder() {
            kvs = new ArrayList<Kv>();
            readHashes = new ArrayList<Long>();
            virtualWriteHashes = new ArrayList<Long>();
            builderLookupTime = Long.MAX_VALUE;

            warmupGetData = new GetData();
            warmupGetData.pointerListener = Dag.DO_NOTHING_POINTER_LISTENER;        
            warmupGetData.cachePolicy = Dag.CACHE_ALL;
        }
        
        public Builder put(byte[] key, byte[] value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, use delete() " +
                		"to delete a key-value pair.");
            }
            kvs.add(new Kv(Keys.toSegments(key), value));
            return this;
        }
        
        public Builder put(long[] key, byte[] value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, use delete() " +
                		"to delete a key-value pair.");
            }
            kvs.add(new Kv(key, value));
            return this;
        }
        
        public Builder put(long[] key, KeyTransformation kt, byte[] value, ValueTransformation vt) {
            if (key == null) {
                throw new IllegalArgumentException("key == null not allowed");
            }
            
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, use delete() " +
                		"to delete a key-value pair.");
            }
            
            Kv kv = new Kv(key, value, kt, vt);
            kvs.add(kv);
            return this;
        }
        
        public Builder put(String key, String value) {
            put(Keys.toBytes(key), value == null ? null : StringUtil.toBytes(value));
            return this;
        }
        
        public Builder put(String key, byte[] value) {
            put(Keys.toBytes(key), value);
            return this;
        }
        
        public Builder lookupTime(long lookupTime) {
            if (lookupTime < 0) {
                throw new IllegalArgumentException("lookupTime = " + lookupTime);
            }
            
            this.builderLookupTime = lookupTime;
            return this;
        }
        
        public Builder keyRead(byte[] key) {
            long[] segments = Keys.toSegments(key);
            long hash = Keys.hash(segments);
            readHashes.add(hash);
            return this;
        }
        
        public Builder keyRead(long[] key) {
            long[] segments = key;
            long hash = Keys.hash(segments);
            readHashes.add(hash);
            return this;
        }
        
        public Builder keyRead(String string) {
            long[] segments = Keys.toSegments(string);
            return keyRead(segments);
        }
        
        public final Builder addReadHash(long hash) {
            readHashes.add(hash);
            return this;
        }
        
        public final Builder addReadHashes(long[] hashes, final int length) {
            assert length <= hashes.length : "length = " + length 
                    + ", hashes.length = " + hashes.length;
            
            for (int i = 0; i < length; i++) {
                readHashes.add(hashes[i]);
            }
            return this;
        }
        
        public Builder delete(String string) {
            return delete(Keys.toBytes(string));
        }

        public Builder delete(byte[] key) {
            kvs.add(new Kv(Keys.toSegments(key), null));
            return this;
        }
        
        public Builder delete(long[] key) {
            kvs.add(new Kv(key, null));
            return this;
        }

        /**
         * Adds a virtual write hash to the list of hashes.
         */
        public Builder addVirtualWriteHash(long hash) {
            virtualWriteHashes.add(hash);
            return this;
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
         */
        public Trans build() {
            // We use a TreeMap to sort and to avoid duplicates.
            // Could be done while we add KVs too.
            // Non-deletes take precedence over deletes.
            
            Trans t = new Trans();
            t.readTime = builderLookupTime;
            t.warmupGetData = warmupGetData;
            
            TreeMap<long[], Kv> map = new TreeMap<long[], Kv>(ARRAY_COMPARATOR);
            
            for (Kv kv : kvs) {
                Kv prev = map.put(kv.getKey(), kv);
                if (kv.getValue() == null && prev != null && prev.getValue() != null) {
                    map.put(kv.getKey(), prev);
                }
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
    
    @Nano
    public static void testTransReuse() {
        Trans t;
        Db db;
        
        db = Db.builder().testSetup().start();
        t = db.trans().put("k", "v").build();
        
        for (int i0 = 0; i0 < 2; i0++) {
            db.execute(t);
        }
        
        db = Db.builder().testSetup().start();
        for (int i0 = 0; i0 < 1; i0++) {
            db.execute(t);
        }
    }
}
