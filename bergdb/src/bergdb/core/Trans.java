package bergdb.core;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.TreeMap;

import bergdb.common.Util;
import bergdb.coreds.GetData;
import bergdb.coreds.Keys;
import bergdb.nanotest.T;

/**
 * Data data for executing a transaction. Input, output and working data.
 * The change set of the transaction is defined in this class.
 * 
 * @author Frans Lundberg
 */
public class Trans {
    //
    // This class is defined in the most preferred, most efficient form for the DB side, 
    // not for the client using DB.
    //
    // We might want to add a size limitation to the transactions.
    // It can easily be enforced in the Builder.
    //
    // Note. It would be good for memory reuse possibilities to use array+size approach.
    // For example; have long[] readKeyHashes *and* int readKeyHashesLength.
    // We would be able to reuse Trans object memory. 
    // Should be neglectable performance degradation for DB.execute.
    //
    
    private static final Kv[] emptyKVArray = new Kv[0];
    
    // -- Input --
    
    public Kv[] kvs;
    public long[] writeKeyHashes;   // Precomputed hashes of keys to set. May be longer than 
                                    // kvs.length due to virtual KVs.
    public long readTime;           // Time when keys were read.
    public long[] readKeyHashes;    // Hashes of keys read. May include hashes of virtual KVs.
    
    // -- Output --
    
    public long transactionTime;    // Transaction time, also used as internally.
    public int splitCount;          // Number of node splits due to transaction.
    public long spos;               // spos of the first byte of the transaction. Available after execute.
    public long lastSpos;           // spos of the last byte of the transaction. Available after execute.
    public long nextSpos;           // spos of the next transaction. Available after execute.
    public int nodeCount;           // Number of nodes written to stream. Useful for testing/debug.
                                    // Note. Not super important, could be removed.
    
    // -- Internal working data --
    public final GetData getData;
    
    // -- Other --
    boolean trace;              // If true, debug trace is printed to System.out.
    boolean isInternal;         // True if transaction was executed on behalf of the database itself.

    private static Comparator<long[]> arrayComparator = new Comparator<long[]>() {
        public int compare(long[] a1, long[] a2) {
            return Keys.compareArrays(a1, a2);
        }
    };
    
    private Trans() {
        readKeyHashes = new long[0];
        getData = new GetData();
    }
    
    public boolean isInternal() {
        return isInternal;
    }
    
    /**
     * Returns a multi-line string representing this object for debug purpose.
     */
    public String print() {
        StringBuilder b = new StringBuilder();
        b.append("readTime: " + readTime + "\n");
        b.append("readKeyHashes: ");
        for (int i = 0; i < this.readKeyHashes.length; i++) {
            b.append(readKeyHashes[i] + " ");
        }
        b.append("\n");
        
        b.append("kv keys:\n");
        for (int i = 0; i < this.kvs.length; i++) {
            Kv kv =  kvs[i];
            b.append("  " + Keys.toStringWithSubstitute(kv.keySegments)
                    + " -> size:" + kv.value.length
                    + ", key hash: " + Keys.hash(kv.keySegments) + "\n");
        }
        
        return b.toString();
    }
    
    /**
     * Creates a builder for a transaction.
     */
    public static Builder builder() {
        // "Effective Java" has example with constructor for builders.
        // Code like         [t = new Trans.Builder().set(key, value).build();]
        // I prefer factory: [t = Trans.create().set(key, value).done();]
        // or:               [t = Trans.builder().set(key, value).build();]
        return new Builder();
    }
    
    /**
     * Used to create a transaction.
     */
    public static class Builder {
        // Note This class does not enforce uniqueness of elements in keyReadSet, kvs, vkeyHashes.
        // NOTE Specialized array implementations would be more efficient.
        
        private long builderLookupTime;
        private ArrayList<Kv> kvs;
        private ArrayList<Long> readHashes;    // hashes of keys read.
        private ArrayList<Long> virtualWriteHashes;    // virtual key hashes for virtual writes
        
        private Builder() {
            kvs = new ArrayList<Kv>();
            readHashes = new ArrayList<Long>();
            virtualWriteHashes = new ArrayList<Long>();
            builderLookupTime = Long.MAX_VALUE;
        }
        
        public Builder set(byte[] key, byte[] value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, use delete() " +
                		"to delete a key-value pair.");
            }
            kvs.add(new Kv(key, value));
            return this;
        }
        
        public Builder set(long[] key, byte[] value) {
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, use delete() " +
                		"to delete a key-value pair.");
            }
            kvs.add(new Kv(key, value));
            return this;
        }
        
        public Builder set(long[] key, KeyTransformation kt, byte[] value, ValueTransformation vt) {
            if (key == null) {
                throw new IllegalArgumentException("key == null not allowed");
            }
            
            if (value == null) {
                throw new IllegalArgumentException("value == null not allowed, use delete() " +
                		"to delete a key-value pair.");
            }
            
            Kv kv = new Kv(key, value);
            kv.keyTransformation = kt;
            kv.valueTransformation = vt;
            kvs.add(kv);
            return this;
        }
        
        public Builder set(String key, String value) {
            set(Keys.toBytes(key), value == null ? null : Util.toBytes(value));
            return this;
        }
        
        public Builder set(String key, byte[] value) {
            set(Keys.toBytes(key), value);
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
            kvs.add(new Kv(key, null));
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
                keyHashes[i] = Keys.hash(kvs[i].keySegments);
            }
            for (int i = 0; i < virtualWriteHashes.size(); i++) {
                keyHashes[kvs.length + i] = virtualWriteHashes.get(i);
            }
            
            return keyHashes;
        }
        
        /**
         * Finishes building the transaction by creating a Transaction
         * instance and returning it.
         */
        public Trans build() {
            // We use a TreeMap to sort and to avoid duplicates.
            // Could be done while we add KVs too.
            // Non-deletes take precedence over deletes. (Needed feature?)
            Trans t = new Trans();
            t.readTime = builderLookupTime;
            
            TreeMap<long[], Kv> map = new TreeMap<long[], Kv>(arrayComparator);
            
            for (Kv kv : kvs) {
                Kv prev = map.put(kv.keySegments, kv);
                if (kv.value == null && prev != null && prev.value != null) {
                    map.put(kv.keySegments, prev);
                }
            }
            
            t.kvs = map.values().toArray(emptyKVArray);
            
            t.readKeyHashes = new long[readHashes.size()];
            for (int i = 0; i < t.readKeyHashes.length; i++) {
                t.readKeyHashes[i] = readHashes.get(i);
            }
            
            t.writeKeyHashes = computeWriteHashes(t.kvs);
            
            return t;
        }
    }
    
    @T
    public static void testTransReuse() {
        Trans t;
        Db db;
        
        //System.out.println("---- PerfDBSet.testTransReuse ----");
        
        t = Trans.builder().set("k", "v").build();
        
        db = Db.builder().testSetup().start();
        for (int i0 = 0; i0 < 2; i0++) {
            db.execute(t);
        }
        
        db = Db.builder().testSetup().start();
        for (int i0 = 0; i0 < 1; i0++) {
            db.execute(t);
        }
    }
}
