package bergdb.core;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.TreeMap;

import bergdb.common.Util;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.dag.TransNodes;
import bergdb.nanotest.T;

/**
 * Data for executing a transaction. Input, output and working data.
 * The change set of the transaction is defined in this class.
 * This class is designed to suit class Db and to achieve high performance.
 * 
 * @author Frans Lundberg
 */
public class Trans {
    //
    // This class is defined in the most preferred, most efficient form for the Db side, 
    // not for the client using Db.
    //
    // We might want to add a size limitation to the transactions.
    // It can easily be enforced in the Builder.
    //
    // Note. It would be good for memory reuse possibilities to use array+size approach.
    // For example; have long[] readKeyHashes *and* int readKeyHashesLength.
    // We would be able to reuse Trans object memory. 
    // Should be neglectable performance degradation for DB.execute().
    //
    
    private static final Kv[] EMPTY_KV_ARRAY = new Kv[0];
    
    // -- Input --
    
    public Kv[] kvs;
    public long[] writeKeyHashes;   // Precomputed hashes of keys to set. May be longer than 
                                    // kvs.length due to virtual KVs.
    public long readTime;           // Time when keys were read.
    public long[] readKeyHashes;    // Hashes of keys read. May include hashes of virtual KVs.
    
    // -- Output --
    
    public long time;               // Transaction time, used internally and as output.
    public int splitCount;          // Number of node splits made during execute().
    public long pos;                // Stream position of the first byte of the transaction. Available after execute().
    public long lastPos;            // Stream position of the last byte of the transaction. Available after execute().
    public long nextPos;            // Stream position of the first byte of the next transaction. Available after execute().
    public int nodeCount;           // Number of nodes written to stream. Useful for testing/debug.
                                    // Note, not super important, could be removed.
    public Listener listener;
    
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
        getData = new GetData();     // NOTE Better to use Db.newGetData().
        listener = NO_ACTION_LISTENER;
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
            b.append("  " + Keys.toStringWithSubstitute(kv.getKey())
                    + " -> size:" + kv.getValue().length
                    + ", key hash: " + Keys.hash(kv.getKey()) + "\n");
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
     * Listens to what happens to a transaction; suitable for testing.
     */
    public static interface Listener {
        /**
         * Reports that the nodes were written to stream.
         */
        public void nodesWritten(TransNodes nodes);
    }
    
    public static final NoActionListener NO_ACTION_LISTENER = new NoActionListener();
    
    /**
     * A Trans.Listener implementation that does nothing.
     */
    public static class NoActionListener implements Listener {
        public void nodesWritten(TransNodes nodes) {}
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
        
        /**
         * Use Db.builder() to create a new Builder object.
         */
        private Builder() {
            kvs = new ArrayList<Kv>();
            readHashes = new ArrayList<Long>();
            virtualWriteHashes = new ArrayList<Long>();
            builderLookupTime = Long.MAX_VALUE;
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
            put(Keys.toBytes(key), value == null ? null : Util.toBytes(value));
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
            
            TreeMap<long[], Kv> map = new TreeMap<long[], Kv>(arrayComparator);
            
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
    }
    
    @T
    public static void testTransReuse() {
        Trans t;
        Db db;
        
        t = Trans.builder().put("k", "v").build();
        
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
