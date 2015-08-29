package bergdb.core;

import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.common.AssertStatus;
import bergdb.common.Bytes;
import bergdb.dag.AccessData;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * A node cache that uses weak references to for a canonicalizing node map.
 * It ensures there is only one Node object for a given node id.
 * It uses weak references to allow Node objects to be garbage collected when 
 * no longer used.
 * 
 * @author Frans Lundberg
 */
public class Cache2 {
    //
    // Cache2, change definition of targetSize. Here, targetSize is the
    // cache distance used to determine accessTimeLimit. 
    // accessTimeLimit = putSize() - targetSize.
    //
    // Sync notes. There is one instance of this class for a Db instance.
    // It is used by: the put thread (holds Db.writeLock), get threads, and
    // any thread calling setTargetSize(). The evictStep() method can run in a user thread
    // that does a db put or a db get. It may, or may not hold the db.writeLock.
    //
    
    private static final int MAP_COUNT = 100;
    private static final long RANDOM_MASK = Bytes.bytesToLongBE(
            new byte[]{0x51, (byte)0xc3, (byte)0x9c, (byte)0xcb, 0x50, 0x03, (byte)0xf7, 0x5b}, 0);
            // Random bytes from random.org.
    private static final long INITIAL_CACHE_SIZE = MAP_COUNT * 500 + MAP_COUNT * 500;
    private static final long NODE_MEM_OVERHEAD = 100;
    
    private final HashMap<Long, NodeReference>[] indexMaps;
    private final HashMap<Long, NodeReference>[] valueMaps;
    private final ReferenceQueue<Node>[] indexRefQueues;
    private final ReferenceQueue<Node>[] valueRefQueues;
    private final Evictor evictor;
    
    private final AtomicLong targetSize;    // target total cache size, set by user
    private final AtomicLong totalSize;     // current total cache size (estimate of memory byte size)
    private final AtomicLong putSize;       // total size of all node put to cache, always increasing
    private final PointerLocks pointerLocks;
    private final DbInfo dbInfo;
    
    @SuppressWarnings("unchecked")
    public Cache2(PointerLocks pointerLocks, DbInfo dbInfo) {
        assert pointerLocks != null;
        assert dbInfo != null;
        
        this.pointerLocks = pointerLocks;
        this.dbInfo = dbInfo;
        
        indexMaps = (HashMap<Long, NodeReference>[]) new HashMap<?, ?>[MAP_COUNT];
        for (int i = 0; i < MAP_COUNT; i++) {
            indexMaps[i] = new HashMap<Long, NodeReference>();
        }
        
        valueMaps = (HashMap<Long, NodeReference>[]) new HashMap<?, ?>[MAP_COUNT];
        for (int i = 0; i < MAP_COUNT; i++) {
            valueMaps[i] = new HashMap<Long, NodeReference>();
        }
        
        indexRefQueues = new ReferenceQueue[MAP_COUNT];
        for (int i = 0; i < MAP_COUNT; i++) {
            indexRefQueues[i] = new ReferenceQueue<Node>();
        }
        
        valueRefQueues = new ReferenceQueue[MAP_COUNT];
        for (int i = 0; i < MAP_COUNT; i++) {
            valueRefQueues[i] = new ReferenceQueue<Node>();
        }
        
        totalSize = new AtomicLong(INITIAL_CACHE_SIZE);
        putSize = new AtomicLong(INITIAL_CACHE_SIZE);
        targetSize = new AtomicLong(10L * 1000000L);       
        evictor = new Evictor();
    }
    
    public void setTargetSize(long targetSize) {
        assert targetSize > 0;
        this.targetSize.set(targetSize);
    }
    
    public void putIndexNode(Node node) {
        // getMemSize() is constant for a particular TopNode instance.
        // But *not* for a KeyNode instance.
        
        assert node.isIndexNode();
        
        long id = node.getId();
        assert id >= 0;
        int mapIndex = mapIndex(id);
        HashMap<Long, NodeReference> map = indexMaps[mapIndex];
        
        int memSize = node.getMemSize();
        
        synchronized (map) {
            cleanupIndexRefQ(mapIndex, 10);
            
            NodeReference ref = new NodeReference(node, indexRefQueues[mapIndex], id, true);
            ref.memSize = memSize;
            
            NodeReference oldRef = map.put(id, ref);
            if (AssertStatus.enabled()) {
                if (oldRef != null && oldRef.get() != null) {
                    throw new AlreadyHasNode("id:" + id + ", index node already in cache");
                }
            }
        }
        
        long totalMemSize = totalMemSize(memSize);
        totalSize.addAndGet(totalMemSize);
        putSize.addAndGet(totalMemSize);
        
        evictor.possiblyEvict();
    }
    
    public void putValueNode(ValueNode node) {
        byte[] value = node.value;
        
        if (value == null) {
            return;
        }
        
        if (value.length < 100) {
            putSmallValueNode(node);
        } else {
            putLargeValueNode(node);
        }
        
        evictor.possiblyEvict();
    }
    
    /**
     * Small value nodes are "unmanaged". They are not added to a map.
     * Small duplicates are preferred considering the overhead with an 
     * entry in the cache (around 100 byte memory used overhead).
     */
    private void putSmallValueNode(ValueNode node) {
        int memSize = node.getMemSize();
        totalSize.addAndGet(memSize);
        putSize.addAndGet(memSize);
    }

    private void putLargeValueNode(ValueNode node) {
        long id = node.getId();
        assert id >= 0 : "value node, node.getId() = " + id;
        int mapIndex = mapIndex(id);
        int memSize = node.getMemSize();
        
        HashMap<Long, NodeReference> map = valueMaps[mapIndex];
        synchronized (map) {
            cleanupValueRefQ(mapIndex, 10);
            
            NodeReference ref = new NodeReference(node, valueRefQueues[mapIndex], id, false);
            ref.memSize = memSize;
            
            NodeReference oldRef = map.put(id, ref);
            if (AssertStatus.enabled()) {
                // TODO B. consider: what happens when old NodeReference becomes eligable for
                // garbage collection? Might never be put on refQ? What if? Is that ok?
                
                if (oldRef != null && oldRef.get() != null) {
                    throw new AlreadyHasNode("id:" + id + ", value node already in cache");
                }
            }
        }
        
        long totalMemSize = totalMemSize(memSize);        
        totalSize.addAndGet(totalMemSize);
        putSize.addAndGet(totalMemSize);
    }

    public static class AlreadyHasNode extends AssertionError {
        private static final long serialVersionUID = 1L;
        
        public AlreadyHasNode(String message) {
            super(message);
        }
    }
    
    private final long totalMemSize(int memSize) {
        return memSize + NODE_MEM_OVERHEAD;
    }
    
    public Node getIndexNode(long id) {
        NodeReference ref;
        Node result;
        int index = mapIndex(id);
        HashMap<Long, NodeReference> map = indexMaps[index];
        
        synchronized (map) {
            ref = map.get(id);
            result = ref == null ? null : ref.get();
        }
        
        return result;
    }
    
    public ValueNode getValueNode(long id) {
        NodeReference ref;
        ValueNode result;
        int index = mapIndex(id);
        HashMap<Long, NodeReference> map = valueMaps[index];
        
        synchronized (map) {
            ref = map.get(id);        
            result = ref == null ? null : (ValueNode) ref.get();
        }
        
        assert result == null || result.getId() == id;
        
        return result;
    }
    
    public Object getIndexLockObject(long id) {
        return indexMap(id);
    }
    
    public Object getValueLockObject(long id) {
        return valueMap(id);
    }
    
    public long targetSize() {
        return targetSize.get();
    }
    
    public long totalSize() {
        return totalSize.get();
    }

    public long putSize() {
        return putSize.get();
    }
    
    public void cleanupAllRefQueues() {
        for (int i = 0; i < MAP_COUNT; i++) {
            synchronized (indexMaps[i]) {
                cleanupIndexRefQ(i, Integer.MAX_VALUE);
            }
        }
        
        for (int i = 0; i < MAP_COUNT; i++) {
            synchronized (valueMaps[i]) {
                cleanupValueRefQ(i, Integer.MAX_VALUE);
            }
        }
    }

    private HashMap<Long, NodeReference> indexMap(long id) {
        return indexMaps[mapIndex(id)];
    }
    
    private HashMap<Long, NodeReference> valueMap(long id) {
        return valueMaps[mapIndex(id)];
    }
    
    /**
     * Computes a hash value between 0 and MAP_COUNT-1 from 'id'.
     */
    private static final int mapIndex(long id) {
        //
        // Assumption: INDEX_MAP_COUNT is less than 256.
        //
        // 150818 Frans: did a study of a real case distribution 
        // of size of the maps. Looked good. Looked completely random to me.
        //
        
        long a;
        int b;
        
        a = id;
        a = RANDOM_MASK ^ id;
        a = (a >>> 32) ^ a;
        a = (a >>> 16) ^ a;
        a = (a >>> 8) ^ a;
        
        b = (int) (a & 0x0000ffffL);
        assert b >= 0;
        return b % MAP_COUNT;
    }
    
    /**
     * Caller must hold lock on indexMaps[mapIndex].
     */
    private void cleanupIndexRefQ(int mapIndex, final int pollLimit) {
        int pollCount = 0;
        Reference<? extends Node> ref;
        ReferenceQueue<Node> refQ = indexRefQueues[mapIndex];
        HashMap<Long, NodeReference> map = indexMaps[mapIndex];
        
        assert Thread.holdsLock(map) : "caller does not hold required lock for index node map " + mapIndex;
        
        ref = refQ.poll();
        pollCount++;
        
        while (ref != null && pollCount <= pollLimit) {
            NodeReference nodeRef = (NodeReference) ref;
            assert nodeRef.isIndexNode : "not an index node ref: " + nodeRef.get();
            
            NodeReference existingRef = map.get(nodeRef.id);
            if (existingRef == nodeRef) {
                map.remove(nodeRef.id);
            }
            
            totalSize.addAndGet(-totalMemSize(nodeRef.memSize));
            ref = refQ.poll();
            pollCount++;
        }
    }
    
    /**
     * Caller should hold lock on valueMaps[mapIndex].
     */
    private void cleanupValueRefQ(int mapIndex, final int pollLimit) {
        int pollCount = 0;
        Reference<? extends Node> ref;
        ReferenceQueue<Node> refQ = valueRefQueues[mapIndex];
        HashMap<Long, NodeReference> map = valueMaps[mapIndex];
        
        assert Thread.holdsLock(map) : "caller does not hold required lock for map " + mapIndex;
        
        ref = refQ.poll();
        pollCount++;
        
        while (ref != null && pollCount <= pollLimit) {
            NodeReference nodeRef = (NodeReference) ref;
            assert !nodeRef.isIndexNode;
            
            NodeReference existingRef = map.get(nodeRef.id);
            if (existingRef == nodeRef) {
                map.remove(nodeRef.id);
            }
            
            totalSize.addAndGet(-totalMemSize(nodeRef.memSize));
            
            ref = refQ.poll();
            pollCount++;
        }
    }
    
    /**
     * Source of dynamic information about the database state.
     * Easy to mock.
     */
    public static interface DbInfo {
        public long getStartupPosForEvict();
    }
    
    public static class TestAccess {
        public static int indexMapSize(Cache2 c, int mapIndex) {
            return c.indexMaps[mapIndex].size();
        }
        
        public static int indexMapCount() {
            return Cache2.MAP_COUNT;
        }

        public static int valueMapSize(Cache2 c, int mapIndex) {
            return c.valueMaps[mapIndex].size();
        }
        
        public static int valueMapCount() {
            return Cache2.MAP_COUNT;
        }
    }
    
    public static class NodeReference extends WeakReference<Node> {
        final long id;
        final boolean isIndexNode;
        int memSize;
        
        public NodeReference(Node node, ReferenceQueue<Node> q, long id, boolean isIndexNode) {
            super(node, q);
            this.id = id;
            this.isIndexNode = isIndexNode;
        }
        
        public String toString() {
            String superToString = super.toString();
            String s;
            
            int index = superToString.indexOf('@');
            if (index == -1 && index == superToString.length() - 1) {
                s = superToString;
            } else {
                s = superToString.substring(index + 1);
            }
            
            s = s + "-" + id;
            if (isIndexNode) {
                s += "-index";
            } else {
                s += "-value";
            }
            
            s += "-" + memSize;
            
            return s;
        }
    }
    
    /**
     * State of evict, last evict.
     */
    private final class Evictor {
        //
        // Most fields are protected by isEvicting; only used while isEvicting == true.
        //
        
        long startupPos;
        long putSize0;     // putSize when last evict was done
        long putSize;
        long deltaPutSize;
        double putRatio;
        long targetSize;
        int nextMapIndex;
        final AtomicBoolean isEvicting;
        long accessTimeLimit;
        final Pointer pointer = new Pointer();    // input/output, temp storage
        @SuppressWarnings("unused")
        long evictCount;
        
        Evictor() {
            putSize0 = Cache2.this.putSize.get();
            nextMapIndex = 0;
            targetSize = 100L*1000000;
            isEvicting = new AtomicBoolean(false);
            evictCount = 0;
        }
        
        void possiblyEvict() {
            // NOTE 0.01 is "magic" here. What is optimal?
            // If is evicting now, return immediately.
            // If processed less than 0.01 of targetSize since last evict step, return.
            // Else, do evict processing.
            
            boolean wasSet = isEvicting.compareAndSet(false, true);
            if (!wasSet) {
                return;
            }
            
            try {
                startupPos = dbInfo.getStartupPosForEvict();
                putSize = Cache2.this.putSize.get();
                targetSize = Cache2.this.targetSize.get();
                deltaPutSize = putSize - putSize0;
                putRatio = (double) deltaPutSize / targetSize;
                
                if (putRatio > 0.01) {
                    evict();
                }
            } finally {
                assert isEvicting.get() == true : "isEvicting not true while evicting";
                isEvicting.set(false);
            }
        }
        
        /** Private inner method; only called from possiblyEvict. */
        private void evict() {
            // NOTE 4.0 is "magic" here. What is optimal?
            
            cleanupAllRefQueues();
            
            int mapsToProcess = (int) (4.0 * putRatio * MAP_COUNT);
            mapsToProcess = mapsToProcess < 1 ? 1 : mapsToProcess;
            mapsToProcess = mapsToProcess > MAP_COUNT ? MAP_COUNT : mapsToProcess;
            
            //System.out.println("Cache2.evictor.evict(), mapsToProcess: " + mapsToProcess);
            
            accessTimeLimit = putSize - targetSize;
            
            for (int i = 0; i < mapsToProcess; i++) {
                evictPointersInOneMap();
            }
            
            cleanupAllRefQueues();
            
            putSize0 = putSize;
        }
        
        /**
         * Evicts pointers from the nodes in one index node map
         * and increases nextMapIndex to the next map to process.
         */
        private void evictPointersInOneMap() {
            evictPointersInMap(nextMapIndex);
            nextMapIndex = (nextMapIndex + 1) % MAP_COUNT;
        }

        private void evictPointersInMap(int mapIndex) {
            HashMap<Long, NodeReference> map = indexMaps[mapIndex];
            
            synchronized (map) {
                for (NodeReference ref : map.values()) {
                    Node node = ref.get();
                    if (node != null) {
                        evictNodePointers(node);
                    }
                }
            }
        }
        
        /**
         * Evicts all evicable out-bound pointers of 'node'.
         */
        private void evictNodePointers(Node node) {
            //
            // It is possible to get pointeePos == Spos.NULL for value nodes.
            // A value node does not get an spos when created, but later when
            // written to stream.
            //
            // TODO A. Analyse - it is not safe to call isDirty() from read threads like in this method.
            //
            
            assert node.isIndexNode();
            
            long spos = node.getSpos();
            assert Spos.isValid(spos);
            
            int count = node.getSize();
            for (int i = 0; i < count; i++) {
                synchronized (pointerLocks.getLock(node, i)) {
                    Node pointee = node.getPointerNode(i); 
                    
                    if (pointee != null) {
                        long pointeePos = pointee.getSpos();
                        
                        if (pointeePos != Spos.NULL
                                && pointeePos < startupPos
                                && AccessData.getAccessTime(node.getPointerAccessData(i)) 
                                        <= accessTimeLimit) {
                            
                            if (pointee.isDirty()) {
                                node.setPointer(i, null, pointeePos);
                                evictCount++;
                            }
                        }
                    }
                }
            }
        }
    }
    
    // ======== Tests ========
    
    private static Cache2 testObject() {
        DbInfo mockDbInfo = new DbInfo() {
            public long getStartupPosForEvict() {
                return Long.MAX_VALUE;
            }
        };
        
        return new Cache2(new PointerLocks(), mockDbInfo);
    }
    
    @Nano private static void testSanity1() {
        Cache2 m = testObject();
        KeyNode node = new KeyNode();
        node.setId(1234L);
        m.putIndexNode(node);
        
        Assert.assertTrue("getIndexNode (existing)", node == m.getIndexNode(1234L));
        Assert.assertTrue(m.getIndexNode(1222L) == null);
    }
    
    @Nano private static void testSanity2() {
        Cache2 m = testObject();
        ValueNode node = new ValueNode(new byte[200]);
        node.setSpos(1234L);
        assert node.getId() == 1234L;
        m.putValueNode(node);
        
        Assert.assertEquals("getValueNode existant", node, m.getValueNode(1234L));
        Assert.assertEquals("getValueNode non-existant", m.getValueNode(1222L), null);
    }
    
    @SuppressWarnings("unused")
    @Nano private static void testMapCount() {
        // Checks assumption of method getMapIndex().
        
        if (MAP_COUNT > 256) {
            throw new IllegalStateException("Bad MAP_COUNT, " + MAP_COUNT);
        }
    }
    
    @Nano private static void testDuplicateValueNodes() {
        Cache2 m = testObject();
        ValueNode node = new ValueNode(new byte[1000]);
        node.setSpos(1234L);
        assert node.getId() == 1234L;
        m.putValueNode(node);
        AlreadyHasNode ex = null;
        
        if (AssertStatus.enabled()) {
            try {
                m.putValueNode(node);
            } catch (Cache2.AlreadyHasNode e) {
                ex = e;
            }
            
            Assert.assertTrue(ex != null);
        }
    }
    
    @Nano private static void testDuplicateIndexNodes() {
        Cache2 m = testObject();
        KeyNode node = new KeyNode();
        node.setId(222L);
        assert node.getId() == 222L;
        m.putIndexNode(node);
        AlreadyHasNode ex = null;
        
        if (AssertStatus.enabled()) {
            try {
                m.putIndexNode(node);
            } catch (Cache2.AlreadyHasNode e) {
                ex = e;
            }
            
            Assert.assertTrue(ex != null);
        }
    }
    
    @Nano private static void testTotalSize1() {
        Cache2 cache = testObject();
        ValueNode node = new ValueNode(new byte[200]);
        node.setSpos(222L);
        int memSize = node.getMemSize();
        
        long mem1 = cache.totalSize.get();
        cache.putValueNode(node);
        long mem2 = cache.totalSize.get();
        
        Assert.assertEquals(memSize + Cache2.NODE_MEM_OVERHEAD, mem2 - mem1);
    }
    
    @Nano private static void testTotalSize2() {
        Cache2 cache = testObject();
        TopNode node = TopNode.createDummy(2);
        node.setId(222L);
        int memSize = node.getMemSize();
        
        long mem1 = cache.totalSize.get();
        cache.putIndexNode(node);
        long mem2 = cache.totalSize.get();
        
        Assert.assertEquals(memSize + Cache2.NODE_MEM_OVERHEAD, mem2 - mem1);
    }
    
    @Nano("f") 
    private static void testGc() throws InterruptedException {
        // This test could fail, but seems to work on cissi / Oracle JVM 7.
        // There is no guarantee that garbage collection is actually run when System.gc() 
        // is called. Also, there is no guarantee when references are added the reference queue.
        
        Cache2 m = testObject();
        KeyNode k = new KeyNode();
        k.setId(1234L);
        
        m.putIndexNode(k);
        Assert.assertTrue(m.indexMap(1234L).containsKey(1234L));
        
        k = null;
        
        System.gc();
        System.gc();
        
        Thread.sleep(1000);
        m.cleanupAllRefQueues();
        
        Assert.assertFalse("contains test", m.indexMap(1234L).containsKey(1234L));
        Assert.assertTrue("get result should be null", m.getIndexNode(1234L) == null);
    }
}

/*

150807 Memory Use
=================

Frans: How much extra memory used by this approach?

On cissi + JVM 7. An empty HashMap uses 50 bytes of memory.
Using jvisualvm for checking memory usage.
Testing with 1000 maps and 1000 key nodes in each; that is 1M nodes in total.
Addition mem use (with maps, NodeReferences, refQ): 103 B / node.
  NodeReference -- 1M, 40 bytes, total 40 MB
  HashMap$Entry -- 1M, 32 bytes, total 32 MB
  Long          -- 1M, 24 bytes, total 24 MB
  HashMap.Entry[] -- 1284, total: 7.2 MB
  103.2 MB for 1M nodes --> 103 B / node.
  
Empty KeyNode: 48 bytes. Typical KeyNode, much more.

With a specialize HashMap for longs, we might reduce mem usage. Currently 63 bytes / node 
is for the HashMap. A special long-to-NodeReference implementation? 
In theory: 8 + 8 + a bit, maybe 20 bytes per entry should be possible. 
Using long[] and Object[] arrays. Would reduce mem per node from 103 to 60.

CONCLUSIONS 
1. We have 103 bytes extra RAM usage per cached node with the 
   current approach. This significant, but acceptable.
2. We can likely reduce memory usage to 60 bytes / node by special long-to-Object hash map.
3. Using many maps is not a problem. Memory overhead of an empty HashMap is only 50 bytes.

*/