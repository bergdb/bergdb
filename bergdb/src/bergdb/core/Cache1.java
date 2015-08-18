package bergdb.core;

import java.io.IOException;
import java.lang.ref.PhantomReference;
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
 * An instance of this class handles the node caching for the database.
 * It has mappings from node ids to Node objects.
 * It ensures there is only one Node object for a given node id. 
 * It is a canonicalizing mapping.
 * It uses weak references to allow Node objects to be garbage collected when 
 * no longer used.
 * 
 * @author Frans Lundberg
 * @deprecated
 */
public class Cache1 {
    //
    // Sync notes. There is one instance of this class for a Db instance.
    // It is access by: the put thread (holds Db.writeLock), get threads, and
    // any calling setTargetSize(). The evictStep() method can run in a user thread
    // that does a db put or a db get. It may, or may not hold the db.writeLock.
    //
    
    private static final int INDEX_MAP_COUNT = 100;
    private static final int VALUE_MAP_COUNT = 100;
    private static final long RANDOM_MASK = Bytes.bytesToLongBE(
            new byte[]{0x51, (byte)0xc3, (byte)0x9c, (byte)0xcb, 0x50, 0x03, (byte)0xf7, 0x5b}, 0);
            // Random bytes from random.org.
    private static final long INITIAL_CACHE_SIZE = INDEX_MAP_COUNT * 500 + VALUE_MAP_COUNT * 500;
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
    
    @SuppressWarnings("unchecked")
    public Cache1(PointerLocks pointerLocks) {
        this.pointerLocks = pointerLocks;
        
        indexMaps = (HashMap<Long, NodeReference>[]) new HashMap<?, ?>[INDEX_MAP_COUNT];
        for (int i = 0; i < INDEX_MAP_COUNT; i++) {
            indexMaps[i] = new HashMap<Long, NodeReference>();
        }
        
        valueMaps = (HashMap<Long, NodeReference>[]) new HashMap<?, ?>[VALUE_MAP_COUNT];
        for (int i = 0; i < VALUE_MAP_COUNT; i++) {
            valueMaps[i] = new HashMap<Long, NodeReference>();
        }
        
        indexRefQueues = new ReferenceQueue[INDEX_MAP_COUNT];
        for (int i = 0; i < INDEX_MAP_COUNT; i++) {
            indexRefQueues[i] = new ReferenceQueue<Node>();
        }
        
        valueRefQueues = new ReferenceQueue[VALUE_MAP_COUNT];
        for (int i = 0; i < VALUE_MAP_COUNT; i++) {
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
    
    /* (non-Javadoc)
     * @see bergdb.core.Cache#putIndexNode(bergdb.dag.Node)
     */
    public void putIndexNode(Node node) {
        // getMemSize() is constant for a particular TopNode instance.
        // But *not* for a KeyNode instance.
        
        assert node.isIndexNode();
        
        long id = node.getId();
        assert id >= 0;
        int mapIndex = getMapIndex(id, INDEX_MAP_COUNT);
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
        
        possiblyEvict();
    }
    
    public void putValueNode(ValueNode node) {
        if (node.value == null) {
            return;
        }
        
        long id = node.getId();
        assert id >= 0 : "value node, node.getId() = " + id;
        int mapIndex = getMapIndex(id, VALUE_MAP_COUNT);
        int memSize = node.getMemSize();
        
        HashMap<Long, NodeReference> map = valueMaps[mapIndex];
        synchronized (map) {
            cleanupValueRefQ(mapIndex, 10);
            NodeReference ref = new NodeReference(node, valueRefQueues[mapIndex], id, false);
            ref.memSize = memSize;
            
            NodeReference oldRef = map.put(id, ref);
            if (AssertStatus.enabled()) {
                if (oldRef != null && oldRef.get() != null) {
                    throw new AlreadyHasNode("id:" + id + ", value node already in cache");
                }
            }
        }
        
        long totalMemSize = totalMemSize(memSize);        
        totalSize.addAndGet(totalMemSize);
        putSize.addAndGet(totalMemSize);
        
        possiblyEvict();
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
    
    /* (non-Javadoc)
     * @see bergdb.core.Cache#getIndexNode(long)
     */
    public Node getIndexNode(long id) {
        NodeReference ref;
        Node result;
        int index = getMapIndex(id, INDEX_MAP_COUNT);
        HashMap<Long, NodeReference> map = indexMaps[index];
        
        synchronized (map) {
            cleanupIndexRefQ(index, 10);
            ref = map.get(id);
            result = ref == null ? null : ref.get();
        }
        
        return result;
    }
    
    /* (non-Javadoc)
     * @see bergdb.core.Cache#getValueNode(long)
     */
    public ValueNode getValueNode(long id) {
        NodeReference ref;
        ValueNode result;
        int index = getMapIndex(id, VALUE_MAP_COUNT);
        HashMap<Long, NodeReference> map = valueMaps[index];
        
        synchronized (map) {
            cleanupValueRefQ(index, 10);
            ref = map.get(id);        
            result = ref == null ? null : (ValueNode) ref.get();
        }
        
        return result;
    }
    
    public final int getIndexMapCount() {
        return INDEX_MAP_COUNT;
    }
    
    public final int getValueMapCount() {
        return VALUE_MAP_COUNT;
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

    /* (non-Javadoc)
     * @see bergdb.core.Cache#putSize()
     */
    public long putSize() {
        return putSize.get();
    }
    
    private final void possiblyEvict() {
        evictor.possiblyEvict();
    }

    private HashMap<Long, NodeReference> indexMap(long id) {
        return indexMaps[getMapIndex(id, INDEX_MAP_COUNT)];
    }
    
    private HashMap<Long, NodeReference> valueMap(long id) {
        return valueMaps[getMapIndex(id, VALUE_MAP_COUNT)];
    }
    
    private final int getMapIndex(long id, int mapCount) {
        long a;
        int b;
        
        a = id;
        a = RANDOM_MASK ^ id;
        a = (a >>> 32) ^ a;     // 32 bits used
        a = (a >>> 16) ^ a;     // 16 bits used, assumes INDEX_MAP_COUNT and VALUE_MAP_COUNT much less than 2^15.
        
        b = (int) (a & 0x0000ffffL);
        assert b >= 0;
        return b % mapCount;
    }
    
    /**
     * Caller must hold lock on indexMaps[mapIndex].
     */
    private void cleanupIndexRefQ(int mapIndex, final int pollLimit) {
        int pollCount = 0;
        Reference<? extends Node> ref;
        ReferenceQueue<Node> refQ = indexRefQueues[mapIndex];
        
        assert Thread.holdsLock(indexMaps[mapIndex]) : "caller does not hold required lock";
        
        ref = refQ.poll();
        pollCount++;
        
        while (ref != null && pollCount <= pollLimit) {
            NodeReference nodeRef = (NodeReference) ref;
            assert nodeRef.isIndexNode : "not an index node ref: " + nodeRef.get();
            
            indexMaps[mapIndex].remove(nodeRef.id);
            totalSize.addAndGet(-totalMemSize(nodeRef.memSize));
            ref = refQ.poll();
            pollCount++;
        }
    }
    
    /**
     * Caller should hold lock on valueMaps[mapIndex].
     */
    private void cleanupValueRefQ(int mapIndex, final int pollLimit) {
        assert Thread.holdsLock(valueMaps[mapIndex]) : "caller must hold lock for valueMap " + mapIndex;
        
        int pollCount = 0;
        Reference<? extends Node> ref;
        ReferenceQueue<Node> refQ = valueRefQueues[mapIndex];
        ref = refQ.poll();
        pollCount++;
        
        while (ref != null && pollCount <= pollLimit) {
            NodeReference nodeRef = (NodeReference) ref;
            assert !nodeRef.isIndexNode;
            
            valueMaps[mapIndex].remove(nodeRef.id);
            totalSize.addAndGet(-totalMemSize(nodeRef.memSize));
            
            ref = refQ.poll();
            pollCount++;
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
    }
    
    /**
     * Reference to an unmanaged value node.
     */
    public static final class UnmanagedReference extends PhantomReference<ValueNode> {
        final int memSize;
        
        public UnmanagedReference(ValueNode node, ReferenceQueue<ValueNode> q, int memSize) {
            super(node, q);
            this.memSize = memSize;
        }
        
        public final int getMemSize() {
            return memSize;
        }
    }
    
    /**
     * State of evict, last evict.
     */
    private final class Evictor {
        //
        // Most fields are protected by isEvicting; only used while isEvicting == true.
        //
        
        long putSize0;     // putSize when last evict was done
        long putSize;
        long deltaPutSize;
        long totalSize;
        long targetSize;
        int nextMapIndex;
        double noEvictDistance;
        final AtomicBoolean isEvicting;
        double fillFactor;
        boolean isCritical;
        long accessTimeLimit;
        final Pointer pointer = new Pointer();    // input/output, temp storage
        
        Evictor() {
            putSize0 = Cache1.this.putSize.get();
            nextMapIndex = 0;
            targetSize = 100L*1000000;
            noEvictDistance = Cache1.this.targetSize.get() * 0.25;
            isEvicting = new AtomicBoolean(false);
        }
        
        /**
         * Use result for debug only, no sync - could be invalid.
         */
        double getNoEvictDistance() {
            return noEvictDistance;
        }
        
        void possiblyEvict() {
            // If is evicting now, return immediately.
            // If process less than 0.02 of targetSize since last evict step, return.
            // Else, do evict processing.
            
            double putRatio;
            
            boolean wasSet = isEvicting.compareAndSet(false, true);
            if (!wasSet) {
                return;
            }
            
            try {
                putSize = Cache1.this.putSize.get();
                totalSize = Cache1.this.totalSize.get();
                targetSize = Cache1.this.targetSize.get();
                fillFactor = ((double) totalSize) / targetSize;
                deltaPutSize = putSize - putSize0;
                putRatio = (double) deltaPutSize / targetSize;
                isCritical = fillFactor > 0.90;
                
                //System.out.format("Cache, putRatio: %.6f, deltaPutSize: %d, putSize0: %d\n", 
                //        putRatio, deltaPutSize, putSize0);
                //System.out.format("Cache fillFactor: %.3f\n", fillFactor);
                
                boolean evictCondition = putRatio > 0.02 && fillFactor > 0.50;
                if (evictCondition) {
                    evict();
                    if (isCritical) {
                        System.gc();
                        cleanupAll();
                    }
                }
            } finally {
                assert isEvicting.get() == true : "isEvicting not true while evicting";
                isEvicting.set(false);
            }
        }
        
        /** Private inner method; only called from possiblyEvict. */
        private void evict() {
            long amountToProcess = deltaPutSize * 4;
            long cacheSizePerMap = (totalSize + INDEX_MAP_COUNT) / INDEX_MAP_COUNT;
            assert cacheSizePerMap >= 1;
            int mapsToProcess = (int) (amountToProcess / cacheSizePerMap);
            
            mapsToProcess = mapsToProcess < 1 ? 1 : mapsToProcess;
            mapsToProcess = mapsToProcess > INDEX_MAP_COUNT ? INDEX_MAP_COUNT : mapsToProcess;
            
            //System.out.println("Cache.evictor.evict(), mapsToProcess: " + mapsToProcess);
            
            updateNoEvictDistance();
            
            for (int i = 0; i < mapsToProcess; i++) {
                evictPointersInOneMap();
            }
            
            putSize0 = putSize;
        }
        
        private void updateNoEvictDistance() {
            // Control theory - regulating noEvictDistance based on 
            // cache fill factor.
            
            double change;
            
            if (fillFactor > 0.90) {
                change = 0.95;
            } else if (fillFactor > 0.70) {
                change = 0.99;
            } else {
                change = 1.01;
            }
            
            noEvictDistance = noEvictDistance * change;
            
            accessTimeLimit = putSize - (long) noEvictDistance;
        }
        
        /**
         * Evicts pointers from the nodes in one index node map
         * and increases nextMapIndex to the next map to process.
         */
        private void evictPointersInOneMap() {
            evictPointersInMap(nextMapIndex);
            nextMapIndex = (nextMapIndex + 1) % INDEX_MAP_COUNT;
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
                
                cleanupIndexRefQ(mapIndex, Integer.MAX_VALUE);
            }
        }
        
        /**
         * Evicts all evicable out-bound pointers of 'node'.
         */
        private void evictNodePointers(Node node) {
            // It is possible to get pointeePos == Spos.NULL for value nodes.
            // A value node does not get an spos when created, but later when
            // written to stream.
            
            int count = node.getSize();
            
            for (int i = 0; i < count; i++) {
                Object lock = pointerLocks.getLock(node, i);
                synchronized (lock) {
                    node.getPointer(i, pointer);
                    if (pointer.isMem()) {
                        Node pointee = pointer.node;
                        
                        if (!pointee.isDirty()) {
                            long pointeePos = pointee.getSpos();
                            
                            if (pointeePos != Spos.NULL) {
                                long pointerAccessTime = AccessData.getAccessTime(pointer.getAccessData());
                                
                                if (pointerAccessTime <= accessTimeLimit) {
                                    node.setPointer(i, null, pointeePos);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    
    // ======== Tests ========
    
    @Nano private static void testSanity1() {
        Cache1 m = new Cache1(new PointerLocks());
        KeyNode node = new KeyNode();
        node.setId(1234L);
        m.putIndexNode(node);
        
        Assert.assertTrue("getIndexNode (existing)", node == m.getIndexNode(1234L));
        Assert.assertTrue(m.getIndexNode(1222L) == null);
    }
    
    @Nano private static void testSanity2() {
        Cache1 m = new Cache1(new PointerLocks());
        ValueNode node = new ValueNode(new byte[0]);
        node.setSpos(1234L);
        assert node.getId() == 1234L;
        m.putValueNode(node);
        
        Assert.assertEquals("getValueNode existant", node, m.getValueNode(1234L));
        Assert.assertEquals("getValueNode non-existant", m.getValueNode(1222L), null);
    }
    
    @SuppressWarnings("unused")
    @Nano private static void testMapCount() {
        // Checks the assumption that map count is << 2^15 (~32000).
        
        if (INDEX_MAP_COUNT > 2000) {
            throw new IllegalStateException("Bad INDEX_MAP_COUNT, " + INDEX_MAP_COUNT);
        }
        
        if (VALUE_MAP_COUNT > 2000) {
            throw new IllegalStateException("Bad VALUE_MAP_COUNT, " + VALUE_MAP_COUNT);
        }
    }
    
    @Nano private static void testDuplicateValueNodes() {
        Cache1 m = new Cache1(new PointerLocks());
        ValueNode node = new ValueNode(new byte[1000]);
        node.setSpos(1234L);
        assert node.getId() == 1234L;
        m.putValueNode(node);
        AlreadyHasNode ex = null;
        
        if (AssertStatus.enabled()) {
            try {
                m.putValueNode(node);
            } catch (Cache1.AlreadyHasNode e) {
                ex = e;
            }
            
            Assert.assertTrue(ex != null);
        }
        
        
    }
    
    @Nano private static void testDuplicateIndexNodes() {
        Cache1 m = new Cache1(new PointerLocks());
        KeyNode node = new KeyNode();
        node.setId(222L);
        assert node.getId() == 222L;
        m.putIndexNode(node);
        AlreadyHasNode ex = null;
        
        if (AssertStatus.enabled()) {
            try {
                m.putIndexNode(node);
            } catch (Cache1.AlreadyHasNode e) {
                ex = e;
            }
            
            Assert.assertTrue(ex != null);
        }
    }
    
    @Nano private static void testTotalSize1() {
        Cache1 cache = new Cache1(new PointerLocks());
        ValueNode node = new ValueNode(new byte[10]);
        node.setSpos(222L);
        int memSize = node.getMemSize();
        
        long mem1 = cache.totalSize.get();
        cache.putValueNode(node);
        long mem2 = cache.totalSize.get();
        
        Assert.assertEquals(memSize + Cache1.NODE_MEM_OVERHEAD, mem2 - mem1);
    }
    
    @Nano private static void testTotalSize2() {
        Cache1 cache = new Cache1(new PointerLocks());
        TopNode node = TopNode.createDummy(2);
        node.setId(222L);
        int memSize = node.getMemSize();
        
        long mem1 = cache.totalSize.get();
        cache.putIndexNode(node);
        long mem2 = cache.totalSize.get();
        
        Assert.assertEquals(memSize + Cache1.NODE_MEM_OVERHEAD, mem2 - mem1);
    }
    
    @Nano("f") 
    private static void testGc() throws InterruptedException {
        // This test could fail, but seems to work on cissi / Oracle JVM 7.
        // There is no guarantee that garbage collection is actually run when System.gc() 
        // is called. Also, there is no guarantee when references are added the reference queue.
        
        Cache1 m = new Cache1(new PointerLocks());
        KeyNode k = new KeyNode();
        k.setId(1234L);
        
        m.putIndexNode(k);
        Assert.assertTrue(m.indexMap(1234L).containsKey(1234L));
        
        k = null;
        
        System.gc();
        System.gc();
        
        Thread.sleep(1000);
        m.cleanupAll();
        
        Assert.assertFalse("contains test", m.indexMap(1234L).containsKey(1234L));
        Assert.assertTrue("get result should be null", m.getIndexNode(1234L) == null);
    }
    
    /**
     * Used for testing.
     */
    public void cleanupAll() {
        for (int i = 0; i < INDEX_MAP_COUNT; i++) {
            synchronized (indexMaps[i]) {
                cleanupIndexRefQ(i, Integer.MAX_VALUE);
            }
        }
        
        for (int i = 0; i < VALUE_MAP_COUNT; i++) {
            synchronized (valueMaps[i]) {
                cleanupValueRefQ(i, Integer.MAX_VALUE);
            }
        }
    }
    
    public static void manualMemTest() throws InterruptedException, IOException {
        // Manual memory testing. Use with jvisualvm or something.
        
        System.out.println("CacheMap.memTest()");
        
        int mapCount = 1*1000;
        int nodesPerMap = 1*1000;
        ReferenceQueue<Node> refQ = new ReferenceQueue<Node>();
        
        KeyNode[] keyNodes = new KeyNode[mapCount * nodesPerMap];
        
        for (int i = 0; i < keyNodes.length; i++) {
            keyNodes[i] = new KeyNode();
            keyNodes[i].setId(i);
        }
        
        gc();
        long mem0 = memUsed();
        System.out.format("mem0: %.1f MB\n", 1e-6*mem0);
        waitForEnter();
        
        @SuppressWarnings("unchecked")
        HashMap<Long, NodeReference>[] maps = (HashMap<Long, NodeReference>[]) new HashMap[mapCount];
        for (int i = 0; i < mapCount; i++) {
            maps[i] = new HashMap<Long, NodeReference>();
            
            for (int j = 0; j < nodesPerMap; j++) {
                long id = i * nodesPerMap + j;
                maps[i].put(id, new NodeReference(keyNodes[(int) id], refQ, id, true));
            }
        }
        
        gc();
        
        long mem1 = memUsed();
        long memDelta = mem1 - mem0;
        
        System.out.format("mem1: %.1f MB\n", 1e-6*mem1);
        System.out.format("Mem used delta, %.1f MB, per node: %.1f B.\n", 1e-6 * memDelta, 1.0 * memDelta / keyNodes.length);
        System.out.println("maps.length: " + maps.length);
        System.out.println("nodes: " + keyNodes.length);
        
        waitForEnter();
    }
    
    private static void waitForEnter() throws IOException {
        System.in.read();
    }

    public static void gc() {
        System.gc(); System.gc(); System.gc();
    }
    
    public static long memUsed() {        
        Runtime r = Runtime.getRuntime();
        long total = r.totalMemory();
        long free = r.freeMemory();
        long used = total - free;
        
        System.out.format("memUsed(), total: %.1f, free: %.1f, total-free: %.1f MB.\n", 
                1e-6 * total, 1e-6 * free, 1e-6 * (total-free));
        
        return used;
    }
    
    public static void main(String[] args) throws Exception {
        manualMemTest();
    }

    public double getNoEvictDistance() {
        return evictor.getNoEvictDistance();
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
   CacheMap approach. This significant, but acceptable.
2. We can likely reduce memory usage to 60 bytes / node by special long-to-Object hash map.
3. Using many maps is not a problem. Memory overhead of an empty HashMap is only 50 bytes.

*/