package bergdb.core;

import java.io.IOException;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.HashMap;

import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * An object with mappings from node ids to Node objects.
 * An instance of this class is used to ensure there is only one Node object for 
 * a given node id. It is a canonicalizing mapping.
 * It uses weak references to allow Node objects to be garbage collected.
 * 
 * Concurrency: external synchronization is required.
 * 
 * @author Frans Lundberg
 */
public class CacheMap {
    // Note, we likely want a separate map for value nodes later.
    // And maybe 100 or 1000 maps? To limit synchronization time... to be able to
    // synchronize over the whole map object.
    
    private static final int INDEX_MAP_COUNT = 100;
    private static final int VALUE_MAP_COUNT = 100;
    
    private final HashMap<Long, NodeReference>[] indexMaps;
    private final HashMap<Long, NodeReference>[] valueMaps;
    private final ReferenceQueue<Node> refQ;
    
    @SuppressWarnings("unchecked")
    public CacheMap() {
        refQ = new ReferenceQueue<Node>();
        
        indexMaps = (HashMap<Long, NodeReference>[]) new HashMap<?, ?>[INDEX_MAP_COUNT];
        for (int i = 0; i < INDEX_MAP_COUNT; i++) {
            indexMaps[i] = new HashMap<Long, NodeReference>();
        }
        
        valueMaps = (HashMap<Long, NodeReference>[]) new HashMap<?, ?>[VALUE_MAP_COUNT];
        for (int i = 0; i < VALUE_MAP_COUNT; i++) {
            valueMaps[i] = new HashMap<Long, NodeReference>();
        }
    }
    
    public void putIndexNode(Node node) {
        assert node.isIndexNode();
        cleanup();
        long id = node.getId();
        assert id >= 0;
        indexMap(id).put(id, new NodeReference(node, refQ, id, true));
    }
    
    public void putValueNode(ValueNode node) {
        cleanup();
        long id = node.getId();
        assert id >= 0;
        valueMap(id).put(id, new NodeReference(node, refQ, id, false));
    }
    
    public Node getIndexNode(long id) {
        cleanup();
        WeakReference<Node> ref = indexMap(id).get(id);
        Node result = ref == null ? null : ref.get();
        return result;
    }
    
    public ValueNode getValueNode(long id) {
        cleanup();
        WeakReference<Node> ref = valueMap(id).get(id);        
        ValueNode result = ref == null ? null : (ValueNode) ref.get();
        return result;
    }
    
    public Object getIndexSyncObject(long id) {
        return indexMap(id);
    }
    
    public Object getValueSyncObject(long id) {
        return valueMap(id);
    }
    
    private HashMap<Long, NodeReference> indexMap(long id) {
        // TODO B. improve this
        int myInt = (int) (id / 8);
        assert myInt >= 0;
        return indexMaps[myInt % INDEX_MAP_COUNT];
    }
    
    private HashMap<Long, NodeReference> valueMap(long id) {
        // TODO B. improve this
        int myInt = (int) id;
        assert myInt >= 0 : "myInt: " + myInt;
        return valueMaps[myInt % VALUE_MAP_COUNT];
    }
    
    /**
     * Removes entries on the map that cannot be used because the
     * value was garbage collected.
     */
    private void cleanup() {
        // TODO B. is synchronized used ok here? Deadlock possible? Think some more.
        //   What if a node eviction is in progress?
        //   An alternative is to use a lock that can be queried (tryLock), 
        //   java.util.concurrent.locks.Lock.
        
        final int MAX_POLL = 10;
        int pollCount = 0;
        Reference<? extends Node> ref;
        
        ref = refQ.poll();
        pollCount++;
        
        while (ref != null && pollCount <= MAX_POLL) {
            NodeReference nodeRef = (NodeReference) ref;
            long id = nodeRef.id;
            
            if (nodeRef.isIndexNode) {
                HashMap<Long, NodeReference> map = indexMap(id);
                synchronized (map) {
                    map.remove(id);
                }
            } else {
                HashMap<Long, NodeReference> map = valueMap(id);
                synchronized (map) {
                    map.remove(id);
                }
            }
            
            ref = refQ.poll();
            pollCount++;
        }
    }
    
    public static class NodeReference extends WeakReference<Node> {
        public final long id;
        public final boolean isIndexNode;
        
        public NodeReference(Node node, ReferenceQueue<Node> q, long id, boolean isIndexNode) {
            super(node, q);
            this.id = id;
            this.isIndexNode = isIndexNode;
        }
    }
    
    
    // ======== Tests ========
    
    @Nano private static void testSanity1() {
        CacheMap m = new CacheMap();
        KeyNode node = new KeyNode();
        node.setId(1234L);
        m.putIndexNode(node);
        
        Assert.assertTrue(node == m.getIndexNode(1234L));
        Assert.assertTrue(m.getIndexNode(1222L) == null);
    }
    
    @Nano private static void testSanity2() {
        CacheMap m = new CacheMap();
        ValueNode node = new ValueNode(new byte[0]);
        node.setSpos(1234L);
        assert node.getId() == 1234L;
        m.putValueNode(node);
        
        Assert.assertEquals("getValueNode existant", node, m.getValueNode(1234L));
        Assert.assertEquals("getValueNode non-existant", m.getValueNode(1222L), null);
    }
    
    @Nano("f") 
    private static void testGc() throws InterruptedException {
        // This test could fail, but seems to work on cissi / Oracle JVM 7.
        // There is no guarantee that garbage collection is actually run when System.gc() 
        // is called. Also, there is no guarantee when references are added the reference queue.
        
        CacheMap m = new CacheMap();
        KeyNode k = new KeyNode();
        k.setId(1234L);
        
        m.putIndexNode(k);
        Assert.assertTrue(m.indexMap(1234L).containsKey(1234L));
        
        k = null;
        
        System.gc();
        System.gc();
        
        Thread.sleep(1000);
        m.cleanup();
        
        Assert.assertFalse("contains test", m.indexMap(1234L).containsKey(1234L));
        Assert.assertTrue("get result should be null", m.getIndexNode(1234L) == null);
    }
    
    public static void main(String[] args) throws Exception {
        memTest();
    }
    
    public static void memTest() throws InterruptedException, IOException {
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
}

/*

Extra Memory Use
================

150807 Frans. How much extra memory used by this approach?

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