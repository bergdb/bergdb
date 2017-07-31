package bergdb.core;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Specialized map, implements fast id-to-Node lookups.
 * No concurrency management is implemented in this class, it is
 * not thread safe. The user of this class must handle that as necessary.
 * 
 * @author Frans Lundberg
 */
public class NodeMap {
    private final int binCount;
    private final Node[] bins;

    public NodeMap() {
        this(1*1000000);
    }
    
    public NodeMap(int binCount) {
        this.binCount = binCount;
        this.bins = new Node[binCount];
    }
    
    /**
     * Puts unconditionally, does not check if value is in the bin there already.
     * Adds value as first value of the bin.
     */
    public void putFast(Node value) {
        assert value != null;
        long id = value.getId();
        int index = index3(id);
        value.setNext(bins[index]);
        bins[index] = value;
    }
    
    public final Node get(long id) {
        int index = index3(id);
        Node existing = bins[index];
        while (existing != null) {
            if (existing.getId() == id) {
                return existing;
            }
            existing = existing.next();
        }
        return null;
    }
    
    private final int index3(long x) {
        x = (x ^ (x >>> 30)) * 0xbf58476d1ce4e5b9L;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebL;
        x = x ^ (x >> 31);
        return (int) (x & 0x7fffffff) % binCount;
    }
    
    
    // ======== Tests ========
    
    @Nano
    private static void testSanity() {
        NodeMap m = new NodeMap(10*1000);
        
        ValueNode n1 = new ValueNode(null);
        n1.setId(123);
        
        m.putFast(n1);
        Node back = m.get(123);
        
        Assert.assertEquals(n1.getId(), back.getId());
        Assert.assertTrue(n1 == back);
    }
    
    @Nano
    private static void test2() {
        NodeMap m = new NodeMap(10*1000);
        
        ValueNode n1 = new ValueNode(null);
        n1.setId(123);
        
        ValueNode n2 = new ValueNode(null);
        n2.setId(124);
        
        m.putFast(n1);
        m.putFast(n2);
        Node g1 = m.get(123);
        Node g2 = m.get(124);
        Node g3 = m.get(125);
        
        Assert.assertEquals(123, g1.getId());
        Assert.assertEquals(124, g2.getId());
        Assert.assertTrue(g3 == null);
    }
}
