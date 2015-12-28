package bergdb.dag;

import java.util.ArrayList;
import java.util.List;

import bergdb.common.Pair;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Iterates all nodes in a DAG including those stored in the stream
 * using valid paths from the super root node.
 * Nodes may be iterated several times, a depth-first tree search algorithm is used.
 * 
 * @author Frans Lundberg
 */
public class DagNodeIterator {
    // Depth-first DAG traversial.
    
    private Dag dag;
    private Node root;
    private boolean rootAdded = false;
    private int nextPointerIndex = 0;
    private DagNodeIterator iter;
    private long maxLookupTime;
    
    public DagNodeIterator(Dag dag) {
        this.dag = dag;
        this.root = dag.getSuperRoot();
        this.maxLookupTime = Long.MAX_VALUE;
    }
    
    public DagNodeIterator(Dag dag, Node root, long maxLookupTime) {
        this.dag = dag;
        this.root = root;
        this.maxLookupTime = maxLookupTime;
    }
    
    /**
     * Returns node or null when done.
     */
    public Node next() {
        if (!rootAdded) {
            createChildIter(maxLookupTime);
            rootAdded = true;
            return root;
        } else {
            if (iter == null) return null;
            
            Node next = iter.next();
            if (next == null) {
                createChildIter(maxLookupTime);
                return next();
            } else {
                return next;
            }
        }
    }
    
    /**
     * Utility method, adds all nodes to a list.
     */
    public void addToList(List<Node> list) {
        Node node;
        while ((node = next()) != null) {
            list.add(node);
        }
    }

    private void createChildIter(long maxLookupTime) {
        Pair<Long, Node> result = getChild(nextPointerIndex, maxLookupTime);
        maxLookupTime = result.getValue0();
        Node child = result.getValue1();
        
        if (child == null) {
            iter = null;
        } else {
            iter = new DagNodeIterator(dag, child, maxLookupTime);
            nextPointerIndex++;
        }
    }
    
    /**
     * Gets new maxLookupTime and next child.
     */
    private Pair<Long, Node> getChild(int pointerIndex, long maxLookupTime) {
        int n = root.getSizeAtTime(maxLookupTime);
        
        Pointer p = new Pointer();
        
        while (pointerIndex < n) {
            root.getPointer(pointerIndex, p);
            if (!p.isNull()) {
                nextPointerIndex = pointerIndex;
                break;
            }
            
            pointerIndex++;
        }
        
        if (p.isNull()) {
            return new Pair<Long, Node>(maxLookupTime, null);
        }
        
        long newMaxLookupTime = maxLookupTime;
        if (root.isKeyNode()) {
            KeyNode keyNode = (KeyNode) root;
            
            long klong = keyNode.klongs[pointerIndex];
            if (Klong.getType(klong) != Klong.TYPE_KEY) {
                throw new Error("pointer not null but klong type is not TYPE_KEY, klong: " 
                        + Klong.toString(klong) + ", p: " + p.toString());
            }
            
            long maxValidTime = keyNode.getMaxValidTime(pointerIndex);
            if (maxValidTime < maxLookupTime) {
                newMaxLookupTime = maxValidTime;
            }
        }
        
        Node child = dag.followPointer(root, pointerIndex, 0, 
                Dag.DO_NOTHING_POINTER_LISTENER, Dag.CACHE_NOTHING);
        
        return new Pair<Long, Node>(newMaxLookupTime, child);
    }
    
    // ======== Test ========
    
    @Nano
    private static void testEmptyDag() {
        Dag g = DagTester.emptyDag(10);
        DagNodeIterator iter = new DagNodeIterator(g);
        ArrayList<Node> list = new ArrayList<Node>();
        iter.addToList(list);
        
        Assert.assertEquals(2, list.size());
        Assert.assertTrue(list.get(0).isTopNode());
        Assert.assertTrue(list.get(1).isKeyNode());
    }
    
    
    @Nano
    private static void testDagWithOneKv() {
        Dag g = DagTester.emptyDag(10);
        PutData pd = g.newPutData();
        pd.tt = 20;
        g.putKv(Keys.toSegments("key"), Util.toBytes("value"), pd);
        
        DagNodeIterator iter = new DagNodeIterator(g);
        ArrayList<Node> list = new ArrayList<Node>();
        iter.addToList(list);
        
        Assert.assertEquals(3, list.size());
        Assert.assertTrue(list.get(0).isTopNode());
        Assert.assertTrue(list.get(1).isKeyNode());
        Assert.assertTrue(list.get(2).isValueNode());
    }
}
