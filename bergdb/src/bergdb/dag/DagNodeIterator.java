package bergdb.dag;

import java.util.ArrayList;
import java.util.List;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Iterates all nodes in a DAG including those stored in the stream.
 * Nodes may be iterated several times, a tree search is used.
 * 
 * NOTE currently all pointers are followed, including "impossible" pointers; 
 * that is, pointers that won't ever be followed while performing normal db operations.
 * 
 * @author Frans Lundberg
 */
public class DagNodeIterator {
    // Depth-first DAG traversial.
    
    private Dag dag;
    private INode root;
    private boolean rootAdded = false;
    private int nextPointerIndex = 0;
    private DagNodeIterator iter;
    
    public DagNodeIterator(Dag dag) {
        this.dag = dag;
        this.root = dag.getSuperRoot();
    }
    
    private DagNodeIterator(Dag dag, INode root) {
        this.dag = dag;
        this.root = root;
    }
    
    /**
     * Returns node or null when done.
     */
    public INode next() {
        if (!rootAdded) {
            createChildIter();
            rootAdded = true;
            return root;
        } else {
            if (iter == null) return null;
            
            INode next = iter.next();
            if (next == null) {
                createChildIter();
                return next();
            } else {
                return next;
            }
        }
    }
    
    /**
     * Utility method, adds all nodes to a list.
     */
    public void addToList(List<INode> list) {
        INode node;
        while ((node = next()) != null) {
            list.add(node);
        }
    }

    private void createChildIter() {
        INode child = getChild(nextPointerIndex);
        if (child == null) {
            iter = null;
        } else {
            iter = new DagNodeIterator(dag, child);
            nextPointerIndex++;
        }
    }
    
    /**
     * Gets the next child.
     */
    private INode getChild(int index) {
        int n = root.getPointerCount();
        
        Pointer p = new Pointer();
        
        while (index < n) {
            root.getPointer(index, p);
            if (!p.isNull()) {
                nextPointerIndex = index;
                break;
            }
            index++;
        }
        
        if (p.isNull()) {
            return null;
        }
        
        return dag.followPointer(root, index, 0, 
                Dag.DO_NOTHING_POINTER_LISTENER, Dag.CACHE_NOTHING);
    }
    
    // ======== Test ========
    
    @Nano
    private static void testEmptyDag() {
        Dag g = DagTester.emptyDag(10);
        DagNodeIterator iter = new DagNodeIterator(g);
        ArrayList<INode> list = new ArrayList<INode>();
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
        ArrayList<INode> list = new ArrayList<INode>();
        iter.addToList(list);
        
        Assert.assertEquals(3, list.size());
        Assert.assertTrue(list.get(0).isTopNode());
        Assert.assertTrue(list.get(1).isKeyNode());
        Assert.assertTrue(list.get(2).isValueNode());
    }
}
