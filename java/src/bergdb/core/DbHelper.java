package bergdb.core;

import java.util.ArrayList;
import java.util.Iterator;

import bergdb.common.Create;
import bergdb.common.StringUtil;
import bergdb.dag.AccessData;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.KeyNodeTester;
import bergdb.dag.Pointer;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Methods to help the Db implementation.
 * This class should only be used by Db.
 * 
 * @author Frans Lundberg
 */
public class DbHelper {

    private DbHelper() {}
    
    /**
     * Returns true if the node has at least one in-memory child
     * that is dirty.
     */
    static boolean hasDirtyChild(Node node) {
        int count = node.getSize();
        Pointer p = new Pointer();
        
        for (int i = 0; i < count; i++) {
            node.getPointer(i, p);
            if (!p.isNull()) {
                Node child = node.getPointerNode(i);
                if (child != null && child.isDirty()) {
                    return true;
                }
            }
        }
        
        return false;
    }

    /**
     * Adds nodes that are still dirty to got-dirty nodes.
     * A node is still dirty after being written to stream if any of its 
     * children is dirty.
     */
    static int handleStillDirtyNodes(Iterator<? extends Node> input, TransSeq.NodeSink output) {
        int stillDirtyCount = 0;
        
        while (input.hasNext()) {
            Node node = input.next();
            
            if (!node.isDirty() && hasDirtyChild(node)) {
                node.setDirty(true);
                output.addGotDirtyNode(node);
                stillDirtyCount++;
            }
        }
        
        return stillDirtyCount;
    }
    
    
    // ======== Testing ========
    
    @Nano private static void testHandleStillDirtyNodes1() {
        KeyNodeTester tester = new KeyNodeTester();
        KeyNode k1 = tester.createT2();
        KeyNode k2 = tester.t2Pointers[0];   // child of k1
        KeyNode k3 = tester.t2Pointers[1];   // child of k1
        KeyNode k4 = new KeyNode();
        
        k1.setDirty(false);
        k2.setDirty(true);
        k3.setDirty(false);
        k4.setDirty(false);
        
        Iterator<Node> iter = Create.list((Node) k1, k2, k3, k4).iterator();
        final ArrayList<Node> nodes = new ArrayList<Node>();
        
        TransSeq.NodeSink output = new TransSeq.NodeSink() {
            public void addGotDirtyNode(Node node) {
                nodes.add(node);
            }
        };
        
        handleStillDirtyNodes(iter, output);
        
        Assert.assertEquals(1, nodes.size());
        Assert.assertEquals(k1, nodes.get(0));
        Assert.assertTrue(k1.isDirty());
        Assert.assertTrue(k2.isDirty());
        Assert.assertFalse(k3.isDirty());
        Assert.assertFalse(k4.isDirty());
    }
    
    @Nano private static void testHandleStillDirtyNodes2() {
        //
        //  k0  k4
        //  |\ /  \
        //  | /\   k5
        //  |/  \
        //  k1   k3
        //  |
        //  k2
        //
        // Only k4 is dirty first. 
        // This will make k0, k1, and k4 dirty, but not the other nodes.
        //
        
        KeyNode[] k = new KeyNode[6];
        for (int i = 0; i < k.length; i++) {
            k[i] = new KeyNode();
            k[i].setDirty(false);
        }
        
        addPointer(k[0], k[1], "01");
        addPointer(k[0], k[3], "03");
        addPointer(k[1], k[2], "12");
        addPointer(k[4], k[1], "41");
        addPointer(k[4], k[5], "45");
        
        k[2].setDirty(true);
        
        int stillDirtyCount;
        do {
            stillDirtyCount = DbHelper.handleStillDirtyNodes(Create.list(k).iterator(), NullNodeSink.INSTANCE);
        } while (stillDirtyCount > 0);
        
        Assert.assertTrue(k[0].isDirty() == true);
        Assert.assertTrue(k[1].isDirty() == true);
        Assert.assertTrue(k[2].isDirty() == true);
        Assert.assertTrue(k[3].isDirty() == false);
        Assert.assertTrue(k[4].isDirty() == true);
        Assert.assertTrue(k[5].isDirty() == false);
    }
    
    private static class NullNodeSink implements TransSeq.NodeSink {
        public static final NullNodeSink INSTANCE = new NullNodeSink();
        public void addGotDirtyNode(Node node) {}
    }
    
    private static void addPointer(KeyNode from, KeyNode to, String label) {
        long time = 10;
        long ad = AccessData.DEFAULT_ACCESS_DATA;
        long klong = Klong.createKey(StringUtil.toBytes(label));
        from.addKlong(time, klong, to, ad);
    }
}
