package bergdb.dag;

import java.util.zip.CRC32;
import bergdb.common.Bug;
import bergdb.common.MyChecksum;
import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Computes checksum on Dag state.
 * 
 * @author Frans Lundberg
 */
public class DagChecksum {
    private final Dag dag;
    private final TopNode root;
    private final long maxLookupTime;
    private final MyChecksum sum;
    
    public DagChecksum(Dag dag, long maxLookupTime) {
        this.dag = dag;
        this.root = dag.getSuperRoot();
        this.maxLookupTime = maxLookupTime;
        this.sum = new MyChecksum(new CRC32());
    }
    
    public DagChecksum(Dag dag) {
        this(dag, Long.MAX_VALUE);
    }
    
    public long compute() {
        DagNodeIterator iter = new DagNodeIterator(dag, root, maxLookupTime);
        
        while (true) {
            Node node = iter.next();
            if (node == null) {
                break;
            }
     
            checksum(node);
        }
        
        return sum.getValue();
    }
    
    private void checksum(Node node) {
        switch (node.getType()) {
        case Node.TYPE_TOP_NODE:
            checksumOfTopNode((TopNode) node);
            break;
        case Node.TYPE_KEY_NODE:
            checksumOfKeyNode((KeyNode) node);
            break;
        case Node.TYPE_VALUE:
        case Node.TYPE_DELETE:
            checksumOfValueNode((ValueNode) node);
            break;
        default:
            throw new Bug("unexpected node type, " + node.toString());
        }
    }
    
    private void checksumOfTopNode(TopNode node) {
        // Limited checking of pointers here. They are checked elsewhere.
        
        sum.update(node.getType());
        sum.updateWithLong(node.getTopNodeId());
        sum.updateWithLong(node.getId());
        
        int size = node.getSize();
        for (int i = 0; i < size; i++) {
            long time = node.getPointerTime(i);
            sum.updateWithLong(time);
        }
    }
    
    private void checksumOfKeyNode(KeyNode node) {
        sum.updateWithLong(node.getId());
        sum.updateWithBoolean(node.isSegmentLeaf());
        int size = node.getSizeAtTime(maxLookupTime);
        sum.updateWithLong(size);
        for (int i = 0; i < size; i++) {
            sum.updateWithLong(node.klongs[i]);
        }
    }
    
    private void checksumOfValueNode(ValueNode node) {
        sum.updateWithLong(node.getId());
        sum.updateWithBoolean(node.isDelete());
        if (!node.isDelete()) {
            byte[] value = node.getValue();
            sum.update(value, 0, value.length);
        }
    }
    
    
    // ======== Testing ========
    
    @Nano
    private static void test0() {
        Dag dag = DagTester.emptyDag(1);
        DagChecksum s1 = new DagChecksum(dag, Long.MAX_VALUE);
        long value1 = s1.compute();
        
        DagChecksum s2 = new DagChecksum(dag, Long.MAX_VALUE);
        long value2 = s2.compute();
        
        Assert.assertEquals(true, value1 != 0);
        Assert.assertEquals(value1, value2);
    }

    @Nano
    private static void testCreateTimeDiff() {
        Dag dag1 = DagTester.emptyDag(1);
        Dag dag2 = DagTester.emptyDag(2);
        long c1 = new DagChecksum(dag1).compute();
        long c2 = new DagChecksum(dag2).compute();
        Assert.assertEquals(false, c1 == c2);
    }
    
    @Nano
    private static void testValueDiff() {
        Dag dag1 = DagTester.emptyDag(1);
        PutData pd1 = dag1.newPutData();
        pd1.tt = 10;
        dag1.putKv(Keys.toSegments("/-key"), StringUtil.toBytes("value1"), pd1);
        long s1 = new DagChecksum(dag1).compute();
        
        Dag dag2 = DagTester.emptyDag(1);
        PutData pd2 = dag1.newPutData();
        pd2.tt = 10;
        dag2.putKv(Keys.toSegments("/-key"), StringUtil.toBytes("value2"), pd2);
        long s2 = new DagChecksum(dag2).compute();
        
        Assert.assertEquals(false, s1 == s2);
    }
}
