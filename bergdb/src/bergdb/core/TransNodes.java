package bergdb.core;

import java.util.Iterator;

import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * A specialized, performant collection containing the nodes and keys included in one transaction.
 * The three nodes types: TopNode, KeyNode, ValueNode are kept in separate arrays to allow
 * for type-specific optimizations.
 * 
 * @author Frans Lundberg
 */
public final class TransNodes implements IDirtyNodes.TransNodesForMe, TransSeq.TransNodesForMe {
    //
    // The class must support the same node added to it several times without causing duplicates.
    // Should be a set of unique nodes.
    //
    
    private static final int INITIAL_SIZE = 64;
    private int counter;
    public long kvSize;    // total byte size of keys plus values
    
    public int topCount;
    public TopNode[] topNodes;
    
    public int keyCount;
    public KeyNode[] keyNodes;
    
    public int valueCount;
    public ValueNode[] valueNodes;
    public long[][] keys;         // key (segmented key) for each value node, size = valueSize
    
    
    public TransNodes() {
        topNodes = new TopNode[INITIAL_SIZE];
        topCount = 0;
        
        keyNodes = new KeyNode[INITIAL_SIZE];
        keyCount = 0;
        
        valueNodes = new ValueNode[INITIAL_SIZE];
        valueCount = 0;
        
        keys = new long[INITIAL_SIZE][];
        
        counter = 0;
        kvSize = 0;
    }
    
    public final void addTopNode(TopNode node) {
        if (!node.isInTransNodes) {
            assert assertNoDuplicateTopNodeId(node);
            
            node.isInTransNodes = true;
            
            if (topCount == topNodes.length) {
                TopNode[] newNodes = new TopNode[topNodes.length * 2];
                System.arraycopy(topNodes, 0, newNodes, 0, topNodes.length);
                topNodes = newNodes;
            }
            
            topNodes[topCount] = node;
            topCount++;
        }
    }

    public final void addKeyNode(KeyNode node) {
        if (!node.isInTransNodes) {
            node.isInTransNodes = true;
            
            if (keyCount == keyNodes.length) {
                KeyNode[] newNodes = new KeyNode[keyNodes.length * 2];
                System.arraycopy(keyNodes, 0, newNodes, 0, keyNodes.length);
                keyNodes = newNodes;
            }
            
            keyNodes[keyCount] = node;
            keyCount++;
        }
    }

    public final void addValueNode(ValueNode node, long[] key) {
        if (!node.isInTransactionNodes) {
            node.isInTransactionNodes = true;
            
            if (valueCount == valueNodes.length) {
                assert keys.length == valueNodes.length : keys.length + " != " + valueNodes.length;
                
                int newSize = valueNodes.length * 2;
                ValueNode[] newNodes = new ValueNode[newSize];
                System.arraycopy(valueNodes, 0, newNodes, 0, valueNodes.length);
                valueNodes = newNodes;
                
                long[][] newKeys = new long[newSize][];
                System.arraycopy(keys, 0, newKeys, 0, keys.length);
                keys = newKeys;
            }
            
            valueNodes[valueCount] = node;
            keys[valueCount] = key;
            
            valueCount++;
            kvSize += key.length * 8;
            if (node.value == null) {
                kvSize += 16;
            } else {
                kvSize += node.value.length;
            }
        }
    }
    
    public final void addIndexNode(Node node) {
        switch (node.getType()) {
        case Node.TYPE_TOP_NODE:
            addTopNode((TopNode) node);
            break;
        case Node.TYPE_KEY_NODE:
            addKeyNode((KeyNode) node);
            break;
        default:
            throw new IllegalStateException("Not an index node, node.getType(), " + node.getType());
        }
    }

    public final int size() {
        return topCount + keyCount + valueCount;
    }

    /** 
     * Sets isDirty = false for all index nodes.
     */
    public void clean() {
        for (int i = 0; i < topCount; i++) {
            topNodes[i].setDirty(false);
        }
        
        for (int i = 0; i < keyCount; i++) {
            keyNodes[i].setDirty(false);
        }
    }

    /**
     * Clears the set of transaction nodes so it becomes empty.
     */
    public final void clear() {
        //
        // The arrays are reset to initialSize once in a while if they are long to 
        // avoid memory leak. Prime numbers are used.
        
        counter++;
        kvSize = 0;
        
        // TopNodes
        
        assert topCount <= topNodes.length;
        
        for (int i = 0; i < topCount; i++) {
            topNodes[i].isInTransNodes = false;
            topNodes[i] = null;
        }
        
        if (counter % 997 == 0 && topNodes.length > INITIAL_SIZE * 4) {
            topNodes = new TopNode[INITIAL_SIZE];
        }
        
        this.topCount = 0;
        
        // KeyNodes
        
        assert keyCount <= keyNodes.length;
        
        for (int i = 0; i < keyCount; i++) {
            keyNodes[i].isInTransNodes = false;
            keyNodes[i] = null;
        }
        
        if (counter % 991 == 0 && keyNodes.length > INITIAL_SIZE * 4) {
            keyNodes = new KeyNode[INITIAL_SIZE];
        }
        
        this.keyCount = 0;
        
        // ValueNodes
        
        assert valueCount <= valueNodes.length;
        
        for (int i = 0; i < valueCount; i++) {
            valueNodes[i].isInTransactionNodes = false;
            valueNodes[i] = null;
            keys[i] = null;
        }
        
        if (counter % 983 == 0 && valueNodes.length > INITIAL_SIZE * 4) {
            valueNodes = new ValueNode[INITIAL_SIZE];
            keys = new long[INITIAL_SIZE][];
        }
        
        this.valueCount = 0;
    }
    
    public Iterator<Node> indexNodeIterator() {
        return new Iterator<Node>() {
            private int index = 0;
            private final int total = topCount + keyCount;

            public boolean hasNext() {
                return index < total;
            }

            public Node next() {
                Node node = get(index);
                index++;
                return node;
            }

            public void remove() {
                throw new UnsupportedOperationException("remove() not supported");
            }
        };
    }

    /**
     * Checks whether the collection of nodes contains the given node 
     * (compare by reference).
     */
    public boolean contains(Node node) {
        boolean result = false;
        
        outer: {
            for (int i = 0; i < topCount; i++) {
                if (topNodes[i] == node) {
                    result = true;
                    break outer;
                }
            }
            
            for (int i = 0; i < keyCount; i++) {
                if (keyNodes[i] == node) {
                    result = true;
                    break outer;
                }
            }
            
            for (int i = 0; i < valueCount; i++) {
                if (valueNodes[i] == node) {
                    result = true;
                    break outer;
                }
            }
        }
        
        return result;
    }

    public final long sumMemSize() {
        long sum = 0;
        
        for (int i = 0; i < topCount; i++) {
            sum += topNodes[i].getMemSize();
        }
        
        for (int i = 0; i < keyCount; i++) {
            sum += keyNodes[i].getMemSize();
        }
        
        for (int i = 0; i < valueCount; i++) {
            sum += valueNodes[i].getMemSize();
        }
        
        return sum;
    }
    
    /**
     * For highest performance iterate directly on the three arrays: topNodes, keyNodes, valueNodes
     * which allows for type-specific optimizations; otherwise the user of this
     * class can iterate all nodes using size() and get() methods.
     */
    public final Node get(int index) {
        Node result;
        
        if (index < topCount) {
            result = topNodes[index];
        } else if (index < (topCount + keyCount)) {
            result = keyNodes[index - topCount];
        } else {
            result = valueNodes[index - (topCount + keyCount)];
        }
        
        return result;
    }
    
    /**
     * Checks for no duplicates.
     *  
     * @throws AssertionError  
     *              If there are duplicates.
     * @return true  
     *              Always returns true when the method returns normally.
     */
    public boolean assertNoDuplicates() {
        for (int i = 0; i < topCount; i++) {
            TopNode n = topNodes[i];
            for (int j = i+1; j < topCount; j++) {
                if (topNodes[j] == n) {
                    throw new AssertionError("Duplicate TopNode, " + i + ", " + j 
                            + ", topSize: " + topCount);
                }
            }
        }
        
        for (int i = 0; i < keyCount; i++) {
            KeyNode n = keyNodes[i];
            for (int j = i+1; j < keyCount; j++) {
                if (keyNodes[j] == n) {
                    throw new AssertionError("Duplicate KeyNode, " + i + ", " + j 
                            + ", keySize: " + keyCount);
                }
            }
        }
        
        for (int i = 0; i < valueCount; i++) {
            ValueNode n = valueNodes[i];
            for (int j = i+1; j < valueCount; j++) {
                if (valueNodes[j] == n) {
                    throw new AssertionError("Duplicate ValueNode, " + i + ", " + j 
                            + ", valueSize: " + valueCount);
                }
            }
        }
        
        return true;
    }

    public String toString() {
        return "node counts: " + topCount + ", " + keyCount + ", " + valueCount;
    }
    
    public String print() {
        StringBuilder b = new StringBuilder();
        if (topCount > 0) {
            b.append("-- Top nodes --\n");
            for (int i = 0; i < topCount; i++) {
                b.append(topNodes[i].toString() + "\n");
            }
        }
        
        if (keyCount > 0) {
            b.append("-- Key nodes --\n");
            for (int i = 0; i < keyCount; i++) {
                b.append(keyNodes[i].print() + "\n");
            }
        }
        
        if (valueCount > 0) {
            b.append("-- Value nodes --\n");
            for (int i = 0; i < valueCount; i++) {
                b.append(valueNodes[i].toString() + "\n");
            }
        }
        
        return b.toString();
    }
    
    
    // ======== Testing ========
    
    /** Assert that there is no existing top node with same top node id. */
    private boolean assertNoDuplicateTopNodeId(TopNode node) {
        int id1 = node.topNodeId;
        for (int i = 0; i < topCount; i++) {
            int id2 = topNodes[i].topNodeId;
            if (id2 == id1) {
                throw new AssertionError("Cannot add TopNode with same topNodeId as existing one, " 
                        + "existing: " + topNodes[i] + ", to add: " + node);
            }
        }
        return true;
    }

    @Nano
    public static void test1() {
        // Tests simple create, add, get, size.
        
        TransNodes nodes = new TransNodes();
        ValueNode v1 = ValueNode.createDelete();
        ValueNode v2 = ValueNode.createDelete();
        
        Assert.assertEquals(0, nodes.valueCount);
        nodes.addValueNode(v1, new long[0]);
        nodes.addValueNode(v2, new long[0]);
        Assert.assertEquals(v1, nodes.valueNodes[0]);
        Assert.assertEquals(v2, nodes.valueNodes[1]);
        Assert.assertEquals(2, nodes.valueCount);
    }
    
    @Nano
    public static void testLarge1() {
        int count = TransNodes.INITIAL_SIZE * 2 + 10;
        int index = count / 2;
        TransNodes nodes = new TransNodes();
        ValueNode v = null;
        
        for (int i = 0; i < count; i++) {
            ValueNode value = ValueNode.createDelete();
            if (i == index) {
                v = value;
            }
            nodes.addValueNode(value, new long[0]);
        }
        
        Assert.assertEquals(count, nodes.valueCount);
        Assert.assertEquals(v, nodes.valueNodes[index]);
        
        nodes.clear();
        Assert.assertEquals(0, nodes.valueCount);
    }
    
    @Nano
    public static void testLarge2() {
        //
        // Tests that length of this.nodes goes back to initialSize.
        //
        int count = TransNodes.INITIAL_SIZE * 4 + 10;
        TransNodes nodes = new TransNodes();
        
        for (int i = 0; i < count; i++) {
            ValueNode value = ValueNode.createDelete();
            nodes.addValueNode(value, new long[0]);
        }
        
        Assert.assertEquals(count, nodes.valueCount);
        
        for (int i = 0; i < 1100; i++) {
            nodes.clear();
        }
        
        Assert.assertEquals(INITIAL_SIZE, nodes.valueNodes.length);
    }
    
    @Nano
    public static void testIndexNodeIterator1() {
        KeyNode k1 = new KeyNode();
        KeyNode k2 = new KeyNode();
        Node[] expected = new Node[]{k1, k2};
        
        TransNodes transNodes = new TransNodes();
        transNodes.addKeyNode(k1);
        transNodes.addKeyNode(k2);
        
        int index = 0;
        Iterator<Node> nodes = transNodes.indexNodeIterator();
        while (nodes.hasNext()) {
            Assert.assertEquals(expected[index], nodes.next());
            index++;
        }
        
        Assert.assertEquals(expected.length, index);
    }
    
    @Nano
    public static void testIndexNodeIterator2() {
        TransNodes transNodes = new TransNodes();
        Assert.assertFalse(transNodes.indexNodeIterator().hasNext());
    }
    
    @Nano
    public static void testIndexNodeIterator3() {
        KeyNode k1 = new KeyNode();
        KeyNode k2 = new KeyNode();
        TopNode t1 = TopNode.createDummy(1);
        Node[] expected = new Node[]{t1, k1, k2};
        
        TransNodes transNodes = new TransNodes();
        transNodes.addKeyNode(k1);
        transNodes.addKeyNode(k2);
        transNodes.addTopNode(t1);
        
        int index = 0;
        Iterator<Node> nodes = transNodes.indexNodeIterator();
        while (nodes.hasNext()) {
            Assert.assertEquals(expected[index], nodes.next());
            index++;
        }
        
        Assert.assertEquals(expected.length, index);
    }
}
