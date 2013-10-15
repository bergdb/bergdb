package bergdb.coreds;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * A specialized, performant collection to keep nodes in the node set of a transaction.
 * The three nodes types: TopNode, KeyNode, ValueNode are kept in separate arrays to allow
 * for type-specific optimizations.
 * 
 * @author Frans Lundberg
 */
public class TransactionNodes implements IDirtyNodes.TransactionNodesForMe, TransSequence.TransactionNodesForMe {
    //
    // The class must support the same node added to it several times without causing duplicates.
    // Should be a set of unique nodes.
    //
    
    private static final int INITIAL_SIZE = 64;
    private int counter;
    
    public int topSize;
    public TopNode[] topNodes;
    
    public int keySize;
    public KeyNode[] keyNodes;
    
    public int valueSize;
    public ValueNode[] valueNodes;
    public long[][] keys;         // key for each value node, size = valueSize
    public Choices[] choices;     // choices for each value node, size = valueSize
    
    public TransactionNodes() {
        topNodes = new TopNode[INITIAL_SIZE];
        topSize = 0;
        
        keyNodes = new KeyNode[INITIAL_SIZE];
        keySize = 0;
        
        valueNodes = new ValueNode[INITIAL_SIZE];
        valueSize = 0;
        
        keys = new long[INITIAL_SIZE][];
        
        choices = new Choices[INITIAL_SIZE];
        for (int i = 0; i < choices.length; i++) {
            choices[i] = new Choices();
        }
        
        counter = 0;
    }
    
    public final int size() {
        return topSize + keySize + valueSize;
    }
    
    public TransSequence.Tset createTSet(long tpos) {
        int size = topSize + keySize;
        INode[] nodes = new INode[size];
        System.arraycopy(topNodes, 0, nodes, 0, topSize);
        System.arraycopy(keyNodes, 0, nodes, topSize, keySize);
        
        TransSequence.Tset result = new TransSequence.Tset(nodes, tpos);
        return result;
    }
    
    public final long sumMemSize() {
        long sum = 0;
        
        for (int i = 0; i < topSize; i++) {
            sum += topNodes[i].getMemSize();
        }
        
        for (int i = 0; i < keySize; i++) {
            sum += keyNodes[i].getMemSize();
        }
        
        for (int i = 0; i < valueSize; i++) {
            sum += valueNodes[i].getMemSize();
        }
        
        return sum;
    }
    
    /**
     * Checks whether the collection of nodes contains the given node 
     * (compare by reference).
     */
    public boolean contains(INode node) {
        boolean result = false;
        
        outer: {
            for (int i = 0; i < topSize; i++) {
                if (topNodes[i] == node) {
                    result = true;
                    break outer;
                }
            }
            
            for (int i = 0; i < keySize; i++) {
                if (keyNodes[i] == node) {
                    result = true;
                    break outer;
                }
            }
            
            for (int i = 0; i < valueSize; i++) {
                if (valueNodes[i] == node) {
                    result = true;
                    break outer;
                }
            }
        }
        
        return result;
    }
    
    /**
     * For highest performance iterate directly on the three arrays: topNodes, keyNodes, valueNodes
     * which allows for type-specific optimizations.
     */
    public final INode get(int index) {
        INode result;
        
        if (index < topSize) {
            result = topNodes[index];
        } else if (index < (topSize + keySize)) {
            result = keyNodes[index - topSize];
        } else {
            result = valueNodes[index - (topSize + keySize)];
        }
        
        return result;
    }
    
    public final void addTopNode(TopNode node) {
        if (!node.isInTransactionNodes) {
            node.isInTransactionNodes = true;
            
            if (topSize == topNodes.length) {
                TopNode[] newNodes = new TopNode[topNodes.length * 2];
                System.arraycopy(topNodes, 0, newNodes, 0, topNodes.length);
                topNodes = newNodes;
            }
            
            topNodes[topSize] = node;
            topSize++;
        }
    }
    
    public final void addKeyNode(KeyNode node) {
        if (!node.isInTransactionNodes) {
            node.isInTransactionNodes = true;
            
            if (keySize == keyNodes.length) {
                KeyNode[] newNodes = new KeyNode[keyNodes.length * 2];
                System.arraycopy(keyNodes, 0, newNodes, 0, keyNodes.length);
                keyNodes = newNodes;
            }
            
            keyNodes[keySize] = node;
            keySize++;
        }
    }
    
    public final void addValueNode(ValueNode node, long[] key) {
        if (!node.isInTransactionNodes) {
            node.isInTransactionNodes = true;
            
            if (valueSize == valueNodes.length) {
                assert keys.length == valueNodes.length : keys.length + " != " + valueNodes.length;
                assert choices.length == valueNodes.length : choices.length + " != " + valueNodes.length;
                
                int newSize = valueNodes.length * 2;
                ValueNode[] newNodes = new ValueNode[newSize];
                System.arraycopy(valueNodes, 0, newNodes, 0, valueNodes.length);
                valueNodes = newNodes;
                
                long[][] newKeys = new long[newSize][];
                System.arraycopy(keys, 0, newKeys, 0, keys.length);
                keys = newKeys;
                
                Choices[] newChoices = new Choices[newSize];
                System.arraycopy(choices, 0, newChoices, 0, choices.length);
                for (int i = choices.length; i < newChoices.length; i++) {
                    newChoices[i] = new Choices();
                }
                choices = newChoices;
            }
            
            valueNodes[valueSize] = node;
            keys[valueSize] = key;
            valueSize++;
        }
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
        for (int i = 0; i < topSize; i++) {
            TopNode n = topNodes[i];
            for (int j = i+1; j < topSize; j++) {
                if (topNodes[j] == n) {
                    throw new AssertionError("Duplicate TopNode, " + i + ", " + j 
                            + ", topSize: " + topSize);
                }
            }
        }
        
        for (int i = 0; i < keySize; i++) {
            KeyNode n = keyNodes[i];
            for (int j = i+1; j < keySize; j++) {
                if (keyNodes[j] == n) {
                    throw new AssertionError("Duplicate KeyNode, " + i + ", " + j 
                            + ", keySize: " + keySize);
                }
            }
        }
        
        for (int i = 0; i < valueSize; i++) {
            ValueNode n = valueNodes[i];
            for (int j = i+1; j < valueSize; j++) {
                if (valueNodes[j] == n) {
                    throw new AssertionError("Duplicate ValueNode, " + i + ", " + j 
                            + ", valueSize: " + valueSize);
                }
            }
        }
        
        return true;
    }
    
    /**
     * Clears the set of transaction nodes so it becomes empty.
     * Caller must hold DB.writeLock.
     */
    public final void clear() {
        //
        // The arrays are reset to initialSize once in a while if they are long to 
        // avoid memory leak.
        // Prime numbers around 1000: 983, 991, 997.
        // Prime numbers around 100:  101, 103, 107.
        
        counter++;
        
        // TopNodes
        
        assert topSize <= topNodes.length;
        
        for (int i = 0; i < topSize; i++) {
            topNodes[i].isInTransactionNodes = false;
            topNodes[i] = null;
        }
        if (counter % 983 == 0 && topNodes.length > INITIAL_SIZE * 4) {
            topNodes = new TopNode[INITIAL_SIZE];
        }
        this.topSize = 0;
        
        // KeyNodes
        
        assert keySize <= keyNodes.length;
        
        for (int i = 0; i < keySize; i++) {
            keyNodes[i].isInTransactionNodes = false;
            keyNodes[i] = null;
        }
        if (counter % 991 == 0 && keyNodes.length > INITIAL_SIZE * 4) {
            keyNodes = new KeyNode[INITIAL_SIZE];
        }
        this.keySize = 0;
        
        // ValueNodes
        
        assert valueSize <= valueNodes.length;
        
        for (int i = 0; i < valueSize; i++) {
            valueNodes[i].isInTransactionNodes = false;
            valueNodes[i] = null;
            choices[i].clear();
            keys[i] = null;
        }
        
        if (counter % 997 == 0 && valueNodes.length > INITIAL_SIZE * 4) {
            valueNodes = new ValueNode[INITIAL_SIZE];
            choices = new Choices[INITIAL_SIZE];
            for (int i = 0; i < choices.length; i++) {
                choices[i] = new Choices();
            }
            keys = new long[INITIAL_SIZE][];
        }
        this.valueSize = 0;
    }
    
    public String toString() {
        return "node counts: " + topSize + ", " + keySize + ", " + valueSize;
    }
    
    public String print() {
        StringBuilder b = new StringBuilder();
        if (topSize > 0) {
            b.append("-- Top nodes --\n");
            for (int i = 0; i < topSize; i++) {
                b.append(topNodes[i].toString() + "\n");
            }
        }
        
        if (keySize > 0) {
            b.append("-- Key nodes --\n");
            for (int i = 0; i < keySize; i++) {
                b.append(keyNodes[i].print() + "\n");
            }
        }
        
        if (valueSize > 0) {
            b.append("-- Value nodes --\n");
            for (int i = 0; i < valueSize; i++) {
                b.append(valueNodes[i].toString() + "\n");
            }
        }
        
        return b.toString();
    }
    
    // ---- Testing ----
    
    @T
    public static void test1() {
        // Tests simple create, add, get, size.
        
        TransactionNodes nodes = new TransactionNodes();
        ValueNode v1 = new ValueNode();
        ValueNode v2 = new ValueNode();
        
        Assert.assertEquals(0, nodes.valueSize);
        nodes.addValueNode(v1, null);
        nodes.addValueNode(v2, null);
        Assert.assertEquals(v1, nodes.valueNodes[0]);
        Assert.assertEquals(v2, nodes.valueNodes[1]);
        Assert.assertEquals(2, nodes.valueSize);
    }
    
    @T
    public static void testIsInTransactionNodes() {
        TransactionNodes nodes = new TransactionNodes();
        ValueNode v1 = new ValueNode();
        
        Assert.assertEquals(false, v1.isInTransactionNodes());
        nodes.addValueNode(v1, null);
        Assert.assertEquals(true, v1.isInTransactionNodes());
        nodes.clear();
        Assert.assertEquals(false, v1.isInTransactionNodes());
    }
    
    @T
    public static void testLarge1() {
        int count = TransactionNodes.INITIAL_SIZE * 2 + 10;
        int index = count / 2;
        TransactionNodes nodes = new TransactionNodes();
        ValueNode v = null;
        
        for (int i = 0; i < count; i++) {
            ValueNode value = new ValueNode();
            if (i == index) {
                v = value;
            }
            nodes.addValueNode(value, null);
        }
        
        Assert.assertEquals(count, nodes.valueSize);
        Assert.assertEquals(v, nodes.valueNodes[index]);
        
        nodes.clear();
        Assert.assertEquals(0, nodes.valueSize);
    }
    
    @T
    public static void testLarge2() {
        //
        // Tests that length of this.nodes goes back to initialSize.
        //
        int count = TransactionNodes.INITIAL_SIZE * 4 + 10;
        TransactionNodes nodes = new TransactionNodes();
        
        for (int i = 0; i < count; i++) {
            ValueNode value = new ValueNode();
            nodes.addValueNode(value, null);
        }
        
        Assert.assertEquals(count, nodes.valueSize);
        
        for (int i = 0; i < 1000; i++) {
            nodes.clear();
        }
        
        Assert.assertEquals(INITIAL_SIZE, nodes.valueNodes.length);
    }
}
