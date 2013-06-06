package kissdb.test.java;

import kissdb.nanotest.Assert;
import kissdb.nanotest.T;

/**
 * A node in a 256-ary prefix tree.
 * 
 * @author Frans Lundberg
 */
public class JudyNode {
    //
    // Bytes are treated as if they were in range 0 to 255.
    //
    //
    private volatile byte[] values; // Set of possible next byte in key.
    private volatile JudyNode[] nodes; // children, nodes.length functions as capacity
    private int size;
    private byte[] label; // Label on edge to parent

    public JudyNode() {
        this(new byte[0]);
    }

    public JudyNode(byte[] label) {
        values = new byte[16];
        nodes = new JudyNode[2];
        size = 0;
        if (label == null) {
            throw new IllegalArgumentException("label == null not allowed");
        }
        this.label = label;
    }

    public int getSize() {
        return size;
    }
    
    public byte[] getLabel() {
        return this.label;
    }

    private final JudyNode get(byte b) {
        JudyNode node;
        if (values == null) {
            node = nodes[valueOf(b)];
        } else {
            int s = search(b);
            node = s % 10 == 0 ? nodes[s / 10] : null;
        }
        return node;
    }

    /**
     * Fast binary search for where a byte value "fits" the existing values.
     * Bytes are considered to have the value range from 0 to 255.
     * <ol>
     * <li>If b is equals to values[i] for any i, 10*i is returned.</li>
     * <li>If b is greater than values[i] and less than values[i+1] for any i in
     * the valid range, 10*i + 5 is returned.</li>
     * <li>If b is greater than values[size-1] or if size is 0,
     * Integer.MAX_VALUE is returned.</li>
     * <li>If b is less than values[0], -5 is returned.</li> </ul> Note that iff
     * returned value % 10 == 0 there was an exact match.
     */
    private int search(byte b) {
        // 
        // * Handle special cases.
        // * Do linear search for size <= 8.
        // * Otherwise do binary search.
        //
        
        int b2 = b < 0 ? b + 256 : b;
        
        if (size == 0) {
            return Integer.MAX_VALUE;
        }
        
        if (values == null) {   // Search is not needed when values == null
            throw new IllegalStateException("no search needed when " +
            		"values == null");
        }
        
        int minIndex = 0;
        int maxIndex = size - 1;
        int minValue = getValue(minIndex);
        int maxValue = getValue(maxIndex);
        int result;
        
        if (b2 > maxValue) {
            return Integer.MAX_VALUE;
        }
        if (b2 < minValue) {
            return -5;
        }
        
        label: if (size < 8) {
            // Linear search fast for this case
            
            result = Integer.MAX_VALUE;
            int value;
            for (int i = 0; i < size; i++) {
                value = values[i];
                if (value < 0) {
                    value += 256;
                }
                if (b2 < value) {
                    result = i * 10 - 5;
                    break label;
                }
                if (b2 == value) {
                    result = i * 10;
                    break label;
                }
            }
        } else {
            // Binary search faster for larger lengths of values
            
            while (true) {
                int midIndex = (minIndex + maxIndex) / 2;
                int midValue = getValue(midIndex);
                
                if (b2 == midValue) {
                    result = midIndex * 10;
                    break label;
                } else if (b2 < midValue) {
                    if (midIndex - minIndex == 1) {
                        result = midIndex * 10 - 5;
                        break label;
                    }
                    maxIndex = midIndex;
                    maxValue = midValue;
                } else if (b2 > midValue) {
                    if (maxIndex - midIndex == 1) {
                        result = midIndex * 10 + 5;
                        break label;
                    }
                    minIndex = midIndex;
                    minValue = midValue;
                } else {
                    throw new Error("Bug!");
                }
            }
        }

        return result;
    }
    
    private final int valueOf(byte b) {
        return b < 0 ? b + 256 : b;
    }
    
    private final int getValue(int index) {
        byte b = values[index];
        return b < 0 ? b + 256 : b;
    }

    private void set(byte b, JudyNode node) {
        int b2 = valueOf(b);

        if (values == null) {
            nodes[b2] = node;
            return;
        }

        int s = search(b);
        if (s % 10 == 0) { // If it already exists
            nodes[s / 10] = node;
        } else {
            size++;

            if (size == 129) {
                // special case, restructure data to plain array of nodes
                JudyNode[] newNodes = new JudyNode[256];
                for (int i = 0; i < size - 1; i++) {
                    int v = values[i];
                    if (v < 0) {
                        v += 256;
                    }
                    newNodes[v] = nodes[i];
                }
                values = null;
                nodes = newNodes;
                set(b, node);       // call again after values == null
                return;
            }

            if (size > getCapacity()) {
                increaseCapacity();
            }

            int insertIndex;
            if (s == Integer.MAX_VALUE) {
                insertIndex = size - 1;
                // no copying of old data required here
            } else {
                insertIndex = (s + 5) / 10;
                int lengthToCopy = size - 1 - insertIndex;
                insertIndex = (s + 5) / 10;
                System.arraycopy(values, insertIndex, values, insertIndex + 1,
                        lengthToCopy);
                System.arraycopy(nodes, insertIndex, nodes, insertIndex + 1,
                        lengthToCopy);
            }
            values[insertIndex] = b;
            nodes[insertIndex] = node;
        }
    }

    private void increaseCapacity() {
        int newCapacity = nodes.length * 2;
        JudyNode[] newNodes = new JudyNode[newCapacity];
        System.arraycopy(nodes, 0, newNodes, 0, nodes.length);
        nodes = newNodes;

        if (values.length < newCapacity) {
            byte[] newValues = new byte[newCapacity];
            System.arraycopy(values, 0, newValues, 0, values.length);
            values = newValues;
        }
    }

    private int getCapacity() {
        return nodes.length;
    }

    //private void remove(byte b) {
    //    throw new Error("not yet implemented");
    //}

    
    
    public static void speed1() {
        long t0, t1;
        int size = 10000000;
        double time;
        
        System.out.println("Testing lookup performance..");
        
        JudyNode n = new JudyNode();
        for (int i = 0; i < 128; i++) {
            n.set((byte) i, null);
        }
        
        t0 = System.nanoTime();
        for (int i = 0; i < size/4; i++) {
            n.get((byte) 64);
            n.get((byte) 64);
            n.get((byte) 64);
            n.get((byte) 64);
        }
        t1 = System.nanoTime();
        time = 1e-9 * (t1 - t0);
        
        System.out.println("Time per lookup is " + time / size);
        
        byte[] bytes = new byte[256];
        bytes[64] = 64;
        
        t0 = System.nanoTime();
        for (int k = 0; k < size; k++) {
            for (int i = 0; i < 256; i++) {
                if (bytes[i] == 64) {
                    break;
                }
            }
        }
        t1 = System.nanoTime();
        time = 1e-9 * (t1 - t0);
        
        System.out.println("Time per sequential lookup " + time / size);
    }
    
    public static void speedCopy() {
        long t0, t1;
        int size = 10000000;
        double time;
        
        System.out.println("Testing array copy performance..");
        
        byte[] bytes = new byte[64];
        
        
        
        t0 = System.nanoTime();
        for (int i = 0; i < size/4; i++) {
            System.arraycopy(bytes, 0, bytes, 1, 63);
            System.arraycopy(bytes, 0, bytes, 1, 63);
            System.arraycopy(bytes, 0, bytes, 1, 63);
            System.arraycopy(bytes, 0, bytes, 1, 63);
        }
        t1 = System.nanoTime();
        time = 1e-9 * (t1 - t0);
        
        System.out.println("Time per copy is " + time / size);
        
    }
    
    public static void main(String[] args) {
        speed1();
        speedCopy();
    }
    
    /**
     * Class for testing; uses Nanotest.
     */
    public static class Tester {
        @T
        public static void testCast() {
            // We cannot use cast from byte to char to make byte non-negative.
            byte b = -1;
            char c = (char) b;
            Assert.assertEquals("c", 65535, (int) c);
        }

        @T
        public static void testSet() {
            JudyNode n = new JudyNode();

            n.set((byte) 3, null); // 0
            Assert.assertEquals("size", 1, n.getSize());
            Assert.assertEquals(3, n.values[0]);

            n.set((byte) 12, null); // 1
            Assert.assertEquals("size", 2, n.getSize());
            Assert.assertEquals(12, n.values[1]);
        }

        @T
        public static void testSetUnordered() {
            JudyNode n = new JudyNode();

            n.set((byte) 3, null); // 0
            Assert.assertEquals("size", 1, n.getSize());
            Assert.assertEquals(3, n.values[0]);

            n.set((byte) 1, null); // 1
            Assert.assertEquals("size", 2, n.getSize());
            Assert.assertEquals(1, n.values[0]);
            Assert.assertEquals(3, n.values[1]);
        }

        @T
        public static void testSearch1() {
            JudyNode n = new JudyNode();

            n.set((byte) 1, null); // 0
            n.set((byte) 3, null); // 1

            Assert.assertEquals("size", 2, n.getSize());
            Assert.assertEquals(5, n.search((byte) 2));
            Assert.assertEquals(Integer.MAX_VALUE, n.search((byte) 4));
            Assert.assertEquals(-5, n.search((byte) 0));
        }

        @T
        public static void testGet() {
            JudyNode n = new JudyNode();
            JudyNode n2 = new JudyNode();

            n.set((byte) 1, null);
            n.set((byte) 133, n2);

            Assert.assertEquals(null, n.get((byte) 1));
            Assert.assertEquals(null, n.get((byte) 10));
            Assert.assertEquals(n2, n.get((byte) 133));
        }
        
        @T
        public static void testGetInLargeValuesArray() {
            JudyNode n = new JudyNode();
            
            JudyNode[] nodes = new JudyNode[16];
            for (int i = 0; i < nodes.length; i++) {
                nodes[i] = new JudyNode();
                n.set((byte) i, nodes[i]);
            }
            
            Assert.assertEquals(nodes[12], n.get((byte) 12));
            Assert.assertEquals(nodes[11], n.get((byte) 11));
            Assert.assertEquals(nodes[1], n.get((byte) 1));
            Assert.assertEquals(nodes[3], n.get((byte) 3));
        }
        
        @T
        public static void testGet2() {
            JudyNode n = new JudyNode();
            
            JudyNode[] nodes = new JudyNode[16];
            for (int i = nodes.length - 1; i >= 0; i--) {
                nodes[i] = new JudyNode();
                n.set((byte) i, nodes[i]);
            }
            
            Assert.assertEquals(nodes[12], n.get((byte) 12));
            Assert.assertEquals(nodes[11], n.get((byte) 11));
            Assert.assertEquals(nodes[1], n.get((byte) 1));
            Assert.assertEquals(nodes[3], n.get((byte) 3));
        }
        
        @T
        public static void testGetSpeed1() {
            JudyNode n = new JudyNode();
            int size = 1000;

            for (int i = 0; i < size; i++) {

                for (int j = 0; j < 64; j++) {
                    n.set((byte) (j * 2), null);
                }
            }
        }

        @T
        public static void testCapacity() {
            JudyNode n = new JudyNode();

            Assert.assertEquals(2, n.getCapacity());
            n.set((byte) 0, null);
            Assert.assertEquals(2, n.getCapacity());
            n.set((byte) 1, null);
            Assert.assertEquals(2, n.getCapacity());

            n.set((byte) 2, null);
            Assert.assertEquals(4, n.getCapacity());
            n.set((byte) 3, null);
            Assert.assertEquals(4, n.getCapacity());

            n.set((byte) 4, null);
            Assert.assertEquals(8, n.getCapacity());
        }
    }
}

/*
081127

Speed conclusion.
There does not seem to be a big advantage of using binary search of up to
128 values instead of a simple linear search.
Both search types are around 50 ns on sessi.
Linear search is so simple (three lines) that we can easily copy the code
into many places to avoid any method call overhead.
We could at every 10'th read, put the read byte in front of the values 
array to increase lookup performance.
Copying with System.arraycopy of 64 byte byte[] array one byte to the right
takes 16 ns only, so it may be worth it. However, a synch is required.

Direct lookup in array is a factor of 10-20 times faster (when over 128
children).
*/