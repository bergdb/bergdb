package bergdb.coreds;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * An instance of this class keep a list (sequence) of node sets in the
 * startup interval. Each node set contains the key/top nodes of a particular 
 * transaction.
 * This class is not thread-safe, use external synchronization.
 * Normally, and object of this class is protected by Db.writeLock.
 * 
 * @author Frans Lundberg
 */
public class TransSequence {
    private TSet first;     // Head of linked list, may be null.
    private TSet last;     // Last set of linked list, may be null.
    private int size;
    
    public TransSequence() {
        first = null;
        last = null;
        size = 0;
    }
    
    public boolean isEmpty() {
        return first == null;
    }
    
    public int getSize() {
        return size;
    }
    
    /**
     * Adds a TSet to the end of the list.
     * 
     * @param tset  The TSet to add, condition: tset.tpos > last.tpos (or empty list).
     */
    public void add(TSet tset) {
        if (tset == null) throw new IllegalArgumentException("tset == null not allowed");
        
        if (isEmpty()) {
            first = tset;
            last = tset;
        } else {
            if (tset.tpos <= last.tpos) {
                throw new IllegalArgumentException(
                        "tset.tpos <= last.tpos, " + tset.tpos + ", " + last.tpos);
            }
            last.next = tset;
            last = tset;
        }
        
        size += 1;
    }
    
    /**
     * Removes all TSets with a tpos < pos.
     * 
     * @return The number of sets removed from the list.
     */
    public int removeBeforeSpos(long pos) {
        if (isEmpty()) {
            return 0;
        }
        
        assert first != null;
        
        while (first.tpos < pos) {
            if (first.next == null) {
                first = null;
                last = null;
                size -= 1;
                assert size == 0 : "size: " + size;
                break;
            } else {
                first = first.next;
                size -= 1;
            }
        }
        
        return 0;
    }
    
    /**
     * A TSet is a collection of all top node and key nodes for a particular 
     * transaction.
     */
    public static class TSet {
        /** Next element in the linked list. */
        public TSet next;
        
        /** Transaction time. */
        public long tt;
        
        /** Transaction stream position. */
        public long tpos;
        
        /** The top/key nodes of the transaction. */
        public INode[] nodes;
    }
    
    
    @T
    public static void test0() {
        TransSequence s = new TransSequence();
        
        Assert.assertEquals(0, s.getSize());
        Assert.assertTrue(s.isEmpty());
    }
    
    @T
    public static void test1() {
        TransSequence s = new TransSequence();
        TSet ts = new TSet();
        ts.tpos = 100;
        s.add(ts);
        
        Assert.assertEquals(1, s.getSize());
        Assert.assertFalse(s.isEmpty());
    }
    
    @T
    public static void test2() {
        TransSequence s = new TransSequence();
        TSet ts1 = new TSet();
        ts1.tpos = 100;
        TSet ts2 = new TSet();
        ts2.tpos = 200;
        
        s.add(ts1);
        s.add(ts2);
        
        Assert.assertEquals(2, s.getSize());
        Assert.assertFalse(s.isEmpty());
        s.removeBeforeSpos(99);
        Assert.assertEquals(2, s.getSize());
        s.removeBeforeSpos(100);
        Assert.assertEquals(2, s.getSize());
        s.removeBeforeSpos(101);
        Assert.assertEquals(1, s.getSize());
        s.removeBeforeSpos(400);
        Assert.assertEquals(0, s.getSize());
        Assert.assertTrue(s.isEmpty());
    }
}

// Linked list? 
// -> a -> b -> c
// Add new one, d, to end.
// -> a -> b -> c -> d.
// Remove from beginning. Set new head.
