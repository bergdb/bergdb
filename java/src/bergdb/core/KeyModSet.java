package bergdb.core;

import java.util.Arrays;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * An implementation of IKeyModSet that stores a fixed maximum number of hashOfKey-time pairs.
 * 
 * @author Frans Lundberg
 */
public class KeyModSet implements IKeyModSet {
    private static final int BIN_COUNT = 4;
    private final Bin[] bins;
    private static final int INITIAL_SIZE_OF_LONG_ARRAY = 4;
    private final int totalSize;
    private long lastTime = -1;     // The time of the newest add, or -1.
    
    public KeyModSet() {
        this(128*1000);
    }
    
    private KeyModSet(int totalSize) {
        assert totalSize > 0;
        if (totalSize % BIN_COUNT != 0) {
            throw new IllegalArgumentException("size was " + totalSize + ", must be dividable by " 
                    + BIN_COUNT + ".");
        }
        this.totalSize = totalSize;
        
        bins = new Bin[BIN_COUNT];
        bins[0] = new Bin(totalSize / BIN_COUNT);     // The other bins set to null to start with.
    }

    /**
     * Sets a new, empty set's coverage boundary to the last recovered commit's time.
     * Earlier reads cannot be validated (bergdb 005-70, option A).
     */
    void setFirstTime(long time) {
        assert time >= 0;
        assert bins[0].size == 0 && bins[0].firstTime == -1 && bins[1] == null;
        bins[0].firstTime = time;
    }
    
    /**
     * Returns the first (oldest) time that is currently handled.
     */
    public long getFirstTime() {
        long result = -1;
        for (int i = BIN_COUNT - 1; i >= 0; i--) {
            Bin bin = bins[i];
            if (bin == null) {
                continue;
            } else {
                result = bin.firstTime;
                break;
            }
        }
        
        return result;
    }
    
    public boolean modifiedAfter(long time, long hash) {
        int endBin = -1;
        
        for (int i = 0; i < BIN_COUNT; i++) {
            Bin bin = bins[i];
            if (bin == null) {
                break;
            }
            
            if (time >= bins[i].firstTime) {
                endBin = i;
            }
        }
        
        if (endBin == -1) {
            return true;
            // Too old time, not enough information, we must be on the 
            // safe side and report that it was modified.
        }
        
        long t = -1;
        boolean result = false;
        
        for (int i = 0; i <= endBin; i++) {
            t = bins[i].getTime(hash);
            if (t == -1) {
                continue;
            }
            
            if (t > time) {
                result = true;
                break;
            }
        }
        
        return result;
    }

    public final void add(long time, long hash) {
        if (bins[0].isFull()) {
            System.arraycopy(bins, 0, bins, 1, BIN_COUNT - 1);
            bins[0] = new Bin(totalSize / BIN_COUNT);
        }
        
        bins[0].add(time, hash);
        lastTime = time;
    }
    
    /**
     * Forgets the modifications at or before 'time', the first available lookup time of a
     * cut that Reclaim has just decided (Db.cutDecided; bergdb 026-10), as far as whole bins
     * hold them: the bins are kept down to the first one that begins at or before 'time',
     * and the older ones go. If that is the newest bin, a new bin begins at the last add, so
     * that a later cut forgets the pairs before it; the old one goes at once if the last add
     * is at or before 'time'. modifiedAfter() answers as before for every time from 'time'
     * on, and true for an earlier one, as for any time before the first time: such a
     * transaction is rerun. Until 026-10 the set kept its last 128,000 pairs, about 2.5 MB,
     * until newer ones pushed them out, also in a database emptied and then quiet (2.47 MB
     * in CountGates' G5).
     */
    void forgetUpTo(long time) {
        for (int i = 0; i < BIN_COUNT && bins[i] != null; i++) {
            if (bins[i].firstTime <= time) {
                Arrays.fill(bins, i + 1, BIN_COUNT, null);
                if (i == 0 && bins[0].size > 0) {
                    Bin next = new Bin(totalSize / BIN_COUNT);
                    next.firstTime = lastTime;
                    bins[1] = lastTime <= time ? null : bins[0];
                    bins[0] = next;
                }
                return;
            }
        }
    }
    
    /**
     * Yes, I need it :-).
     */
    private final int zero() {
        return 0;
    }
    
    /**
     * A bin to store hash-time pairs. Pairs can only be added, not deleted.
     */
    private class Bin {
        private final int maxSize;
        private int subSize;
        long firstTime;
        private final Object[] subBins;
        private int size;
        
        Bin(final int maxSize) {
            assert maxSize > 0;
            
            this.maxSize = maxSize;
            this.subSize = maxSize / 4;
            if (subSize == 0) {
                subSize = 1;
            }
            subBins = new Object[subSize];
            size = 0;
            firstTime = -1;
        }
        
        final boolean isFull() {
            assert size <= maxSize;
            return size == maxSize;
        }
        
        final void add(long time, long hash) {
            assert time >= firstTime;
            assert hash >= 0;
            assert !isFull();
            
            if (size == 0 && firstTime == -1) {
                firstTime = time;
            }
            size++;
            
            int index = (int) ((hash & Long.MAX_VALUE) % subSize);  // never negative (005-21)
            
            Object sub = subBins[index];
            long[] array;
            
            if (sub == null) {
                array = new long[INITIAL_SIZE_OF_LONG_ARRAY];
                for (int i = 0; i < array.length; i+=2) {
                    array[i] = -1;
                }
                subBins[index] = array;
            } else {
                array = (long[]) sub;
            }
            
            boolean set = false;
            final int len = array.length;
            for (int i = 0; i < len; i+=2) {
                if (array[i] == -1 || array[i + 1] == hash) {
                    array[i] = time;
                    array[i + 1] = hash;
                    set = true;
                    break;
                }
            }
            
            if (!set) {
                long[] newArray = new long[array.length * 2];
                System.arraycopy(array, 0, newArray, 0, array.length);
                for (int i = array.length; i < newArray.length; i += 2) {
                    newArray[i] = -1;
                }
                
                newArray[array.length] = time;
                newArray[array.length + 1] = hash;
                subBins[index] = newArray;
            }
        }
        
        /**
         * Returns the last time the hash was modified, or -1 if it does not exist in this bin.
         */
        final long getTime(long hash) {
            assert hash >= 0;
            int index = (int) ((hash & Long.MAX_VALUE) % subSize);  // never negative (005-21)
            
            Object sub = subBins[index];
            long[] array;
            
            if (sub == null) {
                return -1;
            } else {
                array = (long[]) sub;
                for (int i = 0; i < array.length; i += 2) {
                    if (array[i + 1] == hash && array[i] != -1) {
                        return array[i];
                    }
                }
            }
            
            return -1;
        }
    }

    
    // ======== Tests ========

    @Nano
    public static void testStartupBoundary() {
        KeyModSet s = new KeyModSet(8);
        s.setFirstTime(100);
        Assert.assertTrue(s.modifiedAfter(99, 5));
        Assert.assertFalse(s.modifiedAfter(100, 5));
        Assert.assertFalse(s.modifiedAfter(101, 5));
        s.add(110, 7);
        Assert.assertEquals(100L, s.getFirstTime());
        Assert.assertFalse(s.modifiedAfter(100, 5));
        Assert.assertTrue(s.modifiedAfter(100, 7));
        Assert.assertFalse(s.modifiedAfter(110, 7));
        // Once the initialized bin ages out, normal coverage limits take over.
        for (int i = 1; i <= 8; i++) {
            s.add(110 + i, 7);
        }
        Assert.assertEquals(112L, s.getFirstTime());
        Assert.assertTrue(s.modifiedAfter(100, 5));
        Assert.assertFalse(s.modifiedAfter(112, 5));
    }
    
    /**
     * A cut forgets the bins of modifications at or before its time (bergdb 026-10): the
     * answers from that time on are as before, and true before it.
     */
    @Nano
    public static void testForgetUpTo() {
        KeyModSet s = new KeyModSet(8);     // 4 bins of 2 pairs
        s.add(10, 1);
        s.add(11, 2);
        s.add(20, 3);
        s.add(21, 4);
        s.add(30, 5);                       // the bins begin at 30, 20 and 10
        s.forgetUpTo(25);                   // the bin of 20 is kept, the one of 10 goes
        Assert.assertEquals(20L, s.getFirstTime());
        Assert.assertTrue(s.modifiedAfter(25, 5));
        Assert.assertFalse(s.modifiedAfter(25, 3));
        Assert.assertFalse(s.modifiedAfter(20, 1));
        Assert.assertTrue("before the first time", s.modifiedAfter(15, 1));
        
        s.forgetUpTo(30);                   // nothing after 30: an empty bin from 30
        Assert.assertEquals(30L, s.getFirstTime());
        Assert.assertFalse(s.modifiedAfter(30, 5));
        Assert.assertTrue("before the first time", s.modifiedAfter(29, 7));
        s.add(31, 7);
        Assert.assertEquals(30L, s.getFirstTime());
        Assert.assertTrue(s.modifiedAfter(30, 7));
        Assert.assertFalse(s.modifiedAfter(31, 7));
        
        s.forgetUpTo(30);                   // the newest bin begins at 30: a new one at 31
        Assert.assertEquals(30L, s.getFirstTime());
        Assert.assertTrue(s.modifiedAfter(30, 7));
        s.add(40, 8);
        s.forgetUpTo(35);                   // the bin of 31 is the first at or before 35
        Assert.assertEquals(31L, s.getFirstTime());
        Assert.assertTrue(s.modifiedAfter(35, 8));
        Assert.assertFalse(s.modifiedAfter(35, 7));
        Assert.assertTrue("before the first time", s.modifiedAfter(30, 7));
    }
    
    @Nano
    public static void test1() {
        // Any request with time < 1 should return true.
        
        IKeyModSet s = new KeyModSet();
        s.add(1, 1234);
        Assert.assertTrue(s.modifiedAfter(0, 1234));
        Assert.assertFalse(s.modifiedAfter(1, 1234));
        Assert.assertFalse(s.modifiedAfter(9999, 1234)); 
        Assert.assertTrue(s.modifiedAfter(0, 9234));
        Assert.assertFalse(s.modifiedAfter(9999, 9234));
    }
    
    @Nano
    public static void test2() {
        IKeyModSet s = new KeyModSet();
        s.add(1001, 3);
        Assert.assertEquals(true, s.modifiedAfter(100, 3));
        Assert.assertEquals(false, s.modifiedAfter(2000, 3));
    }
    
    @Nano
    public static void test3() {
        IKeyModSet s = new KeyModSet();
        s.add(1, 3); 
        s.add(1001, 3);
        Assert.assertEquals(true, s.modifiedAfter(100, 3));
        Assert.assertEquals(true, s.modifiedAfter(1000, 3));
        Assert.assertEquals(false, s.modifiedAfter(1001, 3));
        Assert.assertEquals(false, s.modifiedAfter(99999, 3));
    }
    
    @Nano
    public static void testFutureTime() {
        IKeyModSet s = new KeyModSet();
        s.add(1001, 3);
        Assert.assertEquals(false, s.modifiedAfter(99999, 3));
        Assert.assertEquals(false, s.modifiedAfter(99999, 4));
    }
    
    @Nano
    public static void testResize() {
        // Resize of array needed.
        
        IKeyModSet s = new KeyModSet();
        for (int i = 0; i < INITIAL_SIZE_OF_LONG_ARRAY * 3; i++) {
            s.add(i, 0);
        }
        
        Assert.assertEquals(false, s.modifiedAfter(INITIAL_SIZE_OF_LONG_ARRAY * 3, 0));
        Assert.assertEquals(false, s.modifiedAfter(INITIAL_SIZE_OF_LONG_ARRAY * 3 - 1, 0));
        Assert.assertEquals(true, s.modifiedAfter(INITIAL_SIZE_OF_LONG_ARRAY * 3 - 2, 0));
    }
    
    @Nano
    public static void testBins1() {
        // + s.zero() avoid compiler warning.
        //
        KeyModSet s = new KeyModSet(8);
        assert KeyModSet.BIN_COUNT + s.zero() == 4;
        
        s.add(10, 0);
        s.add(20, 0);
        s.add(30, 0);
        s.add(30, 1);
        
        Assert.assertEquals(true, s.modifiedAfter(0, 0));
        Assert.assertEquals(true, s.modifiedAfter(29, 0));
        Assert.assertEquals(false, s.modifiedAfter(99, 0));
        Assert.assertEquals(true, s.modifiedAfter(29, 1));
        Assert.assertEquals(false, s.modifiedAfter(30, 1));
    }
    
    @Nano
    public static void testBins2() {
        // Adds enough hash-time pairs so we will create more than 4 bins.
        
        KeyModSet s = new KeyModSet(8);
        assert KeyModSet.BIN_COUNT + s.zero() == 4;
        
        s.add(3, 222);
        for (int i = 0; i < 16; i++) {
            s.add(5 + i*10, 333);
        }
        s.add(200, 444);
        
        Assert.assertEquals(true, s.modifiedAfter(150, 333));
        Assert.assertEquals(false, s.modifiedAfter(161, 333));
        Assert.assertEquals(false, s.modifiedAfter(99, 0));
        Assert.assertEquals(true, s.modifiedAfter(1, 111));    // true because of lack of info
        Assert.assertEquals(false, s.modifiedAfter(120, 111));
        
        Assert.assertTrue(s.getFirstTime() > 50);
        Assert.assertTrue(s.getFirstTime() < 150);
    }
    
    public static void main(String[] args) {
        testResize();
    }
}
