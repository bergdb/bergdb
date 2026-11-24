package bergdb.core;

import java.util.Arrays;
import java.util.Random;

import bergdb.dag.Keys;
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
    private final boolean spread;   // The sub-array index of a mixed hash (subIndex), or not.
    private long lastTime = -1;     // The time of the newest add, or -1.
    
    public KeyModSet() {
        this(128*1000);
    }
    
    private KeyModSet(int totalSize) {
        this(totalSize, true);
    }
    
    /**
     * 'spread' false gives the sub-array index used until bergdb 028-01, the hash modulo the
     * number of sub-arrays; for the tests and the probe (main) only, which compare the two.
     */
    KeyModSet(int totalSize, boolean spread) {
        assert totalSize > 0;
        this.spread = spread;
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
     * The index of the sub-array of a bin that holds 'hash', 0 to subSize - 1. Since bergdb
     * 028-01 it is the hash mixed by MurmurHash3's 64-bit finalizer (fmix64), modulo subSize.
     * Keys.hash mixes a key's 8-byte segments by "* 37 +" only, and modulo subSize (8,000)
     * the hashes of keys such as "/k/%010d", sequential or random, fell in few sub-arrays:
     * 128,000 keys in 500 of the 32,000, 256 pairs each, and a lookup of a key not added
     * scanned about 1,500 pairs; mixed, 21 (the probe, main). Only the index changed: a bin
     * finds a pair by its whole hash, so the answers of modifiedAfter() do not depend on the
     * index (testSpreadSameAnswers); Keys.hash is as before.
     */
    final int subIndex(long hash, int subSize) {
        if (!spread) {
            return (int) ((hash & Long.MAX_VALUE) % subSize);  // never negative (005-21)
        }
        return (int) ((mix(hash) >>> 1) % subSize);
    }
    
    /**
     * MurmurHash3's 64-bit finalizer, fmix64: each bit of the result depends on each bit of h.
     */
    static long mix(long h) {
        h ^= h >>> 33;
        h *= 0xff51afd7ed558ccdL;
        h ^= h >>> 33;
        h *= 0xc4ceb9fe1a85ec53L;
        h ^= h >>> 33;
        return h;
    }
    
    /**
     * The pairs that modifiedAfter(time, hash) scans, counted as getTime() scans them: each
     * slot of the sub-array of 'hash' in each bin it reads, up to the slot that holds the
     * hash. For the tests and the probe (bergdb 028-01): a count, not a time.
     */
    int pairsScanned(long time, long hash) {
        int endBin = -1;
        for (int i = 0; i < BIN_COUNT && bins[i] != null; i++) {
            if (time >= bins[i].firstTime) {
                endBin = i;
            }
        }
        int count = 0;
        for (int i = 0; i <= endBin; i++) {
            Bin bin = bins[i];
            long[] array = (long[]) bin.subBins[subIndex(hash, bin.subSize)];
            if (array == null) {
                continue;
            }
            for (int j = 0; j < array.length; j += 2) {
                count++;
                if (array[j + 1] == hash && array[j] != -1) {
                    if (array[j] > time) {
                        return count;
                    }
                    break;
                }
            }
        }
        return count;
    }
    
    /**
     * The sub-arrays' fill: the sub-arrays used, of all the bins' sub-arrays, the pairs in the
     * fullest, and the mean pairs of a used one. For the tests and the probe (bergdb 028-01).
     */
    long[] subArrayFill() {
        long used = 0;
        long largest = 0;
        long pairs = 0;
        for (int i = 0; i < BIN_COUNT && bins[i] != null; i++) {
            for (Object sub : bins[i].subBins) {
                if (sub == null) {
                    continue;
                }
                long[] array = (long[]) sub;
                int n = 0;
                for (int j = 0; j < array.length; j += 2) {
                    if (array[j] != -1) {
                        n++;
                    }
                }
                used++;
                pairs += n;
                largest = Math.max(largest, n);
            }
        }
        return new long[] {used, largest, used == 0 ? 0 : pairs / used};
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
            
            int index = subIndex(hash, subSize);
            
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
            int index = subIndex(hash, subSize);
            
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
    
    /**
     * The sub-arrays of 128,000 sequential keys are even since bergdb 028-01: a lookup scans
     * a few pairs a bin, not about 250. Counts, not times.
     */
    @Nano
    public static void testSpreadSequentialKeys() {
        long[] before = probe(false, 0, 128*1000);
        long[] after = probe(true, 0, 128*1000);
        Assert.assertTrue("before 028-01, few sub-arrays: " + before[0], before[0] < 1000);
        Assert.assertTrue("before 028-01, a large sub-array: " + before[1], before[1] > 200);
        Assert.assertTrue("before 028-01, pairs scanned: " + before[5], before[5] > 10*1000);
        Assert.assertTrue("sub-arrays used: " + after[0], after[0] > 30*1000);
        Assert.assertTrue("the largest sub-array: " + after[1], after[1] <= 20);
        Assert.assertTrue("mean pairs scanned for a key not added: " + after[5], after[5] <= 400);
        Assert.assertTrue("most pairs scanned for a key not added: " + after[6], after[6] <= 100);
        Assert.assertTrue("mean pairs scanned for a key added: " + after[3], after[3] <= 400);
    }
    
    /**
     * The conflict check's answers do not depend on the sub-array index (bergdb 028-01): a
     * set with the index of 028-01 and one with the index before it, given the same adds and
     * cuts, give the same modifiedAfter() and getFirstTime() for sequential and random hashes.
     */
    @Nano
    public static void testSpreadSameAnswers() {
        Random random = new Random(2801);
        long[] hashes = new long[3000];
        for (int i = 0; i < hashes.length; i++) {
            hashes[i] = i % 2 == 0 ? Keys.hash(Keys.toSegments(String.format("/k/%010d", i)))
                    : random.nextLong() & Long.MAX_VALUE;
        }
        
        for (int size : new int[] {8, 400, 128*1000}) {
            KeyModSet a = new KeyModSet(size, true);
            KeyModSet b = new KeyModSet(size, false);
            long time = 0;
            for (int step = 0; step < 20*1000; step++) {
                time += 1 + random.nextInt(3);
                long hash = hashes[random.nextInt(hashes.length)];
                a.add(time, hash);
                b.add(time, hash);
                if (random.nextInt(500) == 0) {
                    long cut = time - random.nextInt(200);
                    a.forgetUpTo(cut);
                    b.forgetUpTo(cut);
                }
                if (step % 97 == 0) {
                    Assert.assertEquals(b.getFirstTime(), a.getFirstTime());
                    for (int q = 0; q < 50; q++) {
                        long t = time - random.nextInt(size + 100);
                        long h = q % 10 == 0 ? random.nextLong() & Long.MAX_VALUE
                                : hashes[random.nextInt(hashes.length)];
                        Assert.assertEquals("size " + size + ", time " + t + ", hash " + h,
                                b.modifiedAfter(t, h), a.modifiedAfter(t, h));
                    }
                }
            }
        }
    }
    
    /**
     * Fills a set of 'n' pairs with the hashes of 'n' keys, of a kind: 0, "/k/%010d" sequential
     * from 0; 1, "/k/%010d" of random numbers; 2, two random 8-byte segments. Returns: the
     * sub-arrays used, the pairs in the fullest, the mean pairs of a used one; the pairs
     * scanned (pairsScanned) at the set's first time, when every bin is read, for a key added:
     * the mean in tenths and the most; and for a key not added: the mean in tenths and the
     * most. Integers only, as the Core's code (bergdb 005-79).
     */
    static long[] probe(boolean spread, int kind, int n) {
        KeyModSet s = new KeyModSet(n, spread);
        Random random = new Random(2801);
        long[] hashes = new long[2 * n];    // added: 0 to n - 1, not added: n to 2n - 1
        for (int i = 0; i < hashes.length; i++) {
            long[] key = kind == 2 ? new long[] {random.nextLong(), random.nextLong()}
                    : Keys.toSegments(String.format("/k/%010d",
                            kind == 0 ? i : (random.nextLong() >>> 1) % 10_000_000_000L));
            hashes[i] = Keys.hash(key);
        }
        for (int i = 0; i < n; i++) {
            s.add(i + 1, hashes[i]);
        }
        long[] fill = s.subArrayFill();
        long time = s.getFirstTime();
        long sumAdded = 0, maxAdded = 0, sumOther = 0, maxOther = 0;
        for (int i = 0; i < n; i++) {
            int c = s.pairsScanned(time, hashes[i]);
            sumAdded += c;
            maxAdded = Math.max(maxAdded, c);
            c = s.pairsScanned(time, hashes[n + i]);
            sumOther += c;
            maxOther = Math.max(maxOther, c);
        }
        return new long[] {fill[0], fill[1], fill[2], 
                sumAdded * 10 / n, maxAdded, sumOther * 10 / n, maxOther};
    }
    
    /**
     * The probe of bergdb 028-01: the sub-arrays and the pairs scanned a lookup (probe()), for
     * 128,000 keys of each kind, with the sub-array index before 028-01 (modulo) and with
     * today's (mixed). Counts only. Run: java -cp java/build/bergdb.jar bergdb.core.KeyModSet
     */
    public static void main(String[] args) {
        int n = 128*1000;
        System.out.println("KeyModSet probe (bergdb 028-01): " + n + " keys of each kind, "
                + BIN_COUNT + " bins of " + (n / BIN_COUNT / 4) + " sub-arrays; pairs scanned"
                + " at the first time, all bins read.");
        System.out.println("keys          index   sub-arrays  largest  mean"
                + "   scanned, added: mean  most   not added: mean  most");
        String[] kinds = {"sequential", "random /k/", "random bytes"};
        for (int kind = 0; kind < kinds.length; kind++) {
            for (boolean spread : new boolean[] {false, true}) {
                long[] r = probe(spread, kind, n);
                System.out.println(String.format("%-13s %-7s %10d  %7d  %4d  %21s  %4d  %16s  %4d",
                        kinds[kind], spread ? "mixed" : "modulo", r[0], r[1], r[2],
                        r[3] / 10 + "." + r[3] % 10, r[4], r[5] / 10 + "." + r[5] % 10, r[6]));
            }
        }
    }
}
