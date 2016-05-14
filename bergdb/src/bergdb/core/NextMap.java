package bergdb.core;

import java.util.HashMap;

import bergdb.dag.Spos;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Pos-to-next-pos mappings. Used to update stream pointers to latest 
 * stream positions.
 * 
 * @author Frans Lundberg
 */
public class NextMap {
    private HashMap<Long, Long> map = new HashMap<Long, Long>();
    
    /**
     * Adds pos-to-nextPos mapping.
     * 
     * @param pos
     *      If pos is Spos.NULL, this method does nothing.
     */
    public void put(long pos, long nextPos) {
        if (Spos.isNull(pos)) {
            return;
        }
        
        if (!Spos.isValid(pos)) {
            throw new IllegalArgumentException("bad pos: " + pos);
        }
        
        if (!Spos.isValid(nextPos)) {
            throw new IllegalArgumentException("bad nextPos: " + nextPos);
        }
        
        if (!(nextPos > pos)) {
            throw new IllegalArgumentException("nextPos not greater than pos, " + nextPos + ", " + pos);
        }
        
        Long previousValue = map.get(pos);
        if (previousValue != null && previousValue > nextPos) {
            // do nothing; keep existing value since it is larger than nextPos
        } else {
            map.put(pos, nextPos);
        }
        
        /*
        if (previousValue != null) {
            throw new IllegalArgumentException(
                    "There was a mapping for pos " + pos + ", already. " +
                    "previousValue: " + previousValue + ", new value: " + nextPos);
        }
        */
    }
    
    public boolean containsKey(long pos) {
        return map.containsKey(pos);
    }
    
    public long forward(long pos) {
        long p = pos;
        
        while (true) {
            Long posLong = map.get(p);
            
            if (posLong == null) {
                break;
            } else {
                p = posLong.longValue();
            }
        }
        
        return p;
    }
    

    // ======== Tests ========
    
    private static NextMap m1() {
        NextMap m = new NextMap();
        m.put(10, 20);
        m.put(20, 30);
        m.put(50, 80);
        return m;
    }
    
    @Nano
    private static void testNextMapNoIncrease() {
        NextMap m = m1();
        Assert.assertEquals(123, m.forward(123));
        Assert.assertEquals(2, m.forward(2));
        Assert.assertEquals(30, m.forward(30));
    }
    
    @Nano
    private static void testNextMapForForwardsStepsTo30() {
        NextMap m = m1();
        Assert.assertEquals(30, m.forward(10));
        Assert.assertEquals(30, m.forward(20));
        Assert.assertEquals(30, m.forward(30));
    }
    
    @Nano
    private static void testNextMap3() {
        NextMap m = m1();
        Assert.assertEquals(80, m.forward(50));
        Assert.assertEquals(80, m.forward(80));
    }
}