package bergdb.coreds;

import java.util.ArrayList;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

public class DbGraphTester {
    
    @T
    public static void test0() {
        DbGraph g = DbGraph.create(0);
        GetData gd = new GetData();
        
        byte[] result = g.getOne(0, Keys.toSegments("/-k1"), gd);
        
        Assert.assertTrue(result == null);
    }
    
    @T
    public static void test1() {
        // With choices
        DbGraph g = DbGraph.create(0);
        GetData gd = new GetData();
        final ArrayList<Integer> choices = new ArrayList<Integer>();
        
        gd.walker = new DbGraph.PointerListener() {
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                choices.add(pointerIndex);
            }
        };
        
        byte[] result = g.getOne(0, Keys.toSegments("/-k1"), gd);
        
        Assert.assertTrue(result == null);
        Assert.assertEquals(1, choices.size());
        Assert.assertEquals(0, choices.get(0).intValue());
    }
}
