package bergdb.coreds;

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
        // With choices != null.
        DbGraph g = DbGraph.create(0);
        GetData gd = new GetData();
        gd.choices = new Choices();
        
        byte[] result = g.getOne(0, Keys.toSegments("/-k1"), gd);
        
        Assert.assertTrue(result == null);
        Assert.assertEquals(1, gd.choices.getSize());
        Assert.assertEquals(0, gd.choices.get(0));
    }
}
