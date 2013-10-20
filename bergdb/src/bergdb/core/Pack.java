package bergdb.core;

// TODO A. Fix classes - move some to coreds.
import bergdb.common.IPack;
import bergdb.coreds.AccessData;
import bergdb.coreds.GetData;
import bergdb.coreds.KeyAccessPath;
import bergdb.coreds.Keys;
import bergdb.coreds.TransactionNodes;

public class Pack implements IPack {
    
    private static Class<?>[] classes = new Class<?>[] {
        AccessData.class,
        CacheTester.class,
        Db.class,
        Db.Tester.class,
        DbClock.class,
        DbTester.class,
        DbTesterGetMany.class,
        DbTesterRestart.class,
        DbTesterStream.class,
        GetData.class,
        KeyAccessPath.class,
        KeyModSet2.class,
        Keys.class,
        Kv.class,
        NodeStream.class,
        NodeStreamTester.class,
        Pack.class,
        RerunException.class,
        Reclaim.class,
        Reclaim.Tester.class,
        StoredNode.class,
        Trans.class,
        TransactionNodes.class,
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
