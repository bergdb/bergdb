package bergdb.core;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        CacheTester.class,
        DatabaseId.class,
        Db.class,
        DbClock.class,
        DbStarter1.class,
        DbStarter2.class,
        DbStarter3.class,
        DbTester.class,
        DbTesterGetMany.class,
        DbTesterRestart.class,
        DbTesterStream.class,
        DbUtil.class,
        KeyModSet.class,
        Kv.class,
        NodeStream.class,
        NodeStreamTester.class,
        Pack.class,
        RerunException.class,
        Reclaim.class,
        Reclaim.Tester.class,
        StoredNode.class,
        StoredKeyNode.class,
        StoredTopNode.class,
        StoredTrans.class,
        StoredValueNode.class,
        Trans.class,
        TransNodes.class,
        TransSeq.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
