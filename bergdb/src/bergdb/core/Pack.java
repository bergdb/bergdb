package bergdb.core;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        CacheTester.class,
        Db.class,
        DbClock.class,
        DbTester.class,
        DbTesterGetMany.class,
        DbTesterRestart.class,
        DbTesterStream.class,
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
        Trans.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
