package bergdb.core;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        CacheTester.class,
        Db.class,
        Db.Tester.class,
        DbClock.class,
        DbTester.class,
        DbTesterGetMany.class,
        DbTesterRestart.class,
        DbTesterStream.class,
        KeyModSet2.class,
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
        StoredValueNode.class,
        Trans.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
