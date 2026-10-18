package bergdb.core;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        Cache2.class,
        Cache3.class,
        DatabaseId.class,
        Db.class,
        DbClock.class,
        DbHelper.class,
        DbScan.class,
        DbStarter.class,
        DbTester.class,
        DbTesterGetMany.class,
        DbTesterRestart.class,
        DbTesterStream.class,
        DbUtil.class,
        CapacityTester.class,
        Eviction.class,
        EvictionReaderTester.class,
        KeyModSet.class,
        Kv.class,
        NodeChecksum.class,
        NodeCollection.class,
        NodeStream.class,
        NodeStreamTester.class,
        Pack.class,
        PointerLocks.class,
        RerunException.class,
        Residents.class,
        Reclaim.class,
        Reclaim.Tester.class,
        ReclaimReaderTester.class,
        ReclaimRetentionTester.class,
        Reclaim.IterationInfo.class,
        StoredNode.class,
        StoredKeyNode.class,
        StoredTopNode.class,
        StoredTrans.class,
        StoredValueNode.class,
        Tester.class,
        Trans.class,
        TransNodes.class,
        TransSeq.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
