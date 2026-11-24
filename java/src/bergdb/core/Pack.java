package bergdb.core;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        Cache3.class,
        DatabaseId.class,
        Db.class,
        DbClock.class,
        DbHelper.class,
        DbScan.class,
        DbStarter.class,
        DbTester.class,
        DbTesterCoreKeys.class,
        DbTesterDelete.class,
        DbTesterDirtyCount.class,
        DbTesterFailure.class,
        DbTesterGetMany.class,
        DbTesterJavadoc.class,
        DbTesterLimits.class,
        DbTesterLongKeys.class,
        DbTesterMerge.class,
        DbTesterRestart.class,
        DbTesterStream.class,
        DbUtil.class,
        CapacityTester.class,
        CorruptStreamTester.class,
        Eviction.class,
        EvictionAccountingTester.class,
        EvictionReaderTester.class,
        FileStreamPowerLossTester.class,
        StorageFaultTester.class,
        InterruptTester.class,
        KeyModSet.class,
        Kv.class,
        LimitsTester.class,
        NodeChecksum.class,
        NodeCollection.class,
        NodeStream.class,
        NodeStreamTester.class,
        Pack.class,
        RerunException.class,
        Residents.class,
        Reclaim.class,
        Reclaim.Tester.class,
        ReclaimMaintainTester.class,
        ReclaimReaderTester.class,
        ReclaimRetentionTester.class,
        Reclaim.IterationInfo.class,
        StoredNode.class,
        StoredKeyNode.class,
        StoredTopNode.class,
        StoredTrans.class,
        StoredValueNode.class,
        SystemClock.class,
        Tester.class,
        Trans.class,
        TransCheckTester.class,
        TransNodes.class,
        TransSeq.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
