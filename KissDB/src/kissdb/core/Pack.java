package kissdb.core;

import kissdb.common.IPack;
import kissdb.storage.BufferedStream;
import kissdb.storage.MetaBlock;
import kissdb.storage.RecoverableStream;
import kissdb.storage.StorageManager;
import kissdb.storage.StreamException;
import kissdb.storage.StreamFormatException;
import kissdb.storage.StreamIoException;

public class Pack implements IPack {
    
    private static Class<?>[] classes = new Class<?>[] {
        AccessData.class,
        BufferedStream.class,
        CacheTester.class,
        Db.class,
        Db.Tester.class,
        DbClock.class,
        DbTester.class,
        DbTesterGetMany.class,
        DbTesterStream.class,
        DirtyNodes2.class,
        GetData.class,
        KeyAccessPath.class,
        KeyModSet2.class,
        Keys.class,
        Klong.class,
        KlongIter.class,
        KlongWithPointer.class,
        Kv.class,
        MetaBlock.class,
        MetaBlock.Tester.class,
        NodeInfo.class,
        NodeStream.class,
        NodeStreamTester.class,
        KeyNodeTester.class,
        Pack.class,
        Pointer.class,
        RecoverableStream.class,
        RecoverableStream.Tester.class,
        RerunException.class,
        Reclaim.class,
        Reclaim.Tester.class,
        Spos.class,
        StoredNode.class,
        StorageManager.class,
        StreamException.class,
        StreamFormatException.class,
        StreamIoException.class,
        TopDs.class,
        TopNode.class,
        TopTester.class,
        Trans.class,
        TransactionNodes.class,
        ValueNode.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
