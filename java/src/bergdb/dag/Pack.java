package bergdb.dag;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        AccessData.class,
        GetData.class,
        DagTester.class,
        KeyAccessPath.class,
        Klong.class,
        KlongIter.class,
        KlongWithPointer.class,
        NodeInfo.class,
        KeyNodeTester.class,
        MergeTester.class,
        Keys.class,
        Pack.class,
        Pointer.class,
        Spos.class,
        TopDs.class,
        TopNode.class,
        TopTester.class,
        ValueNode.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
