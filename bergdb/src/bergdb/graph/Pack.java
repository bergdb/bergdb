package bergdb.graph;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        AccessData.class,
        GetData.class,
        GraphTester.class,
        KeyAccessPath.class,
        Klong.class,
        KlongIter.class,
        KlongWithPointer.class,
        NodeInfo.class,
        KeyNodeTester.class,
        Keys.class,
        Pack.class,
        Pointer.class,
        Spos.class,
        TopDs.class,
        TopNode.class,
        TopTester.class,
        TransNodes.class,
        TransSeq.class,
        ValueNode.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
