package bergdb.coreds;

import bergdb.common.IPack;

public class Pack implements IPack {
    
    private static Class<?>[] classes = new Class<?>[] {
        GraphTester.class,
        Klong.class,
        KlongIter.class,
        KlongWithPointer.class,
        NodeInfo.class,
        KeyNodeTester.class,
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
