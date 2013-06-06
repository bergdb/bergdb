package kissdb.pubimp;

import kissdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        BlankConstructorFactory.class,
        ConnectionImp.class,
        DatabaseImp.class,
        DbBoolean.class,
        DbInt.class,
        DbLong.class,
        DbString.class,
        DbByteArray.class,
        DbArray.class,
        DbObject.class,
        IndexManager.class,
        IndexManager.Tester.class,
        UseIndexBuilderImp.class,
        KvToObjectImp.class,
        Pack.class,
        PubKeys.class,
        PubTester.class,
        PubTesterComposite.class,
        PubTesterIndex.class,
        PubTesterPrimary.class,
        PubUtil.class,
        WBuilderImp.class,
        WTransaction.class,
        RwEnvironmentImp.class,
        DbObjectTester.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
