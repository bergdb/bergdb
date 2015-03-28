package bergdb.pubimp;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        BlankConstructorFactory.class,
        ConnectionImp.class,
        DatabaseImp.class,
        DbArray.class,
        DbBoolean.class,
        DbByteArray.class,
        DbInt.class,
        DbLong.class,
        DbString.class,
        DbObject.class,
        DbValue.class,
        Entries.class,
        FieldIndexFunction.Tester.class,
        IndexManager.class,
        IndexManager.Tester.class,
        UseIndexBuilderImp.class,
        KvToObjectImp.class,
        Pack.class,
        PubKeys.class,
        PubTester.class,
        PubTesterComposite.class,
        PubTesterIndex.class,
        PubTesterNestedFields.class,
        PubTesterPrimary.class,
        PubUtil.class,
        SortBytesBuilder.class,
        WBuilderImp.class,
        TimeResolver.class,
        WTransaction.class,
        RwEnvironmentImp.class,
        DbObjectTester.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
