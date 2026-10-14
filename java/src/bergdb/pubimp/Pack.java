package bergdb.pubimp;

import bergdb.nanotest.IPack;
import bergdb.pub.CryptoKey;

public class Pack implements IPack {
    // It's OK to include classes from bergdb.pub. Don't want
    // Pack class in the public Javadoc API description.
    
    private static Class<?>[] classes = new Class<?>[] {
        BlankConstructorFactory.class,
        ConnectionImp.class,
        CryptoKey.class,
        DatabaseBuilderImp.class,
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
        IndexEntryBuilder.class,
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
