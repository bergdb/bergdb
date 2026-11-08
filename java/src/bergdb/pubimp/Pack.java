package bergdb.pubimp;

import bergdb.nanotest.IPack;
import bergdb.pub.CryptoKey;

public class Pack implements IPack {
    // It's OK to include classes from bergdb.pub. Don't want
    // Pack class in the public Javadoc API description.
    
    private static Class<?>[] classes = new Class<?>[] {
        ConnectionImp.class,
        CryptoKey.class,
        DatabaseBuilderImp.class,
        DatabaseImp.class,
        DataObjectsTester.class,
        DbArray.class,
        DbBoolean.class,
        DbByteArray.class,
        DbDouble.class,
        DbLong.class,
        DbString.class,
        DbObject.class,
        DbObjectFormatTester.class,
        DbValue.class,
        Entries.class,
        IndexManager.class,
        IndexDefinitionTester.class,
        IndexKeysTester.class,
        PubTesterIndexRaces.class,
        UseIndexBuilderImp.class,
        KvToObjectImp.class,
        ObjectFormat.class,
        ObjectFormatTester.class,
        Pack.class,
        PubKeys.class,
        PubInterruptTester.class,
        PubPromiseTester.class,
        PubTester.class,
        PubTesterComposite.class,
        PubTesterIndex.class,
        PubTesterIndexJobs.class,
        PubTesterNestedFields.class,
        PubTesterOutput.class,
        PubTesterPrimary.class,
        PrimaryHarness.class,
        Utf8ReadTester.class,
        WBuilderImp.class,
        TimeResolver.class,
        WTransaction.class,
        RwEnvironmentImp.class,
        RwTransaction.class,
        DbObjectTester.class,
        IndexReference.class,
        IndexHarness.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
