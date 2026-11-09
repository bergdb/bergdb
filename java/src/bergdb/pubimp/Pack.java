package bergdb.pubimp;

import bergdb.nanotest.IPack;
import bergdb.pub.CryptoKey;
import bergdb.pub.DbArray;
import bergdb.pub.DbBoolean;
import bergdb.pub.DbByteArray;
import bergdb.pub.DbDouble;
import bergdb.pub.DbLong;
import bergdb.pub.DbObject;
import bergdb.pub.DbString;
import bergdb.pub.DbValue;

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
        FormatFuzzer.class,
        IndexManager.class,
        IndexDefinitionTester.class,
        IndexKeysTester.class,
        PubTesterIndexRaces.class,
        IndexBuilderImp.class,
        ObjectKeysTester.class,
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
        PubTesterCoreKeys.class,
        PubTesterIndex.class,
        PubTesterIndexJobs.class,
        PubTesterJavadoc.class,
        PubTesterJavadocRest.class,
        PubTesterLongKeys.class,
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
        IndexHarness.class,
        IndexJobsHarness.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
