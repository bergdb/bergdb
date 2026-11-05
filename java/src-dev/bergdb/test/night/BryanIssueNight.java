package bergdb.test.night;

import java.io.File;
import java.io.IOException;
import bergdb.core.DbBuilder;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.DatabaseBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.stream.FileStream;
import bergdb.test.BryanIssue;

/**
 * A version of BryanIssue that uses the file system and more iterations.
 * 
 * @author Frans Lundberg
 */
public class BryanIssueNight extends BryanIssue {
    private String dbPath;
    
    public BryanIssueNight(TestEnvironment env) throws IOException {
        super(env);
        File tempDir = env.createTempDir();
        this.dbPath = tempDir.getAbsolutePath();
    }

    @Nano("night")
    private static void testIt(TestEnvironment env) throws Exception {
        new BryanIssueNight(env).go();
    }

    private void go() throws Exception {
        int id = 0;
       
        for (int i = 0; i < 100; i++) {
            id = runJob(id + 1);
        }
    }
    
    public void initDb(DatabaseBuilder builder) throws IOException {
        DbBuilder b = ((DatabaseBuilderImp) builder).getDbBuilder();
        b.mainStream(new FileStream(new File(dbPath)));
        b.testSetupExceptStream();
        b.startupDistance(20 * 1000000);
    }
}
