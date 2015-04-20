package bergdb.test.night;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.DbScan;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.pubimp.DatabaseImp;
import bergdb.stream.MemoryStream;

/**
 * Recreates issue with restart (ISSUE-150420-1). Found issue when trying database with 
 * data from ARX. Data used by this class is a small version of it without confidential data.
 * This class uses a resource.
 * 
 * @author Frans Lundberg
 */
public class Issue150420 {

    @Nano("night")
    private static void runTest(TestEnvironment env) throws Exception {
        new Issue150420().go(env);
    }
    
    private void go(TestEnvironment env) throws Exception {
        List<String> keys = readKeys();
        
        env.out().println("keys.size : " + keys.size());
        
        MemoryStream stream = new MemoryStream();
        
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().startupDistance(100*1000);
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database database = builder.start();
        Connection connection = database.connection();
        
        for (String key : keys) {
            connection.put(key, new byte[10*1000]);
        }
        connection.sync();
        
        Db db = ((DatabaseImp) database).getDb();
        DbScan.Result r1 = new DbScan(db).scan();
        
        MemoryStream stream2 = stream.copy();
        stream = null;
        db = null;
        connection = null;
        database = null;
        
        builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream2);
        database = builder.start();
        connection = database.connection();
        
        db = ((DatabaseImp) database).getDb();
        DbScan.Result r2 = new DbScan(db).scan();
        
        Assert.assertEquals("kv count", r1.kvCount, r2.kvCount);
        Assert.assertEquals("checksum", r1.checksum, r2.checksum);
    }

    private List<String> readKeys() throws IOException {
        String resourceName = Issue150420.class.getSimpleName() + "-data.txt";
        InputStream in = this.getClass().getResourceAsStream(resourceName);
        if (in == null) {
            throw new IllegalStateException("Unexpected, could not find resource " + resourceName);
        }
        BufferedReader reader = new BufferedReader(new InputStreamReader(in, "UTF-8"));
        
        ArrayList<String> list = new ArrayList<String>();
        
        while (true) {
            String line = reader.readLine();
            if (line == null) {
                break;
            }
            list.add(line);
        }
        
        return list;
    }
}
