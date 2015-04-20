package bergdb.test.night;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.DbScan;
import bergdb.core.DbUtil;
import bergdb.core.SyncLevel;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pubimp.PubKeys;
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
        
        Db db1 = Db.builder().startupDistance(100*1000).mainStream(stream).start();
        
        int index = 0;
        
        for (String key : keys) {
            String ikey = PubKeys.u2i(key);
            db1.execute(db1.trans().put(ikey, new byte[10*1000]));
            
            System.out.println("index: " + index);
            DbUtil.compareWithRestarted(db1);
            
            index++;
        }
        
        db1.sync(SyncLevel.ORDINARY);
        DbScan.Result r1 = new DbScan(db1).scan();
        //System.out.println("---- db1 ----");
        //db1.printGraph(System.out);
        
        stream = stream.copy();
        Db db2 = Db.builder().mainStream(stream).start();
        DbScan.Result r2 = new DbScan(db2).scan();
        
        //System.out.println("---- db2 ----");
        //db2.printGraph(System.out);
        
        Collection<String> one = getKeys(db1);
        Collection<String> two = getKeys(db2);
        one.removeAll(two);
        
        if (one.size() > 0) {
            env.out().println("DIFF:");
            for (String s : one) {
                env.out().println(s);
            }
        }
        
        Assert.assertEquals("kv count", r1.kvCount, r2.kvCount);
        Assert.assertEquals("checksum", r1.checksum, r2.checksum);
        
        db1.stop();
        db2.stop();
    }
        
    private List<String> getKeys(Db db) {
        GetMany g = db.newGetMany();
        g.lookupTime = Long.MAX_VALUE;
        g.startKey = null;
        g.stopCondition = new GetMany.DontStop();
        
        db.getMany(g);
        
        List<String> keys = new ArrayList<String>();
        
        for (Kvt kvt : g.result) {
            keys.add(Keys.toString(kvt.key));
        }
        return keys;
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
    
    public static void main(String[] args) throws Exception {
        Issue150420.runTest(new BasicTestEnvironment());
    }
}
