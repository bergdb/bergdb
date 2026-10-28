package bergdb.test.night;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Locale;

import bergdb.core.DagComparison;
import bergdb.core.Db;
import bergdb.core.DbScan;
import bergdb.core.KvComparison;
import bergdb.core.TestClock;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.SyncLevel;
import bergdb.pubimp.PubKeys;
import bergdb.stream.MemoryStream;

/**
 * Recreates issue with restart (ISSUE-150420-1). Found issue when trying database with 
 * data from ARX. Data used by this class is a small version of it without confidential data.
 * The startupDistance set to 100k to decrease problem size.
 * This class uses resource: Issue150420-data.txt which has 1000 lines (keys).
 * 
 * @author Frans Lundberg
 */
@SuppressWarnings("unused")
public class Issue150420 {
    private int errorCount;
    private int index;
    private TestEnvironment env;

    @Nano("night")
    private static void runTest(TestEnvironment env) throws Exception {
        new Issue150420().go(env);
    }
    
    private void go(TestEnvironment env) throws Exception {
        index = 0;
        errorCount = 0;
        this.env = env;
        
        List<String> keys = readKeys();
        
        MemoryStream stream = new MemoryStream();
        Db db1 = Db.builder()
                .clock(new TestClock())
                .startupDistance(100*1000)
                .mainStream(stream)
                .noEvict()
                .retainForever()
                .start();
        
        for (String key : keys) {
            if (index % 10 == 0) env.out().print(".");
            
            String ikey = PubKeys.u2i(key);
            db1.execute(db1.trans().put(ikey, new byte[10*1000 + index]));
            db1.sync(SyncLevel.ORDINARY);
            
            kvCompare(db1);
            //dagCompare(db1);
            //checkPointerInvariant(db1);
            
            // kvCompare() is the primary test. If this works, the test works.
            // dagCompare() and checkPointerInvariant() are helper test used to diagnose 
            // a kvCompare error.
            
            if (errorCount > 0) {
                break;
            }
            
            index++;
        }
        
        db1.stop();
        
        if (errorCount > 0) {
            throw new AssertionError("errorCount = " + errorCount);
        }
    }

    private boolean kvCompare(Db db1) {
        boolean kvCompare = KvComparison.comparisonWithRestarted(db1).compare();
        if (kvCompare == false) {
            errorCount++;
            env.out().println("index: " + index + " KV COMPARE ERROR.");
        }
        
        return kvCompare;
    }

    
    private boolean dagCompare(Db db1) {
        boolean dagCompare = DagComparison.comparisonWithRestarted(db1).compare();
        if (dagCompare == false) {
            errorCount++;
            env.out().println("index: " + index + " DAG COMPARE ERROR.");
        }
        
        return dagCompare;
    }
    
    private void diff(Db db1, Db db2) {
        Collection<String> one = getKeys(db1);
        Collection<String> two = getKeys(db2);
        one.removeAll(two);
        
        if (one.size() > 0) {
            env.out().println("DIFF:");
            for (String s : one) {
                env.out().println(s);
            }
        }
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

    public static List<String> readKeys() throws IOException {
        String resourceName = Issue150420.class.getSimpleName() + "-data.txt";
        InputStream in = Issue150420.class.getResourceAsStream(resourceName);
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

    public static List<String> testKeys() {
        int n = 1000;
        ArrayList<String> list = new ArrayList<String>(n);
        
        for (int i = 0; i < n; i++) {
            String key = String.format(Locale.US, "/mydir/key%03d", i);
            list.add(key);
        }
        
        return list;
    }
    
    public static List<String> testKeysBackwards() {
        int n = 1000;
        ArrayList<String> list = new ArrayList<String>(n);
        
        for (int i = 0; i < n; i++) {
            String key = String.format(Locale.US, "/mydir/key%03d", (n - 1 - i));
            list.add(key);
        }
        
        return list;
    }
    
    public static void main(String[] args) throws Exception {
        Issue150420.runTest(new SimpleTestEnvironment());
    }
}
