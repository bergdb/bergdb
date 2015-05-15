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
import bergdb.core.SyncLevel;
import bergdb.core.TestClock;
import bergdb.core.Trans;
import bergdb.core.Db.ExecuteData;
import bergdb.dag.GetMany;
import bergdb.dag.INode;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pubimp.PubKeys;
import bergdb.stream.MemoryStream;

@SuppressWarnings("unused")
public class Issue150420b {
    private int errorCount;
    private int index;
    private TestEnvironment env;

    @Nano("night")
    private static void runTest(TestEnvironment env) throws Exception {
        new Issue150420b().go(env);
    }
    
    private void go(TestEnvironment env) throws Exception {
        index = 0;
        errorCount = 0;
        this.env = env;
        
        List<String> keys = Issue150420.readKeys();
        //List<String> keys = Issue150420.testKeys();
        //List<String> keys = Issue150420.testKeysBackwards();
        
        MemoryStream stream = new MemoryStream();
        Db db1 = Db.builder()
                .clock(new TestClock())
                .startupDistance(100*1000)
                .mainStream(stream)
                .noEvict()
                .retainForever()
                .start();
        
        Trans.Listener listener = new Trans.Listener() {
            public void transExecuted(ExecuteData x) {
                System.out.println("== (" + index + ") t" + x.trans.tt + ", tpos:" + x.trans.tpos 
                        + ", stpos:" + x.transInfo.startupPos);
                int size = x.transNodes.size();
                for (int i = 0; i < size; i++) {
                    System.out.println(x.transNodes.get(i));
                }
                
                if (x.transInfo.gotDirtyNodes.size() > 0) {
                    System.out.print("Got dirty: ");
                    for (INode node : x.transInfo.gotDirtyNodes) {
                        System.out.print(node + "; ");
                    }
                    System.out.println();
                }
                
                System.out.println();
            }
        };
        
        for (String key : keys) {
            String ikey = PubKeys.u2i(key);
            Trans t = db1.trans().put(ikey, new byte[10*1000 + index]).build();
            t.listener = listener;
            
            db1.execute(t);
            db1.sync(SyncLevel.ORDINARY);
            
            //if (index == 21) {
            //    db1.printDag(System.out);
            //}
            
            kvCompare(db1);
            //dagCompare(db1);
            //checkPointerInvariant(db1);
            
            index++;
            
            if (errorCount > 0) {
                break;
            }
            
        }
        
        System.out.println("\nError count: " + errorCount);
        
        //System.out.println("==== db1 ====");
        //db1.printDag(System.out);
        
        db1.stop();
    }

    private boolean checkPointerInvariant(Db db) {
        try {
            db.internal().dag().checkForwardPointerInvariantApprox(db.internal().getStartupPos(), 15000);
        } catch (AssertionError e) {
            errorCount++;
            env.out().println("index: " + index + ", inv-forward-pointer\n" + e.getMessage());
            return false;
        }
        
        return true;
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
    
    public static void main(String[] args) throws Exception {
        Issue150420b.runTest(new BasicTestEnvironment());
    }
}
