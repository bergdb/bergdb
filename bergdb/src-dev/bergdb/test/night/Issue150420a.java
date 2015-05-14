package bergdb.test.night;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import bergdb.core.DagComparison;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.KvComparison;
import bergdb.core.SyncLevel;
import bergdb.core.TestClock;
import bergdb.dag.GetMany;
import bergdb.dag.INode;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.BasicTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pubimp.PubKeys;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.ReadOnlyStream;

/**
 * Problem at index = 298.
 */
@SuppressWarnings("unused")
public class Issue150420a {
    private int errorCount;
    private int index;
    private TestEnvironment env;
    private Db db2;

    @Nano("night")
    private static void runTest(TestEnvironment env) throws Exception {
        new Issue150420a().go(env);
    }
    
    private void go(TestEnvironment env) throws Exception {
        index = 0;
        errorCount = 0;
        this.env = env;
        
        List<String> keys = Issue150420.readKeys();
        
        env.out().println("keys.size : " + keys.size());
        
        MemoryStream stream = new MemoryStream();
        Db db1 = Db.builder()
                .clock(new TestClock())
                .startupDistance(100*1000)
                .mainStream(stream)
                .start();
        
        for (String key : keys) {
            //env.out().println("index: " + index);
            //if (index % 10 == 0) env.out().print(".");
            
            String ikey = PubKeys.u2i(key);
            db1.execute(db1.trans().put(ikey, new byte[10*1000 + index]));
            
            // TODO B. A place to work
            //db1.internal().dag().checkForwardPointerInvariant(db1.internal().getStartupPos());
            
            if (index == 298) {
                env.out().println("index: " + index);                
                kvCompare(db1);
                //dagCompare(db1);
                
                if (errorCount > 0) {
                    break;
                }
            }
            
            index++;
        }
        
        System.out.println("\nError count: " + errorCount);
        if (errorCount == 0) {
            return;
        }
        
        /*
        stream = stream.copy();
        Db db2 = Db.builder().mainStream(stream).build();
        
        db2.start(Db.StartParams.NULL, new Db.StartListener() {
            public void reportStartupDistance(long startupDistance) {
            }

            public void reportStartPos(long startPos) {
            }

            public void reportStartupTransactions(ArrayList<StoredTrans> transactions) {
                
                System.out.println("==== Startup transactions..." + transactions.size());
                for (StoredTrans s : transactions) {
                    System.out.println(s);
                    for (StoredNode n : s.nodes) {
                        System.out.println("    " + n);
                    }
                }
            }
        });*/
        
        diff(db1, db2);
        
        db1.stop();
        db2.stop();
    }

    private void kvCompare(Db db1) {
        db1.sync(SyncLevel.ORDINARY);
        AppendOnlyStream stream = db1.internal().getMainStream();
        ReadOnlyStream ro = new ReadOnlyStream(stream, false);
        
        System.out.println("Starting db2...");
        db2 = Db.builder().mainStream(ro).start();
        System.out.println("  db2 started.");
        
        KvComparison c = new KvComparison(db1, db2);
        boolean kvCompare = c.compare();
        
        if (kvCompare == false) {
            errorCount++;
            env.out().println("index: " + index + " KV COMPARE ERROR.");
        }
    }

    private void dagCompare(Db db1) {
        boolean dagCompare = DagComparison.comparisonWithRestarted(db1).compare();
        if (dagCompare == false) {
            errorCount++;
            env.out().println("index: " + index + " DAG COMPARE ERROR.");
        }
    }
    
    private void diff(Db db1, Db db2) {
        Collection<String> one = getKeys(db1);
        Collection<String> two = getKeys(db2);
        one.removeAll(two);
        
        String firstDiffKey = null;
        
        if (one.size() > 0) {
            env.out().println("DIFF:");
            for (String s : one) {
                if (firstDiffKey == null) {
                    firstDiffKey = s;
                }
                env.out().println(s);
            }
        }
             
        //env.out().println("==== path1 ====");
        //printPath(db1, firstDiffKey);
        
        //env.out().println("==== path2 ====");
        //printPath(db2, firstDiffKey);
        
        //System.out.println("Stream node @2950792:\n" + getNodeAt(db1, 2950792L).print("    "));
    }
    
    private void printPath(Db db, String key) {
        List<INode> path = DbUtil.getNodesOnPathToKv(db, key);
        String indent = "";
        for (INode n : path) {
            env.out().println(n.print(indent));
            indent = indent + "    ";
        }
    }
    
    
    private INode getNodeAt(Db db, long spos) {
        return db.getStream().readNode(spos);
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
        Issue150420a.runTest(new BasicTestEnvironment());
    }
}
