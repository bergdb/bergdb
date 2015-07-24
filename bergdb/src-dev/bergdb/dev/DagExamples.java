package bergdb.dev;

import java.io.IOException;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.TestClock;
import bergdb.dag.Dag;
import bergdb.dag.Dag.NodeReader;
import bergdb.dag.Node;
import bergdb.dag.Keys;
import bergdb.dag.PutData;

/**
 * Dag examples for a document.
 * 
 * @author Frans Lundberg
 */
public class DagExamples {
    // See frans.DagExamples, possibility to merge.
    
    private static final int MAX_NODE_SIZE = 30;
    
    private static final NodeReader DUMMY_NODE_READER = new NodeReader() {
        public Node readNode(long spos) {
            throw new IllegalStateException("No nodeReader was set, use "
                    + Dag.class.getName() + ".setNodeReader().");
        }
    };
    
    /**
     * Default Dag created at time 10 with the default max node size.
     */
    public static Dag dag() {        
        return Dag.createEmpty(10, MAX_NODE_SIZE, DUMMY_NODE_READER);
    }
    
    /**
     * Creates an empty Dag with the specified max node size.
     */
    public static Dag dag(int maxNodeSize) {        
        return Dag.createEmpty(10, maxNodeSize, DUMMY_NODE_READER);
    }
    
    private DagExamples() {}
    
    public static void empty() {
        Dag g = dag();
        g.printGraph(System.out);
    }
    
    public static void simpleKey() {
        Dag g = dag();
        PutData pd = g.newPutData();
        pd.tt = 20;
        g.putKv(Keys.toSegments("/myKey"), Util.toBytes("v1"), pd);
        g.printGraph(System.out);
    }
    
    public static void longerKey() {
        Dag g = dag();
        PutData pd = g.newPutData();
        pd.tt = 20;
        g.putKv(Keys.toSegments("/myLongerKey"), Util.toBytes("v1"), pd);
        g.printGraph(System.out);
    }
    
    public static void severalKeys1() {
        Dag g = dag(8);
        PutData pd = g.newPutData();
        pd.tt = 20;
        
        for (int i = 0; i < 3; i++) {
            g.putKv(Keys.toSegments("/k" + i), Util.toBytes("v" + i), pd);
        }
        
        g.printGraph(System.out);
    }
    
    public static void severalKeys2() {
        Dag g = dag(8);
        PutData pd = g.newPutData();
        pd.tt = 20;
        
        for (int i = 2; i >= 0; i--) {
            g.putKv(Keys.toSegments("/k" + i), Util.toBytes("v" + i), pd);
        }
        
        g.printGraph(System.out);
    }
    
    public static void prefixDemo() {
        Dag g = dag();
        
        PutData pd = g.newPutData();
        pd.tt = 20;
        
        for (int i = 0; i < 4; i++) {
            g.putKv(Keys.toSegments("/prefix-" + i), Util.toBytes("v" + i), pd);
        }
        
        g.printGraph(System.out);
    }
    
    /**
     * Smallest example of a key node split.
     */
    public static void split() {
        Dag g = dag(8);
        
        for (int i = 0; i < 5; i++) {
            PutData pd = g.newPutData();
            pd.tt = 100 + i;
            g.putKv(Keys.toSegments("/firstx/k" + i), Util.toBytes("v" + i), pd);
        }
        
        g.printGraph(System.out);
    }
    
    /**
     * Example of Dag including a key node with multiple predecessors.
     */
    public static void noTree() throws IOException {
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup().clock(clock).maxNodeSize8().start();
        
        for (int i = 0; i < 10; i++) {
            db.execute(db.trans().put(Keys.toSegments("/firstx/k" + i), Util.toBytes("v" + i)));
        }
        
        db.execute(db.trans().put(Keys.toSegments("/firstx/k3-10"), Util.toBytes("v10")));
        
        Dag dag = db.internal().dag();
        dag.printGraph(System.out);
        
        //new VizFigure().go(dag, "no-tree.gv", false);
    }


    
    public static void main(String[] args) throws IOException {
        System.out.println("==== empty() ====");
        empty();
        
        System.out.println("==== simpleKey() ====");
        simpleKey();
        
        System.out.println("==== longerKey() ====");
        longerKey();
        
        System.out.println("==== severalKeys1() ====");
        severalKeys1();
        
        System.out.println("==== severalKeys2() ====");
        severalKeys2();
        
        System.out.println("==== prefixDemo() ====");
        prefixDemo();
        
        System.out.println("==== split() ====");
        split();
        
        System.out.println("==== noTree() ====");
        noTree();
    }
}
