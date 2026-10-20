package bergdb.core;

import java.io.PrintStream;
import java.util.Arrays;

import bergdb.common.Pair;
import bergdb.dag.Dag;
import bergdb.dag.DagNodeIterator;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.ReadOnlyStream;

/**
 * This class is used to compare whether two Dags are equal.
 * Useful for testing.
 * 
 * @author Frans Lundberg
 */
public class DagComparison {
    private final Dag dag1;
    private final Dag dag2;
    private boolean printDiffs = false;
    private boolean printAll = false;
    private boolean stopAtDiff = true;
    private Pair<Node, Node> pair;
    private PrintStream out = System.out;
    private Db db2 = null;    // database to stop.
    
    public DagComparison(Dag dag1, Dag dag2) {
        this.dag1 = dag1;
        this.dag2 = dag2;
    }
    
    public static DagComparison comparisonWithRestarted(Db db1) {
        db1.sync(SyncLevel.ORDINARY);
        
        AppendOnlyStream stream = db1.internal().getMainStream();
        ReadOnlyStream ro = new ReadOnlyStream(stream, false);
        Db db2 = Db.builder().mainStream(ro).start();
        
        return new DagComparison(db1.internal().dag(), db2.internal().dag())
            .printDiffs(true).stopAtDiff(true).dbToStop(db2);
    }
    
    public DagComparison dbToStop(Db db2) {
        // A more general post-compare callback could possibly be better.
        this.db2 = db2;
        return this;
    }
    
    public DagComparison printDiffs(boolean b) {
        this.printDiffs = b;
        return this;
    }
    
    public DagComparison stopAtDiff(boolean b) {
        this.stopAtDiff = b;
        return this;
    }
    
    /**
     * Returns true if dags are equal.
     */
    public boolean compare() {
        boolean equal = true;
        NodePairIterator iter = new NodePairIterator(dag1, dag2);
        
        while ((pair = iter.next()) != null) {
            Node n1 = pair.value0();
            Node n2 = pair.value1();
            
            String s = compare(n1, n2);
            if (s != null) {
                equal = false;
                if (printDiffs) {
                    out.println("DAG DIFF " + s);
                }
            }
            
            if (printAll) {
                out.println(n1);
                out.println(n2);
                out.println("--");
            }
            
            if (!equal && stopAtDiff) {
                break;
            }
            
            if (n1 == null || n2 == null) {
                break;
            }
        }
        
        if (db2 != null) {
            db2.stop();
        }
        
        return equal;
    }
    
    private String compare(Node n1, Node n2) {
        
        if (n1 == null && n2 == null) {
            return null;
        }
        
        if (n1 == null) {
            return "n1 is null, n2: " + n2;
        }
        
        if (n2 == null) {
            return "n2 is null, n1: " + n1;
        }
        
        
        int t1 = n1.getType();
        int t2 = n2.getType();
        
        if (t1 != t2) {
            return "Different nodes types, " + n1 + ", " + n2;
        }
        
        switch (n1.getType()) {
        case Node.TYPE_TOP_NODE:
            String diffString = compareTopNodes((TopNode) n1, (TopNode) n2);
            return diffString;
        case Node.TYPE_KEY_NODE:
            return compareKeyNodes((KeyNode) n1, (KeyNode) n2);
        case Node.TYPE_VALUE:
        case Node.TYPE_DELETE:
            return compareValueNodes((ValueNode) n1, (ValueNode) n2);
        default:
            throw new Error("Bad node type, " + n1);
        }
    }

    private String compareValueNodes(ValueNode n1, ValueNode n2) {
        long p1 = n1.getSpos();
        long p2 = n2.getSpos();
        
        if (p1 != p2) {
            return "spos of value nodes differ: " + p1 + " != " + p2 
                    + ", ids: " + n1.getId() + " " + n2.getId();
        }
        
        boolean equal = Arrays.equals(n1.value, n2.value);
        return equal ? null : "Values not equal, " + n1 + ", " + n2;
    }

    private String compareKeyNodes(KeyNode n1, KeyNode n2) {
        //
        // Note that key nodes can have different sizes and still be 
        // considered equal. A key node can exist in different parts of the graph
        // and have different sizes as long as it is long enough to match the
        // largest possible lookup time that can be used to access it.
        // This is because of the fact that a node (with a specific id) at two different
        // locations in the graph may be represented with one Java object or two 
        // distinct Java objects (if read from two different stream locations).
        //
        
        int minSize = Math.min(n1.size, n2.size);
        long id1 = n1.getId();
        long id2 = n2.getId();
        
        if (id1 != id2) {
            return "KeyNode.id differs, " + n1 + " != " + n2 
                    + "\n" + keyNodePairToString(n1, n2);
        }
        
        for (int i = 0; i < minSize; i++) {
            if (n1.klongs[i] != n2.klongs[i]) {
                return "KeyNode.klongs differ at " + i + ", " + n1 + ", " + n2;
            }
        }
        
        return null;
    }

    private String compareTopNodes(TopNode n1, TopNode n2) {
        if (n1.id != n2.id) {
            return "TopNode.id diff, " + n1 + ", " + n2;
        }
        
        if (n1.rootTime != n2.rootTime) {
            return "TopNode.rootTime diff, " + n1.rootTime + ", " + n2.rootTime;
        }
        
        if (n1.spos != n2.spos) {
            return "TopNode.spos diff, " + n1 + ", " + n2;
        }
        
        return null;
    }
    
    private String keyNodePairToString(KeyNode n1, KeyNode n2) {
        StringBuilder b = new StringBuilder();
        b.append("-- Key node 1:\n" + n1.print());
        b.append("-- Key node 2:\n" + n2.print());
        return b.toString();
    }
    
    /**
     * Iterates until at least one iterator returns null.
     */
    public static class NodePairIterator {
        private DagNodeIterator iter1;
        private DagNodeIterator iter2;
        private boolean done = false;
        
        public NodePairIterator(DagNodeIterator iter1, DagNodeIterator iter2) {
            this.iter1 = iter1;
            this.iter2 = iter2;
        }
        
        public NodePairIterator(Dag d1, Dag d2) {
            this(new DagNodeIterator(d1), new DagNodeIterator(d2));
        }
        
        public Pair<Node, Node> next() {
            if (done) {
                return null;
            }
            
            Node n1 = iter1.next();
            Node n2 = iter2.next();
            
            if (n1 == null && n2 == null) {
                done = true;
                return null;
            }
            
            if (n1 == null || n2 == null) {
                done = true;
            }
            
            return new Pair<Node, Node>(n1, n2);
        }
    }
}
