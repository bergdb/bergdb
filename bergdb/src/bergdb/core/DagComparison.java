package bergdb.core;

import java.io.PrintStream;
import java.util.Arrays;

import bergdb.common.Pair;
import bergdb.dag.Dag;
import bergdb.dag.DagNodeIterator;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.ReadOnlyStream;

/**
 * Used to compare whether two Dags are equal.
 * For testing.
 * 
 * @author Frans Lundberg
 */
public class DagComparison {
    private final Dag dag1;
    private final Dag dag2;
    private boolean printDiffs = false;
    private boolean printAll = false;
    private boolean stopAtDiff = true;
    private Pair<INode, INode> pair;
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
            .printDiffs(true).stopAtDiff(true).toStop(db2);
    }
    
    public DagComparison toStop(Db db2) {
        this.db2 = db2;
        return this;
    }
    
    public DagComparison printDiffs(boolean b) {
        this.printDiffs = b;
        return this;
    }
    
    public DagComparison printAll(boolean b) {
        this.printAll = b;
        return this;
    }
    
    public DagComparison stopAtDiff(boolean b) {
        this.stopAtDiff = b;
        return this;
    }
    
    public DagComparison out(PrintStream out) {
        this.out = out;
        return this;
    }
    
    public boolean compare() {
        boolean equal = true;
        NodePairIterator iter = new NodePairIterator(dag1, dag2);
        
        while ((pair = iter.next()) != null) {
            INode n1 = pair.getValue0();
            INode n2 = pair.getValue1();
            
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
    
    public Pair<INode, INode> getLastPair() {
        return pair;
    }
    
    private String compare(INode n1, INode n2) {
        
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
        case INode.TYPE_TOP_NODE:
            String diffString = compareTopNodes((TopNode) n1, (TopNode) n2);
            return diffString;
        case INode.TYPE_KEY_NODE:
            return compareKeyNodes((KeyNode) n1, (KeyNode) n2);
        case INode.TYPE_VALUE:
        case INode.TYPE_DELETE:
            return compareKeyNodes((ValueNode) n1, (ValueNode) n2);
        default:
            throw new Error("Bad node type, " + n1);
        }
    }

    private String compareKeyNodes(ValueNode n1, ValueNode n2) {
        boolean equal = Arrays.equals(n1.value, n2.value);
        return equal ? null : "Values not equal, " + n1 + ", " + n2;
    }

    private String compareKeyNodes(KeyNode n1, KeyNode n2) {
        int s1 = n1.size;
        int s2 = n2.size;
        
        if (s1 != s2) {
            return "KeyNode.size differs, " + s1 + " != " + s2 + ", " + n1 + ", " + n2 
                    + "\n" + keyNodePairToString(n1, n2);
        }
        
        for (int i = 0; i < s1; i++) {
            if (n1.klongs[i] != n2.klongs[i]) {
                return "KeyNode.klongs differ at " + i + ", " + n1 + ", " + n2;
            }
        }
        
        // could do more... pos, pointers?
        
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
        
        public Pair<INode, INode> next() {
            if (done) {
                return null;
            }
            
            INode n1 = iter1.next();
            INode n2 = iter2.next();
            
            if (n1 == null && n2 == null) {
                done = true;
                return null;
            }
            
            if (n1 == null || n2 == null) {
                done = true;
            }
            
            return new Pair<INode, INode>(n1, n2);
        }
    }
}
