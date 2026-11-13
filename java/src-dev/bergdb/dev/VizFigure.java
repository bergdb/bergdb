package bergdb.dev;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.HashSet;
import java.util.Set;

import bergdb.core.Db;
import bergdb.core.TestNodeSize;
import bergdb.core.Trans;
import bergdb.dag.Dag;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;

/**
 * This class can generate a GraphViz dot file that can be plotted
 * with graphviz.
 * 
 * <pre>
 * See http://www.graphviz.org/.
 * Install graphviz on Ubuntu:
 *   sudo apt-get install graphviz graphviz-doc
 * Create svg file with:
 *   dot -Tsvg -O 1.gv
 *   
 * Run java and create SVG file:
 *   j bergdb.db.VizFigure; dot -Tsvg -O 1.gv
 * </pre>
 */
public class VizFigure {
    Dag dag;
    Writer writer;
    boolean includeValues;
    
    /** 
     * Creates a new object; use a new object for every dot-file generation.
     */
    public VizFigure() {
        includeValues = false;
    }
    
    /**
     * Creates the GraphViz dot file.
     */
    public void go(Dag dag, String filename, boolean includeValues) throws IOException {
        FileOutputStream fout = new FileOutputStream(filename);
        this.dag = dag;
        this.includeValues = includeValues;
        
        try {
            writer = new OutputStreamWriter(fout, "UTF-8");
            reallyGo();
        } catch (IOException e) {
            if (writer != null) {
                try { writer.close(); } catch (IOException e2) {}
            }
            try { fout.close(); } catch (IOException e2) {}
        }
    }
    
    private void reallyGo() throws IOException {
        //
        // * Create list of all in-memory nodes.
        // * Loop through nodes and node.getPointers.
        // * Print a line to GraphViz file for each memory pointer.
        //
        
        Set<Node> nodes = new HashSet<Node>();
        addNodes(nodes, dag.getTopDs().getSuperRoot());
        
        String line = "digraph BergDB { node [fontsize=\"10\"]; graph [rankdir=\"LR\"]; \n";
        writer.write(line);
        
        // Node output:
        
        for (Node node : nodes) {
            String label;
            
            switch (node.getType()) {
            case Node.TYPE_TOP_NODE: {
                TopNode t = (TopNode) node;
                int pCount = t.getSize();
                StringBuffer b = new StringBuffer();
                b.append("<a> T" + node.getId() + " t=" + t.getRootTime());
                for (int i = 0; i < pCount; i++) {
                    b.append(" | <" + i + ">" + i + ": t=" + t.getPointerTime(i));
                }
                label = "\"" + b.toString() + "\"";
                break;
            }
            
            case Node.TYPE_KEY_NODE: {
                KeyNode k = (KeyNode) node;
                StringBuffer b = new StringBuffer();
                b.append("<a> K");
                if (k.isSegmentLeaf()) {
                    b.append("L");
                }
                b.append("" + k.getId());
                
                for (int i = 0; i < k.getSize(); i++) {
                    long klong = k.getKlong(i);
                    b.append(" | <" + i + ">" + i + ":" + Klong.toString(klong));
                }
                label = "\"" + b.toString() + "\"";
                break;
            }
            
            case Node.TYPE_VALUE:
            case Node.TYPE_DELETE:
                if (!includeValues) {
                    continue;
                }
                
                ValueNode v = (ValueNode) node;
                label = "\"<a> V" + node.getId() + " | " + v.valueString() + "\"";
                break;
            default:
                throw new Error("Bad node type: " + node.getType());
            }
            
            line = "\"" + node.getId() + "\" [label=" + label + " shape=record labeljust=\"l\"];\n";
            writer.write(line);
        }
        
        // Link output:
        
        for (Node node : nodes) {
            if (!includeValues) {
                if (node instanceof ValueNode) {
                    continue;
                }
            }
            
            for (int i = 0; i < node.getSize(); i++) {
                Node pointerNode = node.getPointerNode(i);
                if (pointerNode == null) {
                    continue;
                }
                
                if (!includeValues && pointerNode instanceof ValueNode) {
                    continue;
                }
                
                line = "\"" + node.getId() + "\":" + i + " -> \"" + pointerNode.getId() + "\":a;\n";
                writer.write(line);
            }
        }
        
        line = "}\n";
        writer.write(line);
        writer.flush();
    }
    
    /**
     * Adds 'node' and its children recursively to the 'nodes' collection.
     */
    private void addNodes(Set<Node> nodes, Node node) {
        nodes.add(node);
        
        int pointerCount = node.getSize();
        
        for (int i = 0; i < pointerCount; i++) {
            Node pointerNode = node.getPointerNode(i);
            if (pointerNode != null) {
                addNodes(nodes, pointerNode);
            }
        }
        
    }
    
    public static void main1() throws Exception {
        Db db = TestNodeSize.builder(8).testSetup().start();
        int index = 0;
        
        for (int i = 0; i < 1; i++) {
            
            Trans.Builder b = db.trans();
            
            for (int j = 0; j < 4; j++) {
                String key = "accounts/" + index;
                b.put(key, "v-" + index);
                index++;
            }
            
            db.execute(b.build());
        }
        
        new VizFigure().go(db.internal().dag(), "1.gv", false);
    }
    
    public static void main(String[] args) throws Exception {
        main1();
    }
}
