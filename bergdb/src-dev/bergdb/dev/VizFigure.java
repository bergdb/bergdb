package bergdb.dev;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.HashSet;
import java.util.Set;

import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.dag.INode;
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
 *   $ java -cp ./p/BergDB/ com.bergdb.db.VizFigure; dot -Tsvg -O 1.gv
 * </pre>
 */
public class VizFigure {
    Db db;
    Writer writer;
    boolean includeValues;
    // NOTE IDEA We could print old edges dashed, never used for last time.
    
    /** 
     * Creates a new object; use a new object for every dot-file generation.
     */
    public VizFigure() {
        includeValues = false;
    }
    
    /**
     * Creates the GraphViz dot file.
     */
    public void go(Db db, String filename, boolean includeValues) throws IOException {
        FileOutputStream fout = new FileOutputStream(filename);
        this.db = db;
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
        
        Set<INode> nodes = new HashSet<INode>();
        addNodes(nodes, db.internal().superRoot());
        
        String line = "digraph BergDB { node [fontsize=\"10\"]; graph [rankdir=\"LR\"]; \n";
        writer.write(line);
        
        // Node output:
        
        for (INode node : nodes) {
            String label;
            
            switch (node.getType()) {
            case INode.TYPE_TOP_NODE: {
                TopNode t = (TopNode) node;
                int pCount = t.getPointerCount();
                StringBuffer b = new StringBuffer();
                b.append("<a> T" + node.getId() + " t=" + t.getRootTime());
                for (int i = 0; i < pCount; i++) {
                    b.append(" | <" + i + ">" + i + ": t=" + t.getPointerTime(i));
                }
                label = "\"" + b.toString() + "\"";
                break;
            }
            
            case INode.TYPE_KEY_NODE: {
                KeyNode k = (KeyNode) node;
                StringBuffer b = new StringBuffer();
                b.append("<a> K");
                if (k.isSegmentLeaf()) {
                    b.append("L");
                }
                b.append("" + k.getId());
                
                for (int i = 0; i < k.getPointerCount(); i++) {
                    long klong = k.getKlong(i);
                    b.append(" | <" + i + ">" + i + ":" + Klong.toString(klong));
                }
                label = "\"" + b.toString() + "\"";
                break;
            }
            
            case INode.TYPE_VALUE:
            case INode.TYPE_DELETE:
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
        
        for (INode node : nodes) {
            if (!includeValues) {
                if (node instanceof ValueNode) {
                    continue;
                }
            }
            
            for (int i = 0; i < node.getPointerCount(); i++) {
                INode pointerNode = node.getPointerNode(i);
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
    private void addNodes(Set<INode> nodes, INode node) {
        nodes.add(node);
        
        int pointerCount = node.getPointerCount();
        
        for (int i = 0; i < pointerCount; i++) {
            INode pointerNode = node.getPointerNode(i);
            if (pointerNode != null) {
                addNodes(nodes, pointerNode);
            }
        }
        
    }
    
    public static void main1() throws Exception {
        Db db = Db.builder().testSetup().maxNodeSize8().start();
        int index = 0;
        
        for (int i = 0; i < 1; i++) {
            
            Trans.Builder b = Trans.builder();
            
            for (int j = 0; j < 4; j++) {
                String key = "accounts/" + index;
                b.put(key, "v-" + index);
                index++;
            }
            
            db.execute(b.build());
        }
        
        new VizFigure().go(db, "1.gv", false);
    }
    
    public static void main(String[] args) throws Exception {
        main1();
    }
}
