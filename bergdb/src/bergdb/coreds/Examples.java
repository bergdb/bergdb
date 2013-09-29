package bergdb.coreds;

import bergdb.common.Util;
import bergdb.coreds.Graph.PutData;

/**
 * Examples for the DB Graph document (docs/2013-dbgraph.odt).
 * 
 * @author Frans Lundberg
 */
public class Examples {
    
    public static void empty() {
        Graph g = Graph.builder().createEmpty(10);
        g.printGraph(System.out);
    }
    
    public static void simpleKey() {
        Graph g = Graph.builder().createEmpty(10);
        PutData pd = new PutData();
        pd.tt = 20;
        g.putKv(Keys.toSegments("/myKey"), Util.toBytes("v1"), pd);
        g.printGraph(System.out);
    }
    
    public static void longerKey() {
        Graph g = Graph.builder().createEmpty(10);
        PutData pd = new PutData();
        pd.tt = 20;
        g.putKv(Keys.toSegments("/myLongerKey"), Util.toBytes("v1"), pd);
        g.printGraph(System.out);
    }
    
    public static void severalKeys1() {
        Graph g = Graph.builder().maxNodeSize8().createEmpty(10);
        PutData pd = new PutData();
        pd.tt = 20;
        
        for (int i = 0; i < 3; i++) {
            g.putKv(Keys.toSegments("/k" + i), Util.toBytes("v" + i), pd);
        }
        
        g.printGraph(System.out);
    }
    
    public static void severalKeys2() {
        Graph g = Graph.builder().maxNodeSize8().createEmpty(10);
        PutData pd = new PutData();
        pd.tt = 20;
        
        for (int i = 2; i >= 0; i--) {
            g.putKv(Keys.toSegments("/k" + i), Util.toBytes("v" + i), pd);
        }
        
        g.printGraph(System.out);
    }
    
    public static void prefixDemo() {
        Graph g = Graph.builder().maxNodeSize8().createEmpty(10);
        PutData pd = new PutData();
        pd.tt = 20;
        
        for (int i = 0; i < 4; i++) {
            g.putKv(Keys.toSegments("/prefix-" + i), Util.toBytes("v" + i), pd);
        }
        
        g.printGraph(System.out);
    }

    
    public static void main(String[] args) {
        //empty();
        //simpleKey();
        //longerKey();
        //severalKeys1();
        //severalKeys2();
        prefixDemo();
    }
}
