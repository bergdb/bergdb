package bergdb.dev.props;

/**
 * Executable class that determines total stream size for Scenario SS2.
 * Fixed scenario without parameters. 100M of raw kv data (key+value size)
 * and 100k kvs each 1 kB. Each trans contains 1 KV.
 * Some key ordering, not random.
 * 
 * @author Frans Lundberg
 */
public class SS2 extends SS1 {
    
    public double go() {
        kvsPerTrans = 1;
        transCount = 100*1000 / kvsPerTrans;
        keySize = 10;
        valueSize = 1000 - keySize;
        
        return super.go();
    }
    
    public static void main(String[] args) {
        SS2 s = new SS2();
        s.go();
        s.reportResult();
    }
}

/*

150105 Frans: got Factor 1.34.

*/

