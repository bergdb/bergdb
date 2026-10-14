package bergdb.dev.props;

/**
 * Total stream size for Scenario SS4, small KVs (100 bytes).
 * Total 100M of data. 1 KV per trans.
 * 
 * @author Frans Lundberg
 */
public class SS4 extends SS1 {
    
    public double go() {
        kvsPerTrans = 1;
        transCount = 1000*1000 / kvsPerTrans;
        keySize = 10;
        valueSize = 100 - keySize;
        
        return super.go();
    }
    
    public static void main(String[] args) {
        SS4 s = new SS4();
        s.go();
        s.reportResult();
    }
}

/*

150105 Frans: got Factor 2.12.

*/
