package bergdb.dev.props;

/**
 * Total stream size for Scenario SS3, small KVs (100 bytes).
 * KV size: 100 bytes, total 100M of data. 100 KVs per trans.
 * 
 * @author Frans Lundberg
 */
public class SS3 extends SS1 {
    
    public double go() {
        kvsPerTrans = 100;
        transCount = 1000*1000 / kvsPerTrans;
        keySize = 10;
        valueSize = 100 - keySize;
        
        return super.go();
    }
    
    public static void main(String[] args) {
        SS3 s = new SS3();
        s.go();
        s.reportResult();
    }
}

/*

150105 Frans: got Factor 1.66.

*/
