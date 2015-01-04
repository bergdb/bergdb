package bergdb.dev;

/**
 * Total stream size for Scenario SS3, small KVs (100 bytes).
 * KV size: 100 bytes, total 100M of data. 1 KV per trans.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeSS4 {
    public static void main(String[] args) {
        StreamSizeSS1 s = new StreamSizeSS1();
        
        s.kvsPerTrans = 1;
        s.transCount = 1000*1000 / s.kvsPerTrans;
        s.keySize = 10;
        s.valueSize = 100 - s.keySize;
        s.go();
    }
}

/*


*/
