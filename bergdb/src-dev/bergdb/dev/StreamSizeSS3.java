package bergdb.dev;

/**
 * Total stream size for Scenario SS3, small KVs (100 bytes).
 * KV size: 100 bytes, total 100M of data. 100 KVs per trans.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeSS3 {
    public static void main(String[] args) {
        StreamSizeSS1 s = new StreamSizeSS1();
        
        s.kvsPerTrans = 100;
        s.transCount = 1000*1000 / s.kvsPerTrans;
        s.keySize = 10;
        s.valueSize = 100 - s.keySize;
        s.go();
    }
}

/*


*/
