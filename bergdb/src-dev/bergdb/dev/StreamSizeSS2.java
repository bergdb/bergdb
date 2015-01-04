package bergdb.dev;

/**
 * Executable class that determines total stream size for Scenario SS2.
 * Fixed scenario without parameters. 100M of raw kv data (key+value size)
 * and 100k kvs each 1 kB. Each trans contains 1 KV.
 * Some key ordering, not random.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeSS2 {
    
    public static void main(String[] args) {
        StreamSizeSS1 s = new StreamSizeSS1();
        s.kvsPerTrans = 1;
        s.transCount = 100*1000 / s.kvsPerTrans;
        s.keySize = 10;
        s.valueSize = 1000 - s.keySize;
        s.go();
    }
}

/*
 
  
*/

