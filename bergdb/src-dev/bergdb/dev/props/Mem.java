package bergdb.dev.props;
import java.io.IOException;

import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.nanotest.CommandLine;
import bergdb.stream.DummyStream;

/**
 * Computes the MEM property; the memory usage per KV in a database
 * with one million small KVs.
 * 
 * @author Frans Lundberg.
 */
public class Mem {
    String report;

    public double go() throws Exception {
        return go(new CommandLine(new String[0]));
    }
    
    private double go(CommandLine line) throws Exception {
        int n = 1000*1000;
        int valueSize = 0;
        Db db = Db.builder().testSetup().mainStream(new DummyStream()).start();
        
        System.gc(); System.gc(); System.gc();
        long emptyMem = usedMem();
        
        int batchSize = 100;
        for (int i = 0; i < n/batchSize; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batchSize; j++) {
                String key = "" + (i*batchSize + j);
                byte[] value = new byte[valueSize];
                b.put(key, value);
            }
            Trans t = b.build();
            db.execute(t);
        }
        
        System.gc(); System.gc(); System.gc();
        long fullMem = usedMem();
        
        double memPerKv = (double)(fullMem - emptyMem) / (double) n;
        report = String.format("MEM:%.0f", memPerKv);
        
        if (line.has("wait")) {
            System.out.println("Waiting for ENTER.");
            waitForEnter();
            
            System.out.println("Stream length: " + db.getStreamLength() + ", startupDistance: " + db.getStartupDistance());
        }
        
        db.stop();
        
        return memPerKv;
    }
    
    private long usedMem() {
        Runtime rt = Runtime.getRuntime();
        System.gc(); System.gc(); System.gc();
        long mem = rt.totalMemory() - rt.freeMemory();
        return mem;
    }
    
    private void waitForEnter() throws IOException {
        System.in.read();
    }
    
    public static void main(String[] args) throws Exception {
        CommandLine line = new CommandLine(args);
        
        Mem m = new Mem();
        m.go(line);
        System.out.println(m.report);
    }
}

/*

150818, Mem:185 on cissi, Oracle JVM 1.7.0_76.
    Now using more advanced caching (Cache2 class).

150809, Mem:159 on cissi, Oracle JVM 1.7.0_76.

150515, Mem:161 on cissi, Oracle JVM 1.7.0_76.

*/