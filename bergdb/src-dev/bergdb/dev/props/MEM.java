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
public class MEM {
    String report;

    public double go() throws Exception {
        return go(new CommandLine(new String[0]));
    }
    
    private double go(CommandLine line) throws Exception {
        int n = 1000*1000;
        int valueSize = 0;
        Runtime rt = Runtime.getRuntime();
        Db db = Db.builder().testSetup().mainStream(new DummyStream()).start();
        
        System.gc(); System.gc(); System.gc();
        long emptyMem = rt.totalMemory() - rt.freeMemory();
        
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
        long fullMem = rt.totalMemory() - rt.freeMemory();
        
        double memPerKv = (double)(fullMem - emptyMem) / (double) n;
        report = String.format("MEM:%.0f", memPerKv);
        
        if (line.has("wait")) {
            System.out.println("Waiting for ENTER.");
            waitForEnter();
        }
        
        db.stop();
        
        return memPerKv;
    }
    
    private void waitForEnter() throws IOException {
        System.in.read();
    }
    
    public static void main(String[] args) throws Exception {
        CommandLine line = new CommandLine(args);
        
        MEM m = new MEM();
        m.go(line);
        System.out.println(m.report);
    }
}

/*

150515, MEM:161 on cissi and JVM 1.7.0_76 from Oracle.


*/