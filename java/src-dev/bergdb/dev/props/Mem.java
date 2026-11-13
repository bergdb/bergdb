package bergdb.dev.props;
import java.io.IOException;
import java.util.Locale;

import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.nanotest.CommandLine;
import bergdb.stream.DummyStream;

/**
 * Computes the MEM property; the memory usage per KV in a database
 * with one million small KVs.
 * 
 * <p>The heap in use after the fill minus before it, divided by the number of KVs, in a
 * database that holds everything (testSetup(): no eviction, no reclaim; a DummyStream);
 * values of 0 bytes, 100 KVs a transaction, keys in key order. Options, for the key-shape
 * runs of level1.sh (bergdb 024-08, section 7; 024-15): -n N, the number of KVs, a
 * multiple of 100, by default 1,000,000; -keys FORMAT, the keys as
 * String.format(FORMAT, i) for i from 0 to N - 1, such as %07d or /k/%010d, by default
 * "" + i. Without options it measures what it measured from 2015 on (bergdb 006-02).
 * The report is MEM: and the figure rounded, then the figure with one decimal.</p>
 * 
 * @author Frans Lundberg.
 */
public class Mem {
    String report;

    public double go() throws Exception {
        return go(new CommandLine(new String[0]));
    }
    
    private double go(CommandLine line) throws Exception {
        int n = line.hasOne("n") ? Integer.parseInt(line.getOne("n")) : 1000*1000;
        String keys = line.hasOne("keys") ? line.getOne("keys") : null;
        int valueSize = 0;
        Db db = Db.builder().testSetup().mainStream(new DummyStream()).start();
        
        System.gc(); System.gc(); System.gc();
        long emptyMem = usedMem();
        
        int batchSize = 100;
        if (n <= 0 || n % batchSize != 0) {
            throw new IllegalArgumentException("-n must be a positive multiple of 100: " + n);
        }
        for (int i = 0; i < n/batchSize; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batchSize; j++) {
                int k = i*batchSize + j;
                String key = keys == null ? "" + k : String.format(Locale.ROOT, keys, k);
                byte[] value = new byte[valueSize];
                b.put(key, value);
            }
            Trans t = b.build();
            db.execute(t);
        }
        
        // The write buffer grows with use and shrinks after 2 s with nothing to write
        // (2026-11-13, bergdb 026-07). The fill grows it to about 8 MB; MEM measures the KVs,
        // so it waits 3 s for the shrink, as the buffer, then 10 MB from the start, was in
        // emptyMem before. Without the wait MEM was 137.5, not 129.
        Thread.sleep(3000);
        System.gc(); System.gc(); System.gc();
        long fullMem = usedMem();
        
        double memPerKv = (double)(fullMem - emptyMem) / (double) n;
        report = String.format(Locale.ROOT, "MEM:%.0f (%.1f bytes a KV, %d KVs, keys %s)",
                memPerKv, memPerKv, n, keys == null ? "\"\" + i" : keys);
        
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

160317, Mem:169 on cisso, Oracle JVM 1.7.0_76.

150818, Mem:185 on cissi, Oracle JVM 1.7.0_76.
    Now using more advanced caching (Cache2 class).

150809, Mem:159 on cissi, Oracle JVM 1.7.0_76.

150515, Mem:161 on cissi, Oracle JVM 1.7.0_76.

*/