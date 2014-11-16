package bergdb.test.manual;

import java.io.File;
import java.io.IOException;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.pub.Clock;
import bergdb.stream.FileStream;

/**
 * Executable class that creates a database with 1M entries and then deletes most of them.
 * The size of the stream is observed.
 * 
 * @author Frans Lundberg
 */
public class Shrink {
    private int n = 10*1000;
    private FileStream stream;

    public void go(String[] args) throws IOException, InterruptedException {
        stream = new FileStream(new File("temp-Shrink"));
        Db db = Db.builder().mainStream(stream).start();
        db.setRetainDuration(Clock.UNITS_PER_SEC * 1);
        byte[] value10k = new byte[10*1000];
        
        // ---- Create entries
        
        long t0 = System.nanoTime();
        int index = 0;
        while (index < n) {
            Trans.Builder b = db.trans();
            for (int i = 0; i < 100; i++) {
                b.put("" + index, value10k);
                index++;
            }
            
            Trans trans = b.build();
            db.execute(trans);
            //System.out.println("trans.spos: " + trans.spos);
        }
        db.sync(SyncLevel.ORDINARY);
        
        double time = (System.nanoTime() - t0) * 1e-9;
        System.out.println("Created " + n + " entries in " + Util.oneDecimal(time) + " s.");
        printSize();
        
        // ---- Delete entries
        
        t0 = System.nanoTime();
        index = 0;
        while (index < n) {
            Trans.Builder b = db.trans();
            for (int i = 0; i < 100; i++) {
                b.delete("" + index);
                index++;
            }
            
            db.execute(b.build());
        }
        db.sync(SyncLevel.ORDINARY);
        
        time = (System.nanoTime() - t0) * 1e-9;
        System.out.println("Deleted all entries in " + Util.oneDecimal(time) + " s.");
        printSize();
        
        // ---- Write something to force stream shrink
        
        t0 = System.nanoTime();
        index = 0;
        while (index < n) {
            Trans.Builder b = db.trans();
            b.put("k0", value10k);
            Trans trans = b.build();
            db.execute(trans);
            
            if (index > 0.999*n) {
                System.out.println(index + " trans in stream: " + trans.pos + " -- " + trans.lastPos);
            }
            index++;
        }
        db.sync(SyncLevel.ORDINARY);
        
        time = (System.nanoTime() - t0) * 1e-9;
        System.out.println("Wrote k0 " + n + " times in " + Util.oneDecimal(time) + " s.");
        printSize();
    }
    
    private void printSize() {
        long length = stream.getLength();
        long firstPos = stream.getFirstPos();
        double streamSize = (length - firstPos) * 1e-6;
        
        System.out.println("Stream size: " + Util.oneDecimal(streamSize) 
                + ", length: " + Util.oneDecimal(length * 1e-6)
                + ", firstSpos: " + Util.oneDecimal(firstPos * 1e-6));
    }
    
    public static void main(String[] args) throws IOException, InterruptedException {
        new Shrink().go(args);
    }

}
