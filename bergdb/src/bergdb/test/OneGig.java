package bergdb.test;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import bergdb.common.Bytes;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.FixedDurationEvictBoss;
import bergdb.core.IEvictBoss;
import bergdb.core.KeyFactory;
import bergdb.core.Keys;
import bergdb.core.Trans;
import bergdb.coreds.GetData;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.OneFileStream;


// NOTE Day 120605. Reading is slow when done after creating the file, t1(). When reading
// separately, it is fast. Same code, different performance. Strange behaviour of the JVM.
// JVM: Oracle JVM build 1.7.0_02-b13. 32-bit, Ubuntu.

/**
 * Tests writing a one gigabyte db to disk.
 * Checks whether cache eviction works.
 */
public class OneGig {
    
    @T("perf")
    public static void t1(TestCollector c) throws IOException, InterruptedException {
        String fname = t1Inner(c);
       
        System.gc();
        Thread.sleep(1000);
        System.gc();
        Thread.sleep(1000);
        System.gc();
        
        // Reads and checks the created file.
        readFile(c, fname);
        
        File f = new File(fname);
        f.delete();
    }
    
    private static String t1Inner(TestCollector c) throws IOException {
        final PrintStream out = c.out();
        File f = File.createTempFile("OneGig-", ".bergdb");
        out.println("DB stream file: " + f);
        OneFileStream s = new OneFileStream(f);
        final int n = 100*1000;   // Number of transactions
            // Normally 100*1000. It makes 1 GB. We have 10*n KVs.
            // n = 10*1000, 1000 are suitable for faster testing.
        final int valueSize = 1000 - 4;
        
        c.report("transaction-count", n);
        c.report("kv-size", valueSize + 4);
        
        Db db = Db.builder().mainStream(s).start();
        long t = System.nanoTime();
        
        for (int i = 0; i < n; i++) {
            Trans.Builder b = Trans.builder();
            int keyIndex = -1;
            
            for (int j = 0; j < 10; j++) {
                keyIndex = i * 10 + j;
                byte[] key = KeyFactory.binaryIntKey(keyIndex);
                byte[] value = new byte[valueSize];
                Bytes.intToBytesLE(keyIndex, value, 0);
                b.set(key, value);
            }
            
            db.execute(b.build());
            
            if (i % 5000 == 0) {
                double totalKvSize = Math.round(i * 1000.0 * 10.0 * 1e-6);
                out.println("OneGig.t1: i=" + i + ", stream size=" 
                        + Math.round(db.getStreamLength() / 1e6) + ", keyIndex=" + keyIndex
                        + ", kv size written:" + totalKvSize + " MB. Memory used: " 
                        + Math.round(mem()/(1000.0*1000)) + ".");
            }
        }
        t = System.nanoTime() - t;
        s.stop();
        
        c.report("write-time", t*1e-9);
        c.report("stream-size-mb", (db.getStreamLength() * 1e-6));
        c.report("stream-size", db.getStreamLength());
        c.report("write-time-per-kv", t*1e-9/(10.0*n));
        c.report("write-time-per-trans", t*1e-9/n);
        c.report("write-time-per-stream-mb", t*1e-9 / (db.getStreamLength() * 1e-6));
        c.report("write-time-per-data-mb", t*1e-9 / (n*0.01));
        c.report("filename", f.getAbsolutePath());
        
        return f.getAbsolutePath();
    }
    
    /*public static void read(ICollector c) throws Exception {
        String fname = "/tmp/OneGig-3613683099766874225.bergdb";
        readFile(c, fname);
    }*/
    
    public static void readFile(TestCollector c, String fname) throws IOException {
        // Now, let's read the file and check it.
        PrintStream out = c.out();
        out.println("Reads db file: " + fname);
        OneFileStream s = new OneFileStream(new File(fname));
        Db db = Db.builder().mainStream(s).build();
        int n = 100*1000;
        
        long t = System.nanoTime();
        db.start();
        t = System.nanoTime() - t;
        c.report("startup-time", t*1e-9);
        
        t = System.nanoTime();
        for (int i = 0; i < 10*n; i++) {
            byte[] key = KeyFactory.binaryIntKey(i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);            
            Assert.assertTrue("i=" + i, value != null);
            Assert.assertEquals(1000 - 4, value.length);
            int valueInt = Bytes.bytesToIntLE(value, 0);
            Assert.assertEquals(i, valueInt);
            
            if (i % 25000 == 0) {
                System.gc();
                out.println(i + ". Memory used: " + Math.round(mem()/(1000.0*1000)));
            }
        }
        t = System.nanoTime() - t;
        s.stop();
        
        c.report("read-time", t*1e-9);
        c.report("read-time-per-kv", t*1e-9/(10.0*n));
        c.report("read-time-per-stream-mb", t*1e-9 / (db.getStreamLength() * 1e-6));
        c.report("read-time-per-data-mb", t*1e-9 / (n*0.01));
    }
    
    @T("perf")
    public static void t1mem(TestCollector c) throws IOException {
        //
        // In-memory version similar to t1().
        // Smaller, 100 MB. Use "-Xmx1000m" or something to run test.
        //
        
        final PrintStream out = c.out();
        AppendOnlyStream s = new MemoryStream();
        
        final int n = 10*1000;   // Number of transactions
            // Normally 10*1000. It makes 0.1 GB. We have 10*n KVs and n transactions.
        final int valueSize = 1000 - 4;   // Should be 1000-4.
        
        c.report("transaction-count", n);
        c.report("kv-size", valueSize + 4);
        
        IEvictBoss boss = new FixedDurationEvictBoss(10*1000000);
        Db db = Db.builder().mainStream(s).evictBoss(boss).start();
        
        long t = System.nanoTime();
        
        for (int i = 0; i < n; i++) {
            Trans.Builder b = Trans.builder();
            int keyIndex = -1;
            
            for (int j = 0; j < 10; j++) {
                keyIndex = i * 10 + j;
                byte[] key = KeyFactory.binaryIntKey(keyIndex);
                byte[] value = new byte[valueSize];
                Bytes.intToBytesLE(keyIndex, value, 0);
                b.set(key, value);
            }
            
            db.execute(b.build());
            
            if (i % 1000 == 0) {
                double totalKvSize = Math.round(i * 1000.0 * 10.0 * 1e-6);
                out.println("OneGig.t1mem: i=" + i + ", stream size=" 
                        + Math.round(db.getStreamLength() / 1e6) + ", keyIndex=" + keyIndex
                        + ", kv size written:" + totalKvSize + " MB. Memory used: " 
                        + Math.round(mem()/(1000.0*1000)) + ".");
            }
        }
        
        t = System.nanoTime() - t;
        
        c.report("write-time", t*1e-9);
        c.report("stream-size-mb", (db.getStreamLength() * 1e-6));
        c.report("stream-size", db.getStreamLength());
        c.report("write-time-per-kv", t*1e-9/(10.0*n));
        c.report("write-time-per-trans", t*1e-9/n);
        c.report("write-time-per-stream-mb", t*1e-9 / (db.getStreamLength() * 1e-6));
        c.report("write-time-per-data-mb", t*1e-9 / (n*0.01));
        
        db = null;
        System.gc();
        
        out.println("Now reads the stream and checks the data.");
        
        db = Db.builder().mainStream(s).build();
        
        t = System.nanoTime();
        db.start();
        t = System.nanoTime() - t;
        c.report("startup-time", t*1e-9);
        
        GetData gd = new GetData();
        
        t = System.nanoTime();
        for (int i = 0; i < 10*n; i++) {
            if (i % 10000 == 0) {
                out.print(i + " ");
                out.flush();
            }
            
            byte[] key = KeyFactory.binaryIntKey(i);
            byte[] value = db.get(Long.MAX_VALUE, Keys.toSegments(key), gd);
            
            Assert.assertTrue("i=" + i, value != null);
            Assert.assertEquals(valueSize, value.length);
            int valueInt = Bytes.bytesToIntLE(value, 0);
            Assert.assertEquals(i, valueInt);
        }
        t = System.nanoTime() - t;
        
        System.out.println();
        c.report("read-time", t*1e-9);
        c.report("read-time-per-kv", t*1e-9/(10.0*n));
        c.report("read-time-per-stream-mb", t*1e-9 / (db.getStreamLength() * 1e-6));
        c.report("read-time-per-data-mb", t*1e-9 / (n*0.01));
    }
    
    private static long mem() {
        Runtime rt = Runtime.getRuntime();
        return rt.totalMemory() - rt.freeMemory();
    }
    
    public static void main(String[] args) throws Exception {
        t1mem(new BasicCollector());
    }
}

/*
For testing, it may be useful to clear file system cache.

sudo sync
sudo bash -c 'echo 3 > /proc/sys/vm/drop_caches'

http://ubuntuforums.org/showthread.php?t=589975
http://www.linuxask.com/questions/permission-denied-when-doing-redirection-with-sudo
*/