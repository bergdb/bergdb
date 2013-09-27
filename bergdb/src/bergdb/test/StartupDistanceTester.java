package bergdb.test;

import java.io.PrintStream;
import java.util.Random;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.Keys;
import bergdb.core.RerunException;
import bergdb.core.Trans;
import bergdb.coreds.GetData;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.MemoryStream;

/**
 * f-tests for DB.setStartupDistance().
 * 
 * @author Frans Lundberg
 */
public class StartupDistanceTester {
    private Db db;
    private Random random;
    private MemoryStream stream;
    private int noOfAccounts = 100;
    private Trans trans;
    private PrintStream out;
    
    public StartupDistanceTester() {}
    
    public void go(TestCollector c) throws InterruptedException {
        out = c.out();
        random = new Random(0);
        stream = new MemoryStream();
        db = Db.builder().mainStream(stream).startupDistance(100*1000).retainForever().build();
        db.start();
        createAccounts();
        
        long posZero = trans.lastSpos;
        
        db.setStartupDistance(200*1000);
        Assert.assertEquals(100*1000, db.getStartupDistance());
        db.sync();
        out.println("Stream length: " + stream.getLength());
        
        payTillStreamSize(1.5e6);
        checkAccountSum(db);
        Assert.assertEquals(200*1000, db.getStartupDistance());
        out.println("Stream length: " + db.getStreamLength());
        
        db.setStartupDistance(50*1000);
        payTillStreamSize(2.5e6);
        checkAccountSum(db);
        Assert.assertEquals(50*1000, db.getStartupDistance());
        out.println("Stream length: " + db.getStreamLength());
        
        db.setStartupDistance(2000*1000);
        payTillStreamSize(5.5e6);
        checkAccountSum(db);
        Assert.assertEquals(2000*1000, db.getStartupDistance());
        out.println("Stream length: " + db.getStreamLength());
        
        db.setStartupDistance(10*1000);
        payTillStreamSize(6.5e6);
        checkAccountSum(db);
        Assert.assertEquals(10*1000, db.getStartupDistance());
        out.println("Stream length: " + db.getStreamLength());
        db.sync();
        db.stop();
        
        Assert.assertEquals(db.getStreamLength(), stream.getLength());
        db = null;
        stream.assertOk();
        
        MemoryStream origStream = stream;
        MemoryStream stream = origStream.copy();
            // copy() needed to avoid db closing stream when garbage collected.
        stream.assertOk();
        
        Assert.assertEquals(origStream.getLength(), stream.getLength());
        Assert.assertEquals(origStream.getFirstArrayIndex(), stream.getFirstArrayIndex());
        Assert.assertEquals(origStream.getFirstPos(), stream.getFirstPos());
        
        // OK, we have db with stream of around 6.5M. Lets truncate stream at multiple
        // lenghts. 
        
        // Checks assumption that stream not pretruncated.
        Assert.assertEquals(0, stream.getFirstPos());
        long length = origStream.getLength();
        int counter = 0;
        
        while (true) {
            stream = origStream.copy();    // Yes, it is very inefficient.
            
            int toTruncate = random.nextInt(400*1000) + 1;
            long newLength = length - toTruncate;
            if (newLength <= posZero) {
                break;
            }
            
            stream.truncate(newLength);
            length = newLength;
            
            Assert.assertEquals(newLength, stream.getLength());
            out.println(counter++ + ", truncated stream to length: " + newLength);
            
            Db myDb = Db.builder().mainStream(stream).retainForever().start();
            checkAccountSum(myDb);
            myDb.sync();
            myDb.stop();
        }
    }
    
    private void checkAccountSum(Db myDb) {
        long sum = 0;
        
        for (int i = 0; i < noOfAccounts; i++) {
            String s = DbUtil.getString(myDb, "" + i);
            sum += Long.parseLong(s);
        }
        
        Assert.assertEquals(sum, 0);
    }
    
    private void createAccounts() {
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < noOfAccounts; i++) {
            b.set("" + i, "0");
        }
        trans = b.build();
        db.execute(trans);
    }
    
    private void payTillStreamSize(double sizeD) throws InterruptedException {
        long size = (long) sizeD;
        
        while (trans.lastSpos < size) {
            makePayment();
        }
    }
    
    private void makePayment() throws InterruptedException {
        int fromInt = random.nextInt(noOfAccounts);
        int toInt = random.nextInt(noOfAccounts);
        while (toInt == fromInt) toInt = random.nextInt(noOfAccounts);
        String from = "" + fromInt;
        String to   = "" + toInt;
        
        
        while (true) {
            GetData gd = new GetData();
            byte[] v1 = db.get(Long.MAX_VALUE, Keys.toSegments(from), gd);
            long lookupTime = gd.actualLookupTime;
            byte[] v2 = db.get(lookupTime, Keys.toSegments(to), gd);
            
            long fromBalance = Long.parseLong(Util.toString(v1));
            long toBalance = Long.parseLong(Util.toString(v2));
            
            trans = Trans.builder()
                    .lookupTime(lookupTime)
                    .keyRead(to).keyRead(from)
                    .set(from, "" + (fromBalance - 1))
                    .set(to, "" + (toBalance + 1)).build();
            
            try {
                db.execute(trans);
            } catch (RerunException e) {
                Thread.sleep(10);
                System.out.println("RerunException: " + e.getMessage());
                continue;
            }
            
            break;
        }
    }
    
    @T("f")
    public static void test(TestCollector c) throws Exception {
        new StartupDistanceTester().go(c);
    }
    
    public static void main(String[] args) throws Exception {
        test(new BasicCollector());
    }
}
