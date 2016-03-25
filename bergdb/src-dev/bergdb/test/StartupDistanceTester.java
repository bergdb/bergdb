package bergdb.test;

import java.io.PrintStream;
import java.util.Random;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.MemoryStream;

// TODO LATER We need more startupDistance testing. See "payTillStreamSize(3.0e6);"

/**
 * f-test for Db.setStartupDistance().
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
    private long payCounter = 0;
    
    public StartupDistanceTester() {}
    
    public void go(TestEnvironment c) throws InterruptedException {
        out = c.out();
        random = new Random(0);
        stream = new MemoryStream();
        db = Db.builder().mainStream(stream).startupDistance(500*1000)
                .retainForever()
                .build();
        db.start();
        createAccounts();
        
        long posZero = trans.lastPos;
        
        db.setStartupDistance(1000*1000);
        db.sync(SyncLevel.ORDINARY);
        out.println(this.getClass() + "0. stream length: " + stream.getLength());
        
        payTillStreamSize(1.5e6);
        checkAccountSum(db);
        Assert.assertEquals(1000*1000, db.getStartupDistance());
        out.println("1.1 Stream length: " + db.getStreamLength());
        
        db.setStartupDistance(400*1000);
        out.println("1.2 Stream length: " + db.getStreamLength());
        
        //payTillStreamSize(3.0e6);   // NOTE result in problems
        payTillStreamSize(4.0e6);
        
        checkAccountSum(db);
        Assert.assertEquals(400*1000, db.getStartupDistance());
        out.println("2.1 Stream length: " + db.getStreamLength());
        
        db.setStartupDistance(2000*1000);
        out.println("2.2. Stream length: " + db.getStreamLength());
        Assert.assertEquals(2000*1000, db.getStartupDistance());
        
        payTillStreamSize(5.5e6);
        checkAccountSum(db);
        Assert.assertEquals(2000*1000, db.getStartupDistance());
        out.println("3. Stream length: " + db.getStreamLength());
        
        db.setStartupDistance(500*1000);
        out.println("4. after setStartupDistance(500k). Stream length: " + db.getStreamLength());
        
        payTillStreamSize(6.5e6);
        
        checkAccountSum(db);
        
        Assert.assertEquals(500*1000, db.getStartupDistance());
        out.println("StartupDistanceTester: stream length: " + db.getStreamLength());
        out.println("Calling sync()...");
        db.sync(SyncLevel.ORDINARY);
        out.println("Calling stop()...");
        db.stop();
        out.println("  stop() done.");
        
        Assert.assertEquals(db.getStreamLength(), stream.getLength());
        db = null;
        stream.assertOk();
        c.out().println("db = null, now restarting from memory stream...");
        
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
            
            c.out().println("newLength: " + newLength);
            
            stream.truncate(newLength);
            length = newLength;
            
            Assert.assertEquals(newLength, stream.getLength());
            
            Db myDb = Db.builder().mainStream(stream).retainForever().start();
            out.println(counter++ + ", truncated stream to length: " + newLength 
                    + ", startupDistance: " + myDb.getStartupDistance());

            checkAccountSum(myDb);
            myDb.sync(SyncLevel.ORDINARY);
            myDb.stop();
        }
    }
    
    private void checkAccountSum(Db myDb) {
        long sum = 0;
        
        for (int i = 0; i < noOfAccounts; i++) {
            String s = DbUtil.getString(myDb, "" + i);
            sum += Long.parseLong(s);
        }
        
        Assert.assertEquals("sum of all " + noOfAccounts + " accounts", 0, sum);
    }
    
    private void createAccounts() {
        Trans.Builder b = db.trans();
        for (int i = 0; i < noOfAccounts; i++) {
            b.put("" + i, "0");
        }
        trans = b.build();
        db.execute(trans);
    }
    
    private void payTillStreamSize(double sizeD) throws InterruptedException {
        long size = (long) sizeD;
        
        while (trans.lastPos < size) {
            makePayment();
        }
    }
    
    private void makePayment() throws InterruptedException {
        int fromInt = random.nextInt(noOfAccounts);
        int toInt = random.nextInt(noOfAccounts);
        while (toInt == fromInt) toInt = random.nextInt(noOfAccounts);
        String from = "" + fromInt;
        String to   = "" + toInt;
        
        GetData gd = db.newGetData();
        byte[] v1 = db.getOne(Long.MAX_VALUE, Keys.toSegments(from), gd);
        long lookupTime = gd.actualLookupTime;
        byte[] v2 = db.getOne(lookupTime, Keys.toSegments(to), gd);
        
        long fromBalance = Long.parseLong(Util.toString(v1));
        long toBalance = Long.parseLong(Util.toString(v2));
        
        trans = db.trans()
                .lookupTime(lookupTime)
                .keyRead(to).keyRead(from)
                .put(from, "" + (fromBalance - 1))
                .put(to, "" + (toBalance + 1)).build();
        
        db.execute(trans);
        
        payCounter++;
        if (payCounter % 2000 == 0) out.println("payCounter: " + payCounter + ", stream length: " + db.getStreamLength());
    }
    
    @Nano("f")
    public static void test1(TestEnvironment c) throws Exception {
        new StartupDistanceTester().go(c);
    }
    
    public static void main(String[] args) throws Exception {
        test1(new SimpleTestEnvironment());
    }
}
