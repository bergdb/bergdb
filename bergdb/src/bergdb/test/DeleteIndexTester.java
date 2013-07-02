package bergdb.test;

import java.util.List;

import bergdb.core.Db;
import bergdb.core.GetMany;
import bergdb.core.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.pub.NoSuchIndexException;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.pubimp.DatabaseImp;
import bergdb.pubimp.PubKeys;
import bergdb.stream.MemoryStream;

/**
 * Tests deleting an index while the database is running and when it is restarted.
 * f-tests.
 * 
 * @see CreateIndexTester
 * @author Frans Lundberg
 */
public class DeleteIndexTester {
    
    public static class Employee {
        public String key;
        public long salary;
        
        public Employee() {}
        
        public Employee(String key, long salary) {
            this.key = key;
            this.salary = salary;
        }
    }
    
    private static String getEmployeeKey(int i) {
        return "/e/" + (i + 1000) + ".obj";
    }
    
    
    @T("f")
    public static void deleteIndexWhileAddingMore(TestCollector coll) {
        int n = 100;
        Database database = Factory.database().memory().start();
        
        database.indexBuilder("e-salary").dir("/e/").type("long").field("salary").start().join();
        
        long timeA = database.getTime();
        
        Connection c = database.connection();
        
        int i = 0;
        for (; i < n; i++) {
            c.w().set(new Employee(getEmployeeKey(i), i * 10)).execute();
        }
        database.sync();
        
        
        Db db = ((DatabaseImp) database).getDb();
        
        long time0 = database.getTime();
        
        Job job = database.deleteIndex("e-salary");
        
        JobStatus status = job.getStatus();
        coll.out().println("deleteIndex job status = " + status.note());
        
        long time1 = database.getTime();
        
        // Setting more objects while index is being deleted.
        
        coll.out().println("Setting more objects while deleting index..., i = " + i);
        
        for (; i < n*2; i++) {
            c.w().set(new Employee(getEmployeeKey(i), i * 10 + 1)).execute();
        }
        
        status = job.getStatus();
        coll.out().println("deleteIndex job status = " + status.note());
        status = job.join();
        database.sync();
        coll.out().println("deleteIndex job status = " + status.note());
        
        long time2 = database.getTime();
        
        // Checks index exists or not at different times
        
        c.setLookupTime(time0);
        c.useIndex("e-salary", byte[].class).objects();      // No exception should be thrown
        
        c.setLookupTime(time1);
        try {
            c.useIndex("e-salary", byte[].class).objects();
            throw new AssertionError("Expected not to reach this code, exception should have been thrown.");
        } catch (NoSuchIndexException e) {}
        
        c.setLookupTime(time2);
        try {
            c.useIndex("e-salary", byte[].class).objects();
            throw new AssertionError("Expected not to reach this code, exception should have been thrown.");
        } catch (NoSuchIndexException e) {}
        
        // Internal check that there are index entries before deletion starts, but they
        // are gone when deletion is done.
        
        String dir = Db.INTERNAL_KEY_PREFIX + "di/de-salary/";  // Note the added d's.
        Assert.assertEquals('d', PubKeys.DIR_PREFIX);
        
        GetMany g;
        
        g = new GetMany();
        g.inclusive = false;
        g.lookupTime = timeA;
        g.startKey = Keys.toSegments(dir);
        g.stopCondition = new GetMany.PrefixN(g.startKey, 10);
        db.getMany(g);
        Assert.assertEquals("timeA", 0, g.result.size());
        
        
        g = new GetMany();
        g.inclusive = false;
        g.lookupTime = time0;
        g.startKey = Keys.toSegments(dir);
        g.stopCondition = new GetMany.PrefixN(g.startKey, 10);
        db.getMany(g);
        Assert.assertEquals("time0", 10, g.result.size());
        
        
        g = new GetMany();
        g.inclusive = false;
        g.lookupTime = time1;
        g.startKey = Keys.toSegments(dir);
        g.stopCondition = new GetMany.PrefixN(g.startKey, 10);
        db.getMany(g);
        Assert.assertEquals("time1", 10, g.result.size());
        
        // There should be no index entries left once delete job finishes.
        
        g = new GetMany();
        g.inclusive = false;
        g.lookupTime = time2;
        g.startKey = Keys.toSegments(dir);
        g.stopCondition = new GetMany.PrefixN(g.startKey, 10);
        db.getMany(g);
        Assert.assertEquals("time2", 0, g.result.size());
    }
    
    @T("f")
    public static void testRestart(TestCollector coll) throws InterruptedException {
        //
        // Tests that an index deletion process survives a database restart.
        //
        
        int n = 1000;
        MemoryStream stream = new MemoryStream();
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        Database database = b.mainStream(stream).start();
        database.indexBuilder("e-salary").dir("/e/").type("long").field("salary").start().join();
        Connection c = database.connection();
        
        long t0 = System.nanoTime();
        int i = 0;
        for (; i < n; i++) {
            c.w().set(new Employee(getEmployeeKey(i), i * 10)).execute();
        }
        double setTime = (System.nanoTime() - t0) * 1e-9;
        database.sync();
        
        Job job = database.deleteIndex("e-salary");
        
        Thread.sleep((long) (setTime * 0.03 * 1000));           // Sleep 3% of setTime
        Assert.assertTrue(job.getStatus().progress() < 100);    // Assert not done yet.
        coll.out().println("Job status = " + job.getStatus().note());
        
        database.sync();
        database.stop();
        database = null;
        
        stream = stream.copy();
        b = (DatabaseBuilderImp) Factory.database();
        database = b.mainStream(stream).build();
        
        coll.out().println("Restarting... calling start() on restarted database.");
        List<Job> jobs = database.start();
        c = database.connection();
        
        Assert.assertEquals("start() jobs.size()", 1, jobs.size());
        job = jobs.get(0);
        coll.out().println("Job status: " + job.getStatus().note());
        Thread.sleep(100);
        coll.out().println("Job status: " + job.getStatus().note());
        JobStatus status = job.join();
        Assert.assertEquals(100, status.progress());
        coll.out().println("Job status: " + status.note());
    }
    
    public static void main(String[] args) throws InterruptedException {
        //deleteIndexWhileAddingMore(new BasicCollector());
        testRestart(new BasicCollector());
    }
}
