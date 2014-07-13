package bergdb.test;

import java.util.List;

import bergdb.core.Db;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.pub.NoSuchIndexException;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.pubimp.DatabaseImp;
import bergdb.stream.MemoryStream;

/**
 * Tests creating an index while the database is running and when restarting.
 * f-tests.
 * 
 * @author Frans Lundberg
 */
public class CreateIndexTester {
    
    @T("f")
    public static void createIndexWhileAddingMore(TestCollector coll) {
        int n = 4*1000;
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        int i = 0;
        for (; i < n; i++) {
            c.w().put(new Employee("/e/" + i, i * 10)).execute();
        }
        database.sync();
        
        Db db = ((DatabaseImp) database).getDb();
        long length = db.getStreamLength();
        coll.out().println("Created database, stream length: " + (length/1e6));
        
        long time0 = database.getTime();
        
        Job job = database.indexBuilder("e-salary").type("long").dir("/e/").field("salary").start();
        
        long time1 = database.getTime();
        
        for (; i < n*2; i++) {
            c.w().put(new Employee("/e/" + i, (i-n) * 10 + 1)).execute();
        }
        
        JobStatus status = job.getStatus();
        coll.out().println("Index job status = " + status.note());
        status = job.join();
        database.sync();
        coll.out().println("Index job status = " + status.note());
        
        long time2 = database.getTime();
        
        coll.out().println("Index created, stream length = " + (db.getStreamLength()/1e6));
        
        
        // Checks index before it exists completely
        
        c.setLookupTime(time0);
        NoSuchIndexException ex = null;
        try {
            c.useIndex("e-salary", Employee.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue("Tries c.index() before it exists", ex != null);
        
        c.setLookupTime(time1);
        ex = null;
        try {
            c.useIndex("e-salary", Employee.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue("Tries c.index() while it is being created", ex != null);
        
        // Checking resulting index at current time
        
        c.setLookupTime(time2);
        
        long index = 0;
        for (Employee e : c.useIndex("e-salary", Employee.class).objects()) {
            long half = index / 2;
            long expectedSalary = index % 2 == 0 ? half * 10 : half * 10 + 1;
            Assert.assertEquals("index:" + index, expectedSalary, e.salary);
            index++;
        }
        
        coll.out().println("Done, checks OK.");
    }
    
    @T("f")
    public static void testRestart(TestCollector coll) throws InterruptedException {
        //
        // Tests that an index creation process survives a database restart.
        //
        int n = 4*1000;
        MemoryStream stream = new MemoryStream();
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        Database database = b.mainStream(stream).start();
        Connection c = database.connection();
        
        int i = 0;
        for (; i < n; i++) {
            c.w().put(new Employee("/e/" + i, (n - i) * 10)).execute();
        }
        database.sync();
        
        Db db = ((DatabaseImp) database).getDb();
        long length = db.getStreamLength();
        coll.out().println("Created database, stream length: " + (length/1e6));
        
        Job job = database.indexBuilder("e-salary").type("long").dir("/e/").field("salary").start();
        
        long time1 = database.getTime();
        
        Thread.sleep(100);
        
        JobStatus status = job.getStatus();
        coll.out().println("Index job status = " + status.note());
        coll.out().println("Restarting...");
        database.sync();
        database.stop();
        database = null;
        
        stream = stream.copy();
        b = (DatabaseBuilderImp) Factory.database();
        DatabaseBuilder builder = b.mainStream(stream);
        
        coll.out().println("Restarting... calling database.start()");
        database = builder.start();
        c = database.connection();
        
        // TODO database.getStartInfo().getJobs()
        /*Assert.assertEquals("start() jobs.size()", 1, jobs.size());
        job = jobs.get(0);
        coll.out().println("Job status: " + job.getStatus().note());
        Thread.sleep(100);
        coll.out().println("Job status: " + job.getStatus().note());
        status = job.join();
        Assert.assertEquals(100, status.progress());
        
        coll.out().println("Job status: " + status.note());
        */
        
        // Checks index by iterating it.
        
        int index = 0;
        for (Employee e : c.useIndex("e-salary", Employee.class).objects()) {
            long expectedSalary = (index + 1) * 10;
            Assert.assertEquals(expectedSalary, e.salary);
            index++;
        }
        
        // Checks non-existant index at time1 and existing at time4.
        
        c.setLookupTime(time1);
        NoSuchIndexException ex = null;
        try {
            c.useIndex("e-salary", Employee.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue("Tries c.index() while it is being created", ex != null);
        
        c.setLookupTime(Long.MAX_VALUE);
        c.useIndex("e-salary", Employee.class);
    }
    
    public static class Employee {
        public String key;
        public long salary;
        
        public Employee() {}
        
        public Employee(String key, long salary) {
            this.key = key;
            this.salary = salary;
        }
    }
    
    public static void main(String[] args) throws InterruptedException {
        testRestart(new BasicCollector());
    }
}
