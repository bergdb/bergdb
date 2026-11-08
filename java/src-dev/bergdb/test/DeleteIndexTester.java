package bergdb.test;

import bergdb.core.Db;
import bergdb.core.DbConstants;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.Time;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pubimp.DatabaseImp;
import bergdb.pubimp.PubKeys;

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
        return "/e/" + (i + 1000);
    }
    
    
    @Nano("f")
    public static void deleteIndexWhileAddingMore(TestEnvironment coll) {
        int n = 100;
        Database database = Factory.database().memory().start();
        
        database.indexBuilder("e-salary").dir("/e/").type("long").field("salary").start().join();
        
        Time timeA = database.currentTime();
        
        Connection c = database.connection();
        
        int i = 0;
        for (; i < n; i++) {
            c.w().put(getEmployeeKey(i), new Employee(getEmployeeKey(i), i * 10)).execute();
        }
        database.sync();
        
        
        Db db = ((DatabaseImp) database).getDb();
        
        Time time0 = database.currentTime();
        
        Job job = database.deleteIndex("e-salary");
        
        JobStatus status = job.getStatus();
        coll.out().println("deleteIndex job status = " + status.note());
        
        Time time1 = database.currentTime();
        
        // Setting more objects while index is being deleted.
        
        coll.out().println("Setting more objects while deleting index..., i = " + i);
        
        for (; i < n*2; i++) {
            c.w().put(getEmployeeKey(i), new Employee(getEmployeeKey(i), i * 10 + 1)).execute();
        }
        
        status = job.getStatus();
        coll.out().println("deleteIndex job status = " + status.note());
        status = job.join();
        database.sync();
        coll.out().println("deleteIndex job status = " + status.note());
        
        Time time2 = database.currentTime();
        
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
        
        String dir = DbConstants.INTERNAL_PREFIX + "di/de-salary/";  // Note the added d's.
        Assert.assertEquals('d', PubKeys.DIR_PREFIX);
        
        GetMany g;
        
        g = db.newGetMany();
        g.inclusive = false;
        g.lookupTime = timeA.units();
        g.startKey = Keys.toSegments(dir);
        g.stopCondition = new GetMany.PrefixN(g.startKey, 10);
        db.getMany(g);
        Assert.assertEquals("timeA", 0, g.result.size());
        
        
        g = db.newGetMany();
        g.inclusive = false;
        g.lookupTime = time0.units();
        g.startKey = Keys.toSegments(dir);
        g.stopCondition = new GetMany.PrefixN(g.startKey, 10);
        db.getMany(g);
        Assert.assertEquals("time0", 10, g.result.size());
        
        
        // The background job may already have removed entries at time1. Its logical
        // disappearance is checked above; internal counts are checked before and after
        // the job, when they do not depend on how quickly its thread was scheduled.

        // There should be no index entries left once delete job finishes.
        
        g = db.newGetMany();
        g.inclusive = false;
        g.lookupTime = time2.units();
        g.startKey = Keys.toSegments(dir);
        g.stopCondition = new GetMany.PrefixN(g.startKey, 10);
        db.getMany(g);
        Assert.assertEquals("time2", 0, g.result.size());
        database.stop();
    }
    
    public static void main(String[] args) throws InterruptedException {
    }
}
