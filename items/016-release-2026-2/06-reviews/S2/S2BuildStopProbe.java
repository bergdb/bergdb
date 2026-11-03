package bergdb.pubimp;

import bergdb.common.EventToWaitFor;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.stream.MemoryStream;

/**
 * Probe (bergdb 016-06/S2): the database stops while an index is built (IndexBuilder.start:
 * "If the database is stopped before the index has been created, the index creation process
 * will automatically continue when the database is started again"). What does the job say,
 * and does the build go on after a restart?
 */
public class S2BuildStopProbe {
    public static class Item {
        public long amount;
        public Item() {}
        public Item(long a) { amount = a; }
    }
    
    static Database start(MemoryStream stream) {
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        return builder.start();
    }
    
    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        Job build;
        try {
            for (int i = 0; i < 3000; i++) {
                db.newConnection().w().put("/items/" + i, new Item(i)).execute();
            }
            EventToWaitFor wait = new EventToWaitFor();
            IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("by-amount");
            builder.createInThreadWaitEvent(wait);
            build = builder.dir("/items/").type("long").field("amount").start();
            db.close();
            wait.happened();
            JobStatus status = build.join();
            System.out.println("after close: progress " + status.progress() + ", note: " + status.note());
        } finally {
            db.close();
        }
        Database db3 = start(stream.copy());
        try {
            Job resumed = db3.getStartupInfo().getStartupJobs()[0];
            JobStatus deleted = db3.deleteIndex("by-amount").join();
            JobStatus status = resumed.join();
            System.out.println("resumed build, its index deleted (deletion: " + deleted.progress() 
                    + "): progress " + status.progress() + ", note: " + status.note());
            System.out.println("   the index exists: " 
                    + ((DatabaseImp) db3).getIndexManager().hasIndex("by-amount"));
        } finally {
            db3.close();
        }
        Database db2 = start(stream.copy());
        try {
            Thread.sleep(2000);
            int n = 0;
            try {
                for (Item item : db2.newConnection().useIndex("by-amount", Item.class).objects()) {
                    n++;
                }
                System.out.println("after restart and 2 s: the index gives " + n + " objects");
            } catch (RuntimeException e) {
                System.out.println("after restart and 2 s: useIndex throws " + e);
            }
        } finally {
            db2.close();
        }
    }
}
