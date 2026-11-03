package bergdb.pubimp;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;

import bergdb.core.Db;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.util.JobStatus;

/**
 * Probe (bergdb 016-06/S2): a put whose index set (getActiveIndexesForDir) is read before
 * deleteIndex() sets the index deleting, and whose read time is set after it. The put is
 * held there by a hook in a subclass of IndexManager; so is the deletion job, after it has
 * deleted the entries and before it deletes the index info. Then an index of the same name
 * is made, on a field that no object has.
 */
public class S2DeleteRaceProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    static final CountDownLatch snapshotTaken = new CountDownLatch(1);
    static final CountDownLatch go = new CountDownLatch(1);
    static final CountDownLatch entriesDeleted = new CountDownLatch(1);
    static final CountDownLatch writerDone = new CountDownLatch(1);
    static volatile Thread writer = null;
    
    static class HookedIndexManager extends IndexManager {
        HookedIndexManager() {
            super(new OptionalIcuCollatorFactory());
        }
        
        public IndexForDir[] getActiveIndexesForDir(String dirname) {
            IndexForDir[] result = super.getActiveIndexesForDir(dirname);
            if (Thread.currentThread() == writer && snapshotTaken.getCount() > 0) {
                snapshotTaken.countDown();
                await(go);
            }
            return result;
        }
        
        void deleteIndexEntries(String indexName, Db db, long[] deletedCounter) {
            super.deleteIndexEntries(indexName, db, deletedCounter);
            entriesDeleted.countDown();
            await(writerDone);
        }
    }
    
    static void await(CountDownLatch latch) {
        try {
            latch.await();
        } catch (InterruptedException e) {
            throw new Error(e);
        }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Field f = DatabaseImp.class.getDeclaredField("indexManager");
            f.setAccessible(true);
            f.set(db, new HookedIndexManager());
            
            db.indexBuilder("X").type("long").dir("/p/").field("v").createFast();
            final Connection c = db.newConnection();
            for (int i = 1; i <= 3; i++) {
                c.put("/p/" + i, new P(i));
            }
            Thread w = new Thread(() -> {
                db.newConnection().put("/p/9", new P(9));
            });
            writer = w;
            w.start();
            snapshotTaken.await();
            bergdb.pub.util.Job deletion = db.deleteIndex("X");
            entriesDeleted.await();
            go.countDown();
            w.join();
            writerDone.countDown();
            JobStatus status = deletion.join();
            System.out.println("deletion: progress " + status.progress() + ", " + status.note());
            
            db.indexBuilder("X").type("string").dir("/p/").field("noSuchField").createFast();
            List<Long> got = new ArrayList<Long>();
            try {
                for (P p : c.useIndex("X", P.class).objects()) {
                    got.add(p.v);
                }
                System.out.println("the new index X, on a field no object has, gives: " + got);
            } catch (RuntimeException e) {
                System.out.println("a scan of the new index X throws " + e);
            }
        } finally {
            db.close();
        }
    }
}
