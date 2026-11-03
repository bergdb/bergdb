package bergdb.core;

import bergdb.common.EventToWaitFor;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pubimp.IndexBuilderImp;

/** JobStatus promises immutability even when its job progresses. */
public final class JobStatusProbe {
    public static final class Item {
        public long amount;
        public Item() {}
        Item(long n) { amount = n; }
    }
    public static void main(String[] args) {
        Database db = Factory.database().memory().start();
        EventToWaitFor event = new EventToWaitFor();
        Job job = null;
        try {
            db.newConnection().w().put("/items/a", new Item(1)).put("/items/b", new Item(2)).execute();
            IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("amount")
                    .dir("/items/").type("long").field("amount");
            builder.createInThreadWaitEvent(event);
            job = builder.start();
            JobStatus snapshot = job.getStatus();
            String before = snapshot.note();
            event.happened();
            if (job.join(2000).progress() != 100) throw new AssertionError("build did not finish");
            String after = snapshot.note();
            System.out.println("same JobStatus note before: " + before);
            System.out.println("same JobStatus note after:  " + after);
            System.out.println("FAULT: immutable status changed: " + !before.equals(after));
            System.out.println("old status progress remains: " + snapshot.progress());
        } finally {
            event.happened();
            if (job != null) job.join(2000);
            db.close();
        }
    }
}
