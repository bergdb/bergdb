import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): an index scan whose last entry is stale (its object deleted).
 * The stale entry is made as in S2-F16: a build indexes an object of a subdirectory, which
 * is then deleted.
 */
public class S2StaleLastProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.put("/p/1", new P(1));
            c.put("/p/q/2", new P(2));
            db.indexBuilder("byV").type("long").dir("/p/").field("v").start().join();
            c.delete("/p/q/2");
            Iterator<P> it = c.useIndex("byV", P.class).objects().iterator();
            List<String> log = new ArrayList<String>();
            try {
                while (it.hasNext()) {
                    log.add("hasNext true");
                    log.add("next " + it.next().v);
                }
                log.add("hasNext false");
            } catch (RuntimeException e) {
                log.add("next throws " + e);
            }
            System.out.println(log);
        } finally {
            db.close();
        }
    }
}
