import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.RwEnvironment;
import bergdb.pub.Transaction;

/**
 * Probe (bergdb 016-06/S2): an rw-transaction that reads an indexed object and puts it
 * changed; in its first run another connection changes the object, so it runs again. The
 * index must then hold one entry, for the final value.
 */
public class S2RerunProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("byV").type("long").dir("/p/").field("v").createFast();
            final Connection c = db.newConnection();
            c.put("/p/1", new P(1));
            final int[] runs = {0};
            Transaction t = c.rw(new Action() {
                public void run(RwEnvironment env) {
                    runs[0]++;
                    P p = env.get("/p/1", P.class);
                    if (runs[0] == 1) {
                        Thread other = new Thread(() -> db.newConnection().put("/p/1", new P(100)));
                        other.start();
                        try {
                            other.join();
                        } catch (InterruptedException e) {
                            throw new Error(e);
                        }
                    }
                    env.put("/p/1", new P(p.v + 1));
                    env.put("/p/2", new P(p.v + 2));
                }
            });
            List<String> all = new ArrayList<String>();
            for (bergdb.pub.Kv<P> kv : c.useIndex("byV", P.class).kvs()) {
                all.add(kv.key() + "=" + kv.value().v);
            }
            System.out.println("runs " + runs[0] + "; /p/1 = " + c.get("/p/1", P.class).v + ", /p/2 = " 
                    + c.get("/p/2", P.class).v + "; index: " + all + "; eq(2): " 
                    + c.useIndex("byV", P.class).eq(2).objects().iterator().hasNext()
                    + ", eq(100): " + c.useIndex("byV", P.class).eq(100).objects().iterator().hasNext());
        } finally {
            db.close();
        }
    }
}
