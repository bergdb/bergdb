import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): a String or a byte[] put to the key of an indexed object, in a
 * directory with an index. Connection.put: "If an entry with the given key already
 * exists, it is overwritten."
 */
public class S2BytesOverObject {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("byV").type("long").dir("/p/").field("v").createFast();
            Connection c = db.newConnection();
            c.put("/p/1", new P(1));
            c.put("/p/2", new P(2));
            System.out.println("before: scan " + scan(c));
            
            // 1. A byte[] that is the object of v = 7, over the object of v = 1.
            c.put("/p/1", bergdb.pubimp.DbObject.toDbObject(new P(7)).getBytes());
            System.out.println("1. byte[] of v=7 put over /p/1: get " + c.get("/p/1", P.class).v
                    + ", eq(1) " + eq(c, 1) + ", eq(7) " + eq(c, 7));
            
            // 2. A String over the object of v = 2.
            c.put("/p/2", "hello");
            System.out.println("2. String put over /p/2: get '" + c.get("/p/2", String.class) + "'");
            try {
                System.out.println("   scan " + scan(c));
            } catch (RuntimeException e) {
                System.out.println("   scan throws " + e);
            }
            try {
                c.delete("/p/2");
                System.out.println("   delete /p/2: ok, exists " + c.exists("/p/2"));
            } catch (RuntimeException e) {
                System.out.println("   delete /p/2 throws " + e + "; exists " + c.exists("/p/2"));
            }
            try {
                c.put("/p/2", new P(3));
                System.out.println("   put of an object to /p/2: ok");
            } catch (RuntimeException e) {
                System.out.println("   put of an object to /p/2 throws " + e);
            }
        } finally {
            db.close();
        }
    }
    
    static List<Long> eq(Connection c, long v) {
        List<Long> list = new ArrayList<Long>();
        for (P p : c.useIndex("byV", P.class).eq(v).objects()) {
            list.add(p.v);
        }
        return list;
    }
    
    static List<Long> scan(Connection c) {
        List<Long> list = new ArrayList<Long>();
        for (P p : c.useIndex("byV", P.class).objects()) {
            list.add(p.v);
        }
        return list;
    }
}
