import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pubimp.DbObject;

/**
 * Probe (bergdb 016-06/S2): a DbObject (what get(key, DbObject.class) returns) in a field of
 * an object that is put.
 */
public class S2NestedDbObjectProbe {
    public static class P {
        public long v;
        public P() {}
    }
    public static class Holder {
        public DbObject inner;
        public Holder() {}
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            P p = new P();
            p.v = 42;
            c.put("/o/p", p);
            DbObject d = c.get("/o/p", DbObject.class);
            System.out.println("get(\"/o/p\", DbObject.class): v = " + d.getLong("v") + ", fields " + d.getFieldCount());
            Holder h = new Holder();
            h.inner = d;
            c.put("/o/h", h);
            DbObject back = c.get("/o/h", Holder.class).inner;
            System.out.println("put in a DbObject field, read back: " + (back == null ? "null" 
                    : "v = " + back.getLong("v") + ", has v: " + back.has("v", 'l')));
        } finally {
            db.close();
        }
    }
}
