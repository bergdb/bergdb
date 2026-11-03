import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): an object whose indexed String field is null, put to a
 * directory with a string index on it; and the same object put before a build.
 */
public class S2NullStringIndexProbe {
    public static class P {
        public String name;
        public P() {}
    }
    
    public static void main(String[] args) throws Exception {
        for (String type : new String[] {"string", "string/sv"}) {
            final Database db = Factory.database().memory().start();
            try {
                Connection c = db.newConnection();
                c.put("/b/1", new P());
                db.indexBuilder("byName").type(type).dir("/p/").field("name").createFast();
                try {
                    c.put("/p/1", new P());
                    System.out.println(type + ": put of an object with name == null: ok, eq(\"x\") " 
                            + c.useIndex("byName", P.class).eq("x").objects().iterator().hasNext());
                } catch (Throwable e) {
                    System.out.println(type + ": put of an object with name == null throws " + e);
                }
                bergdb.pub.util.JobStatus st = db.indexBuilder("byName2").type(type).dir("/b/").field("name").start().join(5000);
                System.out.println("   a build over such an object: progress " + st.progress() + ", " + st.note());
            } finally {
                db.close();
            }
        }
    }
}
