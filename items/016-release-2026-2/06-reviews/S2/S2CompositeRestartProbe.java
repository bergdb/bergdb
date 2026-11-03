package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.stream.MemoryStream;

/**
 * Probe (bergdb 016-06/S2): a composite index whose second level has two fields,
 * type("long").field("a").type("long").field("x").field("y"), before and after a restart.
 */
public class S2CompositeRestartProbe {
    public static class P {
        public long a, x, y;
        public P() {}
        public P(long a, long x, long y) { this.a = a; this.x = x; this.y = y; }
    }
    
    static Database start(MemoryStream stream) {
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        return builder.start();
    }
    
    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            db.indexBuilder("ax").dir("/p/").type("long").field("a").type("long").field("x").field("y").createFast();
            Connection c = db.newConnection();
            c.put("/p/1", new P(1, 10, 20));
            System.out.println("before the restart, eq(1): " + scan(c, 1));
            System.out.println("   stored fields: " + java.util.Arrays.toString(
                    Data.createIndexDo(((DatabaseImp) db).getIndexManager().getIndex("ax")).fields));
        } finally {
            db.close();
        }
        db = start(stream.copy());
        try {
            Connection c = db.newConnection();
            c.put("/p/2", new P(2, 30, 40));
            c.put("/p/1", new P(1, 11, 21));
            System.out.println("after the restart, /p/2 put (2, 30, 40), eq(2): " + scan(c, 2));
            System.out.println("   /p/1 updated to (1, 11, 21), eq(1): " + scan(c, 1));
            List<String> keys = new ArrayList<String>();
            for (bergdb.pub.Kv<byte[]> kv : c.useIndex("ax", byte[].class).eq(1).kvs()) {
                keys.add(kv.key());
            }
            System.out.println("   the keys eq(1) gives: " + keys);
        } finally {
            db.close();
        }
    }
    
    static List<String> scan(Connection c, long a) {
        List<String> list = new ArrayList<String>();
        for (P p : c.useIndex("ax", P.class).eq(a).objects()) {
            list.add("(" + p.a + "," + p.x + "," + p.y + ")");
        }
        return list;
    }
}
