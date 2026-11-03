import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): usePrimary(String.class) over a directory with a String value
 * and an object; Connection.get(key, String.class) reads "a String directly from the raw
 * value bytes".
 */
public class S2PrimaryStringProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.put("/k/s", "hello");
            c.put("/k/o", new P(1));
            for (Class<?> type : new Class<?>[] {String.class, byte[].class, Object.class}) {
                List<String> got = new ArrayList<String>();
                for (bergdb.pub.Kv<?> kv : c.usePrimary(type).dir("/k/").kvs()) {
                    Object v = kv.value();
                    String s = v instanceof byte[] ? ((byte[]) v).length + " bytes" : String.valueOf(v);
                    got.add(kv.key() + "=" + (s.length() > 20 ? s.substring(0, 5) + "..." + s.length() + " chars" : s));
                }
                System.out.println("usePrimary(" + type.getSimpleName() + ".class).dir(\"/k/\"): " + got);
            }
            System.out.println("get(\"/k/s\", String.class): " + c.get("/k/s", String.class));
        } finally {
            db.close();
        }
    }
}
