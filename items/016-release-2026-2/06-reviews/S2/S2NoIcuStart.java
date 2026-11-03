import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): a database with a "string/sv" index, made with ICU on the class
 * path ("make DIR"), started on a class path without ICU ("open DIR"). IndexBuilder.type:
 * such an index "can be impossible to use" without ICU.
 */
public class S2NoIcuStart {
    public static class P {
        public String name;
        public P() {}
    }
    
    public static void main(String[] args) throws Exception {
        String dir = args[1];
        if (args[0].equals("make")) {
            Database db = Factory.database().dir(dir).start();
            try {
                db.indexBuilder("byName").type("string/sv").dir("/p/").field("name").createFast();
                Connection c = db.newConnection();
                P p = new P();
                p.name = "Åsa";
                c.put("/p/1", p);
                c.put("/other/x", "plain value");
                c.sync();
            } finally {
                db.close();
            }
            System.out.println("made, ICU on the class path: " + hasIcu());
        } else {
            System.out.println("ICU on the class path: " + hasIcu());
            Database db;
            try {
                db = Factory.database().dir(dir).start();
            } catch (Throwable e) {
                System.out.println("start throws " + e);
                return;
            }
            try {
                Connection c = db.newConnection();
                System.out.println("get /other/x: " + c.get("/other/x", String.class));
                try {
                    P p = new P();
                    p.name = "Bo";
                    c.put("/p/2", p);
                    System.out.println("put to the indexed directory: ok");
                } catch (Throwable e) {
                    System.out.println("put to the indexed directory throws " + e);
                }
            } finally {
                db.close();
            }
        }
    }
    
    static boolean hasIcu() {
        try {
            Class.forName("bergdb.icu50.text.Collator");
            return true;
        } catch (ClassNotFoundException e) {
            return false;
        }
    }
}
