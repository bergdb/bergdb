import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): prefix() on string indexes, without and with ICU.
 */
public class S2PrefixProbe {
    public static class P {
        public String s;
        public P() {}
    }
    static final String[] NAMES = {"a", "ab", "abc", "abd", "b", "ba", "Åsa", "åsa", "Ångström", "ö", "öl", "Ölund", "z", "x/y"};
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            String[] types = {"string", "string/sv", "string/sv/L3", "string/en/L2"};
            for (int t = 0; t < types.length; t++) {
                db.indexBuilder("i" + t).type(types[t]).dir("/p/").field("s").createFast();
            }
            Connection c = db.newConnection();
            for (int i = 0; i < NAMES.length; i++) {
                P p = new P();
                p.s = NAMES[i];
                c.put("/p/" + i, p);
            }
            String[] prefixes = {"a", "ab", "å", "Å", "ö", "x"};
            for (int t = 0; t < types.length; t++) {
                System.out.println(types[t] + ": scan " + names(c.useIndex("i" + t, P.class).objects()));
                for (String prefix : prefixes) {
                    System.out.println("   prefix(\"" + prefix + "\"): " + names(c.useIndex("i" + t, P.class).prefix(prefix).objects())
                        + ", startAt(\"b\"): " + names(c.useIndex("i" + t, P.class).prefix(prefix).startAt("b").objects()));
                }
            }
        } finally {
            db.close();
        }
    }
    
    static List<String> names(Iterable<P> it) {
        List<String> list = new ArrayList<String>();
        for (P p : it) {
            list.add(p.s);
        }
        return list;
    }
}
