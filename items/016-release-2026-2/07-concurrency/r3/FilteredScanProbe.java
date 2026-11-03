package bergdb.core;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;

/** An empty filtered batch is not the end of the primary range. */
public final class FilteredScanProbe {
    public static final class Item {
        public long amount;
        public Item() {}
        Item(long amount) { this.amount = amount; }
    }
    public static void main(String[] args) {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            WBuilder w = c.w();
            for (int i = 0; i < 100; i++) w.put(String.format("/items/a%03d", i), "raw bytes");
            w.put("/items/z", new Item(1)).execute();
            System.out.println("object after raw entries exists: " + (c.get("/items/z", Item.class) != null));
            int n = 0;
            for (Item item : c.usePrimary(Item.class).dir("/items/").objects()) n++;
            System.out.println("typed primary scan result count, expected 1: " + n);
        } finally { db.close(); }
    }
}
