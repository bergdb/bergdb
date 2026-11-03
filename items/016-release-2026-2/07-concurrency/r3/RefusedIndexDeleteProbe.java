package bergdb.core;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.util.DbException;
import bergdb.pubimp.DatabaseImp;
import bergdb.stream.MemoryStream;

/** A refused metadata transaction must leave its cached directory mappings unchanged. */
public final class RefusedIndexDeleteProbe {
    public static final class Item {
        public long amount;
        public Item() {}
        Item(long amount) { this.amount = amount; }
    }
    static int count(Connection c) {
        int n = 0;
        for (Item item : c.useIndex("amount", Item.class).objects()) n++;
        return n;
    }
    public static void main(String[] args) {
        MemoryStream stream = new MemoryStream();
        Db core = Db.builder().testSetup(stream).build();
        Database db = DatabaseImp.createAndStart(core);
        try {
            db.indexBuilder("amount").dir("/items/").type("long").field("amount").createFast();
            Connection c = db.newConnection();
            c.put("/items/old", new Item(1));
            long length = core.getStreamLength();
            long savedLimit = StoredTrans.recordLimit;
            try {
                // The same test seam as DbTester.testTransactionTooLarge: make a
                // normal metadata transaction too large without allocating 2 GB.
                StoredTrans.recordLimit = 64;
                db.deleteIndex("amount");
                throw new AssertionError("oversized metadata transaction accepted");
            } catch (DbException expected) {
                System.out.println("delete refused before go: " + expected.getMessage());
                if (!expected.getMessage().contains("too large")) throw expected;
            } finally {
                StoredTrans.recordLimit = savedLimit;
            }
            System.out.println("refusal changed stream length: " + (core.getStreamLength() != length));
            System.out.println("database still active: " + core.internal().isActive());
            c.put("/items/new", new Item(2));
            System.out.println("primary new object exists: " + c.exists("/items/new"));
            System.out.println("active index result count, expected 2: " + count(c));
        } finally { db.close(); }
        Database reopened = DatabaseImp.createAndStart(Db.builder().testSetup(stream.copy()).build());
        try {
            Connection c = reopened.newConnection();
            System.out.println("index result count after reopen, expected 2: " + count(c));
        } finally { reopened.close(); }
    }
}
