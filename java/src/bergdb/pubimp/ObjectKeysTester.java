package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * The object keys as the put Javadoc and the package page state them (bergdb 020-11, N4): an
 * object is put only at a key whose name has no suffix or ".obj"; the suffix is what follows
 * the name's last '.'; a '.' in a directory is not one.
 *
 * @author Frans Lundberg
 */
public class ObjectKeysTester {
    
    /** A Data Object class. */
    public static class Item {
        public int n;
        
        public Item() {
        }
        
        public Item(int n) {
            this.n = n;
        }
    }
    
    /** The examples of the package page, in w() and rw(); a String and a byte[] anywhere. */
    @Nano
    public static void testObjectKeysOfThePutJavadoc() {
        Database d = Factory.database().memory().start();
        try {
            final Connection c = d.connection();
            String[] objectKeys = {"/notes/a", "/d/x.", "/v1.2/k", "/a.obj", "/a.b/c.d/e"};
            String[] otherKeys = {"/notes/a.txt", "/d/.h", "/v1.2/k.bin", "/a.obj.txt"};
            for (String k : objectKeys) {
                c.put(k, new Item(1));
                c.rw(env -> env.put(k, new Item(2)));
                Assert.assertEquals(k, 2, c.get(k, Item.class).n);
            }
            for (String k : otherKeys) {
                for (int i = 0; i < 2; i++) {
                    IllegalArgumentException ex = null;
                    try {
                        if (i == 0) {
                            c.w().put(k, new Item(1)).execute();
                        } else {
                            c.rw(env -> env.put(k, new Item(1)));
                        }
                    } catch (IllegalArgumentException e) {
                        ex = e;
                    }
                    Assert.assertTrue(k + ": no refusal", ex != null);
                    Assert.assertTrue(ex.getMessage(), ex.getMessage().contains("Bad key"));
                    Assert.assertFalse(k + ": written", c.exists(k));
                }
                c.put(k, "text");
                c.put(k, new byte[] {1});
                Assert.assertEquals(1, c.get(k, byte[].class)[0]);
            }
        } finally {
            d.stop();
        }
    }
}
