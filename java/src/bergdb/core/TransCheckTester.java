package bergdb.core;

import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * TransCheck, Java's own check of the writer's contract (bergdb 030-09, section 3), finds
 * a fault: each test makes one in the space root's klongs during a transaction, as Java never
 * does, through the test hooks (Db.TestHooks.kvApplied), and the transaction must throw the
 * check's AssertionError. With the check off (no system property transcheck=1) the tests do
 * nothing; unit.sh, f.sh and before-commit.sh turn it on.
 */
public class TransCheckTester {

    /** A fault made in the space root. */
    private interface Fault {
        void make(KeyNode root);
    }

    /**
     * Puts /a, /b and /c, then puts 'keys' in one transaction, with 'fault' made in the space
     * root just before the Dag gets key 'at'; returns the check's message.
     */
    private static String failure(String[] keys, final int at, final Fault fault) {
        Db db = Db.builder().testSetup().start();
        try {
            db.execute(db.trans().put("/a", "a").put("/b", "b").put("/c", "c").build());
            db.execute(db.trans().put("/b", "b2").build());
            final KeyNode root = (KeyNode) db.internal().superRoot().getPointerNode(0);
            Assert.assertTrue("the space root is a segment leaf", root.isSegmentLeaf());
            Db.testHooks = new Db.TestHooks() {
                int n = 0;
                public void transExecuted(Db.ExecuteData x) {}
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void nodeTouched(Node node) {}
                public void nodeReplaced(Node node) {}
                public void kvApplied(long[] key, byte[] value) {
                    if (n++ == at) fault.make(root);
                }
            };
            TransCheck.faultTest = true;
            try {
                Trans.Builder b = db.trans();
                for (String k : keys) b.put(k, "v");
                db.execute(b.build());
            } catch (AssertionError e) {
                return e.getMessage();
            } finally {
                Db.testHooks = null;
                TransCheck.faultTest = false;
            }
            throw new AssertionError("the fault was not found");
        } finally {
            db.close();
        }
    }

    private static void assertFound(String message, String text) {
        Assert.assertTrue("the check's failure: " + message,
                message != null && message.startsWith("transcheck") && message.contains(text));
    }

    /** The index of the first key klong of x. */
    private static int firstKey(KeyNode x) {
        for (int i = 0; i < x.size; i++) {
            if (Klong.getIntType(x.klongs[i]) == Klong.INT_TYPE_KEY) return i;
        }
        throw new AssertionError("no key klong");
    }

    /** A klong of a node made before gets another compare value: the frame. */
    @Nano
    public static void testKlongChanged() {
        if (!TransCheck.ON) return;
        assertFound(failure(new String[] {"/d"}, 0, new Fault() {
            public void make(KeyNode root) {
                int i = firstKey(root);
                long c = Klong.getCompareValue(root.klongs[i]);
                root.klongs[i] = Klong.compareValueToKeyKlong(c ^ (1L << 22));
            }
        }), "has a klong changed");
    }

    /**
     * A node made before loses its last klong: the frame. The put that follows writes over
     * it, so the check finds the klong at its index changed.
     */
    @Nano
    public static void testKlongRemoved() {
        if (!TransCheck.ON) return;
        assertFound(failure(new String[] {"/d"}, 0, new Fault() {
            public void make(KeyNode root) {
                root.size = (short) (root.size - 1);
            }
        }), "has a klong changed");
    }

    /** A klong added to a node made before without the transaction's time klong: the frame. */
    @Nano
    public static void testKlongAddedWithoutTime() {
        if (!TransCheck.ON) return;
        assertFound(failure(new String[] {"/d"}, 0, new Fault() {
            public void make(KeyNode root) {
                int i = firstKey(root);
                long z = Klong.compareValueToKeyKlong(Keys.toSegments("/z")[0]);
                root.addToEnd(z, root.getPointee(i), root.getPointerPos(i));
            }
        }), "do not start with a time klong");
    }

    /**
     * A bitmap at the transaction's time deletes the klong of /a, a key the transaction does
     * not change: the contents.
     */
    @Nano
    public static void testOtherKeyDeleted() {
        if (!TransCheck.ON) return;
        assertFound(failure(new String[] {"/d", "/e"}, 1, new Fault() {
            public void make(KeyNode root) {
                long bitmap = Klong.delete(Klong.createDelete(), firstKey(root));
                root.addToEnd(bitmap, null, -1);
            }
        }), "is lost or changed");
    }
}
