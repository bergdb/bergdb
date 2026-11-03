package bergdb.core;

import bergdb.dag.Keys;
import bergdb.pub.util.DbFailedException;

/**
 * 016-06/R7, F2: a value transformation's result is not checked against the value limit
 * before the go point (checkSize sees the input value), so a result above the limit fails
 * the database in store(). Record limit lowered to 100 kB as in StoredTrans's test.
 */
public class R7TransformSizeProbe {
    public static void main(String[] args) {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 100 * 1000;
        Db db = Db.builder().testSetup().start();
        try {
            final int size = Integer.getInteger("size", 120 * 1000);
            Trans.Builder b = db.trans();
            b.put(Keys.toSegments("/t"), null, new byte[0], new ValueTransformation() {
                public byte[] transform(long transTime, byte[] in, byte[] previous) {
                    return new byte[size];
                }
            });
            try {
                db.execute(b.build());
                System.out.println("taken: a transformed value of " + size + " bytes");
            } catch (DbFailedException e) {
                System.out.println("FAULT: " + e.getMessage());
                System.out.println("  cause: " + e.getCause());
            } catch (RuntimeException e) {
                System.out.println("refused (database goes on): " + e);
            }
            try {
                db.execute(db.trans().put("/x", "1").build());
                System.out.println("next put taken");
            } catch (RuntimeException e) {
                System.out.println("next put: " + e.getClass().getSimpleName());
            }
            // The same value given directly is refused before the go point.
            try {
                db.execute(db.trans().put("/d", new byte[size]).build());
                System.out.println("direct put taken");
            } catch (RuntimeException e) {
                System.out.println("direct put: " + e);
            }
        } finally {
            StoredTrans.recordLimit = saved;
            db.close();
        }
    }
}
