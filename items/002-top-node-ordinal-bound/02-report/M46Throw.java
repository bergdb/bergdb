package bergdb.core;

import bergdb.dag.Keys;
import bergdb.stream.MemoryStream;

/**
 * Bergdb item 002 (M46), a side finding: what a transaction that throws in the middle of
 * its puts leaves behind, without the ordinal bound. Transaction 1 puts /a, then /b with a
 * value transformation that throws. Transaction 2 puts /c. Then a restart from the stream.
 * In-memory database (Db.builder().testSetup), today's code.
 *
 * Usage: java -ea -cp bergdb.jar:. bergdb.core.M46Throw
 */
public final class M46Throw {
    static String str(byte[] b) { return b == null ? "null" : new String(b); }

    public static void main(String[] args) {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("/a", "a0").put("/b", "b0").build());
        clock.setTime(20);
        ValueTransformation fails = new ValueTransformation() {
            public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
                throw new IllegalStateException("the transformation fails");
            }
        };
        try {
            db.execute(db.trans().put("/a", "a1")
                    .put(Keys.toSegments(Keys.toBytes("/b")), null, "b1".getBytes(), fails).build());
            System.out.println("transaction 1 committed (unexpected)");
        } catch (Throwable e) {
            System.out.println("transaction 1 threw: " + e);
        }
        System.out.println("after transaction 1: /a = " + str(DbUtil.get(db, "/a")) + ", /b = "
                + str(DbUtil.get(db, "/b")) + "; nodes left in the transaction's node list: "
                + db.internal().x().transNodes.size());
        clock.setTime(30);
        try {
            db.execute(db.trans().put("/c", "c2").build());
            StringBuilder vals = new StringBuilder();
            for (StoredValueNode svn : db.getTrans(db.internal().x().transInfo.tpos).getValueNodes()) {
                vals.append(str(svn.getValueNode().value)).append(' ');
            }
            System.out.println("transaction 2 (put /c = c2) committed; its record holds the values: " + vals);
        } catch (Throwable e) {
            System.out.println("transaction 2 threw: " + e);
        }
        System.out.println("before the restart: /a = " + str(DbUtil.get(db, "/a")) + ", /b = "
                + str(DbUtil.get(db, "/b")) + ", /c = " + str(DbUtil.get(db, "/c")));
        db.sync(SyncLevel.STRONG);
        db.stop();
        try {
            Db db2 = Db.builder().testSetup(stream.copy()).clock(clock).start();
            System.out.println("after the restart: /a = " + str(DbUtil.get(db2, "/a")) + ", /b = "
                    + str(DbUtil.get(db2, "/b")) + ", /c = " + str(DbUtil.get(db2, "/c")));
            db2.stop();
        } catch (Throwable e) {
            System.out.println("restart FAILED: " + e);
        }
    }
}
