package bergdb.core;

import java.io.IOException;

import bergdb.common.StringUtil;
import bergdb.dag.Keys;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Probe for bergdb 005-01 (M49), run against the build before and after the fix: a
 * transaction that fails after its go point, then a next transaction, then a restart.
 * Uses only API that both builds have. Case 1: a value transformation that throws (003-01,
 * 2.1). Case 2: a corrupt index node, loaded by a put after eviction (a checksum error; the
 * storage stays healthy).
 */
public class M49Probe {
    public static void main(String[] args) throws Exception {
        valueTransformation();
        corruptNode();
    }

    static void valueTransformation() throws Exception {
        System.out.println("== Case 1: a value transformation that throws");
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").put("/b", "b0").build());
        db.sync(SyncLevel.STRONG);
        long length = s.getLength();
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, StringUtil.toBytes("a1"), null)
                .put(Keys.toSegments("/b"), null, StringUtil.toBytes("b1"), new ValueTransformation() {
                    public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
                        throw new IllegalStateException("the transformation fails");
                    }
                })
                .build();
        after(db, t, s, length, new Restart() {
            public Db start(AppendOnlyStream copy) { return Db.builder().testSetup(copy).start(); }
        }, s);
    }

    static void corruptNode() throws Exception {
        System.out.println("== Case 2: a corrupt index node loaded by a put, after eviction");
        final Fault s = new Fault();
        Restart r = new Restart() {
            public Db start(AppendOnlyStream copy) {
                return Db.builder().testSetup(copy).maxNodeSize8().startupDistance(1000)
                        .evictionSchedule(Eviction.Schedule.EVERY, 1).start();
            }
        };
        Db db = r.start(s);
        for (int i = 0; i < 2000; i += 10) {
            Trans.Builder b = db.trans();
            for (int j = i; j < i + 10; j++) b.put("/k" + (10000 + j), "v" + j);
            db.execute(b.build());
        }
        db.sync(SyncLevel.STRONG);
        long length = s.getLength();
        KeyTransformation kt = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                s.corrupt = true;
                long[] key = Keys.toSegments("/k11000");
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
            }
        };
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, StringUtil.toBytes("a1"), null)
                .put(Keys.toSegments("/z"), kt, StringUtil.toBytes("x"), null)
                .build();
        after(db, t, s, length, r, s.inner);
    }

    interface Restart { Db start(AppendOnlyStream copy); }

    static void after(Db db, Trans t, AppendOnlyStream s, long length, Restart r, MemoryStream bytes)
            throws Exception {
        try {
            db.execute(t);
            System.out.println("the transaction committed (unexpected)");
        } catch (Throwable e) {
            System.out.println("the transaction threw: " + e.getClass().getSimpleName() 
                    + (e.getCause() != null ? ", cause " + e.getCause().getClass().getSimpleName() : ""));
        }
        if (s instanceof Fault) ((Fault) s).corrupt = false;
        try {
            System.out.println("a read of /a after it: " + DbUtil.getString(db, "/a"));
        } catch (Throwable e) {
            System.out.println("a read of /a after it: " + e.getClass().getSimpleName());
        }
        try {
            db.execute(db.trans().put("/c", "c2").build());
            db.sync(SyncLevel.STRONG);
            System.out.println("the next transaction (/c = c2) committed; the stream grew by " 
                    + (s.getLength() - length) + " bytes");
        } catch (Throwable e) {
            System.out.println("the next transaction: " + e.getClass().getSimpleName() 
                    + "; the stream grew by " + (s.getLength() - length) + " bytes");
        }
        long lengthBeforeClose = s.getLength();
        db.close();
        System.out.println("stream length " + length + " before, " + lengthBeforeClose 
                + " at the close, " + bytes.getLength() + " after it");
        MemoryStream copy = bytes.copy();
        Db db2 = r.start(copy);
        System.out.println("after a restart: /a = " + DbUtil.getString(db2, "/a") + ", /c = " 
                + DbUtil.getString(db2, "/c") + ", /k10000 = " + DbUtil.getString(db2, "/k10000")
                + ", /k11000 = " + DbUtil.getString(db2, "/k11000") + ", /k11990 = " 
                + DbUtil.getString(db2, "/k11990") + ", lookup time " + db2.lookupTime(Long.MAX_VALUE));
        db2.close();

    }

    static class Fault implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile boolean corrupt = false;
        public long getLength() { return inner.getLength(); }
        public long getFirstPos() { return inner.getFirstPos(); }
        public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
            inner.read(position, dest, destOffset, length);
            if (corrupt && length > 8) dest[destOffset + length - 1] ^= 0x55;
        }
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            inner.append(source, sourceOffset, length);
        }
        public void pretruncate(long position) throws IOException { inner.pretruncate(position); }
        public void seekFirstPos(long position) throws IOException { inner.seekFirstPos(position); }
        public void close() throws IOException { inner.close(); }
    }
}
