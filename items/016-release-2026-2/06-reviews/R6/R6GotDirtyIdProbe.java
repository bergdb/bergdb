package bergdb.core;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.Spos;
import bergdb.stream.MemoryStream;

/**
 * R6's probe of a corrupt got-dirty id (bergdb 016-06/R6): DbStarter.canonicalNode reads the
 * node at the stored position of a got-dirty entry whose id is in neither the node table nor
 * the section, and compares the ids with an assert only. Records A, B, C put /a, /b, /c
 * with a startup distance of 1 MB; the id of an entry of A's got-dirty list whose position
 * is a stream position (a node written before) is set to 123456789, an id no node has.
 */
public class R6GotDirtyIdProbe {
    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long a, c;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).retainForever().start()) {
            clock.setTime(10);
            Trans ta = db.trans().put("/a", "1").build();
            db.execute(ta);
            a = ta.tpos;
            clock.setTime(20);
            db.execute(db.trans().put("/b", "2"));
            clock.setTime(30);
            Trans t = db.trans().put("/c", "3").build();
            db.execute(t);
            c = t.tpos;
        }
        MemoryStream corrupt = stream.copy();
        c = a;      // A's record holds the got-dirty entries: B and C dirty no new node
        byte[] size = new byte[4];
        corrupt.read(c, size, 0, 4);
        byte[] record = new byte[Bytes.bytesToIntLE(size, 0)];
        corrupt.read(c, record, 0, record.length);
        StoredTrans parsed = StoredTrans.parse(c, record);
        long[] dirty = parsed.gotDirtyIdsAndSpos;
        int entry = -1;
        for (int i = 0; i < dirty.length / 2; i++) {
            System.out.println("got-dirty entry " + i + ": id " + dirty[2 * i] + ", spos " 
                    + dirty[2 * i + 1]);
            if (entry < 0 && Spos.isValid(dirty[2 * i + 1]) && !Spos.isVpos(dirty[2 * i + 1])) {
                entry = i;
            }
        }
        // The list ends before the last byte and the padding: find the entry's 16 bytes.
        byte[] pair = new byte[16];
        Bytes.longToBytesLE(dirty[2 * entry], pair, 0);
        Bytes.longToBytesLE(dirty[2 * entry + 1], pair, 8);
        int at = -1;
        for (int i = record.length - 16; i >= 0 && at < 0; i--) {
            if (java.util.Arrays.equals(java.util.Arrays.copyOfRange(record, i, i + 16), pair)) {
                at = i;
            }
        }
        byte[] id = new byte[8];
        Bytes.longToBytesLE(123456789L, id, 0);
        MemoryStream.TestAccess.write(corrupt, id, c + at);
        System.out.println("entry " + entry + "'s id " + dirty[2 * entry] + " -> 123456789");
        try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                .startupDistance(1000000).retainForever().start()) {
            final StringBuilder d = new StringBuilder();
            db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE,
                    new TransSeq.NodeVisitor() {
                public void node(bergdb.dag.Node node, long tpos, long lastTpos) {
                    d.append(" " + node.getId());
                }
            });
            System.out.println("START ACCEPTED: /a=" + str(DbUtil.get(db, Long.MAX_VALUE, "/a"))
                    + ", /b=" + str(DbUtil.get(db, Long.MAX_VALUE, "/b"))
                    + ", /c=" + str(DbUtil.get(db, Long.MAX_VALUE, "/c")) + "; D's ids:" + d);
        } catch (RuntimeException | AssertionError e) {
            System.out.println("START REFUSED: " + e);
        }
    }

    private static String str(byte[] v) {
        return v == null ? "null" : StringUtil.toString(v);
    }
}
