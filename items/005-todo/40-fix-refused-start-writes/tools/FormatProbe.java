package bergdb.core;

import java.util.ArrayList;
import java.util.List;

import bergdb.common.Bytes;
import bergdb.dag.Node;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.SalsaStream;

/**
 * Bergdb 005-40: what a start does with a stream whose version bytes are not this code's:
 * the format byte of the records, of a value node, and the version of the meta blocks.
 * Today's code, the core API, a MemoryStream; the bytes are changed in place, as a stream
 * of another format would have them.
 *
 * And a start with a wrong crypto key, or without one, or with one on a stream that is
 * not encrypted, after a crash in a meta block; then a start as it should be (crypto). And
 * n wrong keys, each on its own copy, at three cuts in a meta block (keys n).
 *
 * Usage: tools/run.sh format | crypto | keys [n] | all
 */
public class FormatProbe {
    static final int DIST = RecoverableStream.META_BLOCK_DISTANCE;
    static final int META = RecoverableStream.META_BLOCK_SIZE;

    public static void main(String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("crypto")) crypto();
        else if (args.length > 0 && args[0].equals("keys")) keys(Integer.parseInt(args[1]));
        else format();
    }

    /** The version bytes of records, of a value node and of the meta blocks. */
    static void format() throws Exception {
        MemoryStream created = create(null);
        long end = created.getLength();
        List<Long> recs = records(created);
        long last = recs.get(recs.size() - 1);
        int blocks = metaBlocks(created);
        System.out.println("The stream: " + end + " bytes, " + recs.size() + " records, "
                + blocks + " meta blocks (at 0" + (blocks > 1 ? " to " + (blocks - 1) * DIST : "")
                + "), record format " + byteAt(created, formatPos(last)) + ", meta block version "
                + (Bytes.bytesToUShortLE(read(created, 4, 2), 0)) + ".");
        System.out.println("The last record starts at " + last + ".");
        System.out.println();

        MemoryStream m;

        m = created.copy();
        print("C0. As written", m);

        m = created.copy();
        setRecordFormat(m, 6);
        print("C1. Every record of format 6 (a newer format)", m);

        m = created.copy();
        setRecordFormat(m, 2);
        print("C2. Every record of format 2 (before 2026-10-15)", m);

        m = created.copy();
        setRecordFormat(m, 6);
        m.truncate(end - 10);
        print("C3. As C1, the last 10 bytes cut (a torn last record)", m);

        m = created.copy();
        setRecordFormat(m, 6);
        m.truncate(last + 3);
        print("C4. As C1, cut 3 bytes into the last record (a torn header)", m);

        m = created.copy();
        setMetaVersion(m, 155);
        print("C5. Every meta block of version 155 (a newer format)", m);

        long lastBlock = (long) (blocks - 1) * DIST;
        m = created.copy();
        setMetaVersion(m, 155);
        m.truncate(lastBlock + 50);
        print("C6. As C5, cut 50 bytes into the meta block at " + lastBlock, m);

        m = created.copy();
        setMetaVersion(m, 155);
        m.truncate(end - 10);
        print("C7. As C5, the last 10 bytes cut (a torn last record)", m);

        m = created.copy();
        m.truncate(lastBlock + 50);
        print("C8. As written, cut 50 bytes into the meta block at " + lastBlock, m);

        long vpos = valueNodeIn(created, last);
        m = created.copy();
        setNodeFormat(m, vpos, 5, true);
        print("C9. A value node of format 5 in the last record (at " + vpos
                + "), its checksum computed again", m);

        m = created.copy();
        setNodeFormat(m, vpos, 5, false);
        print("C10. As C9, its checksum as it was", m);
    }

    /** A database with enough puts to pass the meta block at 200,000; key null: not encrypted. */
    static MemoryStream create(byte[] key) throws Exception {
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(open(s, key)).start();
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < 1000; i++) b.append((char) ('a' + i % 26));
        String v = b.toString();
        for (int i = 0; i < 300; i++) {
            db.execute(db.trans().put("/k" + i, i + v).build());
        }
        db.close();
        return s;
    }

    static void print(String what, MemoryStream m) throws Exception {
        System.out.println(what + ":");
        System.out.println(outcome(m, null));
    }

    /**
     * Starts a database on m, through a SalsaStream if key is not null; the outcome, and
     * what the start did to the stream (to its bytes in m, encrypted or not).
     */
    static String outcome(MemoryStream m, byte[] key) throws Exception {
        long before = m.getLength();
        byte[] bytes = read(m, 0, (int) before);
        final Db db = Db.builder().testSetup(open(m, key)).build();
        String o;
        try {
            db.start();
            String v = DbUtil.getString(db, "/k0");
            o = "started, " + (v != null && v.startsWith("0abc") ? "/k0 read" : "/k0 WRONG: " + v);
        } catch (Throwable e) {
            o = e.getClass().getSimpleName() + ": " + e.getMessage();
        }
        db.close();     // Writes what the start appended, also after a failed start.
        long after = m.getLength();
        String s;
        if (!java.util.Arrays.equals(bytes, read(m, 0, (int) before))) {
            s = "CHANGED before its old length";
        } else if (after == before) {
            s = "unchanged";
        } else {
            byte[] added = read(m, before, (int) (after - before));
            s = "grew by " + added.length + " bytes at " + before + ": " + describe(added, before);
        }
        return "    " + o + "\n    The stream then: " + s + ".";
    }

    static AppendOnlyStream open(MemoryStream m, byte[] key) throws Exception {
        return key == null ? m : new SalsaStream(m, NONCE, key);
    }

    static final byte[] NONCE = filled(8, 7);
    static final byte[] KEY_A = filled(32, 1);
    static final byte[] KEY_B = filled(32, 2);

    static byte[] filled(int n, int b) {
        byte[] r = new byte[n];
        java.util.Arrays.fill(r, (byte) b);
        return r;
    }

    /**
     * A start with the wrong key, or with none, or with a key on a stream that is not
     * encrypted, after a crash in the meta block at 200,000; then a start as it should be.
     */
    static void crypto() throws Exception {
        MemoryStream enc = create(KEY_A);
        MemoryStream plain = create(null);
        System.out.println("Two streams of the same puts: one encrypted with key A, "
                + enc.getLength() + " bytes; one not encrypted, " + plain.getLength() + " bytes.");
        System.out.println();
        cryptoCase("K0. Encrypted, as written; key B", enc, -1, KEY_B, true, KEY_A);
        cryptoCase("K1. Not encrypted, as written; key A", plain, -1, KEY_A, true, null);
        cryptoCase("K2. Encrypted, the last 10 bytes cut (a torn last record); key B", enc,
                enc.getLength() - 10, KEY_B, true, KEY_A);
        int k = 3;
        for (int x : new int[] {0, 3, 5, 50}) {
            long cut = DIST + x;
            String c = ", cut at " + cut + " (" + x + " bytes into the meta block at " + DIST + ")";
            cryptoCase("K" + k++ + ". Encrypted" + c + "; key A", enc, cut, KEY_A, false, null);
            cryptoCase("K" + k++ + ". Encrypted" + c + "; key B", enc, cut, KEY_B, true, KEY_A);
            cryptoCase("K" + k++ + ". Encrypted" + c + "; no key", enc, cut, null, true, KEY_A);
            cryptoCase("K" + k++ + ". Not encrypted" + c + "; key A", plain, cut, KEY_A, true,
                    null);
        }
    }

    /**
     * A start on a copy of s, cut at cut (-1: not cut), with key1 (null: no key); if then, a
     * second start on what the first one left, with key2.
     */
    static void cryptoCase(String what, MemoryStream s, long cut, byte[] key1, boolean then,
            byte[] key2) throws Exception {
        MemoryStream m = s.copy();
        if (cut >= 0) m.truncate(cut);
        System.out.println(what + ":");
        System.out.println(outcome(m, key1));
        if (then) {
            System.out.println("  Then " + (key2 == null ? "no key" : "key A") + ":");
            System.out.println(outcome(m.copy(), key2));
        }
    }

    /**
     * Starts with n wrong keys, each on its own copy of the encrypted stream cut at one of
     * three positions in the meta block at 200,000; counts what a start with the right key
     * then does, and how often that key reads the torn block as valid.
     */
    static void keys(int n) throws Exception {
        MemoryStream enc = create(KEY_A);
        System.out.println("The encrypted stream: " + enc.getLength() + " bytes. For each cut, " + n
                + " starts with a wrong key, each on its own copy; then a start with key A.");
        for (int x : new int[] {6, 50, 127}) {
            MemoryStream cut = enc.copy();
            cut.truncate(DIST + x);
            java.util.TreeMap<String, Integer> outcomes = new java.util.TreeMap<String, Integer>();
            for (int i = 0; i < n; i++) {
                byte[] key = filled(32, 2);
                Bytes.intToBytesLE(i, key, 0);
                MemoryStream m = cut.copy();
                startQuietly(m, key);
                // Does key A read the torn block as valid now? Its last byte is 10 then.
                byte[] last = new byte[1];
                if (m.getLength() >= DIST + META) {
                    new SalsaStream(m.copy(), NONCE, KEY_A).read(DIST + META - 1, last, 0, 1);
                }
                String o = (last[0] == 10 ? "the block read as valid; " : "")
                        + startQuietly(m.copy(), KEY_A);
                Integer c = outcomes.get(o);
                outcomes.put(o, c == null ? 1 : c + 1);
            }
            System.out.println("Cut " + x + " bytes into the meta block, then key A:");
            for (String o : outcomes.keySet()) {
                System.out.println("    " + outcomes.get(o) + " of " + n + ": " + o);
            }
        }
    }

    static String startQuietly(MemoryStream m, byte[] key) throws Exception {
        Db db = Db.builder().testSetup(open(m, key)).build();
        String o;
        try {
            db.start();
            String v = DbUtil.getString(db, "/k0");
            o = "started, " + (v != null && v.startsWith("0abc") ? "/k0 read" : "/k0 WRONG");
        } catch (Throwable e) {
            String msg = String.valueOf(e.getMessage());
            o = e.getClass().getSimpleName() + ": " + (msg.length() > 70 ? msg.substring(0, 70)
                    + "..." : msg);
        }
        db.close();
        return o;
    }

    /** All zero; the plain bytes of a meta block's fill-out (from 'from'); or not zero. */
    static String describe(byte[] b, long from) {
        int nonZero = 0;
        boolean template = true;
        StringBuilder first = new StringBuilder();
        for (int i = 0; i < b.length; i++) {
            if (b[i] != 0) {
                nonZero++;
                if (nonZero <= 6) first.append(nonZero > 1 ? ", " : "").append(b[i] & 0xff);
            }
            if (b[i] != templateByte(from + i)) template = false;
        }
        if (nonZero == 0) return "all zero";
        if (template) return "a meta block's fill-out in plain text (\"berg\", 154, zeros)";
        return nonZero + " not zero (" + first + (nonZero > 6 ? ", ..." : "") + ")";
    }

    /** The byte at pos of a meta block filled out by recovery, in plain text. */
    static byte templateByte(long pos) {
        long off = pos % DIST;
        if (off >= META) return 0;
        byte[] t = {'b', 'e', 'r', 'g', (byte) 154, 0};
        return off < t.length ? t[(int) off] : 0;
    }

    /** The start positions of the records, from the first one at 128. */
    static List<Long> records(MemoryStream s) throws Exception {
        RecoverableStream r = new RecoverableStream(s, new MetaBlock());
        List<Long> result = new ArrayList<Long>();
        long pos = META;
        while (pos < s.getLength()) {
            byte[] b = new byte[4];
            r.read(pos, b, 0, 4);
            result.add(pos);
            pos = RecoverableStream.getSpos(pos, Bytes.bytesToIntLE(b, 0));
        }
        return result;
    }

    static int metaBlocks(MemoryStream s) {
        return (int) ((s.getLength() - META) / DIST) + 1;
    }

    /** The stream position of a record's format byte, its byte 4. */
    static long formatPos(long tpos) {
        return RecoverableStream.getSpos(tpos, 4);
    }

    static int byteAt(MemoryStream s, long pos) throws Exception {
        return read(s, pos, 1)[0];
    }

    static void setRecordFormat(MemoryStream s, int format) throws Exception {
        for (long p : records(s)) {
            MemoryStream.TestAccess.write(s, new byte[] {(byte) format}, formatPos(p));
        }
    }

    static void setMetaVersion(MemoryStream s, int version) throws Exception {
        byte[] v = new byte[2];
        Bytes.ushortToBytesLE(version, v, 0);
        for (int k = 0; k < metaBlocks(s); k++) {
            MemoryStream.TestAccess.write(s, v, (long) k * DIST + 4);
        }
    }

    /** A value node of the record at tpos that does not span a meta block. */
    static long valueNodeIn(MemoryStream s, long tpos) throws Exception {
        RecoverableStream r = new RecoverableStream(s, new MetaBlock());
        byte[] b = new byte[4];
        r.read(tpos, b, 0, 4);
        byte[] rec = new byte[Bytes.bytesToIntLE(b, 0)];
        r.read(tpos, rec, 0, rec.length);
        StoredTrans t = StoredTrans.parse(tpos, rec);
        for (StoredNode n : t.nodes) {
            Node node = n.getNode();
            long p = node.getSpos();
            if (node.getType() == Node.TYPE_VALUE && p / DIST == (p + 1100) / DIST) {
                return p;
            }
        }
        throw new IllegalStateException("no value node in the record at " + tpos);
    }

    /** Sets the format byte of the node at pos, byte 5; and its checksum, bytes 6 and 7. */
    static void setNodeFormat(MemoryStream s, long pos, int format, boolean checksum)
            throws Exception {
        MemoryStream.TestAccess.write(s, new byte[] {(byte) format}, pos + 5);
        if (checksum) {
            int size = Bytes.bytesToIntLE(read(s, pos, 4), 0);
            byte[] node = read(s, pos, size);
            byte[] sum = new byte[2];
            Bytes.ushortToBytesLE(NodeChecksum.sumWithZeroReplace(node, 0, size, 6), sum, 0);
            MemoryStream.TestAccess.write(s, sum, pos + 6);
        }
    }

    static byte[] read(MemoryStream s, long pos, int len) throws Exception {
        byte[] b = new byte[len];
        s.read(pos, b, 0, len);
        return b;
    }
}
