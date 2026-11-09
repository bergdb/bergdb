package bergdb.core;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.StringMap;
import bergdb.common.StringUtil;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.KlongWithPointer;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.Kvt;
import bergdb.dag.Pointer;
import bergdb.dag.PointerFollower;
import bergdb.dag.PutData;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.storage.MetaBlock;
import bergdb.pub.util.Clock;
import bergdb.storage.RecoverableStream;
import bergdb.stream.MemoryStream;

/**
 * Writes what Java's classes give for a fixed set of inputs, as the test vectors of the C
 * clone's unit tests (bergdb 012-04): bytes.txt (Bytes), checksum.txt (NodeChecksum),
 * klong.txt (Klong), keys.txt (Keys) and jsem.txt (Java's own arithmetic: casts, shifts,
 * division, comparisons, Math.multiplyHigh and Math.round, and the take's share and dither
 * in integers, TransSeq.shareFp and ditherFp, since bergdb 005-79), and (012-06)
 * records.txt (a small stream that Db writes, its records as StoredTrans.parse parses them,
 * and records it refuses), and (012-07) knode.txt (KeyNode's operations as the Dag makes them,
 * and the node's stored bytes after each) and top.txt (TopDs's chains of top nodes), and
 * (012-09) strmap.txt (StringMap's texts, in HashMap's order) and keymod.txt (KeyModSet's
 * answers), and (012-08) dag.txt (the Dag's transactions: dirtyNodeBound before each, the
 * splits and the state after it), and (012-11) reclaim.txt (runs of Db with reclaim, with
 * the default step reserve and with one of four nodes, which splits the steps: the stream
 * from the decided cut, as its SHA-256), and (022-02) strutil.txt
 * (StringUtil.isWellFormedUtf8) and keys.txt's bkey2ikey (Keys.bkey2ikeyOrNull), the
 * keys of bergdb 021-05 and 021-06, into a directory. C's unit tests read them
 * (c/test/unit/t_vectors.c); 012-05's cross tests run this again and compare with the
 * committed files, so that a change in Java shows.
 *
 * Usage: java -ea -cp build/java/classes bergdb.core.Vectors DIR
 *
 * The format: one case per line, fields separated by one space; '#' starts a comment
 * line. Bytes are hex, "-" for none; a long is 16 hex digits (its bits) where its bits
 * matter, else decimal; a list of longs is hex longs separated by commas, "-" for none.
 * The inputs are fixed or from java.util.Random with fixed seeds, so the files are the
 * same at every run.
 */
public class Vectors {
    private static final String HEAD =
            "# Written by bergdb.core.Vectors (bergdb 012-04) from Java's classes; do not edit.";

    public static void main(String[] args) throws IOException {
        if (args.length != 1) {
            System.err.println("Usage: Vectors DIR");
            System.exit(2);
        }
        String dir = args[0];
        bytes(open(dir, "bytes.txt"));
        checksum(open(dir, "checksum.txt"));
        klong(open(dir, "klong.txt"));
        keys(open(dir, "keys.txt"));
        strutil(open(dir, "strutil.txt"));
        jsem(open(dir, "jsem.txt"));
        records(open(dir, "records.txt"));
        knode(open(dir, "knode.txt"));
        top(open(dir, "top.txt"));
        strmap(open(dir, "strmap.txt"));
        keymod(open(dir, "keymod.txt"));
        dag(open(dir, "dag.txt"));
        reclaim(open(dir, "reclaim.txt"));
        System.out.println("VECTORS OK: " + dir);
    }

    private static PrintWriter open(String dir, String name) throws IOException {
        PrintWriter w = new PrintWriter(new OutputStreamWriter(
                new FileOutputStream(dir + "/" + name), StandardCharsets.UTF_8));
        w.print(HEAD + "\n");
        return w;
    }

    // ---- Bytes ----

    private static void bytes(PrintWriter w) {
        Random r = new Random(1);
        byte[] b = new byte[8];

        w.print("# long VALUE LE BE: Bytes.longToBytesLE and BE; C reads them back too\n");
        List<Long> longs = new ArrayList<>(List.of(0L, 1L, -1L, Long.MIN_VALUE, Long.MAX_VALUE,
                0x0102030405060708L, 0x80L, 0xff00000000000000L, 255L, 256L));
        for (int i = 0; i < 10; i++) {
            longs.add(r.nextLong());
        }
        for (long v : longs) {
            Bytes.longToBytesLE(v, b, 0);
            String le = hex(b, 0, 8);
            Bytes.longToBytesBE(v, b, 0);
            String be = hex(b, 0, 8);
            assert Bytes.bytesToLongBE(b, 0) == v;
            w.print("long " + v + " " + le + " " + be + "\n");
        }

        w.print("# int VALUE LE BE\n");
        List<Integer> ints = new ArrayList<>(List.of(0, 1, -1, Integer.MIN_VALUE,
                Integer.MAX_VALUE, 0x01020304, 0x80, 0xff000000));
        for (int i = 0; i < 8; i++) {
            ints.add(r.nextInt());
        }
        for (int v : ints) {
            Bytes.intToBytesLE(v, b, 0);
            String le = hex(b, 0, 4);
            Bytes.intToBytesBE(v, b, 0);
            String be = hex(b, 0, 4);
            w.print("int " + v + " " + le + " " + be + "\n");
        }

        w.print("# short VALUE LE READ: Bytes.shortToBytesLE(long), and bytesToShortLE of LE\n");
        for (long v : new long[] {0, 1, -1, 32767, -32768, 32768, 65535, 0x12345, -70000}) {
            Bytes.shortToBytesLE(v, b, 0);
            w.print("short " + v + " " + hex(b, 0, 2) + " " + Bytes.bytesToShortLE(b, 0) + "\n");
        }

        w.print("# ushort VALUE LE, or VALUE refused: Bytes.ushortToBytesLE and bytesToUShortLE\n");
        for (int v : new int[] {0, 1, 127, 128, 255, 256, 32768, 65535, -1, 65536, 100000}) {
            try {
                Bytes.ushortToBytesLE(v, b, 0);
                assert Bytes.bytesToUShortLE(b, 0) == v;
                w.print("ushort " + v + " " + hex(b, 0, 2) + "\n");
            } catch (IllegalArgumentException e) {
                w.print("ushort " + v + " refused\n");
            }
        }

        w.print("# double BITS LE: Bytes.doubleToBytesLE of Double.longBitsToDouble(BITS)\n");
        for (double v : new double[] {1.0, 0.0, -0.0, Double.MIN_VALUE, Double.MAX_VALUE,
                Double.NaN, 123.45, -0.0012, Double.NEGATIVE_INFINITY}) {
            Bytes.doubleToBytesLE(v, b, 0);
            w.print("double " + hex16(Double.doubleToRawLongBits(v)) + " " + hex(b, 0, 8) + "\n");
        }

        w.print("# float BITS LE\n");
        for (float v : new float[] {1.0f, 0.0f, Float.MIN_VALUE, Float.MAX_VALUE, Float.NaN,
                123.45f, -0.0012f}) {
            Bytes.floatToBytesLE(v, b, 0);
            w.print("float " + hex8(Float.floatToRawIntBits(v)) + " " + hex(b, 0, 4) + "\n");
        }

        w.print("# longs LONGS LE: Bytes.longsToBytesLE\n");
        long[] arr = new long[] {123, 111222333444L, -1000};
        w.print("longs " + hexLongs(arr) + " " + hex(Bytes.longsToBytesLE(arr)) + "\n");
        w.close();
    }

    // ---- NodeChecksum ----

    private static void checksum(PrintWriter w) {
        Random r = new Random(2);
        w.print("# sum DATA OFFSET LENGTH SUM: NodeChecksum.sum(data, offset, length)\n");
        List<byte[]> data = new ArrayList<>();
        data.add(new byte[0]);
        data.add(new byte[] {0x01, 0x02});
        data.add(new byte[] {(byte) 0xff});
        data.add(filled(300, (byte) 0xff));
        data.add(filled(300, (byte) 0x00));
        data.add(filled(256, (byte) 0x80));
        for (int i = 0; i < 12; i++) {
            byte[] d = new byte[1 + r.nextInt(i < 8 ? 40 : 400)];
            r.nextBytes(d);
            data.add(d);
        }
        for (byte[] d : data) {
            w.print("sum " + hex(d) + " 0 " + d.length + " " + NodeChecksum.sum(d, 0, d.length)
                    + "\n");
            if (d.length >= 4) {
                int off = 1 + r.nextInt(d.length / 2);
                int len = r.nextInt(d.length - off);
                w.print("sum " + hex(d) + " " + off + " " + len + " "
                        + NodeChecksum.sum(d, off, len) + "\n");
            }
        }

        w.print("# zr DATA OFFSET LENGTH REPLACE SUM: NodeChecksum.sumWithZeroReplace\n");
        for (byte[] d : data) {
            if (d.length < 8) {
                continue;
            }
            int off = r.nextInt(4);
            int len = d.length - off - r.nextInt(4);
            int rep = off + 6;
            w.print("zr " + hex(d) + " " + off + " " + len + " " + rep + " "
                    + NodeChecksum.sumWithZeroReplace(d, off, len, rep) + "\n");
        }
        // Not all 0xff: a byte 0xff adds 0 modulo 255, so zeroing it changes nothing.
        byte[] edge = new byte[20];
        for (int i = 0; i < edge.length; i++) {
            edge[i] = (byte) (0x71 * (i + 1));
        }
        for (int rep : new int[] {-1, 0, 18, 19, 25}) {
            w.print("zr " + hex(edge) + " 0 20 " + rep + " "
                    + NodeChecksum.sumWithZeroReplace(edge, 0, 20, rep) + "\n");
        }

        w.print("# longs LONGS OFFSET LENGTH SUM: NodeChecksum.sum(long[], offset, length)\n");
        for (int i = 0; i < 6; i++) {
            long[] ls = new long[1 + r.nextInt(6)];
            for (int j = 0; j < ls.length; j++) {
                ls[j] = i == 0 ? -1 : r.nextLong();
            }
            int off = r.nextInt(ls.length);
            w.print("longs " + hexLongs(ls) + " " + off + " " + (ls.length - off) + " "
                    + NodeChecksum.sum(ls, off, ls.length - off) + "\n");
        }
        w.close();
    }

    // ---- Klong ----

    private static List<byte[]> klongKeys() {
        Random r = new Random(3);
        List<byte[]> keys = new ArrayList<>();
        byte[] edges = new byte[] {0, 1, 0x7f, (byte) 0x80, (byte) 0xff};
        keys.add(new byte[0]);
        for (byte e : edges) {
            for (int n = 1; n <= 7; n++) {
                keys.add(filled(n, e));
            }
        }
        keys.add(new byte[] {0, 1, 3, 127, (byte) 200, (byte) 255});
        keys.add(new byte[] {'a', 0, 0});
        keys.add(new byte[] {'a', 0});
        keys.add(new byte[] {0, 1});
        for (int i = 0; i < 20; i++) {
            byte[] k = new byte[r.nextInt(8)];
            r.nextBytes(k);
            keys.add(k);
        }
        return keys;
    }

    private static void klong(PrintWriter w) {
        Random r = new Random(4);
        w.print("# const NAME KLONG\n");
        w.print("const NULL " + hex16(Klong.NULL) + "\n");
        w.print("const EMPTY_KEY " + hex16(Klong.EMPTY_KEY) + "\n");
        w.print("const DELETE_NONE_BITMAP " + hex16(Klong.DELETE_NONE_BITMAP) + "\n");
        w.print("const DELETE_ALL_BITMAP " + hex16(Klong.DELETE_ALL_BITMAP) + "\n");
        w.print("const TYPE_KEY " + hex16(Klong.TYPE_KEY) + "\n");
        w.print("const TYPE_DELETE_BITMAP " + hex16(Klong.TYPE_DELETE_BITMAP) + "\n");

        w.print("# key BKEY KLONG CV KEYVALUE LENGTH INTTYPE: Klong.createKey(BKEY), then\n"
                + "# getCompareValue, getKeyValue, getLength, getIntType of it; CV is also\n"
                + "# createCompareValue(BKEY, 0, n), and getKey of KLONG gives BKEY\n");
        List<byte[]> keys = klongKeys();
        for (byte[] k : keys) {
            long kl = Klong.createKey(k);
            long cv = Klong.getCompareValue(kl);
            assert cv == Klong.createCompareValue(k, 0, k.length);
            byte[] out = new byte[k.length];
            assert Klong.getKey(kl, out) == k.length;
            w.print("key " + hex(k) + " " + hex16(kl) + " " + hex16(cv) + " "
                    + hex16(Klong.getKeyValue(kl)) + " " + Klong.getLength(kl) + " "
                    + Klong.getIntType(kl) + "\n");
        }

        w.print("# time TIME KLONG: Klong.createTime\n");
        long[] times = new long[] {0, 1, 123, 123456789012345L, Klong.MAX_TIME,
                Klong.MAX_TIME - 1, 1L << 55};
        for (long t : times) {
            w.print("time " + t + " " + hex16(Klong.createTime(t)) + "\n");
        }
        for (int i = 0; i < 5; i++) {
            long t = r.nextLong() & Klong.MAX_TIME;
            w.print("time " + t + " " + hex16(Klong.createTime(t)) + "\n");
        }

        w.print("# delete BITS KLONG: Klong.delete of createDelete() for each bit in BITS\n");
        int[][] bitSets = new int[][] {{0}, {5, 33}, {61}, {0, 1, 2, 60, 61}};
        for (int[] bits : bitSets) {
            long k = Klong.createDelete();
            StringBuilder s = new StringBuilder();
            for (int bit : bits) {
                k = Klong.delete(k, bit);
                s.append(s.length() == 0 ? "" : ",").append(bit);
            }
            w.print("delete " + s + " " + hex16(k) + "\n");
        }

        w.print("# prefix BKEY1 BKEY2 LENGTH: Klong.prefixLength of their key klongs\n");
        for (int i = 0; i < keys.size(); i += 3) {
            for (int j = i; j < keys.size(); j += 5) {
                byte[] a = keys.get(i);
                byte[] b = keys.get(j);
                w.print("prefix " + hex(a) + " " + hex(b) + " "
                        + Klong.prefixLength(Klong.createKey(a), Klong.createKey(b)) + "\n");
            }
        }
        String[][] pairs = {{"ab1", "ab2"}, {"abc", "abcd11"}, {"abc", ""}, {"abcdefg", "abcdefg"},
                {"abc", "Prag"}, {"abcd11", "abcdefg"}, {"a1", "a2"}, {"abcde", "abcdf"},
                {"abcdef", "abcdeg"}, {"abcdefg", "abcdefh"}};
        for (String[] p : pairs) {
            byte[] a = p[0].getBytes(StandardCharsets.UTF_8);
            byte[] b = p[1].getBytes(StandardCharsets.UTF_8);
            w.print("prefix " + hex(a) + " " + hex(b) + " "
                    + Klong.prefixLength(Klong.createKey(a), Klong.createKey(b)) + "\n");
        }
        w.close();
    }

    // ---- Keys ----

    private static void keys(PrintWriter w) {
        Random r = new Random(5);
        w.print("# ikey IKEY BKEY, or IKEY refused: Keys.toBytes(String) of the UTF-8 IKEY\n");
        String[] ikeys = new String[] {"a", "/", "dir/f1.txt", " ", "Stange\n\r  next line",
                "åäö", "\u0000", "\u007f", "\u0080", "dir/customers/anna", ""};
        for (String s : ikeys) {
            byte[] ik = s.getBytes(StandardCharsets.UTF_8);
            try {
                w.print("ikey " + hex(ik) + " " + hex(Keys.toBytes(s)) + "\n");
            } catch (IllegalArgumentException e) {
                w.print("ikey " + hex(ik) + " refused\n");
            }
        }

        w.print("# seg BKEY SEGMENTS BYTESIZE HASH: Keys.toSegments(BKEY), getByteSize and\n"
                + "# hash of them; toBytes(SEGMENTS) gives BKEY\n");
        List<byte[]> bkeys = new ArrayList<>();
        int[] sizes = new int[] {0, 1, 6, 7, 8, 13, 14, 15, 20, 21, 22, 27, 28, 29, 40};
        byte[] edges = new byte[] {0, 1, 0x7f, (byte) 0x80, (byte) 0xff};
        for (int n : sizes) {
            bkeys.add(filled(n, edges[n % edges.length]));
        }
        for (int i = 0; i < 15; i++) {
            byte[] k = new byte[r.nextInt(30)];
            r.nextBytes(k);
            bkeys.add(k);
        }
        for (byte[] k : bkeys) {
            long[] seg = Keys.toSegments(k);
            assert java.util.Arrays.equals(Keys.toBytes(seg), k);
            w.print("seg " + hex(k) + " " + hexLongs(seg) + " " + Keys.getByteSize(seg) + " "
                    + Keys.hash(seg) + "\n");
        }

        w.print("# hash LONGS HASH: Keys.hash of any longs\n");
        List<long[]> hs = new ArrayList<>();
        hs.add(new long[0]);
        hs.add(new long[] {Long.MIN_VALUE - 37 * 37});    // the sum is Long.MIN_VALUE (005-21)
        hs.add(new long[] {Long.MAX_VALUE - 37 * 37});
        hs.add(new long[] {-1});
        hs.add(new long[] {Long.MIN_VALUE, Long.MAX_VALUE, 0});
        for (int i = 0; i < 8; i++) {
            long[] ls = new long[1 + r.nextInt(5)];
            for (int j = 0; j < ls.length; j++) {
                ls[j] = r.nextLong();
            }
            hs.add(ls);
        }
        for (long[] ls : hs) {
            w.print("hash " + hexLongs(ls) + " " + Keys.hash(ls) + "\n");
        }

        w.print("# cmp LONGS1 LONGS2 KEYS ARRAYS: Keys.compareKeys and compareArrays\n");
        List<long[]> cs = new ArrayList<>();
        cs.add(new long[0]);
        cs.add(new long[] {0});
        cs.add(new long[] {1});
        cs.add(new long[] {-1});
        cs.add(new long[] {Long.MIN_VALUE});
        cs.add(new long[] {1, 2, 3});
        cs.add(new long[] {1, 2, 4});
        cs.add(new long[] {1, 2, 3, 4});
        cs.add(new long[] {111222333444L});
        cs.add(new long[] {-111222333444L});
        for (int i = 0; i < 6; i += 2) {
            cs.add(Keys.toSegments(bkeys.get(15 + i)));
        }
        for (long[] a : cs) {
            for (long[] b : cs) {
                w.print("cmp " + hexLongs(a) + " " + hexLongs(b) + " " + Keys.compareKeys(a, b)
                        + " " + Keys.compareArrays(a, b) + "\n");
            }
        }

        w.print("# isprefix BKEY1 BKEY2 RESULT: Keys.isPrefix of their segments\n");
        String[] ps = new String[] {"dir/customers/", "dir/customers/anna", "dir/cust", "d",
                "dir/cus", "dir/cust0", "dir/customers/annabel", "e"};
        for (String a : ps) {
            for (String b : ps) {
                byte[] ka = Keys.toBytes(a);
                byte[] kb = Keys.toBytes(b);
                w.print("isprefix " + hex(ka) + " " + hex(kb) + " "
                        + Keys.isPrefix(Keys.toSegments(ka), Keys.toSegments(kb)) + "\n");
            }
        }

        w.print("# bkey2ikey BKEY IKEY, or BKEY none: Keys.bkey2ikeyOrNull, the ikey's UTF-8\n"
                + "# (bergdb 021-06); toBytes(IKEY) gives BKEY\n");
        List<byte[]> bs = new ArrayList<>();
        bs.add(new byte[0]);
        for (String s : ikeys) {
            if (!s.isEmpty()) {
                bs.add(Keys.toBytes(s));
            }
        }
        bs.add(Keys.toBytes("/dd/-a\uFFFD"));               // 021-04's CK2
        int[][] none = {{0xef, 0xa2, 0x82}, {0xc2, 0x82}, {0xe4, 0x84}, {0xf6, 0x92, 0x82, 0x82},
                {0x00}, {0x31}, {0xfe}, {0xff}};              // Keys.testBkeyWithoutIkey's
        for (int[] more : none) {
            bs.add(withBytes(Keys.toBytes("/dd/-a"), more));
        }
        bs.add(withBytes(new byte[0], new int[] {0xe4, 0x84, 0x63}));
        for (int b = 0; b < 256; b++) {
            bs.add(new byte[] {(byte) b});
        }
        int[] near = {0x00, 0x01, 0x02, 0x03, 0x31, 0x33, 0x63, 0x81, 0x82, 0x91, 0x92, 0xa1,
                0xa2, 0xc1, 0xc2, 0xc3, 0xc4, 0xe1, 0xe2, 0xe3, 0xee, 0xef, 0xf0, 0xf1, 0xf2,
                0xf3, 0xf5, 0xf6, 0xf7, 0xfe, 0xff};          // Keys.testBkeyIkeyRoundTrip's
        Random rb = new Random(2106);
        for (int i = 0; i < 600; i++) {
            byte[] b = new byte[1 + rb.nextInt(6)];
            for (int j = 0; j < b.length; j++) {
                b[j] = (byte) near[rb.nextInt(near.length)];
            }
            bs.add(b);
        }
        for (int i = 0; i < 200; i++) {       // the bkeys of ikeys of whole characters
            bs.add(Keys.toBytes(randomText(rb)));
        }
        for (byte[] b : bs) {
            String ikey = Keys.bkey2ikeyOrNull(b);
            if (ikey == null) {
                w.print("bkey2ikey " + hex(b) + " none\n");
            } else {
                assert ikey.isEmpty() || java.util.Arrays.equals(Keys.toBytes(ikey), b);
                w.print("bkey2ikey " + hex(b) + " " + hex(ikey.getBytes(StandardCharsets.UTF_8))
                        + "\n");
            }
        }
        w.close();
    }

    private static byte[] withBytes(byte[] start, int[] more) {
        byte[] result = java.util.Arrays.copyOf(start, start.length + more.length);
        for (int i = 0; i < more.length; i++) {
            result[start.length + i] = (byte) more[i];
        }
        return result;
    }

    /** 1 to 4 characters, no surrogate: of 1 and 2 bytes in UTF-8 mostly, of 3 and 4 too. */
    private static String randomText(Random r) {
        StringBuilder s = new StringBuilder();
        for (int j = 1 + r.nextInt(4); j > 0; j--) {
            int cp;
            do {
                cp = r.nextInt(4) == 0 ? r.nextInt(0x110000) : r.nextInt(0x800);
            } while (cp >= 0xd800 && cp <= 0xdfff);
            s.appendCodePoint(cp);
        }
        return s.toString();
    }

    // ---- StringUtil ----

    private static void strutil(PrintWriter w) {
        w.print("# utf8 BYTES RESULT: StringUtil.isWellFormedUtf8 (bergdb 021-06); as an ikey,\n"
                + "# BYTES are refused unless RESULT is true (021-05)\n");
        List<byte[]> bs = new ArrayList<>();
        bs.add(new byte[0]);
        for (int a = 0; a < 256; a++) {
            bs.add(new byte[] {(byte) a});
        }
        int[][] edges = {{0xed, 0x9f, 0xbf}, {0xed, 0xa0, 0x80}, {0xee, 0x80, 0x80},
                {0xe0, 0x9f, 0xbf}, {0xe0, 0xa0, 0x80}, {0xc0, 0x80}, {0xc1, 0xbf},
                {0xc2, 0x80}, {0xf0, 0x8f, 0xbf, 0xbf}, {0xf0, 0x90, 0x80, 0x80},
                {0xf4, 0x8f, 0xbf, 0xbf}, {0xf4, 0x90, 0x80, 0x80}, {0xf5, 0x80, 0x80, 0x80},
                {0xef, 0xbf, 0xbd}, {0xe2, 0x82}, {0x61, 0xe2, 0x82, 0xac, 0x62},
                {0x61, 0xed, 0xa0, 0x80}, {0xed, 0xb0, 0x80}, {0x3f, 0xed, 0xa0, 0xbd},
                {0xed, 0xb8, 0x80, 0xf0, 0x9f, 0x98, 0x80}, {0x61, 0x3f, 0xf0, 0x9f, 0x98, 0x80}};
        for (int[] e : edges) {
            bs.add(withBytes(new byte[0], e));
        }
        int[] near = {0x00, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc1, 0xc2,
                0xdf, 0xe0, 0xe1, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf3, 0xf4, 0xf5, 0xff};
        for (int a : near) {
            for (int b : near) {
                bs.add(new byte[] {(byte) a, (byte) b});
            }
        }
        Random r = new Random(2106);
        for (int i = 0; i < 1000; i++) {
            byte[] b = new byte[1 + r.nextInt(8)];
            for (int j = 0; j < b.length; j++) {
                b[j] = (byte) near[r.nextInt(near.length)];
            }
            bs.add(b);
        }
        for (int i = 0; i < 300; i++) {       // sequences of whole characters, all well-formed
            bs.add(randomText(r).getBytes(StandardCharsets.UTF_8));
        }
        for (byte[] b : bs) {
            w.print("utf8 " + hex(b) + " " + StringUtil.isWellFormedUtf8(b) + "\n");
        }
        w.close();
    }

    // ---- Java's semantics (c/src/jsem.h; the rules in c/readme.md) ----

    private static void jsem(PrintWriter w) {
        Random r = new Random(6);

        w.print("# d2 BITS LONG INT: (long) and (int) of the double with BITS\n");
        List<Double> ds = new ArrayList<>(List.of(0.0, -0.0, 0.5, -0.5, 0.9999, -0.9999, 1.0,
                -1.0, 2.9, -2.9, 7 * 1.20, 1000 * 1.20, Double.NaN, Double.POSITIVE_INFINITY,
                Double.NEGATIVE_INFINITY, Double.MIN_VALUE, -Double.MIN_VALUE, Double.MAX_VALUE,
                -Double.MAX_VALUE, 0x1.0p63, -0x1.0p63, Math.nextDown(0x1.0p63),
                Math.nextUp(-0x1.0p63), Math.nextDown(-0x1.0p63), 0x1.0p64, 0x1.0p31, -0x1.0p31,
                2147483647.0, 2147483647.5, -2147483648.5, -2147483649.0, 0x1.0p53 + 1.0));
        ds.add(Double.longBitsToDouble(0x7ff0000000000001L));      // a signalling NaN
        ds.add(Double.longBitsToDouble(0xfff8000000000001L));      // a negative NaN
        double scale = 1;               // 100^i, exact; Math.pow need not be
        for (int i = 0; i < 12; i++) {
            ds.add(r.nextGaussian() * scale);
            scale *= 100;
        }
        for (double d : ds) {
            w.print("d2 " + hex16(Double.doubleToRawLongBits(d)) + " " + (long) d + " " + (int) d
                    + "\n");
        }

        w.print("# l2d LONG BITS: the bits of (double) LONG, rounded to the nearest\n");
        List<Long> ls = new ArrayList<>(List.of(0L, 1L, -1L, Long.MAX_VALUE, Long.MIN_VALUE,
                (1L << 53) + 1, (1L << 53) + 3, -(1L << 53) - 1, (1L << 62) + 511,
                (1L << 62) + 512, (1L << 62) + 513, (1L << 62) + 1536));
        for (int i = 0; i < 6; i++) {
            ls.add(r.nextLong());
        }
        for (long v : ls) {
            w.print("l2d " + v + " " + hex16(Double.doubleToRawLongBits((double) v)) + "\n");
        }

        w.print("# narrow LONG INT SHORT BYTE: (int), (short) and (byte) of LONG\n");
        List<Long> ns = new ArrayList<>(List.of(0L, 1L, -1L, 127L, 128L, 255L, 256L, 32767L,
                32768L, 65535L, 65536L, 0x7fffffffL, 0x80000000L, 0xffffffffL, 0x100000000L,
                Long.MAX_VALUE, Long.MIN_VALUE));
        for (int i = 0; i < 4; i++) {
            ns.add(r.nextLong());
        }
        for (long v : ns) {
            w.print("narrow " + v + " " + (int) v + " " + (short) v + " " + (byte) v + "\n");
        }

        w.print("# sh64 VALUE N SHL SHR USHR: VALUE << N, >> N and >>> N of a long\n");
        long[] vs = new long[] {1, -1, Long.MIN_VALUE, Long.MAX_VALUE, 0x0123456789abcdefL,
                r.nextLong()};
        int[] counts = new int[] {0, 1, 8, 31, 32, 33, 63, 64, 65, 127, -1, -63, -64};
        for (long v : vs) {
            for (int n : counts) {
                w.print("sh64 " + hex16(v) + " " + n + " " + hex16(v << n) + " " + hex16(v >> n)
                        + " " + hex16(v >>> n) + "\n");
            }
        }
        w.print("# sh32 VALUE N SHL SHR USHR: likewise for an int\n");
        int[] ivs = new int[] {1, -1, Integer.MIN_VALUE, Integer.MAX_VALUE, 0x89abcdef};
        for (int v : ivs) {
            for (int n : counts) {
                w.print("sh32 " + hex8(v) + " " + n + " " + hex8(v << n) + " " + hex8(v >> n)
                        + " " + hex8(v >>> n) + "\n");
            }
        }

        w.print("# div N D QUOT REM FLOORDIV: N / D, N % D and Math.floorDiv(N, D) of longs\n");
        long[][] divs = new long[][] {{7, 2}, {-7, 2}, {7, -2}, {-7, -2}, {6, 3}, {-6, 3},
                {0, 5}, {0, -5}, {Long.MIN_VALUE, -1}, {Long.MIN_VALUE, 1}, {Long.MAX_VALUE, -1},
                {Long.MIN_VALUE, 2}, {Long.MIN_VALUE, Long.MAX_VALUE}, {5, Long.MIN_VALUE},
                {-5, Long.MIN_VALUE}, {Long.MIN_VALUE, Long.MIN_VALUE}, {-1, 255}, {-256, 255},
                {r.nextLong(), r.nextInt()}, {r.nextLong(), -1 - r.nextInt(1000)}};
        for (long[] p : divs) {
            w.print("div " + p[0] + " " + p[1] + " " + (p[0] / p[1]) + " " + (p[0] % p[1]) + " "
                    + Math.floorDiv(p[0], p[1]) + "\n");
        }
        w.print("# idiv N D QUOT REM: N / D and N % D of ints\n");
        int[][] idivs = new int[][] {{7, 2}, {-7, 2}, {7, -2}, {-7, -2}, {Integer.MIN_VALUE, -1},
                {Integer.MAX_VALUE, -1}, {Integer.MIN_VALUE, 3}, {-1, 255}, {-300, 255}};
        for (int[] p : idivs) {
            w.print("idiv " + p[0] + " " + p[1] + " " + (p[0] / p[1]) + " " + (p[0] % p[1])
                    + "\n");
        }

        w.print("# cmp A B SIGNED UNSIGNED: Long.compare and Long.compareUnsigned, as -1, 0, 1\n");
        long[] cs = new long[] {0, 1, -1, Long.MIN_VALUE, Long.MAX_VALUE};
        for (long a : cs) {
            for (long b : cs) {
                w.print("cmp " + a + " " + b + " " + Long.signum(Long.compare(a, b)) + " "
                        + Long.signum(Long.compareUnsigned(a, b)) + "\n");
            }
        }

        w.print("# nlz LONG N: Long.numberOfLeadingZeros\n");
        for (long v : new long[] {0, 1, -1, Long.MIN_VALUE, Long.MAX_VALUE, 1L << 32, 255,
                r.nextLong() >>> 7}) {
            w.print("nlz " + v + " " + Long.numberOfLeadingZeros(v) + "\n");
        }

        w.print("# mulhi A B HIGH: Math.multiplyHigh(A, B), the high word of the signed product\n");
        long[] ms = new long[] {0, 1, -1, Long.MAX_VALUE, Long.MIN_VALUE, 0xFFFFFFFFL,
                1L << 32, 0x9E3779B97F4A7C15L, r.nextLong(), r.nextLong(), r.nextLong() >>> 1};
        for (long a : ms) {
            for (long b : ms) {
                w.print("mulhi " + a + " " + b + " " + Math.multiplyHigh(a, b) + "\n");
            }
        }

        w.print("# divu N D QUOT REM: Long.divideUnsigned and Long.remainderUnsigned\n");
        long[][] dus = new long[][] {{7, 2}, {-1, 2}, {-1, -1}, {-2, -1}, {Long.MIN_VALUE, 3},
                {5, -5}, {-5, 5}, {r.nextLong(), r.nextLong() >>> 30}, {r.nextLong(), 0xFFFFFFFFL}};
        for (long[] p : dus) {
            w.print("divu " + p[0] + " " + p[1] + " " + Long.divideUnsigned(p[0], p[1]) + " "
                    + Long.remainderUnsigned(p[0], p[1]) + "\n");
        }

        // Math.round, which the API uses to convert a double setting to an integer: the
        // reclaim fraction to units of 2^-16 (bergdb 005-79, Db.setReclaimInternalFraction).
        w.print("# round BITS LONG: Math.round of the double with BITS\n");
        List<Double> rs = new ArrayList<>(List.of(0.0, -0.0, 0.5, -0.5, 1.5, 2.5, -1.5, -2.5,
                0.49999999999999994, -0.49999999999999994, Math.nextDown(0.5), 4503599627370495.5,
                4503599627370497.0, -4503599627370495.5, 0x1.0p52, 0x1.0p63, -0x1.0p63, 1e19,
                -1e19, Double.NaN, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY,
                Double.MIN_VALUE, 0.001 * 65536, 0.9 * 65536, 0.1 * 65536, 0.25 * 65536,
                0.37 * 65536, 0.05 * 65536));
        for (int i = 0; i < 8; i++) {
            rs.add((0.05 + 0.45 * r.nextDouble()) * 65536);     // Gen's fractions, as units
        }
        for (double d : rs) {
            w.print("round " + hex16(Double.doubleToRawLongBits(d)) + " " + Math.round(d) + "\n");
        }

        // The take's share (TransSeq.shareFp, bergdb 005-79): in units of 2^-16 of a node,
        // floor(D o S 2^16 / (O sd)) at most D 2^16, Long.MAX_VALUE outside the bounds.
        w.print("# sharefp D OWN TOTAL DIST SD SHARE: TransSeq.shareFp(D, OWN, TOTAL, DIST, SD)\n");
        long[][] edges = new long[][] {{100, 100, 1000, 2000, 800}, {6, 1000, 1000, 49606, 65536},
                {1L << 32, 48, 1000, 2000, 800}, {100, 48, 1000, 1L << 47, 800},
                {100, 1L << 31, 1000, 2000, 800}, {100, 48, 0, 2000, 800},
                {100, 48, 1000, 2000, 0}, {-1, 48, 1000, 2000, 800},
                {(1L << 32) - 1, (1L << 31) - 1, 1, (1L << 47) - 1, 10},
                {0, 48, 48, 1000, 10}, {1000, 0, 48, 1000, 10}};
        for (long[] e : edges) {
            w.print("sharefp " + e[0] + " " + e[1] + " " + e[2] + " " + e[3] + " " + e[4] + " "
                    + TransSeq.shareFp(e[0], e[1], e[2], e[3], (int) e[4]) + "\n");
        }
        for (int i = 0; i < 24; i++) {
            long dirty = 1 + r.nextInt(i < 12 ? 50 : 1_000_000);
            long own = 48 + r.nextInt(i < 12 ? 2000 : 100_000_000);
            long total = own + r.nextInt(i < 12 ? 100_000 : Integer.MAX_VALUE);
            int sd = 1 + r.nextInt(i < 12 ? 1_000_000 : Integer.MAX_VALUE - 1);
            long dist = i % 3 == 0 ? r.nextLong() >>> 17 : (long) (r.nextDouble() * 4 * sd);
            w.print("sharefp " + dirty + " " + own + " " + total + " " + dist + " " + sd + " "
                    + TransSeq.shareFp(dirty, own, total, dist, sd) + "\n");
        }

        w.print("# ditherfp POS U: TransSeq.ditherFp(POS), the top 16 bits of SplitMix64's "
                + "finalizer\n");
        List<Long> ps = new ArrayList<>(List.of(0L, 1L, 128L, 1200L, 1300L, 200_000L, 531_776L,
                1L << 40, Long.MAX_VALUE, -1L));
        for (int i = 0; i < 6; i++) {
            ps.add(r.nextLong() >>> 1);
        }
        for (long pos : ps) {
            w.print("ditherfp " + pos + " " + TransSeq.ditherFp(pos) + "\n");
        }
        w.close();
    }

    // ---- Records and nodes (bergdb 012-06) ----

    /** The position at which each record is parsed a second time: 40 bytes before the meta
     * block at 200,000, so that its nodes after the block have positions 128 bytes further on
     * than their offsets say, and its value nodes' stored offsets differ from their distances
     * in the stream (005-34). */
    private static final long SHIFTED = RecoverableStream.META_BLOCK_DISTANCE - 40;

    private static void records(PrintWriter w) throws IOException {
        MemoryStream ms = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        DbBuilder b = Db.builder();
        b.testSetup(ms);
        b.clock(clock);
        b.maxNodeSize8();
        b.startupDistance(100);
        clock.setTime(1000);
        Db db = b.build();
        db.start();
        Random r = new Random(7);
        for (int i = 0; i < 14; i++) {
            clock.setTime(2000 + 10 * i);
            Trans.Builder t = db.trans();
            int n = 1 + r.nextInt(3);
            for (int j = 0; j < n; j++) {
                String key = "/k/" + r.nextInt(12);
                if (r.nextInt(5) == 0) {
                    t.delete(key);
                } else {
                    t.put(key, "v" + i + "." + j);
                }
            }
            db.execute(t.build());
        }
        db.close();
        byte[] stream = new byte[(int) ms.getLength()];
        ms.read(0, stream, 0, stream.length);
        w.print("# stream HEX: the stream of a database that Db made (MemoryStream, node size 8, "
                + "startup distance 100, 14 transactions)\n");
        w.print("stream " + hex(stream) + "\n");

        List<Long> tposes = new ArrayList<>();
        List<byte[]> bufs = new ArrayList<>();
        Object lock = new Object();
        NodeStream ns = new NodeStream(new RecoverableStream(ms, new MetaBlock()), lock);
        synchronized (lock) {
            NodeStream.TransIterator it = ns.createTransIterator(0);
            while (it.next()) {
                tposes.add(it.tpos);
                bufs.add(it.transBuffer);
            }
        }

        w.print("# record TPOS HEX: a committed record of the stream, its bytes\n");
        w.print("# trans TPOS AT TT STARTUPPOS TOPPOS LASTPOS NNODES DIRTY: StoredTrans.parse of "
                + "the record at AT (TPOS, or " + SHIFTED + "); DIRTY its got-dirty list\n");
        w.print("# node TPOS AT I 10 SPOS ID ORDINAL ROOTTIME ROOT SKIPPOS SKIPTIME\n");
        w.print("# node TPOS AT I 20 SPOS ID PREVPOS LEAF N KLONGS REFS\n");
        w.print("# node TPOS AT I 30|40 SPOS ID TPOS OFFSETFROMTRANS VALUE KEY: a value or a "
                + "delete (VALUE -)\n");
        for (int k = 0; k < tposes.size(); k++) {
            long tpos = tposes.get(k);
            byte[] buf = bufs.get(k);
            w.print("record " + tpos + " " + hex(buf) + "\n");
            for (long at : new long[] {tpos, SHIFTED}) {
                StoredTrans t = StoredTrans.parse(at, buf);
                w.print("trans " + tpos + " " + at + " " + t.tt + " " + t.startupPos + " "
                        + t.topPos + " " + t.lastPos + " " + t.nodes.length + " "
                        + hexLongs(t.gotDirtyIdsAndSpos) + "\n");
                for (int i = 0; i < t.nodes.length; i++) {
                    StoredNode sn = t.nodes[i];
                    Node n = sn.getNode();
                    String head = "node " + tpos + " " + at + " " + i + " " + (n.getType() & 0xff)
                            + " " + n.getSpos() + " " + n.getId() + " ";
                    if (n instanceof TopNode) {
                        TopNode top = (TopNode) n;
                        long[] pos = new long[top.pointersLength];
                        long[] time = new long[top.pointersLength];
                        for (int j = 0; j < pos.length; j++) {
                            pos[j] = top.pointersPos[j];
                            time[j] = top.pointersTime[j];
                        }
                        w.print(head + top.topNodeId + " " + top.rootTime + " "
                                + top.getPointerPos(0) + " " + decLongs(pos) + " "
                                + decLongs(time) + "\n");
                    } else if (n instanceof KeyNode) {
                        KeyNode key = (KeyNode) n;
                        long[] kl = new long[key.size];
                        long[] refs = new long[key.size];
                        for (int j = 0; j < kl.length; j++) {
                            kl[j] = key.klongs[j];
                            refs[j] = key.getPointerPos(j);
                        }
                        w.print(head + sn.getPrevPos() + " " + (key.isSegmentLeaf() ? 1 : 0) + " "
                                + key.size + " " + hexLongs(kl) + " " + decLongs(refs) + "\n");
                    } else {
                        ValueNode v = (ValueNode) n;
                        w.print(head + v.getTpos() + " " + v.getOffsetFromTrans() + " "
                                + (v.value == null ? "-" : hex(v.value)) + " "
                                + hexLongs(((StoredValueNode) sn).getKey()) + "\n");
                    }
                }
            }
        }

        // Refused records: one byte changed, and the changed node's checksum made right
        // again where the change is to reach the parser's own checks.
        w.print("# refuse TPOS OFF BYTES FIX EXCEPTION: the record at TPOS with BYTES (hex) "
                + "written at OFF, and then the checksum of the node at offset FIX computed again "
                + "(-1: none), refused by StoredTrans.parse with EXCEPTION (its simple name), or "
                + "taken\n");
        for (int k = 0; k < tposes.size(); k++) {
            long tpos = tposes.get(k);
            byte[] buf = bufs.get(k);
            refuse(w, tpos, buf, 4, 4, -1);                 // the record's format
            refuse(w, tpos, buf, 4, 6, -1);
            refuse(w, tpos, buf, 0, (buf[0] + 8) & 0xff, -1);     // the size, past the buffer
            int off = 32;
            while (true) {
                int size = Bytes.bytesToIntLE(buf, off);
                if (size == 0) {
                    break;
                }
                int type = buf[off + 4] & 0xff;
                refuse(w, tpos, buf, off + 9, buf[off + 9] ^ 0x10, -1);    // the checksum
                refuse(w, tpos, buf, off + 4, 50, off);             // the type
                refuse(w, tpos, buf, off + 5, buf[off + 5] + 1, off);   // the node's format
                if (type == Node.TYPE_TOP_NODE) {
                    refuse(w, tpos, buf, off + 8, 0x80, off);       // h below 0
                    refuse(w, tpos, buf, off + 8, buf[off + 8] + 1, off);   // h, not the ordinal's
                    refuse(w, tpos, buf, off + 31, 0x80, off);      // the root time below 0
                    refuse(w, tpos, buf, off + 31, 0x01, off);      // the root time past 2^56 - 1
                    refuse(w, tpos, buf, off + 39, 0x80, off);      // the root pointer below 0
                    refuse(w, tpos, buf, off + 0, size + 16, off);  // the size field (assert)
                    if (size > 40) {
                        boolean set = Bytes.bytesToLongLE(buf, off + 40) != -1;
                        byte[] p = new byte[8];
                        Bytes.longToBytesLE(set ? -1 : 4096, p, 0);
                        refuse(w, tpos, buf, off + 40, p, off);     // skip pointer 0 (un)set
                    }
                } else if (type == Node.TYPE_KEY_NODE) {
                    refuse(w, tpos, buf, off + 15, 0x80, off);      // prevPos below -1
                    refuse(w, tpos, buf, off + 16, 2, off);         // the leaf byte
                    refuse(w, tpos, buf, off + 18, 0x80, off);      // n below 0
                } else {
                    refuse(w, tpos, buf, off + 19, 0x7f, off);      // the stored offset
                    if (type == Node.TYPE_VALUE) {
                        refuse(w, tpos, buf, off + 23, 0x80, off);  // the length below 0
                        refuse(w, tpos, buf, off + 22, 0x7f, off);  // the length past the record
                    } else {
                        refuse(w, tpos, buf, off + 20, 7, off);     // the key size
                    }
                }
                off += size;
            }
            refuse(w, tpos, buf, off + 7, 0x80, -1);        // the got-dirty count below 0
        }
        w.close();
    }

    private static void refuse(PrintWriter w, long tpos, byte[] buf, int off, int value,
            int fix) {
        refuse(w, tpos, buf, off, new byte[] {(byte) value}, fix);
    }

    /**
     * Prints a "refuse" line: the record with 'change' written at 'off', and the checksum of
     * the node at 'fix' computed again (over its size field's bytes, as changed), parsed by
     * StoredTrans.parse; EXCEPTION is "taken" if the parser takes it, which C checks too.
     */
    private static void refuse(PrintWriter w, long tpos, byte[] buf, int off, byte[] change,
            int fix) {
        if (off + change.length > buf.length) {
            return;
        }
        byte[] b = buf.clone();
        System.arraycopy(change, 0, b, off, change.length);
        if (fix >= 0) {
            int size = Bytes.bytesToIntLE(b, fix);
            if (fix + size <= b.length) {
                int sum = NodeChecksum.sumWithZeroReplace(b, fix, size, fix + 6);
                b[fix + 6] = (byte) sum;
                b[fix + 7] = (byte) (sum >>> 8);
            }
        }
        String what;
        try {
            StoredTrans.parse(tpos, b);
            what = "taken";
        } catch (RuntimeException | AssertionError e) {
            what = e.getClass().getSimpleName();
        }
        w.print("refuse " + tpos + " " + off + " " + hex(change) + " " + fix + " " + what + "\n");
    }

    private static String decLongs(long[] ls) {
        if (ls.length == 0) {
            return "-";
        }
        StringBuilder s = new StringBuilder();
        for (long l : ls) {
            s.append(s.length() == 0 ? "" : ",").append(l);
        }
        return s.toString();
    }

    // ---- KeyNode (bergdb 012-07) ----

    /**
     * knode.txt: runs of KeyNode's operations, as the Dag makes them, each line an operation
     * and what Java's node is after it: its size and the FNV-1a hash (64 bits) of its stored
     * bytes (StoredKeyNode.toLongs with prevPos 0), and at a run's end the bytes themselves.
     */
    private static void knode(PrintWriter w) {
        w.print("# run SEED LEAF: a new KeyNode(LEAF), id 0, spos 0; the operations follow, each\n");
        w.print("#   with = SIZE HASH: the node after it, its size and its stored bytes' FNV-1a\n");
        w.print("# a T K S: addKlong(T, K, a value node at S)   c T K S: addKlong(T, K, a key node at S)\n");
        w.print("# d T CV DEL: getDeleteBitmap(CV) is DEL; if not 0, addDeleteKlong(T, DEL)\n");
        w.print("# r T K S R: replaceKlong(T, K, a value node at S) gives R (1 replaced)\n");
        w.print("# l T: the node becomes lastVersion(T)   x T: setContentFrom(lastVersion(T))\n");
        w.print("# p T: toPreviousState(T)\n");
        w.print("# s T W N K1 S1 ...: firstAndSecond(T, lastVersion(T), N inserts (K, a value node\n");
        w.print("#   at S)); the node becomes first (W 0) or second (W 1); = also has SECONDKLONG and\n");
        w.print("#   the other node's SIZE HASH\n");
        w.print("# end HEX: the node's stored bytes, at the end of runs 1 to 4\n");
        for (int seed = 1; seed <= 12; seed++) {
            knodeRun(w, seed);
        }
        w.close();
    }

    private static void knodeRun(PrintWriter w, int seed) {
        Random r = new Random(seed);
        long[] cvs = new long[12];
        for (int i = 0; i < cvs.length; i++) {
            byte[] b = new byte[r.nextInt(4)];
            for (int j = 0; j < b.length; j++) {
                b[j] = (byte) (0x61 + r.nextInt(5));
            }
            cvs[i] = Klong.createCompareValue(b, 0, b.length);
        }
        boolean leaf = seed % 3 != 0;
        KeyNode node = new KeyNode(leaf);
        node.setId(0);
        node.setSpos(0);
        w.print("run " + seed + " " + (leaf ? 1 : 0) + "\n");
        long t = 1 + r.nextInt(5);
        long nextSpos = 1000;
        for (int op = 0; op < 40; op++) {
            if (r.nextInt(3) == 0) {
                t += 1 + r.nextInt(3);
            }
            long cv = cvs[r.nextInt(cvs.length)];
            long k = Klong.compareValueToKeyKlong(cv);
            int what = r.nextInt(20);
            String line;
            if (node.size + 3 > 60 || what == 0) {
                if (node.size < 2 || r.nextBoolean()) {
                    t++;
                    KeyNode last = node.lastVersion(t);
                    last.setId(0);
                    last.setSpos(0);
                    node = last;
                    line = "l " + t;
                } else {
                    t++;
                    KeyNode last = node.lastVersion(t);
                    knodeSetContentFrom(node, last);
                    line = "x " + t;
                }
            } else if (what == 1 && node.size >= 3) {
                t++;
                KeyNode last = node.lastVersion(t);
                if (last.size < 2) {
                    node.toPreviousState(t - 2);
                    w.print("p " + (t - 2) + " = " + knodeState(node) + "\n");
                    continue;
                }
                int n = r.nextInt(3);
                KlongWithPointer[] insert = new KlongWithPointer[n];
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < n; i++) {
                    insert[i] = new KlongWithPointer();
                    insert[i].klong = Klong.compareValueToKeyKlong(cvs[r.nextInt(cvs.length)]);
                    ValueNode v = new ValueNode(new byte[0], nextSpos);
                    v.setId(nextSpos);
                    insert[i].node = v;
                    sb.append(" " + hex16(insert[i].klong) + " " + nextSpos);
                    nextSpos += 8;
                }
                KeyNode first = new KeyNode(leaf);
                KeyNode second = new KeyNode(leaf);
                long secondKlong = node.firstAndSecond(t, last, insert, first, second);
                int which = r.nextInt(2);
                KeyNode other = which == 0 ? second : first;
                node = which == 0 ? first : second;
                node.setId(0);
                node.setSpos(0);
                other.setId(0);
                other.setSpos(0);
                w.print("s " + t + " " + which + " " + n + sb + " = " + knodeState(node) + " "
                        + hex16(secondKlong) + " " + knodeState(other) + "\n");
                continue;
            } else if (what == 2) {
                // Before t, so that the next change at t adds a later time, as in a database,
                // whose key nodes' times increase (KeyNode.checkIncreasingTime, which checks
                // that since bergdb 005-75; a tp of t made two TIME klongs of t).
                long tp = t - 1 - r.nextInt(5);
                node.toPreviousState(tp);
                line = "p " + tp;
            } else if (what <= 5) {
                long del = node.getDeleteBitmap(cv);
                if (del != 0) {
                    node.addDeleteKlong(t, del);
                }
                line = "d " + t + " " + hex16(cv) + " " + hex16(del);
            } else if (what == 6 && !knodeHasDelete(node)) {
                ValueNode v = new ValueNode(new byte[0], nextSpos);
                v.setId(nextSpos);
                boolean replaced = node.replaceKlong(t, k, v, AccessData.DEFAULT_ACCESS_DATA);
                line = "r " + t + " " + hex16(k) + " " + nextSpos + " " + (replaced ? 1 : 0);
                nextSpos += 8;
            } else if (what <= 8) {
                KeyNode c = new KeyNode(true);
                c.setId(nextSpos + 1);
                c.setSpos(nextSpos);
                node.addKlong(t, k, c, AccessData.DEFAULT_ACCESS_DATA);
                line = "c " + t + " " + hex16(k) + " " + nextSpos;
                nextSpos += 8;
            } else {
                ValueNode v = new ValueNode(new byte[0], nextSpos);
                v.setId(nextSpos);
                node.addKlong(t, k, v, AccessData.DEFAULT_ACCESS_DATA);
                line = "a " + t + " " + hex16(k) + " " + nextSpos;
                nextSpos += 8;
            }
            w.print(line + " = " + knodeState(node) + "\n");
        }
        if (seed <= 4) {
            w.print("end " + hex(knodeStored(node)) + "\n");
        }
    }

    /** KeyNode.setContentFrom, package-private in bergdb.dag. */
    private static void knodeSetContentFrom(KeyNode node, KeyNode other) {
        try {
            java.lang.reflect.Method m = KeyNode.class.getDeclaredMethod("setContentFrom",
                    KeyNode.class);
            m.setAccessible(true);
            m.invoke(node, other);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }

    private static boolean knodeHasDelete(KeyNode node) {
        for (int i = 0; i < node.size; i++) {
            if (Klong.getType(node.klongs[i]) == Klong.TYPE_DELETE_BITMAP) return true;
        }
        return false;
    }

    private static byte[] knodeStored(KeyNode node) {
        long[] longs = new long[StoredKeyNode.getByteSize(node) / 8];
        StoredKeyNode.toLongs(node, longs, 0, 0);
        return Bytes.longsToBytesLE(longs);
    }

    /** SIZE HASH: the node's size and the FNV-1a hash of its stored bytes. */
    private static String knodeState(KeyNode node) {
        long h = 0xcbf29ce484222325L;
        for (byte b : knodeStored(node)) {
            h ^= b & 0xff;
            h *= 0x100000001b3L;
        }
        return node.size + " " + hex16(h);
    }

    // ---- TopDs (bergdb 012-07) ----

    /**
     * top.txt: chains of top nodes made by TopDs.newSuperRoot, as the Dag makes them, each
     * new top node given its id by the node change listener as Db does (a vpos), and written
     * now and then (a position, canonical); after each step the super root's ordinal and the
     * size and FNV-1a hash of its stored bytes (StoredTopNode.toLongs); and findRoot at times.
     */
    private static void top(PrintWriter w) {
        w.print("# chain SEED T0 R0 SECOND: createFromFirstRoot(T0, a key node at R0), the first top\n");
        w.print("#   node's id 1; setSecondOrdinal(SECOND); every node canonical, as Db makes them\n");
        w.print("# n T R = ORD SIZE HASH: newSuperRoot(T, a key node at R, its id R + 1); each top\n");
        w.print("#   node made gets the next id, 3, 5, ...; then the super root's ordinal and stored bytes\n");
        w.print("# w P: the super root is written at P: its spos P\n");
        w.print("# f T = R: findRoot(T) is the key node at R, -1 for none\n");
        for (int seed = 1; seed <= 8; seed++) {
            topChain(w, seed);
        }
        w.close();
    }

    private static void topChain(PrintWriter w, int seed) {
        Random r = new Random(100 + seed);
        long t = 10 + r.nextInt(10);
        long[] nextId = {1};
        long rootPos = 2000;
        KeyNode root0 = new KeyNode();
        root0.setSpos(rootPos);
        root0.setId(rootPos + 1);
        root0.setCanonical(true);
        TopDs ds = TopDs.createFromFirstRoot(t, root0, 0, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        ds.getSuperRoot().setId(nextId[0]);
        ds.getSuperRoot().setSpos(nextId[0]);
        ds.getSuperRoot().setCanonical(true);
        nextId[0] += 2;
        long second = seed % 4 == 0 ? 1 + r.nextInt(1000) : 1;
        ds.setSecondOrdinal(second);
        w.print("chain " + seed + " " + t + " " + rootPos + " " + second + "\n");
        Dag.NodeChangeListener ids = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) {
                node.setId(nextId[0]);          // as Db: setIdOfNode, registerNewNode
                node.setSpos(nextId[0]);
                node.setCanonical(true);
                nextId[0] += 2;
            }
            public void keyNodeCreated(KeyNode node) {}
            public void keyNodeChanged(KeyNode node) {}
            public void valueNodeCreated(ValueNode node, long[] key) {}
        };
        long pos = 10000;
        long first = t;
        for (int step = 0; step < 40; step++) {
            int what = r.nextInt(10);
            if (what < 6) {
                if (r.nextInt(5) != 0) {
                    t += 1 + r.nextInt(4);
                }
                rootPos += 16;
                KeyNode root = new KeyNode();
                root.setSpos(rootPos);
                root.setId(rootPos + 1);
                root.setCanonical(true);
                ds.newSuperRoot(t, root, 0, Dag.DO_NOTHING_POINTER_CREATED_LISTENER, ids);
                TopNode s = ds.getSuperRoot();
                w.print("n " + t + " " + rootPos + " = " + s.topNodeId + " " + topState(s) + "\n");
            } else if (what < 8) {
                pos += 64 * (1 + r.nextInt(4));
                TopNode s = ds.getSuperRoot();
                s.setSpos(pos);
                w.print("w " + pos + "\n");
            } else {
                long at = first - 2 + r.nextInt((int) (t - first + 4));
                KeyNode found = ds.findRoot(at, topOp());
                w.print("f " + at + " = " + (found == null ? -1 : found.getSpos()) + "\n");
            }
        }
    }

    private static OpData topOp() {
        GetData gd = new GetData();
        gd.pointerFollower = new PointerFollower() {
            public Node followPointer(Node predecessor, int index, OpData op) {
                Node n = predecessor.getPointerNode(index);
                if (n == null) throw new IllegalStateException("not in memory");
                return n;
            }
        };
        gd.pointerListener = Dag.DO_NOTHING_POINTER_LISTENER;
        gd.tempPointer = new Pointer();
        return gd;
    }

    private static String topState(TopNode node) {
        long[] longs = new long[StoredTopNode.getByteSize(node) / 8];
        StoredTopNode.toLongs(node, longs, 0);
        long h = 0xcbf29ce484222325L;
        for (byte b : Bytes.longsToBytesLE(longs)) {
            h ^= b & 0xff;
            h *= 0x100000001b3L;
        }
        return StoredTopNode.getByteSize(node) + " " + String.format("%016x", h);
    }

    // ---- Dag (012-08) ----

    private static void dag(PrintWriter w) {
        w.print("# dag SEED MAXNODE T0: Dag.createEmpty(T0, MAXNODE), its pointers memory pointers\n");
        w.print("# t TT BOUND TSPLITS SSPLITS HASH PAIRS: dirtyNodeBound(the last time, the pairs)\n");
        w.print("#   before the transaction at TT; the pairs put (the value: TT's two low bytes, then\n");
        w.print("#   7) or deleted in order, clearFast after each, clear at the end; PutData's time\n");
        w.print("#   and space split counts after it; HASH, FNV-1a 64 of the latest state's getMany:\n");
        w.print("#   each pair's key segments, Kvt.time and value length as longs, little-endian;\n");
        w.print("#   PAIRS: BKEYHEX:D, D 1 for a delete\n");
        for (int seed = 1; seed <= 12; seed++) {
            dagRun(w, seed);
        }
        w.close();
    }

    private static final PointerFollower MEMORY_FOLLOWER = new PointerFollower() {
        public Node followPointer(Node predecessor, int index, OpData op) {
            Node n = predecessor.getPointerNode(index);
            if (n == null) throw new IllegalStateException("not in memory");
            op.pointerListener.pointerFollowed(predecessor, index, n, Pointer.TYPE_MEMORY);
            return n;
        }
    };

    /** DbTesterGetMany.randomKey's alphabet: keys that share prefixes and segments. */
    private static String dagKey(Random r) {
        String[] parts = {"a", "b", "ab", "abc", "k", "/k/", "/long/", "xyz", "q", "1234567"};
        StringBuilder b = new StringBuilder();
        int count = 1 + r.nextInt(r.nextInt(4) == 0 ? 6 : 3);
        for (int i = 0; i < count; i++) {
            b.append(parts[r.nextInt(parts.length)]);
            if (r.nextBoolean()) {
                b.append(r.nextInt(100));
            }
        }
        return b.toString();
    }

    private static void dagRun(PrintWriter w, int seed) {
        Random r = new Random(200 + seed);
        int maxNode = new int[] {8, 14, 30, 62}[seed % 4];
        long t = 1 + r.nextInt(100);
        Dag dag = Dag.createEmpty(t, maxNode, MEMORY_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        PutData pd = dag.newPutData();
        pd.pointerFollower = MEMORY_FOLLOWER;
        GetData gd = dag.newGetData();
        gd.pointerFollower = MEMORY_FOLLOWER;
        w.print("dag " + seed + " " + maxNode + " " + t + "\n");
        for (int i = 0; i < 80; i++) {
            int n = 1 + r.nextInt(r.nextInt(5) == 0 ? 40 : 6);
            java.util.TreeMap<long[], Boolean> pairs =
                    new java.util.TreeMap<long[], Boolean>(new java.util.Comparator<long[]>() {
                        public int compare(long[] a, long[] b) {
                            return Keys.compareArrays(a, b);
                        }
                    });
            for (int j = 0; j < n; j++) {
                pairs.put(Keys.toSegments(dagKey(r)), r.nextInt(5) == 0);
            }
            long[][] keys = pairs.keySet().toArray(new long[0][]);
            boolean[] deletes = new boolean[keys.length];
            for (int k = 0; k < keys.length; k++) {
                deletes[k] = pairs.get(keys[k]);
            }
            long bound = dag.dirtyNodeBound(t, keys, deletes, gd);
            t += 1 + r.nextInt(20);
            pd.tt = t;
            StringBuilder b = new StringBuilder();
            for (int k = 0; k < keys.length; k++) {
                dag.putKv(keys[k], deletes[k] ? null : new byte[] {(byte) t, (byte) (t >> 8), 7}, pd);
                pd.clearFast();
                b.append(' ').append(hex(Keys.toBytes(keys[k]))).append(deletes[k] ? ":1" : ":0");
            }
            pd.clear();
            GetMany g = dag.newGetMany();
            g.gd.pointerFollower = MEMORY_FOLLOWER;
            g.actualLookupTime = t;
            dag.getMany(g);
            long h = 0xcbf29ce484222325L;
            for (Kvt kvt : g.result) {
                for (long x : kvt.key) {
                    h = fnv(h, x);
                }
                h = fnv(h, kvt.time);
                h = fnv(h, kvt.value.length);
            }
            w.print("t " + t + " " + bound + " " + pd.timeSplitCount + " " + pd.spaceSplitCount + " "
                    + String.format("%016x", h) + b + "\n");
        }
    }

    private static long fnv(long h, long x) {
        for (int i = 0; i < 8; i++) {
            h ^= (x >>> (8 * i)) & 0xff;
            h *= 0x100000001b3L;
        }
        return h;
    }

    // ---- text ----

    private static byte[] filled(int n, byte b) {
        byte[] a = new byte[n];
        java.util.Arrays.fill(a, b);
        return a;
    }

    // ---- KeyModSet (bergdb 012-09) ----

    /** xorshift64*, as the workloads' r: values (012-05, 6.1). */
    private static long xorshift(long[] x) {
        x[0] ^= x[0] >>> 12;
        x[0] ^= x[0] << 25;
        x[0] ^= x[0] >>> 27;
        return x[0] * 0x2545F4914F6CDD1DL;
    }

    /**
     * KeyModSet's answers to a sequence that both sides make: 200,000 adds of hashes below
     * 50,000 (so keys repeat) at times 1000 + 3 i, which turn the default set's four bins of
     * 32,000 over six times; after every 1,000 adds, getFirstTime() and 20 questions
     * modifiedAfter(time, hash), a time up to 200,000 back and a hash below 50,000.
     */
    private static void keymod(PrintWriter w) {
        w.print("# keymod SEED ADDS: the sequence, xorshift64* from SEED (as r: values)\n"
                + "# answers N FIRST BITS: after N adds, getFirstTime() and the 20 answers,\n"
                + "# 1 for modified\n");
        long seed = 0x0123456789abcdefL;
        int adds = 200000;
        w.print("keymod " + seed + " " + adds + "\n");
        long[] x = {seed};
        KeyModSet s = new KeyModSet();
        for (int i = 0; i < adds; i++) {
            long t = 1000 + 3L * i;
            s.add(t, (xorshift(x) >>> 1) % 50000);
            if ((i + 1) % 1000 == 0) {
                StringBuilder b = new StringBuilder();
                for (int q = 0; q < 20; q++) {
                    long qt = t - (xorshift(x) >>> 1) % 200000;
                    long qh = (xorshift(x) >>> 1) % 50000;
                    b.append(s.modifiedAfter(qt, qh) ? '1' : '0');
                }
                w.print("answers " + (i + 1) + " " + s.getFirstTime() + " " + b + "\n");
            }
        }
        w.close();
    }

    // ---- StringMap (bergdb 012-09) ----

    /**
     * StringMap's texts: maps made by puts in order, or by parse, and serialize()'s text, in
     * the order of its HashMap: reclaim's row (Reclaim.IterationInfo.serialize's puts), keys
     * that make the table grow to 32 and 64, keys of one bucket of 16 (the ninth makes
     * HashMap.treeifyBin double the small table), keys beyond ASCII, a parsed text.
     */
    private static void strmap(PrintWriter w) {
        w.print("# new: a new StringMap. put KEY VALUE: put(key, value). parse TEXT: parse(text).\n"
                + "# text TEXT: serialize(). get KEY VALUE: get(key), \"null\" for none.\n"
                + "# Each text, key and value as its UTF-8 bytes in hex, \"-\" for none.\n");
        String[][] row = {
            {"pStart", "5574880"}, {"pCut", "5041560"}, {"tStart", "10000289400000"},
            {"tEnd", "0"}, {"kvCount", "466"}, {"lastKey", "26177508076421160 7 -3"},
            {"done", "false"}, {"cut", "true"}, {"rewritten", "102488"}, {"pEnd", "-1"},
            {"pSafe", "-1"}};
        strmapPuts(w, row);
        String[][] row2 = {
            {"pStart", "0"}, {"pCut", "0"}, {"tStart", "" + Long.MIN_VALUE / 2},
            {"tEnd", "0"}, {"kvCount", "0"}, {"lastKey", "null"}, {"done", "true"},
            {"cut", "false"}, {"rewritten", "0"}, {"pEnd", "" + Long.MAX_VALUE},
            {"pSafe", "" + Long.MIN_VALUE}};
        strmapPuts(w, row2);
        String[][] many = new String[40][];
        for (int i = 0; i < many.length; i++) {
            many[i] = new String[] {"k" + i, "" + i};
        }
        strmapPuts(w, many);
        // Twelve keys of bucket 5 of a table of 16.
        List<String[]> same = new ArrayList<String[]>();
        for (int i = 0; same.size() < 12; i++) {
            String k = "c" + i;
            int h = k.hashCode();
            h ^= h >>> 16;
            if ((h & 15) == 5) {
                same.add(new String[] {k, "v" + i});
            }
        }
        strmapPuts(w, same.toArray(new String[0][]));
        String[][] text = {
            {"\u00fc", "1"}, {"\ud83d\ude00", "2"}, {"\u65e5\u672c", "3"}, {"a=b", "x"},
            {"pStart", "4"}, {"k", ""}};
        strmapPuts(w, text);
        String[] parses = {
            "k1=v1\nk2=v2\n",
            "  a = 1 \n=x\nnone\n\tb==2=\nc=\n\nd=last",
            "pSafe=-1\npEnd=7\npSafe=8\n"};
        for (String t : parses) {
            w.print("new\n");
            w.print("parse " + hex(t.getBytes(StandardCharsets.UTF_8)) + "\n");
            StringMap m = new StringMap(t);
            w.print("text " + hex(m.serialize().getBytes(StandardCharsets.UTF_8)) + "\n");
            for (String k : new String[] {"a ", "b", "c", "d", "k2", "pSafe", "x"}) {
                String v = m.get(k);
                w.print("get " + hex(k.getBytes(StandardCharsets.UTF_8)) + " "
                        + (v == null ? "null" : hex(v.getBytes(StandardCharsets.UTF_8))) + "\n");
            }
        }
        w.close();
    }

    private static void strmapPuts(PrintWriter w, String[][] pairs) {
        StringMap m = new StringMap();
        w.print("new\n");
        for (String[] p : pairs) {
            m.put(p[0], p[1]);
            w.print("put " + hex(p[0].getBytes(StandardCharsets.UTF_8)) + " "
                    + hex(p[1].getBytes(StandardCharsets.UTF_8)) + "\n");
        }
        w.print("text " + hex(m.serialize().getBytes(StandardCharsets.UTF_8)) + "\n");
    }

    // ---- Reclaim (012-11) ----

    /**
     * Runs of Db with reclaim on a MemoryStream (node size 8, startup distance 2000, retain
     * 1 s, 2000 transactions of one put 50 ms apart, the keys and values from the index i:
     * "/k/" + (i * 7919) % 200, 1 + (i * 31) % 30 bytes (byte) (i + j)), with the default
     * step reserve and with one of four nodes (Reclaim.Tester.testStepReserveSplitsSteps'):
     * the stream's length, the first available position and time, the iterations, and the
     * SHA-256 of the stream from the first available position.
     */
    private static void reclaim(PrintWriter w) throws IOException {
        w.print("# reclaim reserve=R n=N length=L firstAvailablePos=P firstAvailableTime=T "
                + "iterations=I sha256=H\n");
        for (long reserve : new long[] {Reclaim.DEFAULT_STEP_RESERVE, 4 * (80 + 48 * 8)}) {
            MemoryStream ms = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            Db db = Db.builder().testSetup(ms).clock(clock).maxNodeSize8().startupDistance(2000)
                    .reclaimStepReserve(reserve).start();
            db.setRetainDuration(Clock.UNITS_PER_SEC);
            final int n = 2000;
            for (int i = 0; i < n; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                byte[] v = new byte[1 + (i * 31) % 30];
                for (int j = 0; j < v.length; j++) {
                    v[j] = (byte) (i + j);
                }
                db.execute(db.trans().put("/k/" + (i * 7919) % 200, v).build());
            }
            long first = db.getFirstAvailablePos();
            long length = db.getStreamLength();
            long firstTime = db.getFirstAvailableLookupTime();
            long iterations = db.getReclaimIterationCount();
            db.close();
            byte[] bytes = new byte[(int) (length - first)];
            ms.read(first, bytes, 0, bytes.length);
            String sha;
            try {
                MessageDigest md = MessageDigest.getInstance("SHA-256");
                sha = hex(md.digest(bytes));
            } catch (NoSuchAlgorithmException e) {
                throw new IOException(e);
            }
            w.print("reclaim reserve=" + reserve + " n=" + n + " length=" + length
                    + " firstAvailablePos=" + first + " firstAvailableTime=" + firstTime
                    + " iterations=" + iterations + " sha256=" + sha + "\n");
        }
        w.close();
    }

    private static String hex(byte[] b) {
        return hex(b, 0, b.length);
    }

    private static String hex(byte[] b, int off, int len) {
        if (len == 0) {
            return "-";
        }
        StringBuilder s = new StringBuilder();
        for (int i = off; i < off + len; i++) {
            s.append(String.format("%02x", b[i] & 0xff));
        }
        return s.toString();
    }

    private static String hex16(long v) {
        return String.format("%016x", v);
    }

    private static String hex8(int v) {
        return String.format("%08x", v);
    }

    private static String hexLongs(long[] ls) {
        if (ls.length == 0) {
            return "-";
        }
        StringBuilder s = new StringBuilder();
        for (long l : ls) {
            s.append(s.length() == 0 ? "" : ",").append(hex16(l));
        }
        return s.toString();
    }
}
