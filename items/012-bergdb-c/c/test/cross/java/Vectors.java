package bergdb.core;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.stream.MemoryStream;

/**
 * Writes what Java's classes give for a fixed set of inputs, as the test vectors of the C
 * clone's unit tests (bergdb 012-04): bytes.txt (Bytes), checksum.txt (NodeChecksum),
 * klong.txt (Klong), keys.txt (Keys) and jsem.txt (Java's own arithmetic: casts, shifts,
 * division, comparisons, and the take's double expressions in TransSeq), and (012-06)
 * records.txt (a small stream that Db writes, its records as StoredTrans.parse parses them,
 * and records it refuses), into a directory. C's unit tests read them
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
        jsem(open(dir, "jsem.txt"));
        records(open(dir, "records.txt"));
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

        // The take's share (TransSeq.take): a double expression of longs and an int,
        // evaluated left to right, without a fused multiply-add.
        w.print("# share DIRTY OWN TOTAL DIST SD BITS: the bits of\n"
                + "# (double) DIRTY * OWN / TOTAL * DIST / SD, as TransSeq.take computes its share\n");
        for (int i = 0; i < 12; i++) {
            long dirty = 1 + r.nextInt(i < 6 ? 50 : 1_000_000);
            long own = 48 + r.nextInt(i < 6 ? 2000 : 100_000_000);
            long total = own + r.nextInt(i < 6 ? 100_000 : Integer.MAX_VALUE);
            long dist = r.nextLong() >>> (i < 6 ? 40 : 20);
            int sd = 1 + r.nextInt(i < 6 ? 1_000_000 : Integer.MAX_VALUE - 1);
            double share = (double) dirty * own / total * dist / sd;
            w.print("share " + dirty + " " + own + " " + total + " " + dist + " " + sd + " "
                    + hex16(Double.doubleToRawLongBits(share)) + "\n");
        }

        w.print("# dither POS BITS: the bits of TransSeq.dither(POS), SplitMix64's finalizer\n");
        List<Long> ps = new ArrayList<>(List.of(0L, 1L, 128L, 200_000L, 1L << 40,
                Long.MAX_VALUE));
        for (int i = 0; i < 6; i++) {
            ps.add(r.nextLong() >>> 1);
        }
        for (long pos : ps) {
            w.print("dither " + pos + " " + hex16(Double.doubleToRawLongBits(TransSeq.dither(pos)))
                    + "\n");
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

    // ---- text ----

    private static byte[] filled(int n, byte b) {
        byte[] a = new byte[n];
        java.util.Arrays.fill(a, b);
        return a;
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
