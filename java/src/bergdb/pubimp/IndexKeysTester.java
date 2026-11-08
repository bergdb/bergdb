package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Random;

import bergdb.core.InternalDataException;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * Tests of IndexKeys: the keys of the user indexes and the encodings of their levels (bergdb
 * 020-10, sections 4.1 and 4.4), as 020-10, section 10.2, asks of step I0:
 * <ul>
 * <li>every encoding's order against Java's comparison (Long.compare; Double.compare with
 *     -0.0 as 0.0; strings by code points; bytes unsigned), for the edges and for
 *     UNIT_PAIRS random pairs per type with a fixed seed;</li>
 * <li>E's prefix rule, succ, the order of entries as tuples, and the ranges of a scan by
 *     020-10, section 4.4's formulae;</li>
 * <li>the parse of an entry and its refusals; the keys of section 4.1; the names of 3.1.</li>
 * </ul>
 * The night group runs NIGHT_SEEDS seeds of NIGHT_PAIRS pairs per type, new each day; main()
 * repeats one seed.
 *
 * @author Frans Lundberg
 */
public class IndexKeysTester {
    private IndexKeysTester() {}

    /** Random pairs per type in the unit group (020-10, section 10.2). */
    static final int UNIT_PAIRS = 100000;

    /** The night's seeds and pairs per type and seed. */
    static final int NIGHT_SEEDS = 20;
    static final int NIGHT_PAIRS = 1000000;

    // ======== The edges ========

    static final long[] LONG_EDGES = {Long.MIN_VALUE, Long.MIN_VALUE + 1, -(1L << 32) - 1,
            Integer.MIN_VALUE - 1L, Integer.MIN_VALUE, -32769, -32768, -129, -128, -2, -1, 0, 1,
            2, 127, 128, 255, 256, 32767, 32768, Integer.MAX_VALUE, Integer.MAX_VALUE + 1L,
            1L << 32, Long.MAX_VALUE - 1, Long.MAX_VALUE};

    static final double[] DOUBLE_EDGES = {Double.NEGATIVE_INFINITY, -Double.MAX_VALUE, -1e300,
            -2.0, -1.0, -Double.MIN_NORMAL, -Math.nextDown(Double.MIN_NORMAL),
            -Double.MIN_VALUE * 2, -Double.MIN_VALUE, -0.0, 0.0, Double.MIN_VALUE,
            Double.MIN_VALUE * 2, Math.nextDown(Double.MIN_NORMAL), Double.MIN_NORMAL, 0.5, 1.0,
            Math.nextUp(1.0), 2.0, 1e300, Double.MAX_VALUE, Double.POSITIVE_INFINITY};

    static final String[] STRING_EDGES = {"", "\u0000", "\u0000\u0000", "\u0000\u0001",
            "\u0001", "\u0001\u0000", "\u0001\u0001", "\u0002", "a", "a\u0000", "a\u0000\u0000",
            "a\u0001", "a\u0002", "aa", "ab", "b", "\u007f", "\u0080", "\u00ff", "\u07ff",
            "\u0800", "\ud7ff", "\ue000", "\uffef", "\ufffd", "\uffff", "\ud800\udc00",
            "\ud800\udc00\u0000", "\ud83d\ude00", "\udbff\udfff", "\udbff\udfff\udbff\udfff"};

    static final byte[][] BYTES_EDGES = {{}, {0}, {0, 0}, {0, 1}, {0, (byte) 0xff}, {1}, {1, 0},
            {1, 1}, {1, 2}, {2}, {2, 0}, {3}, {0x2f}, {0x7f}, {(byte) 0x80}, {(byte) 0xfe},
            {(byte) 0xff}, {(byte) 0xff, 0}, {(byte) 0xff, (byte) 0xff}};

    /** The edges of long (020-10, section 4.4): every pair in Java's order; 4.4's bytes. */
    @Nano
    public static void testLongEdges() {
        for (long a : LONG_EDGES) {
            byte[] ea = IndexKeys.encodeLong(a);
            Assert.assertEquals(8, ea.length);
            Assert.assertArrayEquals(refLong(a), ea);
            Assert.assertEquals(a, IndexKeys.decodeLong(ea, 0));
            for (long b : LONG_EDGES) {
                assertOrder("long " + a + ", " + b, Long.compare(a, b), ea,
                        IndexKeys.encodeLong(b));
            }
        }
        Assert.assertArrayEquals(new byte[8], IndexKeys.encodeLong(Long.MIN_VALUE));
        Assert.assertArrayEquals(new byte[] {(byte) 0x80, 0, 0, 0, 0, 0, 0, 0},
                IndexKeys.encodeLong(0));
    }

    /**
     * The edges of double: every pair in Double.compare's order with -0.0 as 0.0; -0.0 and 0.0
     * one key; -infinity the least, +infinity the greatest; NaN refused; 4.4's bytes.
     */
    @Nano
    public static void testDoubleEdges() {
        for (double a : DOUBLE_EDGES) {
            byte[] ea = IndexKeys.encodeDouble(a);
            Assert.assertEquals(8, ea.length);
            Assert.assertArrayEquals(refDouble(a), ea);
            Assert.assertEquals(Double.doubleToLongBits(a == 0 ? 0.0 : a),
                    Double.doubleToLongBits(IndexKeys.decodeDouble(ea, 0)));
            for (double b : DOUBLE_EDGES) {
                assertOrder("double " + a + ", " + b, compareDoubles(a, b), ea,
                        IndexKeys.encodeDouble(b));
            }
        }
        Assert.assertArrayEquals(IndexKeys.encodeDouble(0.0), IndexKeys.encodeDouble(-0.0));
        byte[] least = IndexKeys.encodeDouble(Double.NEGATIVE_INFINITY);
        byte[] greatest = IndexKeys.encodeDouble(Double.POSITIVE_INFINITY);
        for (double a : DOUBLE_EDGES) {
            byte[] ea = IndexKeys.encodeDouble(a);
            Assert.assertTrue(a + " not below -inf", Arrays.compareUnsigned(least, ea) <= 0);
            Assert.assertTrue(a + " not above +inf", Arrays.compareUnsigned(ea, greatest) <= 0);
        }
        for (long nan : new long[] {0x7ff8000000000000L, 0x7ff0000000000001L,
                0xfff8000000000000L, 0xffffffffffffffffL}) {
            assertRefusedArg("NaN " + Long.toHexString(nan),
                    () -> IndexKeys.encodeDouble(Double.longBitsToDouble(nan)));
        }

        // The stored bits of a double as a sort long (the function's path, no double used).
        for (double a : DOUBLE_EDGES) {
            Assert.assertArrayEquals(IndexKeys.encodeDouble(a),
                    IndexKeys.encodeLong(IndexKeys.doubleSortLong(Double.doubleToLongBits(a))));
        }

        // An 8-byte level that is the encoding of no double (a NaN's) is refused by decode.
        for (long s : new long[] {Long.MIN_VALUE, -0x7ff0000000000001L, 0x7ff0000000000001L,
                Long.MAX_VALUE}) {
            byte[] e = IndexKeys.encodeLong(s);
            assertRefusedArg("decode " + Long.toHexString(s), () -> IndexKeys.decodeDouble(e, 0));
        }
    }

    /**
     * The edges of string: every pair in code-point order (not Java's UTF-16 order: U+E000 is
     * below U+10000); "a" before "a\u0000"; E's bytes; a lone surrogate refused.
     */
    @Nano
    public static void testStringEdges() {
        for (String a : STRING_EDGES) {
            byte[] ea = IndexKeys.encodeString(a);
            Assert.assertEquals(a, decodeString(ea));
            for (String b : STRING_EDGES) {
                assertOrder("string " + show(a) + ", " + show(b), compareCodePoints(a, b), ea,
                        IndexKeys.encodeString(b));
            }
        }
        Assert.assertTrue("UTF-16's order differs", "\ue000".compareTo("\ud800\udc00") > 0);
        assertOrder("U+E000, U+10000", -1, IndexKeys.encodeString("\ue000"),
                IndexKeys.encodeString("\ud800\udc00"));
        assertOrder("a, a\\0", -1, IndexKeys.encodeString("a"),
                IndexKeys.encodeString("a\u0000"));
        Assert.assertArrayEquals(new byte[] {0}, IndexKeys.encodeString(""));
        Assert.assertArrayEquals(new byte[] {'a', 1, 1, 1, 2, 0},
                IndexKeys.encodeString("a\u0000\u0001"));
        for (String bad : new String[] {"\ud800", "a\udc00", "\udbff", "\udc00\ud800"}) {
            assertRefusedArg("lone surrogate " + show(bad), () -> IndexKeys.encodeString(bad));
            assertRefusedArg("prefix, lone surrogate " + show(bad),
                    () -> IndexKeys.encodeStringPrefix(bad));
        }
    }

    /** The edges of bytes: every pair unsigned; E's exact bytes for 00, 01, ff and empty. */
    @Nano
    public static void testBytesEdges() {
        for (byte[] a : BYTES_EDGES) {
            byte[] ea = IndexKeys.encodeBytes(a);
            Assert.assertArrayEquals(a, IndexKeys.decodeEscaped(ea, 0, ea.length - 1));
            Assert.assertEquals(ea.length - 1, IndexKeys.escapedLength(a, 0, a.length));
            for (byte[] b : BYTES_EDGES) {
                assertOrder("bytes " + hex(a) + ", " + hex(b), Arrays.compareUnsigned(a, b), ea,
                        IndexKeys.encodeBytes(b));
            }
        }
        Assert.assertArrayEquals(new byte[] {0}, IndexKeys.encodeBytes(new byte[0]));
        Assert.assertArrayEquals(new byte[] {1, 1, 0}, IndexKeys.encodeBytes(new byte[] {0}));
        Assert.assertArrayEquals(new byte[] {1, 2, 0}, IndexKeys.encodeBytes(new byte[] {1}));
        Assert.assertArrayEquals(new byte[] {2, 0}, IndexKeys.encodeBytes(new byte[] {2}));
        Assert.assertArrayEquals(new byte[] {(byte) 0xff, 0},
                IndexKeys.encodeBytes(new byte[] {(byte) 0xff}));
        Assert.assertArrayEquals(new byte[] {1, 1, 1, 2, (byte) 0xff},
                IndexKeys.encodeBytesPrefix(new byte[] {0, 1, (byte) 0xff}));
        Assert.assertArrayEquals(new byte[0], IndexKeys.encodeBytesPrefix(new byte[0]));

        // A string's encoding is its UTF-8's (one encoding for both types).
        for (String s : STRING_EDGES) {
            Assert.assertArrayEquals(IndexKeys.encodeBytes(s.getBytes(StandardCharsets.UTF_8)),
                    IndexKeys.encodeString(s));
        }
    }

    /** UNIT_PAIRS random pairs of each type, seed 1, in Java's order (020-10, section 10.2). */
    @Nano
    public static void testRandomPairs() {
        Stats st = new Stats();
        runPairs(new Random(1), UNIT_PAIRS, st);
        Assert.assertEquals(4L * UNIT_PAIRS, st.pairs);
        Assert.assertTrue("equal pairs: " + st, st.equal > 1000);
        Assert.assertTrue("prefix pairs: " + st, st.prefixes > 1000);
    }

    // ======== E's prefix rule and succ ========

    /**
     * E's prefix rule (020-10, section 4.4): E'(p) is a prefix of E(v) exactly when v starts
     * with p (by bytes; for strings by code points), and the keys in [x, succ(x)) for x = E'(p)
     * are exactly those that start with x. Edges and random values.
     */
    @Nano
    public static void testPrefixRule() {
        for (byte[] p : BYTES_EDGES) {
            for (byte[] v : BYTES_EDGES) {
                checkBytesPrefix(p, v);
            }
        }
        for (String p : STRING_EDGES) {
            for (String v : STRING_EDGES) {
                checkStringPrefix(p, v);
            }
        }
        Random r = new Random(3);
        for (int k = 0; k < 20000; k++) {
            byte[] v = randomBytes(r);
            byte[] p = r.nextBoolean() ? Arrays.copyOf(v, r.nextInt(v.length + 1)) : randomBytes(r);
            checkBytesPrefix(p, v);
            String s = randomString(r);
            String q = r.nextBoolean() ? cutAtCodePoint(s, r) : randomString(r);
            checkStringPrefix(q, s);
        }
    }

    /** succ(x): the least string above every string that starts with x; null if none. */
    @Nano
    public static void testSucc() {
        assertNull(IndexKeys.succ(new byte[0]));
        assertNull(IndexKeys.succ(new byte[] {(byte) 0xff}));
        assertNull(IndexKeys.succ(new byte[] {(byte) 0xff, (byte) 0xff}));
        Assert.assertArrayEquals(new byte[] {1}, IndexKeys.succ(new byte[] {0}));
        Assert.assertArrayEquals(new byte[] {2}, IndexKeys.succ(new byte[] {1, (byte) 0xff}));
        Assert.assertArrayEquals(new byte[] {0x0b},
                IndexKeys.succ(new byte[] {0x0a, (byte) 0xff, (byte) 0xff}));
        Assert.assertArrayEquals(new byte[] {5, (byte) 0x80},
                IndexKeys.succ(new byte[] {5, 0x7f}));

        Random r = new Random(4);
        byte[] x0 = new byte[] {3};
        for (int k = 0; k < 20000; k++) {
            byte[] x = randomBytes(r);
            byte[] y = r.nextBoolean() ? concat(x, randomBytes(r)) : randomBytes(r);
            byte[] s = IndexKeys.succ(x);
            boolean starts = startsWith(y, x);
            boolean inRange = Arrays.compareUnsigned(x, y) <= 0
                    && (s == null || Arrays.compareUnsigned(y, s) < 0);
            Assert.assertEquals("y " + hex(y) + " in [x, succ(x)), x " + hex(x), starts, inRange);
            if (s != null) {
                Assert.assertFalse("succ(x) starts with x", startsWith(s, x));
                Assert.assertTrue("succ(x) above x", Arrays.compareUnsigned(x, s) < 0);
            }
            Assert.assertArrayEquals(x0, new byte[] {3});    // x not changed
        }
    }

    // ======== Entries as tuples, and the scan's ranges ========

    /**
     * The order of entries (020-10, section 4.4): prefix, levels, K sort as the tuples of
     * the levels' values in Java's order, then K, for random entries of 1 to 3 levels of
     * every type; the Core's order of the keys (Keys.compareKeys) is the same.
     */
    @Nano
    public static void testTupleOrder() {
        Random r = new Random(5);
        for (int round = 0; round < 40; round++) {
            char[] types = randomTypes(r, 1 + r.nextInt(3));
            List<Ref> refs = randomEntries(r, types, 60, 6);
            checkTupleOrder(types, refs);
        }
    }

    /**
     * The ranges of a scan, by 020-10, section 4.4's formulae: eq on levels 1 to k, then a
     * from and a to, each inclusive or not, or a prefix, on level k + 1: the keys in
     * [start, end) are exactly the reference's, which compares Java values.
     */
    @Nano
    public static void testRanges() {
        Random r = new Random(6);
        for (int round = 0; round < 60; round++) {
            char[] types = randomTypes(r, 1 + r.nextInt(3));
            List<Ref> refs = randomEntries(r, types, 80, 5);
            for (int q = 0; q < 30; q++) {
                checkRange(r, types, refs);
            }
        }
    }

    // ======== The parse of an entry ========

    /** An entry is parsed into its levels and K, the values decoded (020-10, section 4.4). */
    @Nano
    public static void testParseEntry() {
        byte[] prefix = IndexKeys.generationPrefix("byFrom", 17941752000000000L);
        char[] types = {IndexKeys.LONG, IndexKeys.DOUBLE, IndexKeys.STRING, IndexKeys.BYTES};
        byte[] levels = concat(IndexKeys.encodeLong(-5), IndexKeys.encodeDouble(-0.0),
                IndexKeys.encodeString("a\u0000b\u0001"), IndexKeys.encodeBytes(new byte[] {0, 1,
                (byte) 0xff}));
        byte[] k = IndexKeys.fileKey("/dpayments/-p\u00e51");
        byte[] key = IndexKeys.entryKey(prefix, levels, k);
        Assert.assertArrayEquals(concat(prefix, levels, k), key);

        IndexKeys.Entry e = IndexKeys.parseEntry(key, prefix, types);
        Assert.assertEquals(4, e.levelCount());
        Assert.assertArrayEquals(levels, e.levels());
        Assert.assertArrayEquals(k, e.k());
        Assert.assertEquals("-p\u00e51", e.fileName());
        Assert.assertEquals(-5L, e.value(0));
        Assert.assertEquals(0.0, e.value(1));
        Assert.assertEquals("a\u0000b\u0001", e.value(2));
        Assert.assertArrayEquals(new byte[] {0, 1, (byte) 0xff}, (byte[]) e.value(3));

        // K of an ikey: its file part, '-' and the name, as a bkey (first byte 0x2f).
        Assert.assertArrayEquals(Keys.toBytes("-p\u00e51"), k);
        Assert.assertEquals(0x2f, k[0]);
        Assert.assertArrayEquals(Keys.toBytes("-x"), IndexKeys.fileKey("/-x"));
        assertRefusedArg("a dir's ikey", () -> IndexKeys.fileKey("/da/db/"));
        assertRefusedArg("no file part", () -> IndexKeys.fileKey("/da/dx"));
        assertRefusedArg("not an ikey", () -> IndexKeys.fileKey("x"));
    }

    /**
     * A key that does not parse is an InternalDataException naming it: another prefix, a cut
     * long or double, an E not ended or with 01 not followed by 01 or 02, K empty, K not
     * starting with 0x2f, a byte below 2 in K.
     */
    @Nano
    public static void testParseEntryRefused() {
        byte[] prefix = IndexKeys.generationPrefix("i", 7);
        byte[] k = IndexKeys.fileKey("/da/-k");
        char[] ls = {IndexKeys.LONG, IndexKeys.STRING};
        byte[] good = concat(prefix, IndexKeys.encodeLong(1), IndexKeys.encodeString("x"), k);
        IndexKeys.parseEntry(good, prefix, ls);

        assertRefusedEntry("another generation", good, IndexKeys.generationPrefix("i", 8), ls);
        assertRefusedEntry("another name", good, IndexKeys.generationPrefix("j", 7), ls);
        assertRefusedEntry("the prefix only", prefix, prefix, ls);
        assertRefusedEntry("a long cut", concat(prefix, new byte[] {1, 2, 3}), prefix, ls);
        assertRefusedEntry("E not ended", concat(prefix, IndexKeys.encodeLong(1),
                new byte[] {'x', 'y'}), prefix, ls);
        assertRefusedEntry("01 03 in E", concat(prefix, IndexKeys.encodeLong(1),
                new byte[] {'x', 1, 3, 0}, k), prefix, ls);
        assertRefusedEntry("01 00 in E", concat(prefix, IndexKeys.encodeLong(1),
                new byte[] {'x', 1, 0}, k), prefix, ls);
        assertRefusedEntry("01 at the end", concat(prefix, IndexKeys.encodeLong(1),
                new byte[] {'x', 1}), prefix, ls);
        assertRefusedEntry("no K", concat(prefix, IndexKeys.encodeLong(1),
                IndexKeys.encodeString("x")), prefix, ls);
        assertRefusedEntry("K not '-'", concat(prefix, IndexKeys.encodeLong(1),
                IndexKeys.encodeString("x"), Keys.toBytes("dk")), prefix, ls);
        assertRefusedEntry("a 01 in K", concat(prefix, IndexKeys.encodeLong(1),
                IndexKeys.encodeString("x"), Keys.toBytes("-k/x")), prefix, ls);
        assertRefusedEntry("a 00 in K", concat(prefix, IndexKeys.encodeLong(1),
                IndexKeys.encodeString("x"), new byte[] {0x2f, 0x40, 0}), prefix, ls);

        // A value that does not decode: a double that is a NaN's encoding, a string level of
        // ill-formed UTF-8 (020-07, R11).
        char[] ds = {IndexKeys.DOUBLE};
        IndexKeys.Entry nan = IndexKeys.parseEntry(concat(prefix,
                IndexKeys.encodeLong(0x7ff8000000000000L), k), prefix, ds);
        assertRefusedInternal("a NaN's encoding", () -> nan.value(0));
        char[] ss = {IndexKeys.STRING};
        IndexKeys.Entry bad = IndexKeys.parseEntry(concat(prefix,
                IndexKeys.encodeBytes(new byte[] {(byte) 0xc0, (byte) 0x80}), k), prefix, ss);
        assertRefusedInternal("ill-formed UTF-8", () -> bad.value(0));
    }

    // ======== The keys of 020-10, section 4.1, and the names of 3.1 ========

    /** The keys of 020-10, section 4.1, made by key-encoding.md's rule from their ikeys. */
    @Nano
    public static void testKeys() {
        Assert.assertArrayEquals(Keys.toBytes("/#i/didef/-byFrom"),
                IndexKeys.definitionKey("byFrom"));
        Assert.assertArrayEquals(Keys.toBytes("/#i/didef/"), IndexKeys.definitionsPrefix());
        Assert.assertEquals("byFrom", IndexKeys.nameOfDefinitionKey(
                IndexKeys.definitionKey("byFrom")));
        Assert.assertEquals("n\u00e4me\u0000x",
                IndexKeys.nameOfDefinitionKey(IndexKeys.definitionKey("n\u00e4me\u0000x")));
        long g = 0x0123456789abcdefL;
        Assert.assertArrayEquals(concat(Keys.toBytes("/#i/dient/dbyFrom/"),
                new byte[] {1, 0x23, 0x45, 0x67, (byte) 0x89, (byte) 0xab, (byte) 0xcd,
                (byte) 0xef}), IndexKeys.generationPrefix("byFrom", g));
        Assert.assertArrayEquals(Keys.toBytes("/#i/dient/"), IndexKeys.entriesPrefix());
        Assert.assertArrayEquals(Keys.toBytes("/#i/didel/dbyFrom/-0123456789abcdef"),
                IndexKeys.markerKey("byFrom", g));
        Assert.assertArrayEquals(Keys.toBytes("/#i/didel/"), IndexKeys.markersPrefix());
        Assert.assertArrayEquals(Keys.toBytes("/#i/dii/"), IndexKeys.format1Prefix());
        IndexKeys.Marker m = IndexKeys.parseMarker(IndexKeys.markerKey("byFrom", g));
        Assert.assertEquals("byFrom", m.name);
        Assert.assertEquals(g, m.gen);
        IndexKeys.Marker m1 = IndexKeys.parseMarker(IndexKeys.markerKey("\u00e5", 1));
        Assert.assertEquals("\u00e5", m1.name);
        Assert.assertEquals(1, m1.gen);
        Assert.assertEquals(Long.MAX_VALUE, IndexKeys.parseMarker(
                IndexKeys.markerKey("x", Long.MAX_VALUE)).gen);

        // No generation's prefix starts with another's: the names end with '/' (01), which no
        // name has, and G has 8 bytes.
        String[] names = {"a", "ab", "a\u0000", "b", "\u00e5", "x.y"};
        long[] gens = {1, 2, 255, 256, Long.MAX_VALUE};
        for (String a : names) {
            for (long ga : gens) {
                for (String b : names) {
                    for (long gb : gens) {
                        if (!a.equals(b) || ga != gb) {
                            Assert.assertFalse(a + " " + ga + ", " + b + " " + gb, startsWith(
                                    IndexKeys.generationPrefix(a, ga),
                                    IndexKeys.generationPrefix(b, gb)));
                        }
                    }
                }
            }
        }

        assertRefusedArg("a gen of 0", () -> IndexKeys.generationPrefix("a", 0));
        assertRefusedArg("a gen below 0", () -> IndexKeys.markerKey("a", -1));
        assertRefusedArg("a bad name", () -> IndexKeys.definitionKey("a/b"));
        assertRefusedArg("a bad name", () -> IndexKeys.generationPrefix("a b", 1));
    }

    /** Keys under the prefixes of 4.1 that do not parse are InternalDataExceptions. */
    @Nano
    public static void testKeysRefused() {
        assertRefusedInternal("a definition key: no name",
                () -> IndexKeys.nameOfDefinitionKey(Keys.toBytes("/#i/didef/-")));
        assertRefusedInternal("a definition key: a dir",
                () -> IndexKeys.nameOfDefinitionKey(Keys.toBytes("/#i/didef/dx/-y")));
        assertRefusedInternal("a definition key: a space",
                () -> IndexKeys.nameOfDefinitionKey(Keys.toBytes("/#i/didef/-a b")));
        assertRefusedInternal("a definition key: another prefix",
                () -> IndexKeys.nameOfDefinitionKey(Keys.toBytes("/#i/dii/-a")));
        assertRefusedInternal("a definition key: a 00 byte",
                () -> IndexKeys.nameOfDefinitionKey(concat(Keys.toBytes("/#i/didef/-a"),
                new byte[] {0})));
        assertRefusedInternal("a definition key: ill-formed UTF-8",
                () -> IndexKeys.nameOfDefinitionKey(concat(Keys.toBytes("/#i/didef/-a"),
                new byte[] {(byte) 0xc2})));
        String[] bad = {"/#i/didel/da/-012345678", "/#i/didel/da/-0123456789abcdeF",
                "/#i/didel/da/-0123456789abcdefa", "/#i/didel/da/-0000000000000000",
                "/#i/didel/da/-8000000000000000", "/#i/didel/da/x0000000000000001",
                "/#i/didel/d/-0000000000000001", "/#i/didel/da b/-0000000000000001",
                "/#i/didel/-a", "/#i/didel/da", "/#i/didel/da/-000000000000000g",
                "/#i/didef/da/-0000000000000001", "/#i/didel/da/db/-0000000000000001"};
        for (String ikey : bad) {
            assertRefusedInternal("a marker " + ikey,
                    () -> IndexKeys.parseMarker(Keys.toBytes(ikey)));
        }
    }

    /**
     * An index's name (020-10, section 3.1): 1 to 255 UTF-8 bytes, without '/', whitespace
     * (Character.isWhitespace) or a lone surrogate.
     */
    @Nano
    public static void testNames() {
        String[] good = {"a", "byFrom", "x.y", "a,b", "#i", "-", "d", "\u00a0", "\u0000",
                "\ud83d\ude00", repeat("a", 255), repeat("\u00e5", 127) + "a",
                repeat("\u20ac", 85), repeat("\ud83d\ude00", 63) + "abc", "primary"};
        for (String name : good) {
            assertNull(show(name), IndexKeys.nameFault(name));
            IndexKeys.checkName(name);
        }
        String[] bad = {"", "/", "a/b", "a/", " ", "a b", "\t", "a\n", "\u2003", "\u3000",
                "\u001c", "\ud800", "a\udc00", repeat("a", 256), repeat("\u00e5", 128),
                repeat("\u20ac", 86), repeat("\ud83d\ude00", 64)};
        for (String name : bad) {
            Assert.assertTrue(show(name), IndexKeys.nameFault(name) != null);
            assertRefusedArg("name " + show(name), () -> IndexKeys.checkName(name));
        }
        Assert.assertTrue("null", IndexKeys.nameFault(null) != null);
        assertRefusedArg("null", () -> IndexKeys.checkName(null));
    }

    /** The type names of 020-10, section 3.1, and their chars. */
    @Nano
    public static void testTypes() {
        Assert.assertEquals(IndexKeys.LONG, IndexKeys.type("long"));
        Assert.assertEquals(IndexKeys.DOUBLE, IndexKeys.type("double"));
        Assert.assertEquals(IndexKeys.STRING, IndexKeys.type("string"));
        Assert.assertEquals(IndexKeys.BYTES, IndexKeys.type("bytes"));
        for (char t : IndexKeys.TYPES) {
            Assert.assertEquals(t, IndexKeys.type(IndexKeys.typeName(t)));
        }
        for (String bad : new String[] {"int", "Long", "string/unicode", "string/sv", "",
                "byte[]", "bytes ", "float"}) {
            assertRefusedArg("type " + bad, () -> IndexKeys.type(bad));
        }
        assertRefusedArg("type null", () -> IndexKeys.type(null));
    }

    /** The Core's order of keys (Keys.compareKeys on segments) is the unsigned order. */
    @Nano
    public static void testCoreOrder() {
        Random r = new Random(7);
        byte[] prefix = IndexKeys.generationPrefix("c", 3);
        for (int k = 0; k < 5000; k++) {
            byte[] a = concat(prefix, randomBytes(r));
            byte[] b = r.nextBoolean() ? concat(a, randomBytes(r)) : concat(prefix, randomBytes(r));
            if (r.nextBoolean()) {
                byte[] t = a;
                a = b;
                b = t;
            }
            Assert.assertEquals(hex(a) + ", " + hex(b), Integer.signum(Arrays.compareUnsigned(a,
                    b)), Integer.signum(Keys.compareKeys(Keys.toSegments(a),
                    Keys.toSegments(b))));
        }
    }

    // ======== The night ========

    /**
     * The night's run: NIGHT_SEEDS seeds, new each day (the day's number times 1000), each
     * with NIGHT_PAIRS random pairs per type; the seeds are printed, so that a failure is
     * repeated with main(seed).
     */
    @Nano("night")
    public static void testPairsNight(TestEnvironment c) {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        c.out().println("IndexKeysTester: seeds " + base + " to " + (base + NIGHT_SEEDS - 1)
                + ", " + NIGHT_PAIRS + " pairs per type each");
        Stats st = new Stats();
        for (long seed = base; seed < base + NIGHT_SEEDS; seed++) {
            runSeed(seed, NIGHT_PAIRS, st);
        }
        c.out().println("IndexKeysTester: " + st);
    }

    /**
     * Usage: IndexKeysTester [SEED [PAIRS]]: PAIRS random pairs per type from SEED (default:
     * the time; PAIRS as one seed of the night's run), with the tuples and ranges; prints the
     * counts.
     */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int pairs = args.length > 1 ? Integer.parseInt(args[1]) : NIGHT_PAIRS;
        long t0 = System.nanoTime();
        Stats st = new Stats();
        runSeed(seed, pairs, st);
        System.out.println("IndexKeysTester: seed " + seed + ": " + st + "; "
                + (System.nanoTime() - t0) / 1000000 + " ms");
    }

    static void runSeed(long seed, int pairs, Stats st) {
        Random r = new Random(seed);
        runPairs(r, pairs, st);
        for (int round = 0; round < pairs / 1000; round++) {
            char[] types = randomTypes(r, 1 + r.nextInt(4));
            List<Ref> refs = randomEntries(r, types, 50, 4);
            checkTupleOrder(types, refs);
            for (int q = 0; q < 10; q++) {
                checkRange(r, types, refs);
            }
        }
    }

    // ======== The random pairs ========

    static final class Stats {
        long pairs, equal, prefixes;

        public String toString() {
            return pairs + " pairs, " + equal + " equal, " + prefixes + " with a prefix";
        }
    }

    /** 'n' random pairs of each type; the second of a pair is often near the first. */
    static void runPairs(Random r, int n, Stats st) {
        for (int k = 0; k < n; k++) {
            long a = randomLong(r);
            long b = r.nextInt(4) == 0 ? a + r.nextInt(5) - 2 : randomLong(r);
            pair("long " + a + ", " + b, Long.compare(a, b), IndexKeys.encodeLong(a),
                    IndexKeys.encodeLong(b), st);
        }
        for (int k = 0; k < n; k++) {
            double a = randomDouble(r);
            double b = r.nextInt(4) == 0 ? near(a, r) : randomDouble(r);
            pair("double " + a + ", " + b, compareDoubles(a, b), IndexKeys.encodeDouble(a),
                    IndexKeys.encodeDouble(b), st);
        }
        for (int k = 0; k < n; k++) {
            String a = randomString(r);
            String b = r.nextInt(2) == 0 ? near(a, r) : randomString(r);
            byte[] ea = IndexKeys.encodeString(a);
            byte[] eb = IndexKeys.encodeString(b);
            pair("string " + show(a) + ", " + show(b), compareCodePoints(a, b), ea, eb, st);
            if (k % 8 == 0) {
                Assert.assertEquals(a, decodeString(ea));
            }
            if (b.startsWith(a) || a.startsWith(b)) {
                st.prefixes++;
            }
        }
        for (int k = 0; k < n; k++) {
            byte[] a = randomBytes(r);
            byte[] b = r.nextInt(2) == 0 ? near(a, r) : randomBytes(r);
            byte[] ea = IndexKeys.encodeBytes(a);
            byte[] eb = IndexKeys.encodeBytes(b);
            pair("bytes " + hex(a) + ", " + hex(b), Arrays.compareUnsigned(a, b), ea, eb, st);
            if (k % 8 == 0) {
                Assert.assertArrayEquals(a, IndexKeys.decodeEscaped(ea, 0, ea.length - 1));
            }
            if (startsWith(a, b) || startsWith(b, a)) {
                st.prefixes++;
            }
        }
    }

    private static void pair(String what, int javaOrder, byte[] ea, byte[] eb, Stats st) {
        int c = Integer.signum(Arrays.compareUnsigned(ea, eb));
        if (c != Integer.signum(javaOrder)) {
            throw new AssertionError(what + ": the encodings' order " + c + ", Java's "
                    + Integer.signum(javaOrder) + ": " + hex(ea) + ", " + hex(eb));
        }
        st.pairs++;
        if (c == 0) {
            st.equal++;
        }
    }

    static long randomLong(Random r) {
        switch (r.nextInt(6)) {
        case 0:
            return r.nextLong();
        case 1:
            return r.nextInt(600) - 300;
        case 2:
            return Long.MIN_VALUE + r.nextInt(3);
        case 3:
            return Long.MAX_VALUE - r.nextInt(3);
        case 4:
            return (r.nextBoolean() ? 1L : -1L) * (1L << r.nextInt(63)) + r.nextInt(3) - 1;
        default:
            return LONG_EDGES[r.nextInt(LONG_EDGES.length)];
        }
    }

    /** A random double, never NaN. */
    static double randomDouble(Random r) {
        switch (r.nextInt(6)) {
        case 0: {
            double d = Double.longBitsToDouble(r.nextLong());
            return Double.isNaN(d) ? 1.5 : d;
        }
        case 1:
            return r.nextInt(600) - 300;
        case 2:
            return (r.nextDouble() - 0.5) * Math.pow(10, r.nextInt(40) - 20);
        case 3:
            return r.nextBoolean() ? 0.0 : -0.0;
        case 4:
            return Double.longBitsToDouble((r.nextBoolean() ? 0x8000000000000000L : 0)
                    | (r.nextLong() & 0x000fffffffffffffL));    // subnormal
        default:
            return DOUBLE_EDGES[r.nextInt(DOUBLE_EDGES.length)];
        }
    }

    static double near(double a, Random r) {
        switch (r.nextInt(4)) {
        case 0:
            return Math.nextUp(a);
        case 1:
            return Math.nextDown(a);
        case 2:
            return -a;
        default:
            return a;
        }
    }

    /** Code points that matter to the order: 00, 01, 02, the UTF-8 widths' edges, astral. */
    static final int[] CODE_POINTS = {0, 1, 2, 'a', 'b', 'z', 0x7f, 0x80, 0xe5, 0x7ff, 0x800,
            0xd7ff, 0xe000, 0xfffd, 0xffff, 0x10000, 0x1f600, 0x10ffff};

    static String randomString(Random r) {
        int n = r.nextInt(8);
        StringBuilder s = new StringBuilder();
        for (int i = 0; i < n; i++) {
            s.appendCodePoint(r.nextInt(3) == 0 ? r.nextInt(0xd800)
                    : CODE_POINTS[r.nextInt(CODE_POINTS.length)]);
        }
        return s.toString();
    }

    static String near(String a, Random r) {
        switch (r.nextInt(4)) {
        case 0:
            return cutAtCodePoint(a, r);
        case 1:
            return a + randomString(r);
        case 2: {
            int[] cps = a.codePoints().toArray();
            if (cps.length == 0) {
                return a;
            }
            cps[r.nextInt(cps.length)] = CODE_POINTS[r.nextInt(CODE_POINTS.length)];
            return new String(cps, 0, cps.length);
        }
        default:
            return a;
        }
    }

    static String cutAtCodePoint(String s, Random r) {
        int[] cps = s.codePoints().toArray();
        return new String(cps, 0, r.nextInt(cps.length + 1));
    }

    static final byte[] BYTE_VALUES = {0, 1, 2, 3, 0x2f, 0x7f, (byte) 0x80, (byte) 0xfe,
            (byte) 0xff};

    static byte[] randomBytes(Random r) {
        byte[] b = new byte[r.nextInt(8)];
        for (int i = 0; i < b.length; i++) {
            b[i] = r.nextBoolean() ? BYTE_VALUES[r.nextInt(BYTE_VALUES.length)]
                    : (byte) r.nextInt(256);
        }
        return b;
    }

    static byte[] near(byte[] a, Random r) {
        switch (r.nextInt(4)) {
        case 0:
            return Arrays.copyOf(a, r.nextInt(a.length + 1));
        case 1:
            return concat(a, randomBytes(r));
        case 2: {
            byte[] b = a.clone();
            if (b.length > 0) {
                b[r.nextInt(b.length)] = BYTE_VALUES[r.nextInt(BYTE_VALUES.length)];
            }
            return b;
        }
        default:
            return a.clone();
        }
    }

    // ======== The reference: Java's order ========

    /** Double.compare with -0.0 as 0.0 (020-10, section 3.3); NaN is not compared. */
    static int compareDoubles(double a, double b) {
        return Double.compare(a == 0 ? 0.0 : a, b == 0 ? 0.0 : b);
    }

    /** Strings by code points (020-10, section 3.1), not by Java's UTF-16 chars. */
    static int compareCodePoints(String a, String b) {
        int i = 0, j = 0;
        while (i < a.length() && j < b.length()) {
            int ca = a.codePointAt(i);
            int cb = b.codePointAt(j);
            if (ca != cb) {
                return Integer.compare(ca, cb);
            }
            i += Character.charCount(ca);
            j += Character.charCount(cb);
        }
        return Boolean.compare(i < a.length(), j < b.length());
    }

    /** A value of a level, compared by its type's order. */
    static int compareValues(char type, Object a, Object b) {
        switch (type) {
        case IndexKeys.LONG:
            return Long.compare((Long) a, (Long) b);
        case IndexKeys.DOUBLE:
            return compareDoubles((Double) a, (Double) b);
        case IndexKeys.STRING:
            return compareCodePoints((String) a, (String) b);
        default:
            return Arrays.compareUnsigned((byte[]) a, (byte[]) b);
        }
    }

    static byte[] encode(char type, Object v) {
        switch (type) {
        case IndexKeys.LONG:
            return IndexKeys.encodeLong((Long) v);
        case IndexKeys.DOUBLE:
            return IndexKeys.encodeDouble((Double) v);
        case IndexKeys.STRING:
            return IndexKeys.encodeString((String) v);
        default:
            return IndexKeys.encodeBytes((byte[]) v);
        }
    }

    private static void checkBytesPrefix(byte[] p, byte[] v) {
        byte[] ep = IndexKeys.encodeBytesPrefix(p);
        byte[] ev = IndexKeys.encodeBytes(v);
        Assert.assertArrayEquals(Arrays.copyOf(IndexKeys.encodeBytes(p), ep.length), ep);
        boolean starts = startsWith(v, p);
        Assert.assertEquals("E'(" + hex(p) + ") a prefix of E(" + hex(v) + ")", starts,
                startsWith(ev, ep));
        byte[] s = IndexKeys.succ(ep);
        boolean inRange = Arrays.compareUnsigned(ep, ev) <= 0
                && (s == null || Arrays.compareUnsigned(ev, s) < 0);
        Assert.assertEquals("E(" + hex(v) + ") in the range of " + hex(p), starts, inRange);
    }

    private static void checkStringPrefix(String p, String v) {
        byte[] ep = IndexKeys.encodeStringPrefix(p);
        byte[] ev = IndexKeys.encodeString(v);
        boolean starts = startsWithCodePoints(v, p);
        Assert.assertEquals("E'(" + show(p) + ") a prefix of E(" + show(v) + ")", starts,
                startsWith(ev, ep));
        byte[] s = IndexKeys.succ(ep);
        boolean inRange = Arrays.compareUnsigned(ep, ev) <= 0
                && (s == null || Arrays.compareUnsigned(ev, s) < 0);
        Assert.assertEquals("E(" + show(v) + ") in the range of " + show(p), starts, inRange);
    }

    /** Whether v's code points start with p's (in Java, startsWith on chars is the same). */
    static boolean startsWithCodePoints(String v, String p) {
        int[] a = v.codePoints().toArray();
        int[] b = p.codePoints().toArray();
        return a.length >= b.length && Arrays.equals(a, 0, b.length, b, 0, b.length);
    }

    // ======== Entries: a reference of Java values ========

    /** An entry of the reference: its levels' Java values and K; its key. */
    static final class Ref {
        final Object[] values;
        final byte[] k;
        final byte[] key;

        Ref(Object[] values, byte[] k, byte[] key) {
            this.values = values;
            this.k = k;
            this.key = key;
        }
    }

    static char[] randomTypes(Random r, int n) {
        char[] types = new char[n];
        for (int i = 0; i < n; i++) {
            types[i] = IndexKeys.TYPES[r.nextInt(4)];
        }
        return types;
    }

    /** A random value of a level, from small pools, so that many are equal or prefixes. */
    static Object randomValue(Random r, char type, int pool) {
        switch (type) {
        case IndexKeys.LONG:
            return r.nextInt(3) == 0 ? randomLong(r) : (long) (r.nextInt(pool) - pool / 2);
        case IndexKeys.DOUBLE: {
            double d = r.nextInt(3) == 0 ? randomDouble(r) : (r.nextInt(pool) - pool / 2) / 2.0;
            return d == 0 && r.nextBoolean() ? -0.0 : d;
        }
        case IndexKeys.STRING: {
            String[] s = {"", "a", "a\u0000", "ab", "\u0001", "b", "\ue000", "\ud800\udc00"};
            return r.nextInt(3) == 0 ? randomString(r) : s[r.nextInt(Math.min(pool, s.length))];
        }
        default: {
            byte[][] b = {{}, {0}, {1}, {0, 0}, {2}, {(byte) 0xff}, {1, 1}, {0x40}};
            return r.nextInt(3) == 0 ? randomBytes(r) : b[r.nextInt(Math.min(pool, b.length))]
                    .clone();
        }
        }
    }

    static List<Ref> randomEntries(Random r, char[] types, int n, int pool) {
        byte[] prefix = IndexKeys.generationPrefix("t", 1 + r.nextInt(1000));
        List<Ref> refs = new ArrayList<>();
        for (int k = 0; k < n; k++) {
            Object[] values = new Object[types.length];
            byte[][] levels = new byte[types.length][];
            for (int i = 0; i < types.length; i++) {
                values[i] = randomValue(r, types[i], pool);
                levels[i] = encode(types[i], values[i]);
            }
            byte[] kk = IndexKeys.fileKey("/dt/-" + (char) ('a' + r.nextInt(3)) + k);
            byte[] key = IndexKeys.entryKey(prefix, concat(levels), kk);
            refs.add(new Ref(values, kk, key));

            // The parse gives the levels back.
            IndexKeys.Entry e = IndexKeys.parseEntry(key, prefix, types);
            Assert.assertArrayEquals(kk, e.k());
            for (int i = 0; i < types.length; i++) {
                Assert.assertEquals("value " + i, 0, compareValues(types[i], values[i],
                        e.value(i)));
            }
        }
        return refs;
    }

    private static Comparator<Ref> tupleOrder(char[] types) {
        return (a, b) -> {
            for (int i = 0; i < types.length; i++) {
                int c = compareValues(types[i], a.values[i], b.values[i]);
                if (c != 0) {
                    return c;
                }
            }
            return Arrays.compareUnsigned(a.k, b.k);
        };
    }

    static void checkTupleOrder(char[] types, List<Ref> refs) {
        List<Ref> byValues = new ArrayList<>(refs);
        byValues.sort(tupleOrder(types));
        List<Ref> byKeys = new ArrayList<>(refs);
        byKeys.sort((a, b) -> Arrays.compareUnsigned(a.key, b.key));
        for (int i = 0; i < refs.size(); i++) {
            if (byValues.get(i) != byKeys.get(i)) {
                throw new AssertionError("types " + new String(types) + ": entry " + i
                        + " differs: by values " + hex(byValues.get(i).key) + ", by keys "
                        + hex(byKeys.get(i).key));
            }
        }
        for (int i = 1; i < byKeys.size(); i++) {
            byte[] a = byKeys.get(i - 1).key;
            byte[] b = byKeys.get(i).key;
            Assert.assertEquals(Integer.signum(Arrays.compareUnsigned(a, b)), Integer.signum(
                    Keys.compareKeys(Keys.toSegments(a), Keys.toSegments(b))));
        }
    }

    /**
     * One random query of 020-10, section 3.4's grammar on the entries: its range by section
     * 4.4's formulae, against the reference's filter of Java values.
     */
    static void checkRange(Random r, char[] types, List<Ref> refs) {
        byte[] prefix = generationOf(refs.get(0).key);
        Ref model = refs.get(r.nextInt(refs.size()));
        int n = types.length;
        int k = r.nextInt(n + 1);       // eq on levels 1 to k
        byte[] base = prefix;
        for (int i = 0; i < k; i++) {
            base = concat(base, encode(types[i], model.values[i]));
        }
        String what = "types " + new String(types) + ", eq on " + k;

        byte[] start = base;
        byte[] end = IndexKeys.succ(base);
        Object from = null, to = null, prefixValue = null;
        boolean fromIncl = false, toIncl = false;
        if (k < n) {
            char t = types[k];
            int kind = r.nextInt(4);
            if (kind == 3 && (t == IndexKeys.STRING || t == IndexKeys.BYTES)) {
                // prefix(p): [base E'(p), succ(base E'(p)))
                Object v = r.nextBoolean() ? refs.get(r.nextInt(refs.size())).values[k]
                        : randomValue(r, t, 4);
                if (t == IndexKeys.STRING) {
                    String p = cutAtCodePoint((String) v, r);
                    prefixValue = p;
                    start = concat(base, IndexKeys.encodeStringPrefix(p));
                } else {
                    byte[] p = Arrays.copyOf((byte[]) v, r.nextInt(((byte[]) v).length + 1));
                    prefixValue = p;
                    start = concat(base, IndexKeys.encodeBytesPrefix(p));
                }
                end = IndexKeys.succ(start);
                what += ", prefix";
            } else {
                if (kind == 0 || kind == 2) {
                    from = r.nextBoolean() ? refs.get(r.nextInt(refs.size())).values[k]
                            : randomValue(r, t, 4);
                    fromIncl = r.nextBoolean();
                    byte[] x = concat(base, encode(t, from));
                    start = fromIncl ? x : IndexKeys.succ(x);
                    what += ", from " + (fromIncl ? "incl" : "excl");
                }
                if (kind == 1 || kind == 2) {
                    to = r.nextBoolean() ? refs.get(r.nextInt(refs.size())).values[k]
                            : randomValue(r, t, 4);
                    toIncl = r.nextBoolean();
                    byte[] x = concat(base, encode(t, to));
                    end = toIncl ? IndexKeys.succ(x) : x;
                    what += ", to " + (toIncl ? "incl" : "excl");
                }
            }
        }

        List<Ref> want = new ArrayList<>();
        for (Ref e : refs) {
            boolean in = true;
            for (int i = 0; i < k && in; i++) {
                in = compareValues(types[i], e.values[i], model.values[i]) == 0;
            }
            if (in && k < n) {
                Object v = e.values[k];
                if (from != null) {
                    int c = compareValues(types[k], v, from);
                    in = fromIncl ? c >= 0 : c > 0;
                }
                if (in && to != null) {
                    int c = compareValues(types[k], v, to);
                    in = toIncl ? c <= 0 : c < 0;
                }
                if (in && prefixValue != null) {
                    in = types[k] == IndexKeys.STRING
                            ? startsWithCodePoints((String) v, (String) prefixValue)
                            : startsWith((byte[]) v, (byte[]) prefixValue);
                }
            }
            if (in) {
                want.add(e);
            }
        }
        List<Ref> got = new ArrayList<>();
        for (Ref e : refs) {
            if (Arrays.compareUnsigned(start, e.key) <= 0
                    && (end == null || Arrays.compareUnsigned(e.key, end) < 0)) {
                got.add(e);
            }
        }
        want.sort(tupleOrder(types));
        got.sort((a, b) -> Arrays.compareUnsigned(a.key, b.key));
        if (!want.equals(got)) {
            throw new AssertionError(what + ": " + got.size() + " entries in the range, "
                    + want.size() + " by the reference");
        }
    }

    /** The generation's prefix of an entry key made by randomEntries: "t" and G8. */
    private static byte[] generationOf(byte[] key) {
        byte[] p = IndexKeys.generationPrefix("t", 1);
        return Arrays.copyOf(key, p.length);
    }

    // ======== Helpers ========

    /**
     * 020-10, section 4.4's long, written apart from IndexKeys: 8 bytes, big-endian, of
     * v + 2^63 (as IndexEntryBuilder.sortBytesFromLong of 2026.3).
     */
    static byte[] refLong(long v) {
        long u = v ^ 0x8000000000000000L;
        byte[] b = new byte[8];
        for (int i = 0; i < 8; i++) {
            b[i] = (byte) (u >>> (56 - 8 * i));
        }
        return b;
    }

    /**
     * 020-10, section 4.4's double, written apart from IndexKeys: x its bits, s = x if x &gt;= 0,
     * else -(x AND 0x7fffffffffffffff), as a long (as IndexEntryBuilder.sortBytesFromDouble).
     */
    static byte[] refDouble(double v) {
        long x = Double.doubleToLongBits(v);
        return refLong(x >= 0 ? x : -(x & 0x7fffffffffffffffL));
    }

    static String decodeString(byte[] e) {
        return new String(IndexKeys.decodeEscaped(e, 0, e.length - 1), StandardCharsets.UTF_8);
    }

    static void assertOrder(String what, int javaOrder, byte[] ea, byte[] eb) {
        int c = Integer.signum(Arrays.compareUnsigned(ea, eb));
        if (c != Integer.signum(javaOrder)) {
            throw new AssertionError(what + ": the encodings' order " + c + ", Java's "
                    + Integer.signum(javaOrder) + ": " + hex(ea) + ", " + hex(eb));
        }
    }

    static void assertNull(Object actual) {
        assertNull("", actual);
    }

    static void assertNull(String what, Object actual) {
        if (actual != null) {
            throw new AssertionError(what + ": expected null, got " + (actual instanceof byte[]
                    ? IndexKeysTester.hex((byte[]) actual) : actual));
        }
    }

    static void assertRefusedArg(String what, Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            return;
        }
        throw new AssertionError(what + ": not refused");
    }

    static void assertRefusedInternal(String what, Runnable r) {
        try {
            r.run();
        } catch (InternalDataException e) {
            return;
        }
        throw new AssertionError(what + ": not refused");
    }

    private static void assertRefusedEntry(String what, byte[] key, byte[] prefix,
            char[] types) {
        try {
            IndexKeys.parseEntry(key, prefix, types);
        } catch (InternalDataException e) {
            String m = e.getMessage();
            Assert.assertTrue(what + ": the key named: " + m, m.contains(Keys.toDisplayString(
                    key)) || m.contains(hex(key)));
            return;
        }
        throw new AssertionError(what + ": parsed");
    }

    static boolean startsWith(byte[] b, byte[] prefix) {
        return b.length >= prefix.length
                && Arrays.equals(b, 0, prefix.length, prefix, 0, prefix.length);
    }

    static byte[] concat(byte[]... parts) {
        int n = 0;
        for (byte[] p : parts) {
            n += p.length;
        }
        byte[] b = new byte[n];
        int i = 0;
        for (byte[] p : parts) {
            System.arraycopy(p, 0, b, i, p.length);
            i += p.length;
        }
        return b;
    }

    static String repeat(String s, int n) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < n; i++) {
            b.append(s);
        }
        return b.toString();
    }

    static String hex(byte[] b) {
        StringBuilder s = new StringBuilder();
        for (byte x : b) {
            s.append(String.format("%02x", x & 0xff));
        }
        return s.toString();
    }

    static String show(String s) {
        StringBuilder b = new StringBuilder("\"");
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c >= ' ' && c <= '~') {
                b.append(c);
            } else {
                b.append(String.format("\\u%04x", (int) c));
            }
        }
        return b.append('"').toString();
    }
}
