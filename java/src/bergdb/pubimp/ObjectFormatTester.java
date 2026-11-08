package bergdb.pubimp;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.ByteBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.BadFormatException;

/**
 * Tests of ObjectFormat, the codec of stored objects in format 2 (bergdb 020-07; 020-08,
 * sections 6.2 and 6.3):
 * <ul>
 * <li>T1: every record of the conformance vectors, doc-files/object-vectors.txt, as 020-07,
 *     section 13.2, says, with the Binson column through a converter in this test;</li>
 * <li>H0a: seeded random values of every type and edge, written by the codec and by Ref, a
 *     second codec written in this test from 020-07: the same bytes, accepted by the full
 *     check, decoded to the value, every lookup and nested path as the value's;</li>
 * <li>H0b: mutations, every byte of ten samples changed ten ways and every cut: the full
 *     check and Ref agree on each; an accepted mutant is written again to the same bytes; a
 *     lookup gives the full read's value, or on a refused mutant any answer or a
 *     BadFormatException, never another exception (020-07, section 7.4);</li>
 * <li>the writer's refusals (020-07, section 6.1) and the reader's limits (section 7.1).</li>
 * </ul>
 * The unit group runs H0 with fixed seeds and sizes, about a second; the night group runs
 * more seeds, new each day; main() repeats one seed.
 *
 * @author Frans Lundberg
 */
public class ObjectFormatTester {
    private ObjectFormatTester() {}

    /** H0a's random values in the unit group. */
    static final int UNIT_TREES = 400;

    /** The night's seeds, and for each its random values (H0a) and mutated samples (H0b). */
    static final int NIGHT_SEEDS = 30;
    static final int NIGHT_TREES = 5000;
    static final int NIGHT_SAMPLES = 40;

    /** The vectors mutated by H0b in the unit group: every type, nested objects and arrays. */
    static final String[] SAMPLES = {"payment", "dialog", "index-definition", "customer",
            "order", "integers", "doubles", "strings", "arrays", "depth-16-mixed"};

    static final long NAN = 0x7ff8000000000000L;

    // ======== T1: the vectors (020-07, section 13) ========

    /**
     * T1: every record of the vectors (020-07, section 13.2): a valid value is accepted,
     * decodes to its value, is written from it to the same bytes, gives each lookup's result,
     * and converts to its Binson and back; an invalid one is refused with one of its rules;
     * a generated one is made by its recipe, with its length and SHA-256; a Binson input
     * converts as the record says. Ref, the second codec of this test, is checked the same way.
     */
    @Nano
    public static void testVectors() throws IOException {
        int valid = 0, invalid = 0, generated = 0, binsonIn = 0, lookups = 0;
        for (Record rec : readVectors()) {
            String where = rec.kind + " " + rec.id;
            switch (rec.kind) {
            case "valid":
                valid++;
                lookups += checkValid(rec, where);
                break;
            case "invalid":
                invalid++;
                checkInvalid(unhex(rec.one("bytes")), rec.one("rules"), where);
                break;
            case "generated":
                generated++;
                checkGenerated(rec, where);
                break;
            case "binson-in":
                binsonIn++;
                checkBinsonIn(rec, where);
                break;
            default:
                throw new AssertionError("unknown kind of record: " + where);
            }
        }

        // 020-07, section 13.3: every record was read.
        Assert.assertEquals("valid records", 32, valid);
        Assert.assertEquals("invalid records", 84, invalid);
        Assert.assertEquals("generated records", 2, generated);
        Assert.assertEquals("binson-in records", 8, binsonIn);
        Assert.assertEquals("lookups", 343, lookups);
    }

    private static int checkValid(Record rec, String where) {
        byte[] b = unhex(rec.one("bytes"));
        Obj value = (Obj) Vn.parse(rec.one("value"));
        checkStored(b, where);
        Assert.assertTrue(where + ": isStoredObject", ObjectFormat.isStoredObject(b));
        Assert.assertEquals(where + ": decoded", value, codecDecode(b));
        Assert.assertEquals(where + ": read by Ref", value, Ref.read(b));
        assertBytes(where + ": written", b, codecWrite(value));
        assertBytes(where + ": written by Ref", b, Ref.write(value, true));

        byte[] binson = unhex(rec.one("binson"));
        assertBytes(where + ": to Binson", binson, toBinson(b));
        assertBytes(where + ": from Binson", b, fromBinson(binson));

        int count = 0;
        for (String lookup : rec.all("lookup")) {
            Vn p = new Vn(lookup);
            List<byte[]> path = p.path();
            String result = lookup.substring(p.i + 1);
            Object want = result.equals("absent") ? null : Vn.parse(result);
            Assert.assertEquals(where + ": lookup " + lookup + " in the value", want,
                    Ref.lookup(value, path));
            Assert.assertEquals(where + ": lookup " + lookup, want, codecLookup(b, path));
            count++;
        }
        return count;
    }

    private static void checkInvalid(byte[] b, String rules, String where) {
        List<String> codes = Arrays.asList(rules.split(","));
        String code = refusal(b, where);
        if (code == null) {
            throw new AssertionError(where + ": accepted");
        }
        if (!codes.contains(code)) {
            throw new AssertionError(where + ": refused as " + code + ", not one of " + rules);
        }
        Assert.assertFalse(where + ": isStoredObject", ObjectFormat.isStoredObject(b));
        try {
            Ref.read(b);
            throw new AssertionError(where + ": accepted by Ref");
        } catch (Refused e) {
            if (!codes.contains(e.code)) {
                throw new AssertionError(where + ": refused by Ref as " + e.code + ", not one of "
                        + rules);
            }
        }
    }

    private static void checkGenerated(Record rec, String where) {
        int n;
        if (rec.id.equals("fields-32767")) {
            n = 32767;
        } else if (rec.id.equals("fields-32768")) {
            n = 32768;
        } else {
            throw new AssertionError(where + ": an unknown recipe");
        }

        // The recipe: field k has the name of 5 ASCII digits, k with leading zeros, and true.
        Obj o = new Obj();
        for (int k = 0; k < n; k++) {
            o.fields.put(String.format("%05d", k), Boolean.TRUE);
        }
        byte[] b;
        if (n <= ObjectFormat.MAX_FIELDS) {
            b = codecWrite(o);
            assertBytes(where + ": written by Ref", Ref.write(o, true), b);
        } else {
            assertRefusedArg(where + ": written", "fields", () -> codecWrite(o));
            b = Ref.write(o, false);
        }
        Assert.assertEquals(where + ": length", Long.parseLong(rec.one("length")), b.length);
        Assert.assertEquals(where + ": SHA-256", rec.one("sha256"), sha256(b));
        if (rec.has("valid")) {
            checkStored(b, where);
            Assert.assertEquals(where + ": decoded", o, codecDecode(b));
        } else {
            checkInvalid(b, rec.one("rules"), where);
        }
    }

    private static void checkBinsonIn(Record rec, String where) {
        byte[] binson = unhex(rec.one("binson"));
        if (rec.has("bytes")) {
            assertBytes(where, unhex(rec.one("bytes")), fromBinson(binson));
            return;
        }

        List<String> codes = Arrays.asList(rec.one("rules").split(","));
        String code;
        try {
            byte[] b = fromBinson(binson);
            throw new AssertionError(where + ": converted to " + StringUtil.toHex(b));
        } catch (Refused e) {
            code = e.code;
        } catch (IllegalArgumentException e) {
            code = code(e);
        }
        if (!codes.contains(code)) {
            throw new AssertionError(where + ": refused as " + code + ", not one of " + codes);
        }
    }

    // ======== The writer's refusals and the reader's limits ========

    /** The writer refuses what has no stored form (020-07, section 6.1). */
    @Nano
    public static void testWriterRefusals() {
        byte[] a255 = new byte[255];
        Arrays.fill(a255, (byte) 'a');
        ObjectFormat.checkName(a255);
        ObjectFormat.checkName(new byte[] {0});
        assertRefusedArg("empty name", "name-length", () -> ObjectFormat.checkName(new byte[0]));
        assertRefusedArg("a name of 256 bytes", "name-length",
                () -> ObjectFormat.checkName(Arrays.copyOf(a255, 256)));
        assertRefusedArg("a name of the byte ff", "utf8",
                () -> ObjectFormat.checkName(new byte[] {(byte) 0xff}));
        assertRefusedArg("a name of a surrogate", "utf8",
                () -> ObjectFormat.checkName(new byte[] {(byte) 0xed, (byte) 0xa0, (byte) 0x80}));

        Assert.assertEquals(255, ObjectFormat.nameBytes(new String(a255,
                StandardCharsets.US_ASCII)).length);
        Assert.assertEquals(254, ObjectFormat.nameBytes("é".repeat(127)).length);
        assertRefusedArg("empty name", "name-length", () -> ObjectFormat.nameBytes(""));
        assertRefusedArg("a name of 256 bytes", "name-length",
                () -> ObjectFormat.nameBytes("é".repeat(128)));
        assertRefusedArg("a name with a lone surrogate", "utf8",
                () -> ObjectFormat.nameBytes("a\uD800"));
        assertRefusedArg("a string with a lone surrogate", "utf8",
                () -> ObjectFormat.utf8("\uDC00a"));
        Assert.assertEquals("f09f9880", StringUtil.toHex(ObjectFormat.utf8("😀")));
        assertRefusedArg("a string of the byte ff", "utf8",
                () -> ObjectFormat.checkUtf8(new byte[] {(byte) 0xff}, "a string"));

        ObjectFormat.checkCount(32767);
        assertRefusedArg("32,768 fields", "fields", () -> ObjectFormat.checkCount(32768));
        ObjectFormat.checkLevel(16);
        assertRefusedArg("level 17", "depth", () -> ObjectFormat.checkLevel(17));
        ObjectFormat.checkStoredSize(Integer.MAX_VALUE);
        assertRefusedArg("2^31 bytes", "size", () -> ObjectFormat.checkStoredSize(1L << 31));

        // Through the codec's writer and Ref's: each refuses with the same condition.
        Obj deep = new Obj();
        Obj inner = deep;
        for (int level = 2; level <= 17; level++) {
            Obj next = new Obj();
            inner.fields.put("o", next);
            inner = next;
        }
        assertWritersRefuse("17 objects", "depth", deep);
        Obj deepArrays = new Obj();
        Arr arr = new Arr();
        deepArrays.fields.put("a", arr);
        for (int level = 3; level <= 17; level++) {
            Arr next = new Arr();
            arr.elements.add(next);
            arr = next;
        }
        assertWritersRefuse("the top object and 16 arrays", "depth", deepArrays);
        Obj names = new Obj();
        names.fields.put("", Boolean.TRUE);
        assertWritersRefuse("an empty name", "name-length", names);
        Obj strings = new Obj();
        strings.fields.put("s", new Str("ÿ"));
        assertWritersRefuse("a string of the byte ff", "utf8", strings);
    }

    private static void assertWritersRefuse(String what, String code, Obj o) {
        assertRefusedArg(what, code, () -> codecWrite(o));
        try {
            Ref.write(o, true);
            throw new AssertionError(what + ": written by Ref");
        } catch (Refused e) {
            Assert.assertEquals(what + ": refused by Ref", code, e.code);
        }
    }

    /** The writer's encodings: each integer in the fewest bytes, one NaN, -0.0 kept. */
    @Nano
    public static void testWriterEncodings() {
        long[] values = {0, 127, -128, 128, -129, 32767, -32768, 32768, -32769,
                Integer.MAX_VALUE, Integer.MIN_VALUE, Integer.MAX_VALUE + 1L,
                Integer.MIN_VALUE - 1L, Long.MAX_VALUE, Long.MIN_VALUE};
        int[] sizes = {2, 2, 2, 3, 3, 3, 3, 5, 5, 5, 5, 9, 9, 9, 9};
        for (int i = 0; i < values.length; i++) {
            byte[] b = new byte[ObjectFormat.integerSize(values[i])];
            Assert.assertEquals("size of " + values[i], sizes[i], b.length);
            Assert.assertEquals(b.length, ObjectFormat.writeInteger(b, 0, values[i]));
            Assert.assertEquals(0x10 + (sizes[i] == 2 ? 0 : sizes[i] == 3 ? 1 : sizes[i] == 5
                    ? 2 : 3), b[0] & 0xff);
            Assert.assertEquals("value of " + values[i], values[i], ObjectFormat.integerAt(b, 0));
        }

        long[] nans = {NAN, 0x7ff8000000000001L, 0xfff8000000000000L, 0x7ff0000000000001L,
                0xffffffffffffffffL, Double.doubleToRawLongBits(Float.NaN)};
        for (long bits : nans) {
            byte[] b = new byte[ObjectFormat.DOUBLE_SIZE];
            Assert.assertEquals(9, ObjectFormat.writeDouble(b, 0, bits));
            Assert.assertEquals("NaN " + Long.toHexString(bits), "46000000000000f87f",
                    StringUtil.toHex(b));
        }
        long[] kept = {0x8000000000000000L, 0L, 0x7ff0000000000000L, 0xfff0000000000000L, 1L,
                Double.doubleToRawLongBits(Math.PI)};
        for (long bits : kept) {
            byte[] b = new byte[ObjectFormat.DOUBLE_SIZE];
            ObjectFormat.writeDouble(b, 0, bits);
            Assert.assertEquals("double " + Long.toHexString(bits), bits,
                    ObjectFormat.doubleBitsAt(b, 0));
        }

        int[] lengths = {0, 127, 128, 32767, 32768, Integer.MAX_VALUE};
        int[] heads = {2, 2, 3, 3, 5, 5};
        for (int i = 0; i < lengths.length; i++) {
            Assert.assertEquals("length " + lengths[i], heads[i],
                    ObjectFormat.lengthSize(lengths[i]));
        }
        Assert.assertEquals(1, ObjectFormat.width(0));
        Assert.assertEquals(1, ObjectFormat.width(255));
        Assert.assertEquals(2, ObjectFormat.width(256));
        Assert.assertEquals(2, ObjectFormat.width(65535));
        Assert.assertEquals(4, ObjectFormat.width(65536));
    }

    /**
     * The reader refuses at its limits before it recurses or allocates (020-07, section 7.1):
     * 100,000 nested arrays at level 17, with no StackOverflowError; a count of 32,767 with no
     * table; never another exception than BadFormatException on a cut or an empty array.
     */
    @Nano
    public static void testReaderLimits() {
        int n = 100000;
        int size = 2 + 2 * n;
        byte[] b = new byte[10 + size];
        b[0] = (byte) 0x82;
        b[1] = 0x4a;
        b[2] = 1;
        b[6] = (byte) size;
        b[7] = (byte) (size >> 8);
        b[8] = (byte) (size >> 16);
        b[10] = 1;
        b[11] = 'a';
        Arrays.fill(b, 12, 12 + n, (byte) 0x42);
        Arrays.fill(b, 12 + n, b.length, (byte) 0x43);
        assertRefused("100,000 arrays", "depth", b);

        assertRefused("a count of 32,767 and no table", "past-end",
                new byte[] {(byte) 0x82, 0x49, (byte) 0xff, 0x7f});
        assertRefused("a count of 32,768", "fields",
                new byte[] {(byte) 0x82, 0x49, 0, (byte) 0x80});
        assertRefused("no bytes", "past-end", new byte[0]);

        // A later format names its version.
        try {
            ObjectFormat.checkStored(new byte[] {(byte) 0x83, 0x48, 0});
            throw new AssertionError("format 3 accepted");
        } catch (BadFormatException e) {
            Assert.assertEquals("header", code(e));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format 3"));
        }
    }

    /** find(): the binary search of 020-07, section 8.2, on objects of 0 to 300 fields. */
    @Nano
    public static void testFind() {
        for (int n : new int[] {0, 1, 2, 3, 7, 8, 85, 300}) {
            Obj o = new Obj();
            for (int k = 0; k < n; k++) {
                o.fields.put(String.format("f%03d", 2 * k), Long.valueOf(k));
            }
            byte[] b = codecWrite(o);
            for (int k = -1; k <= 2 * n; k++) {
                byte[] name = String.format("f%03d", k).getBytes(StandardCharsets.US_ASCII);
                int p = ObjectFormat.find(b, 1, b.length, name);
                if (k >= 0 && k % 2 == 0 && k < 2 * n) {
                    Assert.assertTrue(n + " fields, f" + k, p > 0);
                    Assert.assertEquals(k / 2, ObjectFormat.integerAt(b, p));
                } else {
                    Assert.assertEquals(n + " fields, f" + k, -1, p);
                }
            }
            Assert.assertEquals(-1, ObjectFormat.find(b, 1, b.length, new byte[0]));
        }
    }

    // ======== H0: the harness of the format (020-08, section 6.3) ========

    /** H0a in the unit group: random values of seed 1. */
    @Nano
    public static void testH0aRandomValues() {
        Stats st = new Stats();
        h0a(1, UNIT_TREES, st);
        Assert.assertEquals(UNIT_TREES, st.trees);
    }

    /** H0b in the unit group: the ten vectors of SAMPLES, seed 2 for the random byte. */
    @Nano
    public static void testH0bMutations() throws IOException {
        Map<String, byte[]> valid = new TreeMap<>();
        for (Record rec : readVectors()) {
            if (rec.kind.equals("valid")) {
                valid.put(rec.id, unhex(rec.one("bytes")));
            }
        }
        Random r = new Random(2);
        Stats st = new Stats();
        long bytes = 0;
        for (String id : SAMPLES) {
            h0b(valid.get(id), "H0b " + id, r, st);
            bytes += valid.get(id).length;
        }
        Assert.assertEquals("mutants: ten a byte and every cut", 11 * bytes, st.mutants);
        Assert.assertTrue("mutants accepted and refused: " + st, st.accepted > 1000
                && st.mutants - st.accepted > 5000);
    }

    /**
     * The night's run: NIGHT_SEEDS seeds, new each day (the day's number times 1000), each
     * with H0a on NIGHT_TREES random values and H0b on NIGHT_SAMPLES of them; the seeds are
     * printed, so that a failure is repeated with main(seed).
     */
    @Nano("night")
    public static void testHarnessNight(TestEnvironment c) {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        c.out().println("ObjectFormatTester: seeds " + base + " to " + (base + NIGHT_SEEDS - 1)
                + ", " + NIGHT_TREES + " values and " + NIGHT_SAMPLES + " mutated each");
        Stats st = new Stats();
        for (long seed = base; seed < base + NIGHT_SEEDS; seed++) {
            runSeed(seed, NIGHT_TREES, NIGHT_SAMPLES, st);
        }
        c.out().println("ObjectFormatTester: " + st);
    }

    /**
     * Usage: ObjectFormatTester [SEED [TREES [SAMPLES]]]: H0a on TREES random values and H0b
     * on SAMPLES of them, from SEED (default: the time; TREES and SAMPLES as one seed of the
     * night's run); prints the counts.
     */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int trees = args.length > 1 ? Integer.parseInt(args[1]) : NIGHT_TREES;
        int samples = args.length > 2 ? Integer.parseInt(args[2]) : NIGHT_SAMPLES;
        long t0 = System.nanoTime();
        Stats st = new Stats();
        runSeed(seed, trees, samples, st);
        System.out.println("ObjectFormatTester: seed " + seed + ": " + st + "; "
                + (System.nanoTime() - t0) / 1000000 + " ms");
    }

    static void runSeed(long seed, int trees, int samples, Stats st) {
        h0a(seed, trees, st);
        Gen g = new Gen(seed ^ 0x5DEECE66DL);
        for (int k = 0; k < samples; k++) {
            byte[] sample = Ref.write(g.sample(), true);
            h0b(sample, "H0b seed " + seed + ", sample " + k, g.r, st);
        }
    }

    /**
     * H0a: 'trees' random values from 'seed': Ref's bytes equal the codec's; the full check
     * accepts them; the codec's decoding and Ref's equal the value (NaN made the one pattern);
     * Binson both ways gives the bytes again; every lookup and nested path, absent names
     * included, gives the value's.
     */
    static void h0a(long seed, int trees, Stats st) {
        Gen g = new Gen(seed);
        for (int k = 0; k < trees; k++) {
            Obj t = g.tree();
            String where = "H0a seed " + seed + ", value " + k;
            byte[] b = Ref.write(t, true);
            assertBytes(where + ": written", b, codecWrite(t));
            checkStored(b, where);
            Assert.assertTrue(where, ObjectFormat.isStoredObject(b));
            Obj canon = (Obj) canon(t);
            Assert.assertEquals(where + ": decoded", canon, codecDecode(b));
            Assert.assertEquals(where + ": read by Ref", canon, Ref.read(b));
            assertBytes(where + ": Binson both ways", b, fromBinson(toBinson(b)));
            for (List<byte[]> path : paths(canon, 3000)) {
                Assert.assertEquals(where + ": lookup " + pathText(path), Ref.lookup(canon, path),
                        codecLookup(b, path));
                st.lookups++;
            }
            st.trees++;
            st.bytes += b.length;
        }
    }

    /**
     * H0b: every byte of 'sample' changed ten ways, and every cut. For each mutant, the full
     * check and Ref agree (either may name another condition); an accepted mutant decodes to
     * Ref's value and is written again to the same bytes by both writers; each lookup gives
     * the full read's value, or on a refused mutant any answer or a BadFormatException, and
     * never another exception.
     */
    static void h0b(byte[] sample, String where, Random r, Stats st) {
        List<List<byte[]>> paths = paths(Ref.read(sample), 60);
        for (int i = 0; i < sample.length; i++) {
            int x = sample[i] & 0xff;
            int[] to = {x ^ 0x01, x ^ 0x80, x ^ 0xff, 0x00, 0x7f, 0x80, 0xff, x + 1, x - 1,
                    r.nextInt(256)};
            for (int y : to) {
                byte[] m = sample.clone();
                m[i] = (byte) y;
                mutant(m, paths, where + ", byte " + i + " to " + (y & 0xff), st);
            }
        }
        for (int length = 0; length < sample.length; length++) {
            mutant(Arrays.copyOf(sample, length), paths, where + ", cut at " + length, st);
        }
    }

    private static void mutant(byte[] m, List<List<byte[]>> paths, String where, Stats st) {
        String code;
        try {
            code = refusal(m, where);
        } catch (RuntimeException | StackOverflowError e) {
            throw new AssertionError(where + ": " + e, e);
        }
        Obj v = null;
        String refCode = null;
        try {
            v = Ref.read(m);
        } catch (Refused e) {
            refCode = e.code;
        }
        if ((code == null) != (refCode == null)) {
            throw new AssertionError(where + ": the full check says " + code + ", Ref "
                    + refCode + ": " + StringUtil.toHex(m));
        }
        Assert.assertEquals(where + ": isStoredObject", code == null,
                ObjectFormat.isStoredObject(m));
        st.mutants++;
        if (code == null) {
            st.accepted++;
            Assert.assertEquals(where + ": decoded", v, codecDecode(m));
            assertBytes(where + ": written again", m, codecWrite(v));
            assertBytes(where + ": written again by Ref", m, Ref.write(v, true));
        } else if (!code.equals(refCode)) {
            st.otherCode++;
        }

        for (List<byte[]> path : paths) {
            Object got;
            try {
                got = codecLookup(m, path);
            } catch (BadFormatException e) {
                if (code == null) {
                    throw new AssertionError(where + ": lookup " + pathText(path) + ": " + e, e);
                }
                continue;
            } catch (RuntimeException | StackOverflowError e) {
                throw new AssertionError(where + ": lookup " + pathText(path) + ": " + e, e);
            }
            if (code == null) {
                Assert.assertEquals(where + ": lookup " + pathText(path), Ref.lookup(v, path),
                        got);
            }
        }
    }

    static final class Stats {
        long trees, bytes, lookups, mutants, accepted, otherCode;

        public String toString() {
            return trees + " values (" + bytes + " bytes, " + lookups + " lookups); " + mutants
                    + " mutants, " + accepted + " accepted, " + otherCode
                    + " refused by Ref for another condition";
        }
    }

    // ======== Through the codec ========

    /** The full check; an AssertionError with the refusal if it refuses. */
    static void checkStored(byte[] b, String where) {
        try {
            ObjectFormat.checkStored(b);
        } catch (BadFormatException e) {
            throw new AssertionError(where + ": refused: " + e.getMessage(), e);
        }
    }

    /** The code of the full check's refusal of 'b', or null if it accepts 'b'. */
    static String refusal(byte[] b, String where) {
        try {
            ObjectFormat.checkStored(b);
            return null;
        } catch (BadFormatException e) {
            String m = e.getMessage();
            if (!m.endsWith("(bergdb 020-07, section 7.2)")) {
                throw new AssertionError(where + ": a message without its source: " + m);
            }
            return code(e);
        }
    }

    /**
     * Writes a value of the model with ObjectFormat's encodings and checks, bottom up, as the
     * Builder will (020-08, section 4.4): each object's fields into an array, then its frame in
     * front of them.
     */
    static byte[] codecWrite(Obj o) {
        byte[] object = codecObject(o, 1);
        ObjectFormat.checkStoredSize(1L + object.length);
        byte[] b = new byte[1 + object.length];
        b[0] = (byte) ObjectFormat.HEADER;
        System.arraycopy(object, 0, b, 1, object.length);
        return b;
    }

    private static byte[] codecObject(Obj o, int level) {
        ObjectFormat.checkLevel(level);
        int n = o.fields.size();
        ObjectFormat.checkCount(n);
        byte[][] names = new byte[n][];
        byte[][] values = new byte[n][];
        int[] ends = new int[n];
        long size = 0;
        int i = 0;
        for (Map.Entry<String, Object> e : o.fields.entrySet()) {
            names[i] = bytes(e.getKey());
            ObjectFormat.checkName(names[i]);
            values[i] = codecValue(e.getValue(), level);
            size += 1 + names[i].length + values[i].length;
            ObjectFormat.checkStoredSize(size);
            ends[i] = (int) size;
            i++;
        }
        byte[] b = new byte[ObjectFormat.headSize(n, size) + (int) size];
        int p = ObjectFormat.frame(b, 0, ends, n);
        for (i = 0; i < n; i++) {
            p = ObjectFormat.writeName(b, p, names[i]);
            System.arraycopy(values[i], 0, b, p, values[i].length);
            p += values[i].length;
        }
        Assert.assertEquals(b.length, p);
        return b;
    }

    private static byte[] codecValue(Object v, int level) {
        if (v instanceof Obj) {
            return codecObject((Obj) v, level + 1);
        } else if (v instanceof Arr) {
            ObjectFormat.checkLevel(level + 1);
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            out.write(ObjectFormat.ARRAY_START);
            for (Object e : ((Arr) v).elements) {
                byte[] x = codecValue(e, level + 1);
                out.write(x, 0, x.length);
            }
            out.write(ObjectFormat.ARRAY_END);
            return out.toByteArray();
        } else if (v instanceof Boolean) {
            byte[] b = new byte[1];
            ObjectFormat.writeBoolean(b, 0, (Boolean) v);
            return b;
        } else if (v instanceof Long) {
            long x = (Long) v;
            byte[] b = new byte[ObjectFormat.integerSize(x)];
            ObjectFormat.writeInteger(b, 0, x);
            return b;
        } else if (v instanceof Dbl) {
            byte[] b = new byte[ObjectFormat.DOUBLE_SIZE];
            ObjectFormat.writeDouble(b, 0, ((Dbl) v).bits);
            return b;
        } else if (v instanceof Str) {
            // A Java String, as DbString will hold it, encoded again by the codec.
            byte[] x = bytes(((Str) v).bytes);
            ObjectFormat.checkUtf8(x, "a string");
            x = ObjectFormat.utf8(new String(x, StandardCharsets.UTF_8));
            byte[] b = new byte[ObjectFormat.lengthSize(x.length) + x.length];
            int p = ObjectFormat.writeStringHead(b, 0, x.length);
            System.arraycopy(x, 0, b, p, x.length);
            return b;
        } else {
            byte[] x = bytes(((Bin) v).bytes);
            byte[] b = new byte[ObjectFormat.lengthSize(x.length) + x.length];
            int p = ObjectFormat.writeBytesHead(b, 0, x.length);
            System.arraycopy(x, 0, b, p, x.length);
            return b;
        }
    }

    /** Decodes checked bytes with ObjectFormat's readers. */
    static Obj codecDecode(byte[] b) {
        return codecObjectAt(b, 1);
    }

    private static Obj codecObjectAt(byte[] b, int p) {
        Obj o = new Obj();
        int n = ObjectFormat.countAt(b, p);
        int previous = ObjectFormat.fieldsAt(b, p);
        for (int i = 0; i < n; i++) {
            int f = ObjectFormat.fieldAt(b, p, i);
            Assert.assertEquals(previous, f);
            int length = b[f] & 0xff;
            Object v = codecValueAt(b, f + 1 + length);
            o.fields.put(chars(Arrays.copyOfRange(b, f + 1, f + 1 + length)), v);
            previous = ObjectFormat.fieldsAt(b, p) + ObjectFormat.endAt(b, p, i);
            Assert.assertEquals(previous, ObjectFormat.valueEnd(b, f + 1 + length));
        }
        Assert.assertEquals(previous, ObjectFormat.objectEnd(b, p));
        return o;
    }

    private static Object codecValueAt(byte[] b, int p) {
        char type = ObjectFormat.typeAt(b, p);
        switch (type) {
        case 'n':
            return ObjectFormat.booleanAt(b, p);
        case 'l':
            return ObjectFormat.integerAt(b, p);
        case 'd':
            return new Dbl(ObjectFormat.doubleBitsAt(b, p));
        case 's':
            Assert.assertEquals(ObjectFormat.lengthAt(b, p) + ObjectFormat.contentAt(b, p),
                    ObjectFormat.valueEnd(b, p));
            return new Str(chars(ObjectFormat.stringAt(b, p).getBytes(StandardCharsets.UTF_8)));
        case 'b':
            return new Bin(chars(ObjectFormat.bytesAt(b, p)));
        case 'a': {
            Arr a = new Arr();
            int q = p + 1;
            while ((b[q] & 0xff) != ObjectFormat.ARRAY_END) {
                a.elements.add(codecValueAt(b, q));
                q = ObjectFormat.valueEnd(b, q);
            }
            Assert.assertEquals(q + 1, ObjectFormat.valueEnd(b, p));
            return a;
        }
        case 'o':
            Assert.assertTrue(ObjectFormat.isObjectAt(b, p));
            return codecObjectAt(b, p);
        default:
            throw new AssertionError("type " + type);
        }
    }

    /**
     * Looks up a path by ObjectFormat.find, on bytes that may not be checked (020-07,
     * section 7.4): the value, null if absent, or a BadFormatException. The value found is
     * checked by every rule before it is decoded.
     */
    static Object codecLookup(byte[] b, List<byte[]> path) {
        if (b.length < 2 || (b[0] & 0xff) != ObjectFormat.HEADER) {
            throw new BadFormatException("header: not a stored object");
        }
        int p = 1;
        for (int k = 0; k < path.size(); k++) {
            int q = ObjectFormat.find(b, p, b.length, path.get(k));
            if (q < 0) {
                return null;
            }
            if (k == path.size() - 1) {
                ObjectFormat.checkValue(b, q, b.length, k + 1);
                return codecValueAt(b, q);
            }
            if (!ObjectFormat.isObjectAt(b, q)) {
                return null;
            }
            p = q;
        }
        throw new AssertionError("an empty path");
    }

    /** Format 2 to Binson (020-07, section 10.1), by ObjectFormat's readers of checked bytes. */
    static byte[] toBinson(byte[] stored) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        binsonObject(stored, 1, out);
        return out.toByteArray();
    }

    private static void binsonObject(byte[] b, int p, ByteArrayOutputStream out) {
        out.write(0x40);
        int n = ObjectFormat.countAt(b, p);
        for (int i = 0; i < n; i++) {
            int f = ObjectFormat.fieldAt(b, p, i);
            int length = b[f] & 0xff;
            if (length < 128) {
                out.write(0x14);
                out.write(length);
            } else {
                out.write(0x15);
                out.write(length);
                out.write(0);
            }
            out.write(b, f + 1, length);
            binsonValue(b, f + 1 + length, out);
        }
        out.write(0x41);
    }

    private static int binsonValue(byte[] b, int p, ByteArrayOutputStream out) {
        if (ObjectFormat.isObjectAt(b, p)) {
            binsonObject(b, p, out);
            return ObjectFormat.objectEnd(b, p);
        }
        if ((b[p] & 0xff) == ObjectFormat.ARRAY_START) {
            out.write(0x42);
            int q = p + 1;
            while ((b[q] & 0xff) != ObjectFormat.ARRAY_END) {
                q = binsonValue(b, q, out);
            }
            out.write(0x43);
            return q + 1;
        }
        int end = ObjectFormat.valueEnd(b, p);
        out.write(b, p, end - p);
        return end;
    }

    /**
     * Binson to format 2 (020-07, section 10.2): Refused("binson") for an input that is not a
     * Binson object; the codec's writer refuses, with IllegalArgumentException, what format 2
     * cannot hold, and makes every NaN the one pattern.
     */
    static byte[] fromBinson(byte[] binson) {
        return codecWrite(BinsonReader.read(binson));
    }

    // ======== Ref: a second codec, written in this test from 020-07 ========

    /** Ref's refusal, with the condition's code (020-07, section 7.2). */
    static final class Refused extends RuntimeException {
        private static final long serialVersionUID = 1L;
        final String code;

        Refused(String code) {
            super(code);
            this.code = code;
        }
    }

    /**
     * Another codec than ObjectFormat, from 020-07's text: a reader that decodes as it
     * checks, with another order of checks (each object's table whole before its fields, the
     * top object's trailing bytes before its fields, Java's UTF-8 decoder for well-formed
     * UTF-8); a writer bottom up into streams; lookups in the decoded value.
     */
    static final class Ref {
        private final byte[] b;
        private int p;

        private Ref(byte[] b) {
            this.b = b;
        }

        static Obj read(byte[] b) {
            if (b.length == 0) {
                throw new Refused("past-end");
            }
            if ((b[0] & 0xff) != 0x82) {
                boolean bergo = b.length >= 5
                        && chars(Arrays.copyOf(b, 5)).equals("bergo");
                throw new Refused(bergo ? "format-1" : "header");
            }
            if (b.length < 2) {
                throw new Refused("past-end");
            }
            int t = b[1] & 0xff;
            if (t < 0x48 || t > 0x4a) {
                throw new Refused("type");
            }
            Ref r = new Ref(b);
            r.p = 1;
            Obj o = r.object(b.length, 1, true);
            if (r.p != b.length) {
                throw new Refused("trailing");
            }
            return o;
        }

        private long number(int size, int limit, boolean signed) {
            if (size > limit - p) {
                throw new Refused("past-end");
            }
            long x = 0;
            for (int k = size - 1; k >= 0; k--) {
                x = (x << 8) | (b[p + k] & 0xff);
            }
            p += size;
            if (signed && size < 8) {
                int shift = 64 - 8 * size;
                x = (x << shift) >> shift;
            }
            return x;
        }

        private Obj object(int limit, int level, boolean top) {
            if (level > 16) {
                throw new Refused("depth");
            }
            int w = 1 << ((b[p] & 0xff) - 0x48);
            p++;
            long n = number(w, limit, false);
            if (n > 32767) {
                throw new Refused("fields");
            }
            long[] ends = new long[(int) n];
            for (int i = 0; i < n; i++) {
                ends[i] = number(w, limit, false);
            }
            long size = n == 0 ? 0 : ends[(int) n - 1];
            int f0 = p;
            if (size > limit - f0) {
                throw new Refused("past-end");
            }
            if ((size < 256 ? 1 : size < 65536 ? 2 : 4) != w) {
                throw new Refused("width");
            }
            long previous = 0;
            for (long e : ends) {
                if (e <= previous) {
                    throw new Refused("ends");
                }
                previous = e;
            }
            if (top && f0 + size != limit) {
                throw new Refused("trailing");
            }

            Obj o = new Obj();
            String previousName = null;
            previous = 0;
            for (long e : ends) {
                int fe = f0 + (int) e;
                p = f0 + (int) previous;
                int length = b[p++] & 0xff;
                if (length == 0) {
                    throw new Refused("name-length");
                }
                if (length > fe - p) {
                    throw new Refused("past-end");
                }
                byte[] nameBytes = Arrays.copyOfRange(b, p, p + length);
                p += length;
                if (!wellFormed(nameBytes)) {
                    throw new Refused("utf8");
                }
                String name = chars(nameBytes);
                if (previousName != null) {
                    int c = previousName.compareTo(name);
                    if (c == 0) {
                        throw new Refused("duplicate");
                    } else if (c > 0) {
                        throw new Refused("order");
                    }
                }
                Object v = value(fe, level);
                if (p != fe) {
                    throw new Refused("field-size");
                }
                o.fields.put(name, v);
                previousName = name;
                previous = e;
            }
            p = f0 + (int) size;
            return o;
        }

        private Object value(int limit, int level) {
            if (p >= limit) {
                throw new Refused("past-end");
            }
            int t = b[p++] & 0xff;
            if (t >= 0x10 && t <= 0x13) {
                int size = 1 << (t - 0x10);
                long x = number(size, limit, true);
                if (fewest(x) != size) {
                    throw new Refused("integer-size");
                }
                return x;
            }
            if ((t >= 0x14 && t <= 0x16) || (t >= 0x18 && t <= 0x1a)) {
                int size = 1 << (t & 3);
                long length = number(size, limit, true);
                if (length < 0) {
                    throw new Refused("length");
                }
                if (fewest(length) != size) {
                    throw new Refused("integer-size");
                }
                if (length > limit - p) {
                    throw new Refused("past-end");
                }
                byte[] x = Arrays.copyOfRange(b, p, p + (int) length);
                p += (int) length;
                if (t <= 0x16) {
                    if (!wellFormed(x)) {
                        throw new Refused("utf8");
                    }
                    return new Str(chars(x));
                }
                return new Bin(chars(x));
            }
            switch (t) {
            case 0x44:
                return Boolean.TRUE;
            case 0x45:
                return Boolean.FALSE;
            case 0x46: {
                long bits = number(8, limit, false);
                if (Double.isNaN(Double.longBitsToDouble(bits)) && bits != NAN) {
                    throw new Refused("nan");
                }
                return new Dbl(bits);
            }
            case 0x42: {
                if (level + 1 > 16) {
                    throw new Refused("depth");
                }
                Arr a = new Arr();
                while (true) {
                    if (p >= limit) {
                        throw new Refused("past-end");
                    }
                    if ((b[p] & 0xff) == 0x43) {
                        p++;
                        return a;
                    }
                    a.elements.add(value(limit, level + 1));
                }
            }
            case 0x48: case 0x49: case 0x4a:
                p--;
                return object(limit, level + 1, false);
            default:
                throw new Refused("type");
            }
        }

        /** Writes 'o'; with 'limits' false, any count of fields (for fields-32768). */
        static byte[] write(Obj o, boolean limits) {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            out.write(0x82);
            byte[] x = object(o, 1, limits);
            out.write(x, 0, x.length);
            if (out.size() > Integer.MAX_VALUE - 1) {
                throw new Refused("size");
            }
            return out.toByteArray();
        }

        private static byte[] object(Obj o, int level, boolean limits) {
            if (level > 16) {
                throw new Refused("depth");
            }
            if (limits && o.fields.size() > 32767) {
                throw new Refused("fields");
            }
            ByteArrayOutputStream fields = new ByteArrayOutputStream();
            List<Integer> ends = new ArrayList<>();
            for (Map.Entry<String, Object> e : o.fields.entrySet()) {
                byte[] name = bytes(e.getKey());
                if (name.length < 1 || name.length > 255) {
                    throw new Refused("name-length");
                }
                if (!wellFormed(name)) {
                    throw new Refused("utf8");
                }
                fields.write(name.length);
                fields.write(name, 0, name.length);
                value(fields, e.getValue(), level, limits);
                ends.add(fields.size());
            }
            int size = fields.size();
            int w = size < 256 ? 1 : size < 65536 ? 2 : 4;
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            out.write(w == 1 ? 0x48 : w == 2 ? 0x49 : 0x4a);
            le(out, ends.size(), w);
            for (int e : ends) {
                le(out, e, w);
            }
            byte[] x = fields.toByteArray();
            out.write(x, 0, x.length);
            return out.toByteArray();
        }

        private static void value(ByteArrayOutputStream out, Object v, int level, boolean limits) {
            if (v instanceof Obj) {
                byte[] x = object((Obj) v, level + 1, limits);
                out.write(x, 0, x.length);
            } else if (v instanceof Arr) {
                if (level + 1 > 16) {
                    throw new Refused("depth");
                }
                out.write(0x42);
                for (Object e : ((Arr) v).elements) {
                    value(out, e, level + 1, limits);
                }
                out.write(0x43);
            } else if (v instanceof Boolean) {
                out.write((Boolean) v ? 0x44 : 0x45);
            } else if (v instanceof Long) {
                binsonInteger(out, 0x10, (Long) v);
            } else if (v instanceof Dbl) {
                long bits = ((Dbl) v).bits;
                out.write(0x46);
                le(out, Double.isNaN(Double.longBitsToDouble(bits)) ? NAN : bits, 8);
            } else if (v instanceof Str) {
                byte[] x = bytes(((Str) v).bytes);
                if (!wellFormed(x)) {
                    throw new Refused("utf8");
                }
                binsonInteger(out, 0x14, x.length);
                out.write(x, 0, x.length);
            } else {
                byte[] x = bytes(((Bin) v).bytes);
                binsonInteger(out, 0x18, x.length);
                out.write(x, 0, x.length);
            }
        }

        /** An integer, or a length, in Binson's fewest bytes, after its type byte. */
        static void binsonInteger(ByteArrayOutputStream out, int base, long x) {
            int size = fewest(x);
            out.write(base + (size == 1 ? 0 : size == 2 ? 1 : size == 4 ? 2 : 3));
            le(out, x, size);
        }

        static int fewest(long x) {
            if (x >= -128 && x <= 127) {
                return 1;
            } else if (x >= -32768 && x <= 32767) {
                return 2;
            } else if (x >= Integer.MIN_VALUE && x <= Integer.MAX_VALUE) {
                return 4;
            }
            return 8;
        }

        static void le(ByteArrayOutputStream out, long x, int size) {
            for (int k = 0; k < size; k++) {
                out.write((int) (x >>> (8 * k)) & 0xff);
            }
        }

        static boolean wellFormed(byte[] x) {
            try {
                StandardCharsets.UTF_8.newDecoder()
                        .onMalformedInput(CodingErrorAction.REPORT)
                        .onUnmappableCharacter(CodingErrorAction.REPORT)
                        .decode(ByteBuffer.wrap(x));
                return true;
            } catch (CharacterCodingException e) {
                return false;
            }
        }

        /** The value at a path of names in 'top' (020-07, section 8.1), or null if absent. */
        static Object lookup(Object top, List<byte[]> path) {
            Object v = top;
            for (byte[] name : path) {
                if (!(v instanceof Obj)) {
                    return null;
                }
                v = ((Obj) v).fields.get(chars(name));
                if (v == null) {
                    return null;
                }
            }
            return v;
        }
    }

    /** Reads a Binson object (BINSON-SPEC-1.1, sections 2 and 3), any NaN kept. */
    static final class BinsonReader {
        private final byte[] b;
        private int p;

        private BinsonReader(byte[] b) {
            this.b = b;
        }

        static Obj read(byte[] b) {
            BinsonReader r = new BinsonReader(b);
            Obj o = r.object(0);
            if (r.p != b.length) {
                throw new Refused("binson");
            }
            return o;
        }

        private int next() {
            if (p >= b.length) {
                throw new Refused("binson");
            }
            return b[p] & 0xff;
        }

        private Obj object(int depth) {
            if (next() != 0x40 || depth > 1000) {
                throw new Refused("binson");
            }
            p++;
            Obj o = new Obj();
            String previous = null;
            while (next() != 0x41) {
                if (next() < 0x14 || next() > 0x16) {
                    throw new Refused("binson");
                }
                String name = ((Str) scalar()).bytes;
                if (previous != null && previous.compareTo(name) >= 0) {
                    throw new Refused("binson");
                }
                o.fields.put(name, value(depth));
                previous = name;
            }
            p++;
            return o;
        }

        private Object value(int depth) {
            if (next() == 0x40) {
                return object(depth + 1);
            } else if (next() == 0x42) {
                if (depth > 1000) {
                    throw new Refused("binson");
                }
                p++;
                Arr a = new Arr();
                while (next() != 0x43) {
                    a.elements.add(value(depth + 1));
                }
                p++;
                return a;
            }
            return scalar();
        }

        private long number(int size) {
            if (size > b.length - p) {
                throw new Refused("binson");
            }
            long x = 0;
            for (int k = size - 1; k >= 0; k--) {
                x = (x << 8) | (b[p + k] & 0xff);
            }
            p += size;
            int shift = 64 - 8 * size;
            return (x << shift) >> shift;
        }

        private Object scalar() {
            int t = next();
            p++;
            if (t >= 0x10 && t <= 0x13 || t >= 0x14 && t <= 0x16 || t >= 0x18 && t <= 0x1a) {
                int size = 1 << (t & 3);
                long x = number(size);
                if (Ref.fewest(x) != size) {
                    throw new Refused("binson");
                }
                if (t <= 0x13) {
                    return x;
                }
                if (x < 0 || x > b.length - p) {
                    throw new Refused("binson");
                }
                String data = chars(Arrays.copyOfRange(b, p, p + (int) x));
                p += (int) x;
                return t <= 0x16 ? new Str(data) : new Bin(data);
            }
            switch (t) {
            case 0x44:
                return Boolean.TRUE;
            case 0x45:
                return Boolean.FALSE;
            case 0x46:
                return new Dbl(number(8));
            default:
                throw new Refused("binson");
            }
        }
    }

    // ======== The model of 020-07, section 3 ========
    //
    // An object is an Obj: a map whose keys are the names' bytes, one char a byte (ISO-8859-1),
    // so that its order is the names' order of unsigned bytes (020-07, section 2.3). An array
    // is an Arr, a boolean a Boolean, an integer a Long, a double a Dbl (its 64 bits), a string
    // a Str (its UTF-8 bytes), bytes a Bin.

    static final class Obj {
        final TreeMap<String, Object> fields = new TreeMap<>();

        public boolean equals(Object o) {
            return o instanceof Obj && ((Obj) o).fields.equals(fields);
        }

        public int hashCode() {
            return fields.hashCode();
        }

        public String toString() {
            StringBuilder s = new StringBuilder("{");
            for (Map.Entry<String, Object> e : fields.entrySet()) {
                s.append(s.length() > 1 ? "," : "").append(text(e.getKey())).append(':')
                        .append(e.getValue());
            }
            return s.append('}').toString();
        }
    }

    static final class Arr {
        final List<Object> elements = new ArrayList<>();

        public boolean equals(Object o) {
            return o instanceof Arr && ((Arr) o).elements.equals(elements);
        }

        public int hashCode() {
            return elements.hashCode();
        }

        public String toString() {
            StringBuilder s = new StringBuilder("[");
            for (Object e : elements) {
                s.append(s.length() > 1 ? "," : "").append(e);
            }
            return s.append(']').toString();
        }
    }

    static final class Dbl {
        final long bits;

        Dbl(long bits) {
            this.bits = bits;
        }

        public boolean equals(Object o) {
            return o instanceof Dbl && ((Dbl) o).bits == bits;
        }

        public int hashCode() {
            return Long.hashCode(bits);
        }

        public String toString() {
            return String.format("d%016x", bits);
        }
    }

    static final class Str {
        final String bytes;

        Str(String bytes) {
            this.bytes = bytes;
        }

        public boolean equals(Object o) {
            return o instanceof Str && ((Str) o).bytes.equals(bytes);
        }

        public int hashCode() {
            return bytes.hashCode();
        }

        public String toString() {
            return "s" + text(bytes);
        }
    }

    static final class Bin {
        final String bytes;

        Bin(String bytes) {
            this.bytes = bytes;
        }

        public boolean equals(Object o) {
            return o instanceof Bin && ((Bin) o).bytes.equals(bytes);
        }

        public int hashCode() {
            return bytes.hashCode();
        }

        public String toString() {
            return "b" + text(bytes);
        }
    }

    /** Bytes as a String, one char a byte. */
    static String chars(byte[] b) {
        return new String(b, StandardCharsets.ISO_8859_1);
    }

    static byte[] bytes(String chars) {
        return chars.getBytes(StandardCharsets.ISO_8859_1);
    }

    /** Bytes as VN text (020-07, section 13.1), cut after 100 bytes. */
    static String text(String chars) {
        boolean printable = chars.length() <= 100;
        for (int i = 0; i < chars.length() && printable; i++) {
            char c = chars.charAt(i);
            printable = c >= ' ' && c <= '~' && c != '"' && c != '\\';
        }
        if (printable) {
            return "\"" + chars + "\"";
        }
        byte[] b = bytes(chars);
        return "<" + StringUtil.toHex(b, 0, Math.min(100, b.length))
                + (b.length > 100 ? "...(" + b.length + " bytes)" : "") + ">";
    }

    static String pathText(List<byte[]> path) {
        StringBuilder s = new StringBuilder();
        for (byte[] name : path) {
            s.append(s.length() > 0 ? "." : "").append(text(chars(name)));
        }
        return s.toString();
    }

    /** The value with every NaN as the one pattern, as a writer stores it (020-07, R12). */
    static Object canon(Object v) {
        if (v instanceof Obj) {
            Obj o = new Obj();
            for (Map.Entry<String, Object> e : ((Obj) v).fields.entrySet()) {
                o.fields.put(e.getKey(), canon(e.getValue()));
            }
            return o;
        } else if (v instanceof Arr) {
            Arr a = new Arr();
            for (Object e : ((Arr) v).elements) {
                a.elements.add(canon(e));
            }
            return a;
        } else if (v instanceof Dbl && Double.isNaN(Double.longBitsToDouble(((Dbl) v).bits))) {
            return new Dbl(NAN);
        }
        return v;
    }

    /**
     * Paths to look up in 'o', at most about 'max': each name, at every level of nested
     * objects; absent names before, between and after them (a name and U+0000, a prefix,
     * U+0001, "~~", U+10FFFF); a path through a scalar or an array.
     */
    static List<List<byte[]>> paths(Obj o, int max) {
        List<List<byte[]>> out = new ArrayList<>();
        paths(o, new ArrayList<byte[]>(), out, max);
        return out;
    }

    private static final byte[][] ABSENT = {{1}, {'~', '~'},
            {(byte) 0xf4, (byte) 0x8f, (byte) 0xbf, (byte) 0xbf}};

    private static void paths(Obj o, List<byte[]> prefix, List<List<byte[]>> out, int max) {
        for (byte[] name : ABSENT) {
            out.add(with(prefix, name));
        }
        for (Map.Entry<String, Object> e : o.fields.entrySet()) {
            if (out.size() >= max) {
                return;
            }
            byte[] name = bytes(e.getKey());
            List<byte[]> path = with(prefix, name);
            out.add(path);
            out.add(with(prefix, Arrays.copyOf(name, name.length + 1)));
            if (name.length > 1) {
                out.add(with(prefix, Arrays.copyOf(name, name.length - 1)));
            }
            if (e.getValue() instanceof Obj) {
                paths((Obj) e.getValue(), path, out, max);
            } else {
                out.add(with(path, new byte[] {'x'}));
            }
        }
    }

    private static List<byte[]> with(List<byte[]> prefix, byte[] name) {
        List<byte[]> path = new ArrayList<>(prefix);
        path.add(name);
        return path;
    }

    // ======== Random values (H0a) ========

    /**
     * Random values of every type and edge: integers at the boundaries of every width,
     * doubles of every class (NaN with any payload, -0.0, the infinities, subnormals), strings
     * from U+0000 to U+10FFFF, lengths at 127/128 and 32,767/32,768, names of 1 to 255 bytes,
     * depth 1 to 16, objects of up to about 300 fields, and widths 1, 2 and 4.
     */
    static final class Gen {
        final Random r;
        private int containers;     // still to make in this value
        private int big;            // big strings or bytes still to make in this value

        private static final long[] INTEGERS = {0, 1, -1, 127, 128, -128, -129, 255, 256,
                32767, 32768, -32768, -32769, 65535, 65536, Integer.MAX_VALUE,
                Integer.MAX_VALUE + 1L, Integer.MIN_VALUE, Integer.MIN_VALUE - 1L,
                Long.MAX_VALUE, Long.MIN_VALUE};
        private static final int[] CHARS = {0, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xe000,
                0xfeff, 0xfffd, 0xffff, 0x10000, 0x10ffff};
        private static final int[] NAME_CHARS = {0, ' ', '.', ',', '"', '\\', '~', 0x7f, 0xe9,
                0x20ac, 0xffff, 0x1f600, 0x10ffff};
        private static final int[] BIG = {127, 128, 255, 256, 32767, 32768, 65530, 65536,
                70000};

        Gen(long seed) {
            r = new Random(seed);
        }

        Obj tree() {
            containers = r.nextInt(8) == 0 ? 60 : 12;
            big = r.nextInt(12) == 0 ? 1 : 0;
            return object(1, 1 + r.nextInt(ObjectFormat.MAX_LEVELS));
        }

        /** A small value to mutate: under 600 bytes. */
        Obj sample() {
            while (true) {
                containers = 5;
                big = 0;
                Obj o = object(1, 1 + r.nextInt(ObjectFormat.MAX_LEVELS));
                if (Ref.write(o, true).length < 600) {
                    return o;
                }
            }
        }

        /** An object at 'level', with a path of containers down to 'levels'. */
        private Obj object(int level, int levels) {
            Obj o = new Obj();
            if (level < levels) {
                o.fields.put(chars(name()), container(level, levels));
            }
            int n = r.nextInt(25) == 0 ? 250 + r.nextInt(60) : r.nextInt(6);
            for (int i = 0; i < n; i++) {
                o.fields.put(chars(name()), value(level, levels));
            }
            return o;
        }

        private Arr array(int level, int levels) {
            Arr a = new Arr();
            int n = r.nextInt(6);
            for (int i = 0; i < n; i++) {
                a.elements.add(value(level, levels));
            }
            if (level < levels) {
                a.elements.add(r.nextInt(a.elements.size() + 1), container(level, levels));
            }
            return a;
        }

        /** A container one level below 'level'. */
        private Object container(int level, int levels) {
            containers--;
            return r.nextBoolean() ? object(level + 1, levels) : array(level + 1, levels);
        }

        /** A value in a container at 'level'. */
        private Object value(int level, int levels) {
            int k = r.nextInt(12);
            if (k >= 10 && level < levels && containers > 0) {
                return container(level, levels);
            }
            switch (k % 10) {
            case 0: case 1:
                return integer();
            case 2: case 3:
                return new Dbl(doubleBits());
            case 4: case 5:
                return new Str(chars(string()));
            case 6: case 7:
                return new Bin(chars(byteArray()));
            default:
                return Boolean.valueOf(r.nextBoolean());
            }
        }

        private Long integer() {
            if (r.nextBoolean()) {
                long x = INTEGERS[r.nextInt(INTEGERS.length)];
                return x + (r.nextInt(4) == 0 ? r.nextInt(3) - 1 : 0);
            }
            return r.nextLong() >> r.nextInt(64);
        }

        private long doubleBits() {
            switch (r.nextInt(10)) {
            case 0:
                return r.nextBoolean() ? 0L : 0x8000000000000000L;
            case 1:
                return r.nextBoolean() ? 0x7ff0000000000000L : 0xfff0000000000000L;
            case 2:
                return NAN;
            case 3: {
                long payload = r.nextLong() & 0x000fffffffffffffL;
                return (r.nextBoolean() ? 0x7ff0000000000000L : 0xfff0000000000000L)
                        | (payload == 0 ? 1 : payload);
            }
            case 4:
                return r.nextLong() & 0x800fffffffffffffL;
            case 5:
                return Double.doubleToRawLongBits(r.nextInt(2001) / 8.0 - 125);
            default:
                return r.nextLong();
            }
        }

        private byte[] string() {
            if (big > 0 && r.nextInt(3) == 0) {
                big--;
                byte[] x = new byte[BIG[r.nextInt(BIG.length)]];
                Arrays.fill(x, (byte) ('a' + r.nextInt(26)));
                return x;
            }
            StringBuilder s = new StringBuilder();
            int n = r.nextInt(8);
            for (int i = 0; i < n; i++) {
                s.appendCodePoint(codePoint());
            }
            return s.toString().getBytes(StandardCharsets.UTF_8);
        }

        private int codePoint() {
            switch (r.nextInt(6)) {
            case 0:
                return r.nextInt(0x80);
            case 1:
                return 0x80 + r.nextInt(0x800 - 0x80);
            case 2: {
                int c = 0x800 + r.nextInt(0x10000 - 0x800 - 0x800);
                return c >= 0xd800 ? c + 0x800 : c;
            }
            case 3:
                return 0x10000 + r.nextInt(0x110000 - 0x10000);
            case 4:
                return CHARS[r.nextInt(CHARS.length)];
            default:
                return 'a' + r.nextInt(26);
            }
        }

        private byte[] byteArray() {
            byte[] x;
            if (big > 0 && r.nextInt(3) == 0) {
                big--;
                x = new byte[BIG[r.nextInt(BIG.length)]];
            } else {
                x = new byte[r.nextInt(9)];
            }
            r.nextBytes(x);
            return x;
        }

        /** A name of 1 to 255 bytes: mostly short, from few chars, so that names share
         * prefixes. */
        private byte[] name() {
            if (r.nextInt(40) == 0) {
                byte[] x = new byte[r.nextBoolean() ? 255 : 1 + r.nextInt(255)];
                Arrays.fill(x, (byte) ('a' + r.nextInt(3)));
                return x;
            }
            StringBuilder s = new StringBuilder();
            int n = 1 + r.nextInt(4);
            for (int i = 0; i < n; i++) {
                s.appendCodePoint(r.nextInt(4) == 0 ? NAME_CHARS[r.nextInt(NAME_CHARS.length)]
                        : 'a' + r.nextInt(6));
            }
            return s.toString().getBytes(StandardCharsets.UTF_8);
        }
    }

    // ======== The vectors file (020-07, section 13.1) ========

    static final class Record {
        final String kind, id;
        final Map<String, List<String>> attributes = new LinkedHashMap<>();

        Record(String kind, String id) {
            this.kind = kind;
            this.id = id;
        }

        boolean has(String key) {
            return attributes.containsKey(key);
        }

        List<String> all(String key) {
            List<String> values = attributes.get(key);
            return values == null ? new ArrayList<String>() : values;
        }

        String one(String key) {
            List<String> values = all(key);
            if (values.size() != 1) {
                throw new AssertionError(kind + " " + id + ": " + values.size() + " " + key);
            }
            return values.get(0);
        }
    }

    /** The records of doc-files/object-vectors.txt, beside this class in the jar. */
    static List<Record> readVectors() throws IOException {
        List<Record> records = new ArrayList<>();
        try (InputStream in = ObjectFormatTester.class.getResourceAsStream(
                "doc-files/object-vectors.txt")) {
            if (in == null) {
                throw new AssertionError("doc-files/object-vectors.txt not found beside "
                        + "ObjectFormatTester; build.sh copies it into the jar");
            }
            BufferedReader reader = new BufferedReader(new InputStreamReader(in,
                    StandardCharsets.US_ASCII));
            Record rec = null;
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.isEmpty() || line.startsWith("#")) {
                    rec = null;
                } else if (line.startsWith("  ")) {
                    if (rec == null) {
                        throw new AssertionError("an attribute outside a record: " + line);
                    }
                    int space = line.indexOf(' ', 2);
                    String key = space < 0 ? line.substring(2) : line.substring(2, space);
                    String rest = space < 0 ? "" : line.substring(space + 1);
                    rec.attributes.computeIfAbsent(key, k -> new ArrayList<String>()).add(rest);
                } else {
                    int space = line.indexOf(' ');
                    rec = new Record(line.substring(0, space), line.substring(space + 1));
                    records.add(rec);
                }
            }
        }
        return records;
    }

    /** HEX of 020-07, section 13.1: pairs of hex digits; (HH..*N) the bytes repeated N times. */
    static byte[] unhex(String t) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        int i = 0;
        while (i < t.length()) {
            if (t.charAt(i) == '(') {
                int star = t.indexOf('*', i);
                int close = t.indexOf(')', i);
                byte[] unit = unhex(t.substring(i + 1, star));
                int n = Integer.parseInt(t.substring(star + 1, close));
                for (int k = 0; k < n; k++) {
                    out.write(unit, 0, unit.length);
                }
                i = close + 1;
            } else {
                out.write(Integer.parseInt(t.substring(i, i + 2), 16));
                i += 2;
            }
        }
        return out.toByteArray();
    }

    /** VN, the value notation of 020-07, section 13.1, and the paths of lookups. */
    static final class Vn {
        final String t;
        int i;

        Vn(String t) {
            this.t = t;
        }

        static Object parse(String t) {
            Vn p = new Vn(t);
            Object v = p.value();
            if (p.i != t.length()) {
                throw new AssertionError("VN not ended at " + p.i + ": " + t);
            }
            return v;
        }

        /** NAMEs joined by '.', ended by a space. */
        List<byte[]> path() {
            List<byte[]> names = new ArrayList<>();
            while (true) {
                names.add(text());
                char c = t.charAt(i);
                if (c == ' ') {
                    return names;
                }
                expect('.');
            }
        }

        private void expect(char c) {
            if (t.charAt(i) != c) {
                throw new AssertionError("VN: '" + c + "' expected at " + i + ": " + t);
            }
            i++;
        }

        /** A NAME or TEXT: "..." with \" \\ \xHH, or <HEX>. */
        byte[] text() {
            if (t.charAt(i) == '<') {
                int close = t.indexOf('>', i);
                byte[] b = unhex(t.substring(i + 1, close));
                i = close + 1;
                return b;
            }
            expect('"');
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            while (true) {
                char c = t.charAt(i++);
                if (c == '"') {
                    return out.toByteArray();
                } else if (c == '\\') {
                    char d = t.charAt(i++);
                    if (d == 'x') {
                        out.write(Integer.parseInt(t.substring(i, i + 2), 16));
                        i += 2;
                    } else {
                        out.write(d);
                    }
                } else {
                    out.write(c);
                }
            }
        }

        Object value() {
            char c = t.charAt(i);
            if (c == '{') {
                i++;
                Obj o = new Obj();
                if (t.charAt(i) == '}') {
                    i++;
                    return o;
                }
                while (true) {
                    String name = chars(text());
                    expect(':');
                    if (o.fields.put(name, value()) != null) {
                        throw new AssertionError("VN: a name twice: " + t);
                    }
                    if (t.charAt(i) == ',') {
                        i++;
                    } else {
                        expect('}');
                        return o;
                    }
                }
            } else if (c == '[') {
                i++;
                Arr a = new Arr();
                if (t.charAt(i) == ']') {
                    i++;
                    return a;
                }
                while (true) {
                    a.elements.add(value());
                    if (t.charAt(i) == ',') {
                        i++;
                    } else {
                        expect(']');
                        return a;
                    }
                }
            } else if (t.startsWith("true", i)) {
                i += 4;
                return Boolean.TRUE;
            } else if (t.startsWith("false", i)) {
                i += 5;
                return Boolean.FALSE;
            } else if (c == 'i') {
                int j = ++i;
                if (t.charAt(i) == '-') {
                    i++;
                }
                while (i < t.length() && Character.isDigit(t.charAt(i))) {
                    i++;
                }
                return Long.parseLong(t.substring(j, i));
            } else if (c == 'd') {
                i += 17;
                return new Dbl(Long.parseUnsignedLong(t.substring(i - 16, i), 16));
            } else if (c == 's') {
                i++;
                return new Str(chars(text()));
            } else if (c == 'b') {
                i++;
                return new Bin(chars(text()));
            }
            throw new AssertionError("VN: a value expected at " + i + ": " + t);
        }
    }

    // ======== Helpers ========

    /** The condition's code at the start of a refusal's message: "past-end" of "past-end: ...". */
    static String code(RuntimeException e) {
        String m = String.valueOf(e.getMessage());
        int colon = m.indexOf(':');
        return colon < 0 ? m : m.substring(0, colon);
    }

    static void assertRefused(String what, String code, byte[] b) {
        String got = refusal(b, what);
        if (got == null) {
            throw new AssertionError(what + ": accepted");
        }
        Assert.assertEquals(what, code, got);
    }

    static void assertRefusedArg(String what, String code, Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            Assert.assertEquals(what + ": " + e.getMessage(), code, code(e));
            return;
        }
        throw new AssertionError(what + ": not refused");
    }

    static void assertBytes(String about, byte[] expected, byte[] actual) {
        if (!Arrays.equals(expected, actual)) {
            throw new AssertionError(about + ": expected " + text(chars(expected)) + ", got "
                    + text(chars(actual)));
        }
    }

    static String sha256(byte[] b) {
        try {
            return StringUtil.toHex(MessageDigest.getInstance("SHA-256").digest(b));
        } catch (NoSuchAlgorithmException e) {
            throw new AssertionError(e);
        }
    }
}
