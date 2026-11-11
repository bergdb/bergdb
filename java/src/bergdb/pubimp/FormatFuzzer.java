package bergdb.pubimp;

import java.io.ByteArrayOutputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.management.ManagementFactory;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import bergdb.common.StringUtil;
import bergdb.nanotest.Nano;
import bergdb.nanotest.Platform;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.DbObject;
import bergdb.pub.DbValue;
import bergdb.pub.util.BadFormatException;
import bergdb.pubimp.ObjectFormatTester.Arr;
import bergdb.pubimp.ObjectFormatTester.Bin;
import bergdb.pubimp.ObjectFormatTester.Dbl;
import bergdb.pubimp.ObjectFormatTester.Gen;
import bergdb.pubimp.ObjectFormatTester.Obj;
import bergdb.pubimp.ObjectFormatTester.Ref;
import bergdb.pubimp.ObjectFormatTester.Refused;
import bergdb.pubimp.ObjectFormatTester.Str;

/**
 * A fuzzer of the readers of bytes that 2026.4 added (bergdb 020-16), each with oracles from
 * its spec:
 * <ul>
 * <li>objects: ObjectFormat's full check and lookup against bergdb 020-07. The inputs are
 *     valid values (ObjectFormatTester.Gen), values written with exactly one rule broken by
 *     a deviant writer (so the refusal's code is known), the counts, ends, lengths, integers
 *     and type bytes of valid values set to extremes, bytes changed, inserted, deleted,
 *     repeated and swapped, two values crossed, deep nesting and huge counts. The oracles: a
 *     verdict or a BadFormatException that names a code of 020-07, section 7.2, never
 *     another exception, in a time and with an allocation not sized by a length read; the
 *     same verdict as Ref, ObjectFormatTester's second codec; an accepted value written
 *     again to the same bytes by both writers (one object, one byte string); each lookup by
 *     the binary search equal to a linear scan of the fields and to the decoded value;
 *     DbObject's getters equal to the decoded value. Optionally, a corpus of the inputs and
 *     verdicts for the 020-07 programs written apart (bench 006-15/020-07: check.py, F2).</li>
 * <li>keys: IndexKeys and IndexDefinition against bergdb 020-10, sections 3.3, 4.1, 4.2 and
 *     4.4: each level's encoding keeps the values' order and decodes to the value; no
 *     level's encoding is a proper prefix of another's; the prefix and succ rules; an
 *     entry's, a marker's or a definition's key or bytes, changed, is parsed to the same
 *     bytes again or refused with InternalDataException, nothing else; the index function
 *     against a reference.</li>
 * <li>data: DataObjects' get (bergdb 020-09, section 5): random stored objects into Data
 *     Object classes with a field of every type of the closed list: never a throw for the
 *     data, and the value of a reference written from 020-09's table.</li>
 * <li>kinds: what a stored value is (020-07, section 9; 020-10, section 3.3), through a
 *     database: Strings, byte[]s and objects whose bytes look like the other kinds, read by
 *     every get, every listing and an index, against the rules of Connection.get's
 *     Javadoc.</li>
 * <li>starts: what a start reads of the indexes (020-10, section 4.5): one change of the
 *     internal keys under /#i/ written through the Core, then a start, which goes on or
 *     refuses the database as a reference says.</li>
 * <li>guesses: the smaller readers, ObjectFormat.isFormat1 (the format-1 guess),
 *     StringUtil.isWellFormedUtf8 and ObjectFormat.utf8Fault, Keys.bkey2ikeyOrNull, each
 *     against a reference written from its Javadoc.</li>
 * </ul>
 *
 * <p>Each iteration has its own Random from the seed and its number, so a failure is
 * repeated alone: FormatFuzzer AREA SEED SECONDS ITERATION. java/stress/fuzz.sh runs the
 * areas for minutes, new seeds each day; the unit group runs each for a few thousand
 * iterations (40 databases for kinds, 200 starts), about 2 seconds in all. Planted faults,
 * one at a time in ObjectFormat, IndexKeys, IndexDefinition, DataObjects, Entries,
 * KvToObjectImp, RwEnvironmentImp, UseIndexBuilderImp and IndexManager (21 of them, 2
 * equivalent), were found by their area within 10 seconds (bergdb 020-16).</p>
 *
 * @author Frans Lundberg
 */
public final class FormatFuzzer {

    /** The condition codes of 020-07, section 7.2. */
    static final Set<String> CODES = new HashSet<>(Arrays.asList("past-end", "header",
            "format-1", "trailing", "type", "width", "fields", "ends", "field-size",
            "name-length", "utf8", "order", "duplicate", "integer-size", "length", "nan",
            "depth", "size"));

    /** The expected verdict of a valid value. */
    static final Set<String> OK = Collections.singleton("ok");

    private final long seed;
    private PrintStream corpus;         // the inputs for the programs written apart, or null
    private int corpusEvery = 1;
    Stats stats = new Stats();

    FormatFuzzer(long seed) {
        this.seed = seed;
    }

    /** A failure of an oracle; the message says how to repeat it. */
    static final class Failure extends RuntimeException {
        private static final long serialVersionUID = 1L;

        Failure(String message, Throwable cause) {
            super(message, cause);
        }
    }

    static final class Stats {
        long iterations, inputs, accepted, refused, refusedOther, lookups, expected,
                maxNanos, maxAlloc, corpus;
        final long[] byCode = new long[20];
        final java.util.TreeMap<String, Long> counts = new java.util.TreeMap<>();

        void count(String what) {
            counts.merge(what, 1L, Long::sum);
        }

        public String toString() {
            return iterations + " iterations, " + inputs + " inputs (" + accepted + " accepted, "
                    + refused + " refused, " + refusedOther + " by Ref for another code, "
                    + expected + " with a known verdict), " + lookups + " lookups, max "
                    + maxNanos / 1000 + " us and " + maxAlloc + " bytes a check; " + counts;
        }
    }

    /** The Random of iteration i: from the seed and i alone. */
    static Random random(long seed, long i) {
        long x = seed * 0x9E3779B97F4A7C15L + i * 0xC2B2AE3D27D4EB4FL;
        x ^= x >>> 31;
        return new Random(x);
    }

    // ======== Area 1: the object format (020-07) ========

    /** One iteration of area 1. */
    void objectsOne(long i) {
        Random r = random(seed, i);
        Gen g = new Gen(r.nextLong());
        String where = "objects seed " + seed + " iteration " + i;
        stats.iterations++;
        int s = r.nextInt(100);
        if (s < 22) {
            Obj o = r.nextInt(4) == 0 ? g.tree() : g.sample();
            byte[] base = Ref.write(o, true);
            checkObject(mutateBytes(base, r), null, o, r, where + " (bytes)");
        } else if (s < 47) {
            Obj o = r.nextInt(5) == 0 ? g.tree() : g.sample();
            Deviant d = Deviant.random(o, r);
            if (d == null) {
                return;
            }
            byte[] m = d.stored(o);
            checkObject(m, d.expected, o, r, where + " (deviant " + Deviant.KINDS[d.kind] + ")");
        } else if (s < 62) {
            Obj o = r.nextInt(5) == 0 ? g.tree() : g.sample();
            byte[] base = Ref.write(o, true);
            checkObject(extreme(base, r), null, o, r, where + " (extreme)");
        } else if (s < 72) {
            Obj o = r.nextInt(3) == 0 ? g.tree() : g.sample();
            checkObject(Ref.write(o, true), OK, o, r, where + " (valid)");
        } else if (s < 82) {
            Obj a = g.sample();
            Obj b = g.sample();
            checkObject(cross(Ref.write(a, true), Ref.write(b, true), r), null, a, r,
                    where + " (cross)");
        } else if (s < 90) {
            Nested n = Nested.random(r);
            checkObject(n.bytes, n.expected, null, r, where + " (nested " + n.what + ")");
        } else {
            checkObject(headed(r), null, null, r, where + " (random)");
        }
    }

    /**
     * The oracles of area 1 on one byte string 'm'. 'expect' is null (any verdict, Ref's), OK,
     * or the codes a refusal may name; 'basis' the value 'm' was made from, for its lookup
     * paths, or null.
     */
    void checkObject(byte[] m, Set<String> expect, Obj basis, Random r, String where) {
        stats.inputs++;
        // (a) The full check: a verdict, or a refusal that names a code; nothing else.
        String code = verdict(m, where);
        measure(m, code == null, where);
        // (b) Ref, the second codec, and the expected verdict.
        String refCode;
        Obj refValue = null;
        try {
            refValue = Ref.read(m);
            refCode = null;
        } catch (Refused e) {
            refCode = e.code;
        } catch (Throwable e) {
            throw fail(where, "Ref threw " + e, m, e);
        }
        if ((code == null) != (refCode == null)) {
            throw fail(where, "the full check says " + (code == null ? "ok" : code) + ", Ref "
                    + (refCode == null ? "ok" : refCode), m, null);
        }
        if (expect != null) {
            stats.expected++;
            if (expect == OK ? code != null : code == null || !expect.contains(code)
                    || !expect.contains(refCode)) {
                throw fail(where, "expected " + expect + ", the full check says "
                        + (code == null ? "ok" : code) + ", Ref " + refCode, m, null);
            }
        }
        if (code != null && !code.equals(refCode)) {
            stats.refusedOther++;
        }
        Assert(ObjectFormat.isStoredObject(m) == (code == null), where, "isStoredObject", m);

        List<List<byte[]>> paths = new ArrayList<>();
        if (basis != null) {
            paths.addAll(ObjectFormatTester.paths(basis, 40));
        }
        if (refValue != null) {
            paths.addAll(ObjectFormatTester.paths(refValue, 40));
        }
        paths.add(Collections.singletonList(randomName(r)));

        if (code == null) {
            stats.accepted++;
            accepted(m, refValue, paths, r, where);
        } else {
            stats.refused++;
            stats.count(code);
            refusedLookups(m, paths, r, where);
            try {
                new DbObject(m);
                throw fail(where, "new DbObject took bytes the full check refuses", m, null);
            } catch (BadFormatException e) {
                Assert(code.equals(codeOf(e)), where, "DbObject's code " + codeOf(e), m);
            }
        }
        if (corpus != null && (stats.inputs % corpusEvery == 0 || expect != null)) {
            writeCorpus(m, code, expect, refValue, paths);
        }
    }

    /** The full check's verdict: null, or the code of its refusal, checked. */
    String verdict(byte[] m, String where) {
        try {
            ObjectFormat.checkStored(m);
            return null;
        } catch (BadFormatException e) {
            String message = e.getMessage();
            String code = codeOf(e);
            if (!CODES.contains(code) || !message.startsWith(code + ": ")
                    || !message.endsWith("(bergdb 020-07, section 7.2)")) {
                throw fail(where, "a refusal without a code of 020-07, section 7.2: " + message,
                        m, e);
            }
            return code;
        } catch (Throwable e) {
            throw fail(where, "the full check threw " + e, m, e);
        }
    }

    static String codeOf(BadFormatException e) {
        String m = String.valueOf(e.getMessage());
        int colon = m.indexOf(':');
        return colon < 0 ? m : m.substring(0, colon);
    }

    /**
     * The JVM's threads, for the allocation of the full check; null on Android, which has no
     * java.lang.management: there the fuzzing runs, but no allocation is measured, and the
     * bound on it is checked on a JVM only (bergdb 006-18-03).
     */
    private static final java.lang.management.ThreadMXBean THREADS =
            Platform.android() ? null : ManagementFactory.getThreadMXBean();

    static long allocated() {
        return THREADS == null ? 0
                : ((com.sun.management.ThreadMXBean) THREADS).getCurrentThreadAllocatedBytes();
    }

    /**
     * The full check's time and allocation on 'm': within a bound linear in its length, and
     * no allocation but a refusal's (020-07, section 7.1: nothing allocated for a count or a
     * length read). Measured again, the least of three, before a time is called too long.
     */
    void measure(byte[] m, boolean accepted, String where) {
        long best = Long.MAX_VALUE;
        long alloc = Long.MAX_VALUE;
        for (int k = 0; k < 3; k++) {
            long a0 = allocated();
            long t0 = System.nanoTime();
            try {
                ObjectFormat.checkStored(m);
            } catch (BadFormatException e) {
                // the verdict is checked by verdict()
            }
            long t = System.nanoTime() - t0;
            alloc = Math.min(alloc, allocated() - a0);
            best = Math.min(best, t);
            if (best < 20_000_000L + 200L * m.length) {
                break;
            }
        }
        stats.maxNanos = Math.max(stats.maxNanos, best);
        stats.maxAlloc = Math.max(stats.maxAlloc, alloc);
        if (best >= 20_000_000L + 200L * m.length) {
            throw fail(where, "the full check took " + best / 1000 + " us for " + m.length
                    + " bytes", m, null);
        }
        if (alloc > (accepted ? 4096 : 65536)) {
            throw fail(where, "the full check allocated " + alloc + " bytes for " + m.length
                    + " bytes", m, null);
        }
    }

    /**
     * An accepted value: decoded as Ref decodes it; written again to the same bytes by both
     * writers; each lookup by the binary search as a linear scan of the fields and as the
     * decoded value; DbObject's getters as the decoded value.
     */
    void accepted(byte[] m, Obj refValue, List<List<byte[]>> paths, Random r, String where) {
        Obj decoded;
        try {
            decoded = ObjectFormatTester.codecDecode(m);
        } catch (Throwable e) {
            throw fail(where, "the decoder threw " + e, m, e);
        }
        Assert(decoded.equals(refValue), where, "decoded " + decoded + ", Ref " + refValue, m);
        Assert(Arrays.equals(ObjectFormatTester.codecWrite(decoded), m), where,
                "not canonical: written again by the codec to other bytes", m);
        Assert(Arrays.equals(Ref.write(decoded, true), m), where,
                "not canonical: written again by Ref to other bytes", m);
        Assert(!ObjectFormat.isFormat1(m), where, "isFormat1 of a format-2 object", m);
        for (List<byte[]> path : paths) {
            stats.lookups++;
            Object got;
            try {
                got = ObjectFormatTester.codecLookup(m, path);
            } catch (Throwable e) {
                throw fail(where, "lookup " + ObjectFormatTester.pathText(path) + " threw " + e,
                        m, e);
            }
            Object want = Ref.lookup(decoded, path);
            Assert(want == null ? got == null : want.equals(got), where, "lookup "
                    + ObjectFormatTester.pathText(path) + ": " + got + ", the value has "
                    + want, m);
            int found = findPath(m, path);
            int scanned = scanPath(m, path);
            Assert(found == scanned, where, "lookup " + ObjectFormatTester.pathText(path)
                    + ": the binary search finds " + found + ", a linear scan " + scanned, m);
        }
        dbObject(m, decoded, where);
    }

    /** The value's start at a path by ObjectFormat.find, or -1. */
    static int findPath(byte[] b, List<byte[]> path) {
        int p = 1;
        int end = b.length;
        for (int k = 0; ; k++) {
            int q = ObjectFormat.find(b, p, end, path.get(k));
            if (q < 0 || k == path.size() - 1) {
                return q;
            }
            if (!ObjectFormat.isObjectAt(b, q)) {
                return -1;
            }
            p = q;
            end = ObjectFormat.objectEnd(b, q);
        }
    }

    /** The value's start at a path by a linear scan of each object's fields, or -1. */
    static int scanPath(byte[] b, List<byte[]> path) {
        int p = 1;
        for (int k = 0; ; k++) {
            int q = -1;
            int n = ObjectFormat.countAt(b, p);
            byte[] name = path.get(k);
            for (int i = 0; i < n; i++) {
                int f = ObjectFormat.fieldAt(b, p, i);
                int length = b[f] & 0xff;
                if (Arrays.equals(b, f + 1, f + 1 + length, name, 0, name.length)) {
                    q = f + 1 + length;
                    break;
                }
            }
            if (q < 0 || k == path.size() - 1) {
                return q;
            }
            if (!ObjectFormat.isObjectAt(b, q)) {
                return -1;
            }
            p = q;
        }
    }

    /** DbObject's reading of accepted bytes, field by field, against the decoded value. */
    void dbObject(byte[] m, Obj decoded, String where) {
        DbObject d = new DbObject(m);
        Assert(Arrays.equals(d.getBytes(), m), where, "DbObject.getBytes", m);
        Assert(d.getFieldCount() == decoded.fields.size(), where, "getFieldCount", m);
        for (Map.Entry<String, Object> e : decoded.fields.entrySet()) {
            byte[] nameBytes = ObjectFormatTester.bytes(e.getKey());
            String name = new String(nameBytes, StandardCharsets.UTF_8);
            Object v = e.getValue();
            char type = typeOf(v);
            Assert(d.getType(name) == type, where, "getType(" + name + ") " + d.getType(name)
                    + ", not " + type, m);
            Assert(d.has(name, type), where, "has(" + name + ")", m);
            DbValue dv = d.getDbValue(name);
            int p = ObjectFormat.find(m, 1, m.length, nameBytes);
            int end = ObjectFormat.valueEnd(m, p);
            Assert(dv.getByteSize() == end - p, where, "getDbValue(" + name + ").getByteSize()",
                    m);
            byte[] w = new byte[end - p];
            Assert(dv.write(w, 0) == w.length && Arrays.equals(w, 0, w.length, m, p, end),
                    where, "getDbValue(" + name + ").write()", m);
            switch (type) {
            case 'l': {
                long x = (Long) v;
                Assert(d.getLong(name) == x, where, "getLong(" + name + ")", m);
                Assert(d.getInt(name) == (x == (int) x ? (int) x : 0), where, "getInt", m);
                Assert(d.has(name, DbObject.INT) == (x == (int) x), where, "has INT", m);
                break;
            }
            case 'd':
                Assert(Double.doubleToRawLongBits(d.getDouble(name)) == ((Dbl) v).bits, where,
                        "getDouble(" + name + ")", m);
                break;
            case 's':
                Assert(Arrays.equals(d.getString(name).getBytes(StandardCharsets.UTF_8),
                        ObjectFormatTester.bytes(((Str) v).bytes)), where, "getString", m);
                break;
            case 'b':
                Assert(Arrays.equals(d.getByteArray(name),
                        ObjectFormatTester.bytes(((Bin) v).bytes)), where, "getByteArray", m);
                break;
            case 'n':
                Assert(d.getBoolean(name) == (Boolean) v, where, "getBoolean", m);
                break;
            case 'o':
                Assert(Arrays.equals(d.getObject(name).getBytes(), Ref.write((Obj) v, false)),
                        where, "getObject(" + name + ")", m);
                break;
            case 'a': {
                bergdb.pub.DbArray a = d.getArray(name);
                List<Object> elements = ((Arr) v).elements;
                Assert(a.getSize() == elements.size(), where, "getArray(" + name
                        + ").getSize()", m);
                int k = 0;
                for (DbValue el : a) {
                    byte[] x = new byte[el.getByteSize()];
                    el.write(x, 0);
                    Assert(el.getType() == typeOf(elements.get(k)) && Arrays.equals(x,
                            valueBytes(elements.get(k))), where, "getArray(" + name
                            + ") element " + k, m);
                    k++;
                }
                Assert(k == elements.size(), where, "getArray(" + name + "): " + k
                        + " elements iterated", m);
                break;
            }
            default:
                throw new AssertionError(type);
            }
        }
        // The Builder, given the values read, writes the same bytes (020-07, section 6.1).
        DbObject.Builder builder = new DbObject.Builder();
        for (String key : decoded.fields.keySet()) {
            String name = new String(ObjectFormatTester.bytes(key), StandardCharsets.UTF_8);
            builder.addDbValue(name, d.getDbValue(name));
        }
        Assert(Arrays.equals(builder.build().getBytes(), m), where,
                "the Builder of the values read writes other bytes", m);
        // Nested paths: has() and the typed getters of a path, as the value at it.
        for (List<byte[]> path : ObjectFormatTester.paths(decoded, 30)) {
            if (path.size() < 2) {
                continue;
            }
            String[] parts = new String[path.size()];
            for (int k = 0; k < parts.length; k++) {
                parts[k] = new String(path.get(k), StandardCharsets.UTF_8);
                if (!Arrays.equals(parts[k].getBytes(StandardCharsets.UTF_8), path.get(k))) {
                    parts = null;       // an ill-formed name: no String holds it
                    break;
                }
            }
            if (parts == null) {
                continue;
            }
            Object v = Ref.lookup(decoded, path);
            for (char t : new char[] {'l', 'd', 's', 'n', 'o', 'a', 'b'}) {
                Assert(d.has(parts, t) == (v != null && typeOf(v) == t), where, "has("
                        + ObjectFormatTester.pathText(path) + ", " + t + ")", m);
            }
            Assert(d.getLong(parts) == (v instanceof Long ? (Long) v : 0), where, "getLong("
                    + ObjectFormatTester.pathText(path) + ")", m);
            Assert(Double.doubleToRawLongBits(d.getDouble(parts)) == (v instanceof Dbl
                    ? ((Dbl) v).bits : 0), where, "getDouble(" + ObjectFormatTester.pathText(
                    path) + ")", m);
            String str = d.getString(parts);
            Assert(v instanceof Str ? str != null && Arrays.equals(str.getBytes(
                    StandardCharsets.UTF_8), ObjectFormatTester.bytes(((Str) v).bytes))
                    : str == null, where, "getString(" + ObjectFormatTester.pathText(path)
                    + ")", m);
        }
    }
    
    /** The bytes of a value of the model, as a conforming writer writes it. */
    static byte[] valueBytes(Object v) {
        Obj o = new Obj();
        o.fields.put("v", v);
        byte[] b = Ref.write(o, false);
        return Arrays.copyOfRange(b, ObjectFormat.find(b, 1, b.length, new byte[] {'v'}),
                b.length);
    }

    static char typeOf(Object v) {
        return v instanceof Long ? 'l' : v instanceof Dbl ? 'd' : v instanceof Str ? 's'
                : v instanceof Bin ? 'b' : v instanceof Boolean ? 'n' : v instanceof Obj ? 'o'
                : 'a';
    }

    /**
     * Lookups on refused bytes (020-07, section 7.4): a value, absent or a BadFormatException,
     * never another exception; a value found lies in the stored value.
     */
    void refusedLookups(byte[] m, List<List<byte[]>> paths, Random r, String where) {
        for (List<byte[]> path : paths) {
            stats.lookups++;
            try {
                ObjectFormatTester.codecLookup(m, path);
            } catch (BadFormatException e) {
                continue;
            } catch (Throwable e) {
                throw fail(where, "lookup " + ObjectFormatTester.pathText(path)
                        + " on refused bytes threw " + e, m, e);
            }
            if (m.length >= 2 && (m[0] & 0xff) == ObjectFormat.HEADER) {
                try {
                    int q = ObjectFormat.find(m, 1, m.length, path.get(0));
                    Assert(q == -1 || (q > 1 && q < m.length), where, "find gave " + q, m);
                } catch (BadFormatException e) {
                    // allowed
                }
            }
        }
    }

    /** A random name: a few bytes, sometimes ill-formed. */
    static byte[] randomName(Random r) {
        byte[] x = new byte[1 + r.nextInt(4)];
        for (int k = 0; k < x.length; k++) {
            x[k] = (byte) (r.nextInt(3) == 0 ? r.nextInt(256) : 'a' + r.nextInt(6));
        }
        return x;
    }

    // ======== Area 1's inputs ========

    /** 1 to 8 random changes of bytes: set, flip, insert, delete, repeat, swap, cut, append. */
    static byte[] mutateBytes(byte[] base, Random r) {
        byte[] m = base.clone();
        int changes = 1 + (r.nextInt(3) == 0 ? r.nextInt(8) : 0);
        for (int c = 0; c < changes; c++) {
            if (m.length == 0) {
                m = new byte[] {(byte) 0x82};
            }
            int p = r.nextInt(m.length);
            switch (r.nextInt(9)) {
            case 0:
                m[p] = (byte) SPECIAL[r.nextInt(SPECIAL.length)];
                break;
            case 1:
                m[p] ^= (byte) (1 << r.nextInt(8));
                break;
            case 2: {
                byte[] x = new byte[1 + r.nextInt(16)];
                if (r.nextBoolean()) {
                    r.nextBytes(x);
                } else {
                    int from = r.nextInt(m.length);
                    for (int k = 0; k < x.length; k++) {
                        x[k] = m[(from + k) % m.length];
                    }
                }
                m = insert(m, p, x);
                break;
            }
            case 3: {
                int n = Math.min(m.length - p, 1 + r.nextInt(16));
                m = delete(m, p, n);
                break;
            }
            case 4: {
                int n = Math.min(m.length - p, 1 + r.nextInt(32));
                m = insert(m, p, Arrays.copyOfRange(m, p, p + n));
                break;
            }
            case 5: {
                int q = r.nextInt(m.length);
                int n = Math.min(Math.min(m.length - p, m.length - q), 1 + r.nextInt(8));
                byte[] a = Arrays.copyOfRange(m, p, p + n);
                byte[] b = Arrays.copyOfRange(m, q, q + n);
                System.arraycopy(b, 0, m, p, n);
                System.arraycopy(a, 0, m, q, n);
                break;
            }
            case 6:
                m = Arrays.copyOf(m, p);
                break;
            case 7: {
                byte[] x = new byte[1 + r.nextInt(4)];
                r.nextBytes(x);
                m = insert(m, m.length, x);
                break;
            }
            default:
                m[p] = (byte) r.nextInt(256);
                break;
            }
        }
        return m;
    }

    /** Bytes that matter: type bytes, the header, ends of ranges. */
    static final int[] SPECIAL = {0x00, 0x01, 0x02, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,
            0x17, 0x18, 0x19, 0x1a, 0x1b, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,
            0x49, 0x4a, 0x4b, 0x7f, 0x80, 0x81, 0x82, 0x83, 0xbf, 0xc0, 0xc2, 0xe0, 0xed, 0xef,
            0xf0, 0xf4, 0xf5, 0xfe, 0xff};

    static byte[] insert(byte[] m, int p, byte[] x) {
        byte[] b = new byte[m.length + x.length];
        System.arraycopy(m, 0, b, 0, p);
        System.arraycopy(x, 0, b, p, x.length);
        System.arraycopy(m, p, b, p + x.length, m.length - p);
        return b;
    }

    static byte[] delete(byte[] m, int p, int n) {
        byte[] b = new byte[m.length - n];
        System.arraycopy(m, 0, b, 0, p);
        System.arraycopy(m, p + n, b, p, m.length - p - n);
        return b;
    }

    /** The kinds of the numbers in a stored value, which extreme() changes. */
    static final int S_TYPE = 0, S_COUNT = 1, S_END = 2, S_NAME_LENGTH = 3, S_LENGTH = 4,
            S_INTEGER = 5, S_DOUBLE = 6;

    /** The numbers of checked bytes: {position, size, kind} for each. */
    static void spots(byte[] b, int p, List<int[]> out) {
        int t = b[p] & 0xff;
        out.add(new int[] {p, 1, S_TYPE});
        if (ObjectFormat.isObjectType(t)) {
            int w = ObjectFormat.widthAt(b, p);
            int n = ObjectFormat.countAt(b, p);
            out.add(new int[] {p + 1, w, S_COUNT});
            for (int i = 0; i < n; i++) {
                out.add(new int[] {p + 1 + w + i * w, w, S_END});
                int f = ObjectFormat.fieldAt(b, p, i);
                out.add(new int[] {f, 1, S_NAME_LENGTH});
                spots(b, f + 1 + (b[f] & 0xff), out);
            }
        } else if (t == ObjectFormat.ARRAY_START) {
            int q = p + 1;
            while ((b[q] & 0xff) != ObjectFormat.ARRAY_END) {
                spots(b, q, out);
                q = ObjectFormat.valueEnd(b, q);
            }
            out.add(new int[] {q, 1, S_TYPE});
        } else if (t >= 0x10 && t <= 0x13) {
            out.add(new int[] {p + 1, 1 << (t - 0x10), S_INTEGER});
        } else if ((t >= 0x14 && t <= 0x16) || (t >= 0x18 && t <= 0x1a)) {
            out.add(new int[] {p + 1, 1 << (t & 3), S_LENGTH});
        } else if (t == 0x46) {
            out.add(new int[] {p + 1, 8, S_DOUBLE});
        }
    }

    /** One number of a valid value set to an extreme of its size, or near its value. */
    static byte[] extreme(byte[] base, Random r) {
        List<int[]> spots = new ArrayList<>();
        spots(base, 1, spots);
        byte[] m = base.clone();
        int changes = r.nextInt(4) == 0 ? 2 : 1;
        for (int c = 0; c < changes; c++) {
            int[] s = spots.get(r.nextInt(spots.size()));
            int p = s[0];
            int size = s[1];
            long old = 0;
            for (int k = size - 1; k >= 0; k--) {
                old = (old << 8) | (m[p + k] & 0xff);
            }
            long x;
            if (s[2] == S_TYPE) {
                x = SPECIAL[r.nextInt(SPECIAL.length)];
            } else if (s[2] == S_DOUBLE && r.nextBoolean()) {
                long[] d = {0x7ff8000000000001L, 0xfff8000000000000L, 0x7ff0000000000001L,
                        0x7fffffffffffffffL, 0xffffffffffffffffL, 0x8000000000000000L,
                        0x7ff0000000000000L, 0x7ff8000000000000L};
                x = d[r.nextInt(d.length)];
            } else {
                long[] e = {0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff, 0x10000,
                        0x7fffffffL, 0x80000000L, 0xffffffffL, 0x7ffffff7L, old + 1, old - 1,
                        old + 2, old - 2, r.nextLong(), -1, Long.MAX_VALUE, Long.MIN_VALUE};
                x = e[r.nextInt(e.length)];
            }
            for (int k = 0; k < size; k++) {
                m[p + k] = (byte) (x >>> (8 * k));
            }
        }
        return m;
    }

    /** A cut of one value and a piece of another, at random places. */
    static byte[] cross(byte[] a, byte[] b, Random r) {
        int p = r.nextInt(a.length + 1);
        int q = r.nextInt(b.length + 1);
        byte[] m = Arrays.copyOf(a, p + b.length - q);
        System.arraycopy(b, q, m, p, b.length - q);
        if (r.nextBoolean() && m.length > 0) {
            m[0] = (byte) 0x82;
        }
        return m;
    }

    /** The header, an object's type byte and random bytes. */
    static byte[] headed(Random r) {
        byte[] m = new byte[2 + r.nextInt(r.nextInt(8) == 0 ? 300 : 24)];
        r.nextBytes(m);
        m[0] = (byte) 0x82;
        m[1] = (byte) (0x48 + r.nextInt(3));
        if (r.nextInt(4) == 0 && m.length > 2) {
            m[2] = (byte) r.nextInt(4);
            for (int k = 3; k < m.length; k++) {
                m[k] = (byte) SPECIAL[r.nextInt(SPECIAL.length)];
            }
        }
        return m;
    }

    /** Deep nesting, huge counts and lengths: bytes made directly, with their verdict. */
    static final class Nested {
        String what;
        byte[] bytes;
        Set<String> expected;

        static Nested random(Random r) {
            Nested x = new Nested();
            int[] depths = {14, 15, 16, 17, 18, 100, 5000, 200000};
            int n = depths[r.nextInt(depths.length)];
            switch (r.nextInt(6)) {
            case 0: {       // n arrays in the field "a": the deepest at level n + 1
                byte[] v = new byte[2 * n];
                Arrays.fill(v, 0, n, (byte) 0x42);
                Arrays.fill(v, n, 2 * n, (byte) 0x43);
                x.what = n + " arrays";
                x.bytes = stored(field("a", v));
                x.expected = n + 1 <= 16 ? OK : set("depth");
                break;
            }
            case 1: {       // the same, never ended
                byte[] v = new byte[n];
                Arrays.fill(v, (byte) 0x42);
                x.what = n + " arrays, not ended";
                x.bytes = stored(field("a", v));
                x.expected = n + 1 <= 16 ? set("past-end") : set("depth", "past-end");
                break;
            }
            case 2: {       // n objects, each the field "a" of the one above
                n = Math.min(n, 300);
                byte[] v = new byte[] {0x48, 0};
                for (int k = 1; k < n; k++) {
                    v = field("a", v);
                }
                x.what = n + " objects";
                x.bytes = stored(field("a", v));
                x.expected = n + 1 <= 16 ? OK : set("depth");
                break;
            }
            case 3: {       // mixed, and a scalar at the bottom (not a level, 020-07, Q1)
                n = Math.min(n, 300);
                byte[] v = new byte[] {0x10, 7};
                for (int k = 0; k < n; k++) {
                    v = r.nextBoolean() ? field("b", v) : array(v);
                }
                x.what = n + " objects and arrays";
                x.bytes = stored(field("a", v));
                x.expected = n + 1 <= 16 ? OK : set("depth");
                break;
            }
            case 4: {       // a count of w bytes, and no table
                int w = 1 << r.nextInt(3);
                long[] counts = {0x7fff, 0x8000, 0xffff, 0x7fffffffL, 0x80000000L, 0xffffffffL};
                long c = counts[r.nextInt(counts.length)];
                byte[] b = new byte[2 + w + r.nextInt(12)];
                b[0] = (byte) 0x82;
                b[1] = (byte) (0x48 + Integer.numberOfTrailingZeros(w));
                for (int k = 0; k < w; k++) {
                    b[2 + k] = (byte) (c >>> (8 * k));
                }
                x.what = "count " + c + " in " + w + " bytes";
                x.bytes = b;
                x.expected = null;
                break;
            }
            default: {      // a string or bytes whose length is huge
                int[] heads = {0x16, 0x1a, 0x15, 0x19};
                long[] lengths = {0x7fffffffL, 0x7ffffff7L, 0x80000000L, 0xffffffffL, 0x8000,
                        0x7fff, 0x10000};
                int t = heads[r.nextInt(heads.length)];
                long length = lengths[r.nextInt(lengths.length)];
                int size = 1 << (t & 3);
                byte[] v = new byte[1 + size + r.nextInt(6)];
                v[0] = (byte) t;
                for (int k = 0; k < size; k++) {
                    v[1 + k] = (byte) (length >>> (8 * k));
                }
                x.what = "length " + length + " in " + size + " bytes";
                x.bytes = stored(field("a", v));
                x.expected = null;
                break;
            }
            }
            return x;
        }

        /** An object of one field, its name 'name' and value 'v', framed by the codec. */
        static byte[] field(String name, byte[] v) {
            byte[] nb = name.getBytes(StandardCharsets.UTF_8);
            int size = 1 + nb.length + v.length;
            byte[] b = new byte[ObjectFormat.headSize(1, size) + size];
            int p = ObjectFormat.frame(b, 0, new int[] {size}, 1);
            p = ObjectFormat.writeName(b, p, nb);
            System.arraycopy(v, 0, b, p, v.length);
            return b;
        }

        static byte[] array(byte[] v) {
            byte[] b = new byte[v.length + 2];
            b[0] = 0x42;
            System.arraycopy(v, 0, b, 1, v.length);
            b[b.length - 1] = 0x43;
            return b;
        }

        static byte[] stored(byte[] object) {
            byte[] b = new byte[1 + object.length];
            b[0] = (byte) 0x82;
            System.arraycopy(object, 0, b, 1, object.length);
            return b;
        }
    }

    static Set<String> set(String... codes) {
        return new HashSet<>(Arrays.asList(codes));
    }

    /**
     * A writer of the model that breaks exactly one rule of 020-07, at one place, and writes
     * every other byte as a conforming writer does; 'expected' holds the codes that the
     * bytes then break (020-07, section 7.2: a reader may name any of them).
     */
    static final class Deviant {
        static final String[] KINDS = {"width", "integer-size", "length-size", "nan",
                "order", "duplicate", "empty-name", "name-utf8", "string-utf8", "field-size",
                "type", "count", "length", "depth", "trailing", "header", "top-type",
                "ends"};
        static final int WIDTH = 0, INT_SIZE = 1, LEN_SIZE = 2, NAN = 3, ORDER = 4,
                DUPLICATE = 5, EMPTY_NAME = 6, NAME_UTF8 = 7, STRING_UTF8 = 8, FIELD_SIZE = 9,
                TYPE = 10, COUNT = 11, LENGTH = 12, DEPTH = 13, TRAILING = 14, HEADER = 15,
                TOP_TYPE = 16, ENDS = 17;

        final int kind;
        final Random r;
        int target = -1;        // the eligible place to break, or -1 to count them
        int places;             // the eligible places met
        Set<String> expected;

        Deviant(int kind, Random r) {
            this.kind = kind;
            this.r = r;
        }

        /** A deviant of a random kind that 'o' has a place for, or null. */
        static Deviant random(Obj o, Random r) {
            for (int attempt = 0; attempt < 8; attempt++) {
                Deviant d = new Deviant(r.nextInt(KINDS.length), r);
                d.stored(o);
                if (d.places > 0) {
                    d.target = r.nextInt(d.places);
                    d.places = 0;
                    return d;
                }
            }
            return null;
        }

        /** True at the target place: break the rule here. */
        private boolean here(int k) {
            if (k != kind) {
                return false;
            }
            return places++ == target;
        }

        byte[] stored(Obj o) {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            out.write(0x82);
            byte[] x = object(o, 1);
            if (here(TOP_TYPE)) {
                int[] not = {0x10, 0x14, 0x18, 0x42, 0x44, 0x46, 0x40, 0x00, 0x82, 0xff};
                x = new byte[] {(byte) not[r.nextInt(not.length)], 0, 0};
                expected = set("type");
            }
            out.write(x, 0, x.length);
            if (here(TRAILING)) {
                byte[] t = new byte[1 + r.nextInt(3)];
                r.nextBytes(t);
                out.write(t, 0, t.length);
                expected = set("trailing");
            }
            byte[] b = out.toByteArray();
            if (here(HEADER)) {
                int h;
                do {
                    h = r.nextInt(256);
                } while (h == 0x82);
                b[0] = (byte) h;
                expected = set("header");
            }
            return b;
        }

        private byte[] object(Obj o, int level) {
            int n = o.fields.size();
            List<byte[]> names = new ArrayList<>();
            List<byte[]> values = new ArrayList<>();
            for (Map.Entry<String, Object> e : o.fields.entrySet()) {
                names.add(ObjectFormatTester.bytes(e.getKey()));
                values.add(value(e.getValue(), level));
            }
            if (n >= 2 && here(ORDER)) {
                int i = r.nextInt(n - 1);
                Collections.swap(names, i, i + 1);
                Collections.swap(values, i, i + 1);
                expected = set("order");
            }
            if (n >= 2 && here(DUPLICATE)) {
                int i = r.nextInt(n - 1);
                names.set(i + 1, names.get(i));
                expected = set("duplicate");
            }
            if (n >= 1 && here(EMPTY_NAME)) {
                int i = r.nextInt(n);
                names.set(i, new byte[0]);
                expected = i == 0 ? set("name-length") : set("name-length", "order");
            }
            if (n >= 1 && here(NAME_UTF8)) {
                int i = r.nextInt(n);
                byte[] bad = illFormed(names.get(i), r);
                if (bad.length <= 255) {
                    names.set(i, bad);
                    sortByNames(names, values);
                    expected = set("utf8");
                } else {
                    expected = OK;
                }
            }
            if (n >= 1 && here(FIELD_SIZE)) {
                int i = r.nextInt(n);
                byte[] extra = new byte[1 + r.nextInt(3)];
                r.nextBytes(extra);
                byte[] v = values.get(i);
                byte[] w = Arrays.copyOf(v, v.length + extra.length);
                System.arraycopy(extra, 0, w, v.length, extra.length);
                values.set(i, w);
                expected = set("field-size");
            }
            if (n >= 1 && here(TYPE)) {
                int i = r.nextInt(n);
                byte[] v = values.get(i).clone();
                v[0] = (byte) notType(r);
                values.set(i, v);
                expected = set("type");
            }
            long size = 0;
            long[] ends = new long[n];
            for (int i = 0; i < n; i++) {
                size += 1 + names.get(i).length + values.get(i).length;
                ends[i] = size;
            }
            int w = (int) ObjectFormat.width(size);
            long count = n;
            if (w < 4 && here(WIDTH)) {
                w = w == 1 && r.nextBoolean() ? 2 : 4;
                expected = set("width");
            }
            if (here(COUNT)) {
                long[] counts = {0x8000, 0xffff, 0x7fffffffL, 0xffffffffL};
                count = counts[r.nextInt(counts.length)];
                w = Math.max(w, count > 0xffff ? 4 : 2);
                expected = set("fields", "width", "past-end");
            }
            if (n >= 2 && here(ENDS)) {
                int i = r.nextInt(n - 1);
                ends[i] = r.nextBoolean() ? ends[i + 1] : i == 0 ? 0 : ends[i - 1];
                // A reader that checks each end as it reads its field finds field i's value
                // ending before its end first.
                expected = set("ends", "field-size");
            }
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            out.write(0x48 + Integer.numberOfTrailingZeros(w));
            le(out, count, w);
            for (long e : ends) {
                le(out, e, w);
            }
            for (int i = 0; i < n; i++) {
                out.write(names.get(i).length);
                out.write(names.get(i), 0, names.get(i).length);
                out.write(values.get(i), 0, values.get(i).length);
            }
            return out.toByteArray();
        }

        private byte[] value(Object v, int level) {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            if (v instanceof Obj) {
                byte[] x = object((Obj) v, level + 1);
                if (here(DEPTH)) {
                    x = deeper(x, level + 1);
                }
                out.write(x, 0, x.length);
            } else if (v instanceof Arr) {
                out.write(0x42);
                for (Object e : ((Arr) v).elements) {
                    byte[] x = value(e, level + 1);
                    out.write(x, 0, x.length);
                }
                out.write(0x43);
                if (here(DEPTH)) {
                    byte[] x = deeper(out.toByteArray(), level + 1);
                    out.reset();
                    out.write(x, 0, x.length);
                }
            } else if (v instanceof Boolean) {
                out.write((Boolean) v ? 0x44 : 0x45);
            } else if (v instanceof Long) {
                long x = (Long) v;
                int size = Ref.fewest(x);
                if (size < 8 && here(INT_SIZE)) {
                    size = size == 1 ? 2 << r.nextInt(3) : size == 2 ? 4 << r.nextInt(2) : 8;
                    expected = set("integer-size");
                }
                out.write(0x10 + Integer.numberOfTrailingZeros(size));
                le(out, x, size);
            } else if (v instanceof Dbl) {
                long bits = ((Dbl) v).bits;
                if (Double.isNaN(Double.longBitsToDouble(bits))) {
                    bits = 0x7ff8000000000000L;
                }
                if (here(NAN)) {
                    long payload = r.nextLong() & 0x000fffffffffffffL;
                    bits = (r.nextBoolean() ? 0x7ff0000000000000L : 0xfff0000000000000L)
                            | (payload == 0 ? 1 : payload);
                    if (bits == 0x7ff8000000000000L) {
                        bits = 0xfff8000000000000L;
                    }
                    expected = set("nan");
                }
                out.write(0x46);
                le(out, bits, 8);
            } else {
                boolean string = v instanceof Str;
                byte[] x = ObjectFormatTester.bytes(string ? ((Str) v).bytes : ((Bin) v).bytes);
                if (string && here(STRING_UTF8)) {
                    x = illFormed(x, r);
                    expected = set("utf8");
                }
                long length = x.length;
                int size = Ref.fewest(length);
                if (size < 4 && here(LEN_SIZE)) {
                    size = size == 1 ? 2 << r.nextInt(2) : 4;
                    expected = set("integer-size");
                }
                if (here(LENGTH)) {
                    long[] negative = {-1, -128, -129, -32768, -32769, Integer.MIN_VALUE};
                    length = negative[r.nextInt(negative.length)];
                    size = Ref.fewest(length);
                    expected = set("length");
                }
                out.write((string ? 0x14 : 0x18) + Integer.numberOfTrailingZeros(size));
                le(out, length, size);
                out.write(x, 0, x.length);
            }
            return out.toByteArray();
        }

        /** 'x', a container at 'level', wrapped in arrays and objects down past level 16. */
        private byte[] deeper(byte[] x, int level) {
            int wraps = 16 - level + 1 + r.nextInt(3);
            for (int k = 0; k < wraps; k++) {
                x = r.nextBoolean() ? Nested.array(x) : Nested.field("w", x);
            }
            expected = set("depth");
            return x;
        }

        private static void sortByNames(List<byte[]> names, List<byte[]> values) {
            Integer[] idx = new Integer[names.size()];
            for (int i = 0; i < idx.length; i++) {
                idx[i] = i;
            }
            Arrays.sort(idx, (a, b) -> Arrays.compareUnsigned(names.get(a), names.get(b)));
            List<byte[]> n2 = new ArrayList<>();
            List<byte[]> v2 = new ArrayList<>();
            for (int i : idx) {
                n2.add(names.get(i));
                v2.add(values.get(i));
            }
            names.clear();
            names.addAll(n2);
            values.clear();
            values.addAll(v2);
        }

        static void le(ByteArrayOutputStream out, long x, int size) {
            for (int k = 0; k < size; k++) {
                out.write((int) (x >>> (8 * k)) & 0xff);
            }
        }
    }

    /** A byte that starts no value (020-07, section 4.3). */
    static int notType(Random r) {
        while (true) {
            int t = r.nextInt(256);
            if (!((t >= 0x10 && t <= 0x16) || (t >= 0x18 && t <= 0x1a) || t == 0x42
                    || (t >= 0x44 && t <= 0x46) || (t >= 0x48 && t <= 0x4a))) {
                return t;
            }
        }
    }

    /** Ill-formed UTF-8 sequences of every kind (the Unicode Standard, table 3-7). */
    static final int[][] ILL_FORMED = {{0x80}, {0xbf}, {0xc0, 0x80}, {0xc1, 0xbf},
            {0xe0, 0x80, 0x80}, {0xe0, 0x9f, 0xbf}, {0xf0, 0x80, 0x80, 0x80},
            {0xf0, 0x8f, 0xbf, 0xbf}, {0xed, 0xa0, 0x80}, {0xed, 0xbf, 0xbf},
            {0xf4, 0x90, 0x80, 0x80}, {0xf5, 0x80, 0x80, 0x80}, {0xf8, 0x88, 0x80, 0x80, 0x80},
            {0xfe}, {0xff}, {0xc2}, {0xe1, 0x80}, {0xf1, 0x80, 0x80}, {0xc2, 0x41},
            {0xe1, 0x80, 0x41}, {0xf1, 0x80, 0x80, 0x41}, {0xe0, 0xa0}, {0xf4, 0x8f, 0xbf}};

    /** 'x', well-formed UTF-8, with an ill-formed sequence put at a char boundary. */
    static byte[] illFormed(byte[] x, Random r) {
        List<Integer> boundaries = new ArrayList<>();
        for (int k = 0; k <= x.length; k++) {
            if (k == x.length || (x[k] & 0xc0) != 0x80) {
                boundaries.add(k);
            }
        }
        int p = boundaries.get(r.nextInt(boundaries.size()));
        int[] s = ILL_FORMED[r.nextInt(ILL_FORMED.length)];
        byte[] bad = new byte[s.length];
        for (int k = 0; k < s.length; k++) {
            bad[k] = (byte) s[k];
        }
        // A cut sequence is cut only where no continuation byte follows: at the end, or
        // before ASCII or a lead byte, which a boundary is.
        return insert(x, p, bad);
    }

    // ======== Area 3: the index keys and definitions (020-10) ========
    
    /** One iteration of area 3. */
    void keysOne(long i) {
        Random r = random(seed, i);
        String where = "keys seed " + seed + " iteration " + i;
        stats.iterations++;
        int s = r.nextInt(100);
        if (s < 25) {
            levelPairs(r, where);
        } else if (s < 35) {
            prefixAndSucc(r, where);
        } else if (s < 55) {
            entryKeys(r, where);
        } else if (s < 65) {
            markerAndDefinitionKeys(r, where);
        } else if (s < 85) {
            definitions(r, where);
        } else {
            function(r, where);
        }
    }
    
    /** A random value of a level's type: a Long, a Double (not NaN), a String or a byte[]. */
    static Object levelValue(char type, Random r) {
        switch (type) {
        case IndexKeys.LONG: {
            long[] e = {0, 1, -1, Long.MAX_VALUE, Long.MIN_VALUE, Long.MAX_VALUE - 1,
                    Long.MIN_VALUE + 1, 255, 256, -256, 1L << 32, -(1L << 32)};
            return r.nextBoolean() ? e[r.nextInt(e.length)] : r.nextLong() >> r.nextInt(64);
        }
        case IndexKeys.DOUBLE: {
            double[] e = {0.0, -0.0, Double.MIN_VALUE, -Double.MIN_VALUE, Double.MAX_VALUE,
                    -Double.MAX_VALUE, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY,
                    Double.MIN_NORMAL, -Double.MIN_NORMAL, 1.0, -1.0, Math.nextUp(1.0),
                    Math.nextDown(-1.0)};
            if (r.nextBoolean()) {
                return e[r.nextInt(e.length)];
            }
            while (true) {
                double d = Double.longBitsToDouble(r.nextLong());
                if (d == d) {
                    return d;
                }
            }
        }
        case IndexKeys.STRING:
            return randomString(r);
        default:
            return randomBytes(r);
        }
    }
    
    static final int[] CODE_POINTS = {0, 1, 2, 0x7f, 0x80, 0xff, 0x7ff, 0x800, 0xd7ff, 0xe000,
            0xfffd, 0xffff, 0x10000, 0x10ffff, 'a', 'b', 'z', '/', '.', ','};
    
    static String randomString(Random r) {
        StringBuilder s = new StringBuilder();
        int n = r.nextInt(20) == 0 ? 300 + r.nextInt(4000) : r.nextInt(6);
        for (int k = 0; k < n; k++) {
            int c;
            switch (r.nextInt(4)) {
            case 0:
                c = CODE_POINTS[r.nextInt(CODE_POINTS.length)];
                break;
            case 1:
                c = r.nextInt(0x110000);
                if (c >= 0xd800 && c <= 0xdfff) {
                    c = 'x';
                }
                break;
            default:
                c = 'a' + r.nextInt(3);
                break;
            }
            s.appendCodePoint(c);
        }
        return s.toString();
    }
    
    static byte[] randomBytes(Random r) {
        byte[] b = new byte[r.nextInt(20) == 0 ? 300 + r.nextInt(4000) : r.nextInt(6)];
        for (int k = 0; k < b.length; k++) {
            int[] e = {0, 1, 2, 0xfe, 0xff, 0x7f, 0x80};
            b[k] = (byte) (r.nextBoolean() ? e[r.nextInt(e.length)] : r.nextInt(256));
        }
        return b;
    }
    
    /** A value close to 'v': the same, a prefix, an extension, one element changed. */
    static Object near(char type, Object v, Random r) {
        if (type == IndexKeys.STRING) {
            int[] cps = ((String) v).codePoints().toArray();
            int[] w = nearInts(cps, r, 0x110000);
            StringBuilder s = new StringBuilder();
            for (int c : w) {
                s.appendCodePoint(c >= 0xd800 && c <= 0xdfff ? 'y' : c);
            }
            return s.toString();
        } else if (type == IndexKeys.BYTES) {
            byte[] b = (byte[]) v;
            int[] x = new int[b.length];
            for (int k = 0; k < b.length; k++) {
                x[k] = b[k] & 0xff;
            }
            int[] w = nearInts(x, r, 256);
            byte[] c = new byte[w.length];
            for (int k = 0; k < w.length; k++) {
                c[k] = (byte) w[k];
            }
            return c;
        } else if (type == IndexKeys.LONG) {
            return (Long) v + r.nextInt(5) - 2;
        } else {
            double d = (Double) v;
            double n = r.nextBoolean() ? Math.nextUp(d) : Math.nextDown(d);
            return r.nextInt(3) == 0 ? -d : n != n ? d : n;
        }
    }
    
    private static int[] nearInts(int[] x, Random r, int bound) {
        switch (r.nextInt(4)) {
        case 0:
            return x.clone();
        case 1:
            return Arrays.copyOf(x, x.length == 0 ? 0 : r.nextInt(x.length));
        case 2: {
            int[] y = Arrays.copyOf(x, x.length + 1 + r.nextInt(2));
            for (int k = x.length; k < y.length; k++) {
                y[k] = r.nextInt(3) == 0 ? r.nextInt(3) : r.nextInt(bound);
            }
            return y;
        }
        default: {
            int[] y = x.clone();
            if (y.length > 0) {
                int k = r.nextInt(y.length);
                y[k] = Math.max(0, Math.min(bound - 1, y[k] + r.nextInt(3) - 1));
            }
            return y;
        }
        }
    }
    
    /** The order of two values of a level's type, by 020-10, section 4.4's words. */
    static int compareValues(char type, Object a, Object b) {
        switch (type) {
        case IndexKeys.LONG:
            return Long.compare((Long) a, (Long) b);
        case IndexKeys.DOUBLE: {
            double x = (Double) a;
            double y = (Double) b;
            return x < y ? -1 : x > y ? 1 : 0;     // -0.0 == 0.0: one key
        }
        case IndexKeys.STRING: {
            int[] x = ((String) a).codePoints().toArray();
            int[] y = ((String) b).codePoints().toArray();
            return Arrays.compare(x, y);
        }
        default:
            return Arrays.compareUnsigned((byte[]) a, (byte[]) b);
        }
    }
    
    /** A level's encoding by IndexKeys. */
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
    
    /**
     * A level's encoding written here from 020-10, section 4.4, apart from IndexKeys: long
     * v + 2^63 big-endian, by BigInteger; a double's sort long; E by its escapes.
     */
    static byte[] refEncode(char type, Object v) {
        switch (type) {
        case IndexKeys.LONG:
            return refLong((Long) v);
        case IndexKeys.DOUBLE: {
            long x = Double.doubleToLongBits((Double) v);
            return refLong(x >= 0 ? x : -(x & 0x7fffffffffffffffL));
        }
        case IndexKeys.STRING:
            return refE(((String) v).getBytes(StandardCharsets.UTF_8));
        default:
            return refE((byte[]) v);
        }
    }
    
    static byte[] refLong(long v) {
        byte[] x = java.math.BigInteger.valueOf(v).add(java.math.BigInteger.ONE.shiftLeft(63))
                .toByteArray();
        byte[] b = new byte[8];
        int n = Math.min(8, x.length);
        System.arraycopy(x, x.length - n, b, 8 - n, n);
        return b;
    }
    
    static byte[] refE(byte[] v) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        for (byte x : v) {
            if (x == 0) {
                out.write(1);
                out.write(1);
            } else if (x == 1) {
                out.write(1);
                out.write(2);
            } else {
                out.write(x);
            }
        }
        out.write(0);
        return out.toByteArray();
    }
    
    static boolean startsWith(byte[] b, byte[] prefix) {
        return b.length >= prefix.length
                && Arrays.equals(b, 0, prefix.length, prefix, 0, prefix.length);
    }
    
    /**
     * Pairs of one type: the encodings' unsigned order is the values'; equal values give
     * equal encodings and others neither one a prefix of the other's; the encoding is the
     * reference's and decodes to the value (-0.0 to 0.0); NaN has none.
     */
    void levelPairs(Random r, String where) {
        char type = IndexKeys.TYPES[r.nextInt(4)];
        Object a = levelValue(type, r);
        Object b = r.nextBoolean() ? near(type, a, r) : levelValue(type, r);
        byte[] ea = encode(type, a);
        byte[] eb = encode(type, b);
        stats.inputs++;
        String what = IndexKeys.typeName(type) + " " + show(a) + " and " + show(b);
        Assert(Arrays.equals(ea, refEncode(type, a)), where, what + ": not the reference's "
                + "encoding", ea);
        int c = Integer.signum(compareValues(type, a, b));
        Assert(Integer.signum(Arrays.compareUnsigned(ea, eb)) == c, where, what
                + ": the encodings' order is not the values'", ea);
        if (c == 0) {
            Assert(Arrays.equals(ea, eb), where, what + ": equal values, other encodings", ea);
        } else if (type == IndexKeys.STRING || type == IndexKeys.BYTES) {
            Assert(!startsWith(ea, eb) && !startsWith(eb, ea), where, what
                    + ": one encoding a prefix of the other's", ea);
        }
        switch (type) {
        case IndexKeys.LONG:
            Assert(IndexKeys.decodeLong(ea, 0) == (Long) a, where, what + ": decoded", ea);
            break;
        case IndexKeys.DOUBLE: {
            double d = IndexKeys.decodeDouble(ea, 0);
            double want = (Double) a == 0.0 ? 0.0 : (Double) a;
            Assert(Double.doubleToRawLongBits(d) == Double.doubleToRawLongBits(want), where,
                    what + ": decoded " + d, ea);
            break;
        }
        default: {
            byte[] v = IndexKeys.decodeEscaped(ea, 0, ea.length - 1);
            byte[] want = type == IndexKeys.STRING ? ((String) a).getBytes(
                    StandardCharsets.UTF_8) : (byte[]) a;
            Assert(Arrays.equals(v, want), where, what + ": decoded", ea);
            break;
        }
        }
        if (r.nextInt(50) == 0) {
            long nan = 0x7ff0000000000000L | (1 + (r.nextLong() & 0x000ffffffffffffeL));
            try {
                IndexKeys.encodeDouble(Double.longBitsToDouble(r.nextBoolean() ? nan
                        : nan | 0x8000000000000000L));
                throw fail(where, "a NaN encoded", null, null);
            } catch (IllegalArgumentException e) {
                // as 020-10, section 3.3
            }
        }
    }
    
    static String show(Object v) {
        if (v instanceof byte[]) {
            byte[] b = (byte[]) v;
            return "bytes " + StringUtil.toHex(b, 0, Math.min(40, b.length));
        } else if (v instanceof String) {
            String s = (String) v;
            return "\"" + StringUtil.toHex(s.getBytes(StandardCharsets.UTF_8), 0, Math.min(40,
                    s.getBytes(StandardCharsets.UTF_8).length)) + "\"";
        }
        return String.valueOf(v);
    }
    
    /**
     * The prefix rule: E'(p) is a prefix of E(v) exactly when v starts with p; and succ(x):
     * a string z starts with x exactly when x &lt;= z &lt; succ(x) (020-10, section 4.4).
     */
    void prefixAndSucc(Random r, String where) {
        stats.inputs++;
        char type = r.nextBoolean() ? IndexKeys.STRING : IndexKeys.BYTES;
        Object v = levelValue(type, r);
        Object p = r.nextBoolean() ? near(type, v, r) : levelValue(type, r);
        if (r.nextBoolean()) {      // a true prefix
            if (type == IndexKeys.STRING) {
                int[] cps = ((String) v).codePoints().toArray();
                p = new String(cps, 0, cps.length == 0 ? 0 : r.nextInt(cps.length + 1));
            } else {
                byte[] b = (byte[]) v;
                p = Arrays.copyOf(b, r.nextInt(b.length + 1));
            }
        }
        boolean starts = type == IndexKeys.STRING ? ((String) v).startsWith((String) p)
                : startsWith((byte[]) v, (byte[]) p);
        byte[] ev = encode(type, v);
        byte[] ep = type == IndexKeys.STRING ? IndexKeys.encodeStringPrefix((String) p)
                : IndexKeys.encodeBytesPrefix((byte[]) p);
        Assert(startsWith(ev, ep) == starts, where, "E'(" + show(p) + ") prefix of E("
                + show(v) + "): " + startsWith(ev, ep) + ", starts: " + starts, ev);
        
        byte[] x = r.nextBoolean() ? ep : randomBytes(r);
        byte[] succ = IndexKeys.succ(x);
        byte[][] zs = {ev, x, randomBytes(r), succ == null ? x : succ, insert(x, x.length,
                randomBytes(r)), x.length > 0 ? Arrays.copyOf(x, x.length - 1) : x,
                succ == null ? x : insert(succ, succ.length, randomBytes(r))};
        for (byte[] z : zs) {
            boolean in = Arrays.compareUnsigned(z, x) >= 0
                    && (succ == null || Arrays.compareUnsigned(z, succ) < 0);
            Assert(in == startsWith(z, x), where, "succ(" + StringUtil.toHex(x) + ") = "
                    + (succ == null ? "none" : StringUtil.toHex(succ)) + ": "
                    + StringUtil.toHex(z) + " in range " + in, x);
        }
    }
    
    /** A random index name: 1 to 255 UTF-8 bytes, no '/', no whitespace. */
    static String indexName(Random r) {
        if (r.nextInt(30) == 0) {
            StringBuilder s = new StringBuilder();
            while (s.length() < 85) {
                s.append("€");     // 3 bytes each: 255 bytes
            }
            return s.toString();
        }
        String[] e = {"a", "ab", "a.b", "x,y", "é", "😀", "n0", "\u0000",
                "-", "#", "a-", "aa"};
        StringBuilder s = new StringBuilder(e[r.nextInt(e.length)]);
        if (r.nextBoolean()) {
            s.append(e[r.nextInt(e.length)]);
        }
        return s.toString();
    }
    
    /** A random directory, valid by PubKeys.udir2idir's rules. */
    static String dir(Random r) {
        String[] e = {"/", "/p/", "/p/q/", "/a.b/", "/é/", "/x y/", "/😀/",
                "/-/", "/.h/"};
        return e[r.nextInt(e.length)];
    }
    
    /** A random definition. */
    static IndexDefinition definition(Random r) {
        int n = 1 + r.nextInt(r.nextInt(4) == 0 ? IndexDefinition.MAX_LEVELS : 3);
        String[] types = new String[n];
        String[][] paths = new String[n][];
        for (int k = 0; k < n; k++) {
            types[k] = IndexKeys.typeName(IndexKeys.TYPES[r.nextInt(4)]);
            paths[k] = path(r);
        }
        long[] gens = {1, 2, 255, 1L << 40, Long.MAX_VALUE, 1 + (r.nextLong() >>> 1)};
        return new IndexDefinition(indexName(r), dir(r), gens[r.nextInt(gens.length)],
                r.nextBoolean(), types, paths);
    }
    
    static final String[] PART_NAMES = {"a", "b", "c", "v", "a.b", "x,y", "é", "😀",
            "\u0000", " ", "key", "p"};
    
    static String[] path(Random r) {
        String[] p = new String[1 + (r.nextInt(8) == 0 ? r.nextInt(IndexDefinition.MAX_PARTS)
                : r.nextInt(2))];
        for (int k = 0; k < p.length; k++) {
            p[k] = r.nextInt(40) == 0 ? repeatChar('n', 255) : PART_NAMES[r.nextInt(
                    PART_NAMES.length)];
        }
        return p;
    }
    
    static String repeatChar(char c, int n) {
        char[] x = new char[n];
        Arrays.fill(x, c);
        return new String(x);
    }
    
    /**
     * Entries: the tuple order of (levels, K); the parse of an entry's key; a changed key
     * parsed to the same bytes again (each level and K) or refused with
     * InternalDataException, nothing else (020-10, section 4.4).
     */
    void entryKeys(Random r, String where) {
        stats.inputs++;
        IndexDefinition d = definition(r);
        char[] types = d.types();
        byte[] prefix = d.generationPrefix();
        Object[] a = new Object[types.length];
        Object[] b = new Object[types.length];
        for (int k = 0; k < types.length; k++) {
            a[k] = levelValue(types[k], r);
            b[k] = r.nextInt(3) > 0 ? near(types[k], a[k], r) : levelValue(types[k], r);
        }
        String na = fileName(r);
        String nb = r.nextBoolean() ? na : fileName(r);
        byte[] ka = entryKey(prefix, types, a, na);
        byte[] kb = entryKey(prefix, types, b, nb);
        int c = 0;
        for (int k = 0; k < types.length && c == 0; k++) {
            c = Integer.signum(compareValues(types[k], a[k], b[k]));
        }
        if (c == 0) {
            c = Integer.signum(Arrays.compareUnsigned(IndexKeys.fileKey("/dp/-" + na),
                    IndexKeys.fileKey("/dp/-" + nb)));
        }
        Assert(Integer.signum(Arrays.compareUnsigned(ka, kb)) == c, where, "the entries' "
                + "order is not the tuples': " + d, ka);
        IndexKeys.Entry e = parse(ka, prefix, types, where);
        Assert(e != null, where, "a valid entry refused", ka);
        for (int k = 0; k < types.length; k++) {
            Object v = e.value(k);
            Object want = types[k] == IndexKeys.DOUBLE && (Double) a[k] == 0.0 ? 0.0 : a[k];
            boolean same = want instanceof byte[] ? Arrays.equals((byte[]) want, (byte[]) v)
                    : want instanceof Double ? Double.doubleToRawLongBits((Double) want)
                    == Double.doubleToRawLongBits((Double) v) : want.equals(v);
            Assert(same, where, "level " + (k + 1) + " parsed as " + show(v) + ", not "
                    + show(want), ka);
        }
        Assert(e.fileName().equals("-" + na), where, "K parsed as " + e.fileName(), ka);
        
        for (int t = 0; t < 8; t++) {
            byte[] m;
            if (r.nextInt(4) == 0) {
                m = mutateBytes(ka, r);
            } else {        // the prefix kept
                byte[] tail = mutateBytes(Arrays.copyOfRange(ka, prefix.length, ka.length), r);
                m = insert(prefix, prefix.length, tail);
            }
            changedEntry(m, prefix, types, where);
        }
    }
    
    /** A changed entry's key: parsed and the same bytes again, or InternalDataException. */
    void changedEntry(byte[] m, byte[] prefix, char[] types, String where) {
        stats.inputs++;
        IndexKeys.Entry e = parse(m, prefix, types, where);
        if (e == null) {
            stats.count("entry refused");
            return;
        }
        Object[] values = new Object[types.length];
        String file;
        try {
            for (int k = 0; k < types.length; k++) {
                values[k] = e.value(k);
            }
            file = e.fileName();
        } catch (bergdb.core.InternalDataException x) {
            stats.count("entry refused by a level");
            return;
        } catch (Throwable x) {
            throw fail(where, "a parsed entry's level or K threw " + x, m, x);
        }
        stats.count("entry parsed");
        byte[] again;
        try {
            again = entryKey(prefix, types, values, file.substring(1));
        } catch (IllegalArgumentException x) {
            throw fail(where, "a parsed entry's K, " + file + ", is no file name: " + x, m, x);
        }
        Assert(Arrays.equals(again, m), where, "a parsed entry written again to other bytes "
                + StringUtil.toHex(again), m);
    }
    
    static IndexKeys.Entry parse(byte[] key, byte[] prefix, char[] types, String where) {
        try {
            return IndexKeys.parseEntry(key, prefix, types);
        } catch (bergdb.core.InternalDataException e) {
            return null;
        }
    }
    
    static byte[] entryKey(byte[] prefix, char[] types, Object[] values, String name) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        for (int k = 0; k < types.length; k++) {
            byte[] x = refEncode(types[k], values[k]);
            out.write(x, 0, x.length);
        }
        return IndexKeys.entryKey(prefix, out.toByteArray(), IndexKeys.fileKey("/dp/-" + name));
    }
    
    /** A random file name of a key, without '/'. */
    static String fileName(Random r) {
        String[] e = {"a", "1", "k.obj", "é", "😀", "a b", "\u0000", "z~"};
        return e[r.nextInt(e.length)] + (r.nextBoolean() ? "" : e[r.nextInt(e.length)]);
    }
    
    /**
     * Markers' and definitions' keys: each parsed to its name and generation; changed, parsed
     * to a name and generation whose key is the same bytes, or refused with
     * InternalDataException, nothing else (020-10, section 4.1).
     */
    void markerAndDefinitionKeys(Random r, String where) {
        String name = indexName(r);
        long gen = 1 + (r.nextBoolean() ? r.nextInt(1000) : r.nextLong() >>> 1);
        byte[] marker = IndexKeys.markerKey(name, gen);
        IndexKeys.Marker mk = IndexKeys.parseMarker(marker);
        Assert(mk.name.equals(name) && mk.gen == gen, where, "parsed " + mk, marker);
        byte[] def = IndexKeys.definitionKey(name);
        Assert(IndexKeys.nameOfDefinitionKey(def).equals(name), where, "definition key", def);
        for (int t = 0; t < 8; t++) {
            stats.inputs++;
            byte[] m = r.nextBoolean() ? mutateBytes(marker, r) : extremeKey(marker, r);
            try {
                IndexKeys.Marker x = IndexKeys.parseMarker(m);
                Assert(Arrays.equals(IndexKeys.markerKey(x.name, x.gen), m), where, "a parsed "
                        + "marker " + x + " has another key", m);
                stats.count("marker parsed");
            } catch (bergdb.core.InternalDataException e) {
                stats.count("marker refused");
            } catch (Failure e) {
                throw e;
            } catch (Throwable e) {
                throw fail(where, "parseMarker threw " + e, m, e);
            }
            stats.inputs++;
            m = mutateBytes(def, r);
            try {
                String x = IndexKeys.nameOfDefinitionKey(m);
                Assert(Arrays.equals(IndexKeys.definitionKey(x), m), where, "a parsed "
                        + "definition key " + x + " has another key", m);
                stats.count("definition key parsed");
            } catch (bergdb.core.InternalDataException e) {
                stats.count("definition key refused");
            } catch (Failure e) {
                throw e;
            } catch (Throwable e) {
                throw fail(where, "nameOfDefinitionKey threw " + e, m, e);
            }
        }
    }
    
    /** A key with one byte after its first 8 set to a digit, a letter or a separator. */
    static byte[] extremeKey(byte[] key, Random r) {
        byte[] m = key.clone();
        int p = 8 + r.nextInt(m.length - 8);
        int[] e = {'0' + 2, '9' + 2, 'a' + 2, 'f' + 2, 'g' + 2, 'A' + 2, '-' + 2, '/' + 2, 1, 0,
                2, 0xff};
        m[p] = (byte) e[r.nextInt(e.length)];
        return m;
    }
    
    /**
     * Definitions (020-10, section 4.2): written and read again; their bytes changed, or their
     * fields changed in the model, read as a definition whose bytes are the same again, or
     * refused with InternalDataException, nothing else; a change of the model accepted
     * exactly when the reference says the fields are a definition's.
     */
    void definitions(Random r, String where) {
        stats.inputs++;
        IndexDefinition d = definition(r);
        byte[] b = d.toBytes();
        IndexDefinition back = IndexDefinition.fromBytes(d.name(), b);
        Assert(back.equals(d) && Arrays.equals(back.toBytes(), b), where, "read again "
                + back + ", written " + d, b);
        for (int t = 0; t < 6; t++) {
            stats.inputs++;
            byte[] m;
            Boolean valid = null;
            if (t % 2 == 0) {
                m = r.nextBoolean() ? mutateBytes(b, r) : extreme(b, r);
            } else {
                Obj o = ObjectFormatTester.codecDecode(b);
                changeDefinition(o, r);
                try {
                    m = Ref.write(o, true);
                } catch (Refused e) {
                    continue;
                }
                valid = refValidDefinition(o);
            }
            String name = r.nextInt(10) == 0 ? indexName(r) + "/" : d.name();
            IndexDefinition x;
            try {
                x = IndexDefinition.fromBytes(name, m);
            } catch (bergdb.core.InternalDataException e) {
                Assert(valid == null || !valid || IndexKeys.nameFault(name) != null, where,
                        "a definition the reference takes refused: " + e.getMessage(), m);
                stats.count("definition refused");
                continue;
            } catch (Throwable e) {
                throw fail(where, "IndexDefinition.fromBytes threw " + e, m, e);
            }
            stats.count("definition read");
            Assert(valid == null || valid, where, "a definition the reference refuses read: "
                    + x, m);
            Assert(Arrays.equals(x.toBytes(), m), where, "a definition read, " + x
                    + ", written again to other bytes", m);
        }
    }
    
    /** One change of a definition's fields in the model. */
    static void changeDefinition(Obj o, Random r) {
        Map<String, Object> f = o.fields;
        Object[] values = {1L, 2L, 0L, -1L, Long.MAX_VALUE, new Str("x"), new Str("active"),
                new Str("building"), new Str("deleting"), new Str("/p/"), new Str("/"),
                new Str("p/"), new Str("/p//"), new Str(""), new Str("/p"), Boolean.TRUE,
                new Bin("a"), new Arr(), new Obj(), new Dbl(0x3ff0000000000000L)};
        String[] names = {"dir", "gen", "levels", "state", "version", "name", "x", "levelz"};
        switch (r.nextInt(5)) {
        case 0:
            f.remove(names[r.nextInt(5)]);
            break;
        case 1:
            f.put(names[r.nextInt(names.length)], values[r.nextInt(values.length)]);
            break;
        default: {
            Arr levels = f.get("levels") instanceof Arr ? (Arr) f.get("levels") : new Arr();
            changeLevels(levels, r);
            f.put("levels", levels);
            break;
        }
        }
    }
    
    static void changeLevels(Arr levels, Random r) {
        List<Object> l = levels.elements;
        switch (r.nextInt(6)) {
        case 0:
            if (!l.isEmpty()) {
                l.remove(r.nextInt(l.size()));
            }
            break;
        case 1:
            while (l.size() < IndexDefinition.MAX_LEVELS + r.nextInt(2)) {
                l.add(level(r, "long", 1));
            }
            break;
        case 2:
            l.add(r.nextInt(l.size() + 1), r.nextBoolean() ? new Str("x") : new Obj());
            break;
        default: {
            List<Obj> objects = new ArrayList<>();
            for (Object x : l) {
                if (x instanceof Obj) {
                    objects.add((Obj) x);
                }
            }
            if (objects.isEmpty()) {
                objects.add(level(r, "string", 1));
                l.add(objects.get(0));
            }
            Obj level = objects.get(r.nextInt(objects.size()));
            String[] types = {"long", "double", "string", "bytes", "int", "", "String"};
            switch (r.nextInt(4)) {
            case 0:
                level.fields.put("type", r.nextInt(5) == 0 ? (Object) 1L
                        : new Str(types[r.nextInt(types.length)]));
                break;
            case 1:
                level.fields.put("path", r.nextInt(5) == 0 ? (Object) new Str("a")
                        : pathArr(r, r.nextInt(5) == 0 ? 17 : r.nextInt(3)));
                break;
            case 2:
                level.fields.put(r.nextBoolean() ? "x" : "paths", 1L);
                break;
            default:
                level.fields.remove(r.nextBoolean() ? "type" : "path");
                break;
            }
            break;
        }
        }
    }
    
    static Obj level(Random r, String type, int parts) {
        Obj o = new Obj();
        o.fields.put("type", new Str(type));
        o.fields.put("path", pathArr(r, parts));
        return o;
    }
    
    static Arr pathArr(Random r, int parts) {
        Arr a = new Arr();
        for (int k = 0; k < parts; k++) {
            int c = r.nextInt(10);
            a.elements.add(c == 0 ? (Object) new Str("") : c == 1 ? (Object) 5L : c == 2
                    ? new Str(ObjectFormatTester.chars(repeatChar('n', 256).getBytes(
                    StandardCharsets.UTF_8))) : new Str("a"));
        }
        return a;
    }
    
    /** Whether the fields of 'o' are a definition's, by 020-10, section 4.2's table. */
    static boolean refValidDefinition(Obj o) {
        Map<String, Object> f = o.fields;
        if (!f.keySet().equals(new HashSet<>(Arrays.asList("dir", "gen", "levels", "state",
                "version")))) {
            return false;
        }
        if (!Long.valueOf(1).equals(f.get("version"))) {
            return false;
        }
        if (!(f.get("gen") instanceof Long) || (Long) f.get("gen") <= 0) {
            return false;
        }
        if (!(f.get("state") instanceof Str)) {
            return false;
        }
        String state = text(f.get("state"));
        if (!state.equals("building") && !state.equals("active")) {
            return false;
        }
        if (!(f.get("dir") instanceof Str)) {
            return false;
        }
        String dir = text(f.get("dir"));
        if (dir.isEmpty() || dir.charAt(0) != '/' || dir.charAt(dir.length() - 1) != '/'
                || dir.contains("//")) {
            return false;
        }
        if (!(f.get("levels") instanceof Arr)) {
            return false;
        }
        List<Object> levels = ((Arr) f.get("levels")).elements;
        if (levels.isEmpty() || levels.size() > IndexDefinition.MAX_LEVELS) {
            return false;
        }
        for (Object level : levels) {
            if (!(level instanceof Obj)) {
                return false;
            }
            Map<String, Object> lf = ((Obj) level).fields;
            if (!lf.keySet().equals(new HashSet<>(Arrays.asList("path", "type")))) {
                return false;
            }
            if (!(lf.get("type") instanceof Str) || !Arrays.asList("long", "double", "string",
                    "bytes").contains(text(lf.get("type")))) {
                return false;
            }
            if (!(lf.get("path") instanceof Arr)) {
                return false;
            }
            List<Object> parts = ((Arr) lf.get("path")).elements;
            if (parts.isEmpty() || parts.size() > IndexDefinition.MAX_PARTS) {
                return false;
            }
            for (Object part : parts) {
                if (!(part instanceof Str)) {
                    return false;
                }
                int n = ((Str) part).bytes.length();
                if (n < 1 || n > 255) {
                    return false;
                }
            }
        }
        return true;
    }
    
    /** A Str's text. */
    static String text(Object str) {
        return new String(ObjectFormatTester.bytes(((Str) str).bytes), StandardCharsets.UTF_8);
    }
    
    /**
     * The index function (020-10, section 3.3) on random objects whose fields lie on the
     * definition's paths: the levels by IndexDefinition.entryLevels, as a reference written
     * here from the table of 3.3 and 4.4's encodings computes them; the entry's key the
     * generation's prefix, the levels and K.
     */
    void function(Random r, String where) {
        stats.inputs++;
        IndexDefinition d = definition(r);
        Obj o = new Obj();
        for (int k = 0; k < d.levelCount(); k++) {
            if (r.nextInt(8) > 0) {
                place(o, d.path(k), 0, d.type(k), r);
            }
        }
        if (r.nextInt(4) == 0) {
            o.fields.put("other", new Str("x"));
        }
        byte[] b;
        try {
            b = Ref.write(o, true);
        } catch (Refused e) {
            return;
        }
        if (r.nextInt(6) == 0) {
            b = r.nextBoolean() ? mutateBytes(b, r) : extreme(b, r);
        }
        String[] keys = {"/dp/-k", "/dp/-k.obj", "/dp/-k.txt", "/dp/-.h", "/dp/-k."};
        String ikey = keys[r.nextInt(8) == 0 ? r.nextInt(keys.length) : 0];
        byte[] want = refLevels(d, ikey, b);
        byte[] got;
        try {
            got = d.entryLevels(ikey, b);
        } catch (bergdb.pub.DataFormatException e) {
            Assert(ObjectFormat.isFormat1(b), where, "entryLevels refused " + e, b);
            return;
        } catch (Throwable e) {
            throw fail(where, "entryLevels threw " + e, b, e);
        }
        Assert(Arrays.equals(want, got), where, d + ": levels "
                + (got == null ? "none" : StringUtil.toHex(got)) + ", the reference's "
                + (want == null ? "none" : StringUtil.toHex(want)), b);
        if (got != null) {
            stats.count("entry");
            byte[] entry = d.entry(ikey, b);
            Assert(Arrays.equals(entry, IndexKeys.entryKey(d.generationPrefix(), got,
                    IndexKeys.fileKey(ikey))), where, "entry()", b);
        } else {
            stats.count("no entry");
        }
    }
    
    /** Puts a random value at 'path' from part 'k' in 'o': mostly of the level's kind. */
    static void place(Obj o, String[] path, int k, char type, Random r) {
        String name = ObjectFormatTester.chars(path[k].getBytes(StandardCharsets.UTF_8));
        if (k == path.length - 1 || r.nextInt(12) == 0) {
            o.fields.put(name, r.nextInt(4) == 0 ? anyValue(r) : kindValue(type, r));
            return;
        }
        Object next = o.fields.get(name);
        if (!(next instanceof Obj)) {
            next = new Obj();
            o.fields.put(name, next);
        }
        place((Obj) next, path, k + 1, type, r);
    }
    
    /**
     * A stored value of a level's kind, with lengths around the 111 bytes of levels (L6;
     * around 4,096 until bergdb 024-24).
     */
    static Object kindValue(char type, Random r) {
        switch (type) {
        case IndexKeys.LONG:
            return levelValue(type, r);
        case IndexKeys.DOUBLE:
            return r.nextInt(10) == 0 ? new Dbl(0x7ff8000000000000L) : new Dbl(
                    Double.doubleToRawLongBits((Double) levelValue(type, r)));
        default: {
            byte[] x;
            if (r.nextInt(5) == 0) {
                x = new byte[IndexKeys.MAX_LEVEL_BYTES - 12 + r.nextInt(20)];
                Arrays.fill(x, (byte) 'a');
                for (int k = 0; k < r.nextInt(4); k++) {
                    x[r.nextInt(x.length)] = (byte) r.nextInt(2);
                }
            } else {
                x = type == IndexKeys.STRING ? randomString(r).getBytes(StandardCharsets.UTF_8)
                        : randomBytes(r);
            }
            return type == IndexKeys.STRING ? new Str(ObjectFormatTester.chars(x))
                    : new Bin(ObjectFormatTester.chars(x));
        }
        }
    }
    
    static Object anyValue(Random r) {
        switch (r.nextInt(7)) {
        case 0:
            return Boolean.TRUE;
        case 1:
            return new Arr();
        case 2:
            return new Obj();
        default:
            return kindValue(IndexKeys.TYPES[r.nextInt(4)], r);
        }
    }
    
    /** The levels of 020-10, section 3.3, by the decoded value and refEncode; null for none. */
    static byte[] refLevels(IndexDefinition d, String ikey, byte[] b) {
        if (!IndexReference.isObjectKey(PubKeys.i2u(ikey))) {
            return null;
        }
        Obj o;
        try {
            o = Ref.read(b);
        } catch (Refused e) {
            return null;
        }
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        for (int k = 0; k < d.levelCount(); k++) {
            Object v = o;
            for (String part : d.path(k)) {
                if (!(v instanceof Obj)) {
                    return null;
                }
                v = ((Obj) v).fields.get(ObjectFormatTester.chars(part.getBytes(
                        StandardCharsets.UTF_8)));
            }
            Object value;
            switch (d.type(k)) {
            case IndexKeys.LONG:
                if (!(v instanceof Long)) {
                    return null;
                }
                value = v;
                break;
            case IndexKeys.DOUBLE:
                if (!(v instanceof Dbl) || Double.isNaN(Double.longBitsToDouble(((Dbl) v).bits))) {
                    return null;
                }
                value = Double.longBitsToDouble(((Dbl) v).bits);
                break;
            case IndexKeys.STRING:
                if (!(v instanceof Str)) {
                    return null;
                }
                value = new String(ObjectFormatTester.bytes(((Str) v).bytes),
                        StandardCharsets.UTF_8);
                break;
            default:
                if (!(v instanceof Bin)) {
                    return null;
                }
                value = ObjectFormatTester.bytes(((Bin) v).bytes);
                break;
            }
            byte[] x = refEncode(d.type(k), value);
            out.write(x, 0, x.length);
        }
        return out.size() > IndexKeys.MAX_LEVEL_BYTES ? null : out.toByteArray();
    }
    
    // ======== Area 4: the get into Data Object classes (020-09) ========
    
    /** A Data Object class with a field of every type of 020-09's closed list. */
    public static class AllTypes {
        public boolean z = true;
        public byte b = 7;
        public short s = 7;
        public char c = 'q';
        public int i = 7;
        public long l = 7;
        public float f = 7.5f;
        public double d = 7.5;
        public Boolean zw = Boolean.TRUE;
        public Byte bw = 7;
        public Short sw = 7;
        public Character cw = 'q';
        public Integer iw = 7;
        public Long lw = 7L;
        public Float fw = 7.5f;
        public Double dw = 7.5;
        public String str = "seven";
        public byte[] bytes = {7};
        public boolean[] za = {true};
        public char[] ca = {'q'};
        public short[] sa = {7};
        public int[] ia = {7};
        public long[] la = {7};
        public float[] fa = {7.5f};
        public double[] da = {7.5};
        public Boolean[] zwa = {true};
        public Byte[] bwa = {7};
        public Character[] cwa = {'q'};
        public Short[] swa = {7};
        public Integer[] iwa = {7};
        public Long[] lwa = {7L};
        public Float[] fwa = {7.5f};
        public Double[] dwa = {7.5};
        public String[] stra = {"seven"};
        public byte[][] bb = {{7}};
        public byte[][][] bbb = {{{7}}};
        public int[][] iaa = {{7}};
        public String[][] straa = {{"seven"}};
        public long[][][] laaa = {{{7}}};
        public Inner inner = new Inner();
        public Inner[] inners = {new Inner()};
        public Inner[][] inners2 = {{new Inner()}};
        public transient int notStored = 9;
        public static int alsoNotStored = 9;
        
        public AllTypes() {}
    }
    
    /** A nested Data Object class, which may hold itself. */
    public static class Inner {
        public int v = 3;
        public String t = "t";
        public Inner next;
        public double[] xs = {1.5};
        public char ch = 'w';
        
        public Inner() {}
    }
    
    /** A Data Object class that extends another: its stored fields are both's. */
    public static class Sub extends Inner {
        public long extra = 11;
        public Integer[][] grid;
        
        public Sub() {}
    }
    
    /** The classes a get is made into at the top, with the field that holds the value. */
    static final Class<?>[] TOP_CLASSES = {AllTypes.class, Inner.class, Sub.class, int.class,
            Integer.class, long.class, char.class, Character.class, double.class, float.class,
            boolean.class, Byte.class, Short.class, int[].class, String[].class, byte[][].class,
            Inner[].class, double[][].class, Character[].class};
    
    /** One iteration of area 4. */
    void dataOne(long i) {
        Random r = random(seed, i);
        String where = "data seed " + seed + " iteration " + i;
        stats.iterations++;
        stats.inputs++;
        if (r.nextInt(5) == 0) {
            roundTrip(r, where);
            return;
        }
        Class<?> c = TOP_CLASSES[r.nextInt(r.nextBoolean() ? 3 : TOP_CLASSES.length)];
        Obj o;
        if (isDataClass(c)) {
            o = storedFor(c, r, 1);
        } else {
            o = new Obj();
            if (r.nextInt(6) > 0) {
                o.fields.put(c.isArray() ? "array" : "p", valueFor(c, r, 1));
            }
            if (r.nextInt(4) == 0) {
                o.fields.put(c.isArray() ? "p" : "array", randomValue(r, 2));
            }
        }
        byte[] b;
        try {
            b = Ref.write(o, true);
        } catch (Refused e) {
            return;
        }
        Object want = refTop(o, c);
        Object got;
        try {
            got = r.nextBoolean() ? new KvToObjectImp().createObject(c, "/dp/-k", b)
                    : new DbObject(b).toJavaObject(c);
        } catch (Throwable e) {
            throw fail(where, "a get into " + c.getName() + " threw " + e, b, e);
        }
        String diff = diff(want, got, c.getName());
        if (diff != null) {
            throw fail(where, "a get into " + c.getName() + ": " + diff + "; stored " + o, b,
                    null);
        }
        stats.count(c.getSimpleName());
    }
    
    static boolean isDataClass(Class<?> c) {
        return c == AllTypes.class || c == Inner.class || c == Sub.class;
    }
    
    /** A stored object for the Data Object class 'c': some of its fields, of any kind. */
    static Obj storedFor(Class<?> c, Random r, int level) {
        Obj o = new Obj();
        for (java.lang.reflect.Field f : storedFields(c)) {
            if (r.nextInt(5) < 3) {
                o.fields.put(ObjectFormatTester.chars(f.getName().getBytes(
                        StandardCharsets.UTF_8)), valueFor(f.getType(), r, level));
            }
        }
        if (r.nextInt(4) == 0) {
            o.fields.put(r.nextBoolean() ? "notStored" : "unknown", randomValue(r, level));
        }
        return o;
    }
    
    /** A stored value for a field of type 't': its natural kind half of the time. */
    static Object valueFor(Class<?> t, Random r, int level) {
        if (level >= 12 || r.nextBoolean()) {
            return randomValue(r, level);
        }
        if (t.isArray() && t != byte[].class || (t == byte[].class && r.nextBoolean())) {
            Arr a = new Arr();
            int n = r.nextInt(5);
            Class<?> e = t.getComponentType();
            for (int k = 0; k < n; k++) {
                a.elements.add(valueFor(e, r, level + 1));
            }
            return a;
        }
        if (isDataClass(t)) {
            return storedFor(r.nextInt(4) == 0 ? Sub.class : t, r, level + 1);
        }
        return randomScalar(r);
    }
    
    /** A random stored value: a scalar mostly, an array or an object. */
    static Object randomValue(Random r, int level) {
        int k = r.nextInt(10);
        if (k == 0 && level < 12) {
            Arr a = new Arr();
            for (int n = r.nextInt(4); n > 0; n--) {
                a.elements.add(randomValue(r, level + 1));
            }
            return a;
        } else if (k == 1 && level < 12) {
            return storedFor(Inner.class, r, level + 1);
        }
        return randomScalar(r);
    }
    
    static final String[] TEXTS = {"12", " 12 ", "-5", "+7", "1.5", "-1.9", "1e3", "NaN",
            "Infinity", "-Infinity", "0x1p3", "0x10", "1_000", "١٢", "", " ", "true",
            "TRUE", " true", "1", "abc", "99999999999999999999", "-99999999999999999999",
            "9223372036854775807", "9223372036854775808", "-9223372036854775808",
            "-9223372036854775809", "9007199254740993", " 9007199254740993 ", "1e400",
            "-1e400", "1.00000017881393432617187499", "65", "A", "\u0000", "+", "-", "1d", "1f",
            "  -0  ", "-0", "0", "3.4028235e38", "3.4028236e38", "1.4e-45", "\t5\n", " 5",
            "65535", "65536", "-1", "127.9", "128", "-129", "32768", "2147483648", "+-1",
            "1e", ".5", "5.", "0x1.8p1", "NaNx", "Infinityx", "1e-400", " " + "7"};
    
    static Object randomScalar(Random r) {
        switch (r.nextInt(6)) {
        case 0: {
            long[] e = {0, 1, -1, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768,
                    -32769, 65535, 65536, Integer.MAX_VALUE, Integer.MAX_VALUE + 1L,
                    Integer.MIN_VALUE, Integer.MIN_VALUE - 1L, Long.MAX_VALUE, Long.MIN_VALUE,
                    (1L << 53) + 1, 65};
            return r.nextBoolean() ? e[r.nextInt(e.length)] : r.nextLong() >> r.nextInt(64);
        }
        case 1: {
            double[] e = {0.0, -0.0, Double.NaN, Double.POSITIVE_INFINITY,
                    Double.NEGATIVE_INFINITY, 1.5, -1.9, 0x1p63, -0x1p63, 0x1p64, 1e300, -1e300,
                    3.4028235e38, 3.4028236e38, 1.4e-45, 0.7e-45, Double.MIN_VALUE, 127.9,
                    128.0, -128.9, -129.0, 65535.5, 65536.0, 2147483647.5, 2147483648.0, 0.5,
                    -0.5, 9007199254740993.0, 1.0000001788139343};
            double x = r.nextInt(3) > 0 ? e[r.nextInt(e.length)]
                    : Double.longBitsToDouble(r.nextLong());
            return new Dbl(Double.doubleToRawLongBits(x != x ? Double.NaN : x));
        }
        case 2: {
            String t = r.nextInt(4) > 0 ? TEXTS[r.nextInt(TEXTS.length)] : randomString(r);
            return new Str(ObjectFormatTester.chars(t.getBytes(StandardCharsets.UTF_8)));
        }
        case 3: {
            byte[] x = r.nextBoolean() ? randomBytes(r) : illFormed(
                    "ab".getBytes(StandardCharsets.UTF_8), r);
            return new Bin(ObjectFormatTester.chars(x));
        }
        case 4:
            return Boolean.valueOf(r.nextBoolean());
        default:
            return r.nextBoolean() ? new Obj() : new Arr();
        }
    }
    
    /** The stored fields of a class: public, not static, not transient, its supers' too. */
    static List<java.lang.reflect.Field> storedFields(Class<?> c) {
        List<java.lang.reflect.Field> out = new ArrayList<>();
        for (java.lang.reflect.Field f : c.getFields()) {
            int m = f.getModifiers();
            if (!java.lang.reflect.Modifier.isStatic(m)
                    && !java.lang.reflect.Modifier.isTransient(m)) {
                out.add(f);
            }
        }
        return out;
    }
    
    /** A get at the top by 020-09, section 5.9: a class's object, or the field p or array. */
    static Object refTop(Obj o, Class<?> c) {
        if (isDataClass(c)) {
            return refConvert(o, c);
        }
        Object v = o.fields.get(c.isArray() ? "array" : "p");
        return v == null ? null : refConvert(v, c);
    }
    
    /**
     * A stored value converted to the type 't' by 020-09's table (section 5.4) and sections
     * 5.5 to 5.8, written here from its text, apart from DataObjects.
     */
    static Object refConvert(Object v, Class<?> t) {
        if (t == boolean.class || t == Boolean.class) {
            if (v instanceof Boolean) {
                return v;
            } else if (v instanceof Long) {
                return (Long) v != 0;
            } else if (v instanceof Dbl) {
                double x = Double.longBitsToDouble(((Dbl) v).bits);
                return x != 0.0 && !Double.isNaN(x);
            } else if (v instanceof Str) {
                return Boolean.parseBoolean(text(v));
            }
            return false;
        }
        if (t == long.class || t == Long.class) {
            return refToLong(v);
        } else if (t == int.class || t == Integer.class) {
            return (int) clamp(refToLong(v), Integer.MIN_VALUE, Integer.MAX_VALUE);
        } else if (t == short.class || t == Short.class) {
            return (short) clamp(refToLong(v), Short.MIN_VALUE, Short.MAX_VALUE);
        } else if (t == byte.class || t == Byte.class) {
            return (byte) clamp(refToLong(v), Byte.MIN_VALUE, Byte.MAX_VALUE);
        } else if (t == char.class || t == Character.class) {
            return (char) clamp(refToLong(v), 0, 65535);
        } else if (t == double.class || t == Double.class) {
            if (v instanceof Long) {
                return (double) (Long) v;
            } else if (v instanceof Dbl) {
                return Double.longBitsToDouble(((Dbl) v).bits);
            } else if (v instanceof Boolean) {
                return (Boolean) v ? 1.0 : 0.0;
            } else if (v instanceof Str) {
                try {
                    return Double.parseDouble(text(v));
                } catch (NumberFormatException e) {
                    return 0.0;
                }
            }
            return 0.0;
        } else if (t == float.class || t == Float.class) {
            if (v instanceof Long) {
                return (float) (long) (Long) v;
            } else if (v instanceof Dbl) {
                return (float) Double.longBitsToDouble(((Dbl) v).bits);
            } else if (v instanceof Boolean) {
                return (Boolean) v ? 1f : 0f;
            } else if (v instanceof Str) {
                try {
                    return Float.parseFloat(text(v));
                } catch (NumberFormatException e) {
                    return 0f;
                }
            }
            return 0f;
        } else if (t == String.class) {
            if (v instanceof Str) {
                return text(v);
            } else if (v instanceof Long) {
                return Long.toString((Long) v);
            } else if (v instanceof Dbl) {
                return Double.toString(Double.longBitsToDouble(((Dbl) v).bits));
            } else if (v instanceof Boolean) {
                return (Boolean) v ? "true" : "false";
            } else if (v instanceof Bin) {
                return new String(ObjectFormatTester.bytes(((Bin) v).bytes),
                        StandardCharsets.UTF_8);
            }
            return null;
        } else if (t == byte[].class) {
            if (v instanceof Str) {
                return ObjectFormatTester.bytes(((Str) v).bytes);
            } else if (v instanceof Bin) {
                return ObjectFormatTester.bytes(((Bin) v).bytes);
            } else if (v instanceof Arr) {
                return refArray((Arr) v, t);
            }
            return null;
        } else if (t.isArray()) {
            return v instanceof Arr ? refArray((Arr) v, t) : null;
        }
        if (!(v instanceof Obj)) {
            return null;
        }
        try {
            Object x = t.getConstructor().newInstance();
            for (java.lang.reflect.Field f : storedFields(t)) {
                Object fv = ((Obj) v).fields.get(ObjectFormatTester.chars(f.getName().getBytes(
                        StandardCharsets.UTF_8)));
                if (fv != null) {
                    f.set(x, refConvert(fv, f.getType()));
                }
            }
            return x;
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }
    
    static Object refArray(Arr a, Class<?> t) {
        Class<?> e = t.getComponentType();
        Object x = java.lang.reflect.Array.newInstance(e, a.elements.size());
        for (int k = 0; k < a.elements.size(); k++) {
            java.lang.reflect.Array.set(x, k, refConvert(a.elements.get(k), e));
        }
        return x;
    }
    
    static long clamp(long v, long least, long greatest) {
        return v < least ? least : v > greatest ? greatest : v;
    }
    
    /** As a long: 020-09, section 5.4's rows, and 5.5 for a text. */
    static long refToLong(Object v) {
        if (v instanceof Long) {
            return (Long) v;
        } else if (v instanceof Dbl) {
            return (long) Double.longBitsToDouble(((Dbl) v).bits);
        } else if (v instanceof Boolean) {
            return (Boolean) v ? 1 : 0;
        } else if (v instanceof Str) {
            String t = text(v).trim();
            if (t.matches("[+-]?[0-9]+")) {
                java.math.BigInteger x = new java.math.BigInteger(t);
                return x.bitLength() < 64 ? x.longValue() : x.signum() < 0 ? Long.MIN_VALUE
                        : Long.MAX_VALUE;
            }
            try {
                return (long) Double.parseDouble(t);
            } catch (NumberFormatException e) {
                return 0;
            }
        }
        return 0;
    }
    
    /** Null if 'want' and 'got' are the same value, deeply; else where they differ. */
    static String diff(Object want, Object got, String path) {
        if (want == null || got == null) {
            return want == got ? null : path + ": " + show(want) + ", got " + show(got);
        }
        if (want.getClass() != got.getClass()) {
            return path + ": a " + want.getClass().getSimpleName() + ", got a "
                    + got.getClass().getSimpleName();
        }
        if (want instanceof Double) {
            return Double.compare((Double) want, (Double) got) == 0 ? null : path + ": "
                    + want + ", got " + got;
        } else if (want instanceof Float) {
            return Float.compare((Float) want, (Float) got) == 0 ? null : path + ": " + want
                    + ", got " + got;
        } else if (want.getClass().isArray()) {
            int n = java.lang.reflect.Array.getLength(want);
            if (n != java.lang.reflect.Array.getLength(got)) {
                return path + ": " + n + " elements, got " + java.lang.reflect.Array.getLength(
                        got);
            }
            for (int k = 0; k < n; k++) {
                String d = diff(java.lang.reflect.Array.get(want, k),
                        java.lang.reflect.Array.get(got, k), path + "[" + k + "]");
                if (d != null) {
                    return d;
                }
            }
            return null;
        } else if (want.getClass().getEnclosingClass() == FormatFuzzer.class) {
            for (java.lang.reflect.Field f : want.getClass().getFields()) {
                if (java.lang.reflect.Modifier.isStatic(f.getModifiers())) {
                    continue;
                }
                try {
                    String d = diff(f.get(want), f.get(got), path + "." + f.getName());
                    if (d != null) {
                        return d;
                    }
                } catch (IllegalAccessException e) {
                    throw new AssertionError(e);
                }
            }
            return null;
        }
        return want.equals(got) ? null : path + ": " + show(want) + ", got " + show(got);
    }
    
    /**
     * The put and the get again (020-09, sections 4 and 5): an AllTypes of random values,
     * none null, written by toDbObject and read back is the same, -0.0 kept and every NaN
     * one; and its stored bytes read by the reference give the same.
     */
    void roundTrip(Random r, String where) {
        AllTypes x = new AllTypes();
        for (java.lang.reflect.Field f : storedFields(AllTypes.class)) {
            try {
                if (r.nextInt(3) > 0) {
                    f.set(x, natural(f.getType(), r, 1));
                } else if (!f.getType().isPrimitive() && r.nextInt(4) == 0) {
                    f.set(x, null);     // left out: the get keeps the constructor's value
                }
            } catch (IllegalAccessException e) {
                throw new AssertionError(e);
            }
        }
        DbObject d;
        try {
            d = DbObject.toDbObject(x);
        } catch (Throwable e) {
            throw fail(where, "toDbObject threw " + e, null, e);
        }
        byte[] b = d.getBytes();
        AllTypes back = new KvToObjectImp().createObject(AllTypes.class, "/dp/-k", b);
        AllTypes want = new AllTypes();
        for (java.lang.reflect.Field f : storedFields(AllTypes.class)) {
            try {
                if (f.get(x) != null) {
                    f.set(want, f.get(x));
                }
            } catch (IllegalAccessException e) {
                throw new AssertionError(e);
            }
        }
        String diff = diff(want, back, "AllTypes");
        if (diff != null) {
            throw fail(where, "put and got again: " + diff, b, null);
        }
        diff = diff(want, refConvert(Ref.read(b), AllTypes.class), "AllTypes");
        if (diff != null) {
            throw fail(where, "put, and read by the reference: " + diff, b, null);
        }
        stats.count("round trip");
    }
    
    /** A random Java value of the type 't', never null, no null element. */
    static Object natural(Class<?> t, Random r, int level) {
        if (t == boolean.class || t == Boolean.class) {
            return r.nextBoolean();
        } else if (t == byte.class || t == Byte.class) {
            return (byte) r.nextInt();
        } else if (t == short.class || t == Short.class) {
            return (short) r.nextInt();
        } else if (t == char.class || t == Character.class) {
            return (char) r.nextInt(65536);
        } else if (t == int.class || t == Integer.class) {
            return r.nextBoolean() ? r.nextInt() : r.nextInt(3) - 1;
        } else if (t == long.class || t == Long.class) {
            return r.nextLong() >> r.nextInt(64);
        } else if (t == float.class || t == Float.class) {
            float[] e = {0f, -0f, Float.NaN, Float.intBitsToFloat(0x7fc00001), Float.MAX_VALUE,
                    Float.MIN_VALUE, Float.POSITIVE_INFINITY, 1.1f};
            return r.nextBoolean() ? e[r.nextInt(e.length)] : Float.intBitsToFloat(r.nextInt());
        } else if (t == double.class || t == Double.class) {
            double[] e = {0.0, -0.0, Double.NaN, Double.longBitsToDouble(0x7ff0000000000001L),
                    Double.MAX_VALUE, Double.MIN_VALUE, Double.NEGATIVE_INFINITY, 1.1};
            return r.nextBoolean() ? e[r.nextInt(e.length)]
                    : Double.longBitsToDouble(r.nextLong());
        } else if (t == String.class) {
            return randomString(r);
        } else if (t.isArray()) {
            int n = level > 4 ? 0 : r.nextInt(4);
            Object a = java.lang.reflect.Array.newInstance(t.getComponentType(), n);
            for (int k = 0; k < n; k++) {
                java.lang.reflect.Array.set(a, k, natural(t.getComponentType(), r, level + 1));
            }
            return a;
        } else {
            Inner o = new Inner();
            o.v = r.nextInt();
            o.t = randomString(r);
            o.xs = (double[]) natural(double[].class, r, level + 1);
            o.ch = (char) r.nextInt(65536);
            o.next = level < 8 && r.nextBoolean() ? (Inner) natural(Inner.class, r, level + 1)
                    : null;
            return o;
        }
    }
    
    // ======== Area 2: what a stored value is, through a database ========
    
    /** The Data Object of area 2: the fields of its three indexes. */
    public static class Kind {
        public String s;
        public long l;
        public byte[] b;
        public double d;
        
        public Kind() {}
    }
    
    /** A value put: what the put is given, and the bytes stored. */
    static final class Put {
        final Object value;
        final byte[] stored;
        final String what;
        
        Put(Object value, byte[] stored, String what) {
            this.value = value;
            this.stored = stored;
            this.what = what;
        }
    }
    
    /** The indexes of area 2, all of the directory /k/. */
    static final String[] INDEXES = {"s", "l", "b", "d"};
    static final String[] INDEX_TYPES = {"string", "long", "bytes", "double"};
    static final char[] TYPE_OF = {IndexKeys.STRING, IndexKeys.LONG, IndexKeys.BYTES,
            IndexKeys.DOUBLE};
    
    /** The keys of area 2: own keys of /k/ (indexed) and /n/ (never), of every suffix. */
    static final String[] KEYS;
    
    static {
        List<String> keys = new ArrayList<>();
        for (String dir : new String[] {"/k/", "/n/"}) {
            for (String name : new String[] {"a", "b", "c"}) {
                for (String suffix : new String[] {"", ".obj", ".txt", ".bin"}) {
                    keys.add(dir + name + suffix);
                }
            }
            keys.add(dir + ".h");
            keys.add(dir + "v1.2");
        }
        KEYS = keys.toArray(new String[0]);
    }
    
    /** Whether a ukey is an object key: no suffix, or "obj" (Connection.put's Javadoc). */
    static boolean objectKey(String ukey) {
        String name = ukey.substring(ukey.lastIndexOf('/') + 1);
        int dot = name.lastIndexOf('.');
        String suffix = dot < 0 ? "" : name.substring(dot + 1);
        return suffix.isEmpty() || suffix.equals("obj");
    }
    
    /** One iteration of area 2: a database, puts and deletes, then every read checked. */
    void kindsOne(long i) {
        Random r = random(seed, i);
        String where = "kinds seed " + seed + " iteration " + i;
        stats.iterations++;
        bergdb.pub.Database db = bergdb.pub.Factory.database().memory().start();
        try {
            bergdb.pub.Connection c = db.connection();
            boolean indexFirst = r.nextBoolean();
            boolean indexed = false;
            java.util.TreeMap<String, Put> ref = new java.util.TreeMap<>();
            boolean[] active = new boolean[INDEXES.length];
            if (indexFirst) {
                build(db, ref, active, where);
                indexed = true;
            }
            int ops = 3 + r.nextInt(25);
            for (int k = 0; k < ops; k++) {
                if (r.nextInt(5) == 0) {
                    multiPut(c, indexed, ref, r, where);
                    continue;
                }
                String key = KEYS[r.nextInt(KEYS.length)];
                if (r.nextInt(8) == 0) {
                    c.delete(key);
                    ref.remove(key);
                    continue;
                }
                Put p = kindValue(r);
                put(c, key, p, indexed && key.startsWith("/k/"), ref, r, where);
                stats.inputs++;
            }
            if (!indexFirst) {
                build(db, ref, active, where);
            }
            verify(c, ref, active, r, where);
        } finally {
            db.close();
        }
    }
    
    /** Creates the indexes of /k/; each fails over a format-1 object, else is active. */
    void build(bergdb.pub.Database db, Map<String, Put> ref, boolean[] active, String where) {
        boolean format1 = false;
        for (Map.Entry<String, Put> e : ref.entrySet()) {
            format1 |= e.getKey().startsWith("/k/") && objectKey(e.getKey())
                    && ObjectFormat.isFormat1(e.getValue().stored);
        }
        for (int k = 0; k < INDEXES.length; k++) {
            bergdb.pub.util.JobStatus status;
            try {
                status = db.indexBuilder(INDEXES[k]).dir("/k/").type(INDEX_TYPES[k])
                        .field(INDEXES[k]).start().join();
            } catch (bergdb.pub.util.IndexBuildException e) {
                status = e.getStatus();
                Assert(format1 && e.getCause() instanceof bergdb.pub.DataFormatException,
                        where, "the build of " + INDEXES[k] + " failed: " + e + ", cause "
                        + e.getCause(), null);
                stats.count("build failed over format 1");
                continue;
            }
            Assert(!format1 && status.state() == bergdb.pub.util.JobStatus.State.ACTIVE,
                    where, "the build of " + INDEXES[k] + " ended " + status.state()
                    + (format1 ? ", not FAILED over a format-1 object" : ""), null);
            active[k] = true;
        }
    }
    
    /** Whether a last value of the transaction is refused for L6 (bergdb 024-24). */
    static boolean tooLongAny(Map<String, Put> last, boolean indexed) {
        for (Map.Entry<String, Put> e : last.entrySet()) {
            if (e.getValue() != null && indexed && levelsTooLong(e.getKey(), e.getValue())) {
                return true;
            }
        }
        return false;
    }
    
    /**
     * Whether the put of 'stored' at 'key' is refused for L6 (bergdb 024-17, QL4; 024-24):
     * an object at an object key of /k/ whose levels for one of its indexes pass 111 bytes.
     */
    static boolean levelsTooLong(String key, Put p) {
        if (!key.startsWith("/k/") || !objectKey(key) || p.value instanceof String
                || p.stored == null || ObjectFormat.isFormat1(p.stored)) {
            return false;
        }
        for (int k = 0; k < INDEXES.length; k++) {
            IndexDefinition d = new IndexDefinition(INDEXES[k], "/k/", 1, true,
                    new String[] {INDEX_TYPES[k]}, new String[][] {{INDEXES[k]}});
            try {
                d.entryForPut(PubKeys.u2i(key), p.stored);
            } catch (IllegalArgumentException e) {
                return true;
            }
        }
        return false;
    }
    
    /** A put, by w() or rw(); refused as Connection.put's Javadoc says, else stored. */
    void put(bergdb.pub.Connection c, String key, Put p, boolean indexed, Map<String, Put> ref,
            Random r, String where) {
        boolean object = !(p.value instanceof String) && !(p.value instanceof byte[]);
        Class<? extends Throwable> refused = object && !objectKey(key)
                ? IllegalArgumentException.class : indexed && p.value instanceof byte[]
                && objectKey(key) && ObjectFormat.isFormat1(p.stored)
                ? bergdb.pub.DataFormatException.class : indexed && levelsTooLong(key, p)
                ? IllegalArgumentException.class : null;
        Throwable got = null;
        try {
            if (r.nextBoolean()) {
                c.put(key, p.value);
            } else {
                c.rw(env -> env.put(key, p.value));
            }
        } catch (Throwable e) {
            got = e;
        }
        if (refused == null ? got != null : !refused.isInstance(got)) {
            throw fail(where, "a put of " + p.what + " at " + key + ": " + (got == null
                    ? "taken" : got.toString()) + ", expected " + (refused == null ? "taken"
                    : refused.getSimpleName()), p.stored, got);
        }
        if (got == null) {
            ref.put(key, p);
            stats.count("put " + p.what);
        } else {
            stats.count("put refused " + p.what);
        }
    }
    
    /**
     * An rw() of 2 to 4 puts and deletes, often at one key: each key's last operation is
     * the transaction's (bergdb 015-40); an object at a key with a suffix is refused at its
     * put, and a byte[] of format 1 that is a key's last value at an object key of an
     * indexed directory refuses the transaction; a refused transaction changes nothing.
     */
    void multiPut(bergdb.pub.Connection c, boolean indexed, Map<String, Put> ref, Random r,
            String where) {
        int n = 2 + r.nextInt(3);
        String[] keys = new String[n];
        Put[] puts = new Put[n];
        for (int k = 0; k < n; k++) {
            keys[k] = KEYS[r.nextInt(6)];
            puts[k] = r.nextInt(5) == 0 ? null : kindValue(r);
        }
        Class<? extends Throwable> refused = null;
        Map<String, Put> last = new java.util.LinkedHashMap<>();
        for (int k = 0; k < n && refused == null; k++) {
            if (puts[k] != null && !(puts[k].value instanceof String)
                    && !(puts[k].value instanceof byte[]) && !objectKey(keys[k])) {
                refused = IllegalArgumentException.class;
            }
            last.put(keys[k], puts[k]);
        }
        boolean tooLong = false;            // L6 (bergdb 024-24)
        for (Map.Entry<String, Put> e : last.entrySet()) {
            Put p = e.getValue();
            if (refused == null && p != null && p.value instanceof byte[] && indexed
                    && e.getKey().startsWith("/k/") && objectKey(e.getKey())
                    && ObjectFormat.isFormat1(p.stored)) {
                refused = bergdb.pub.DataFormatException.class;
            }
            tooLong |= refused == null && p != null && indexed && levelsTooLong(e.getKey(), p);
        }
        if (refused == null && tooLong) {
            refused = IllegalArgumentException.class;
        }
        // Format 1 at one key and L6 at another: the first key that indexEntries() reaches
        // decides which; either refuses the transaction.
        final boolean either = refused == bergdb.pub.DataFormatException.class && tooLongAny(
                last, indexed);
        Throwable got = null;
        try {
            c.rw(env -> {
                for (int k = 0; k < n; k++) {
                    if (puts[k] == null) {
                        env.delete(keys[k]);
                    } else {
                        env.put(keys[k], puts[k].value);
                    }
                }
            });
        } catch (Throwable e) {
            got = e;
        }
        StringBuilder ops = new StringBuilder();
        for (int k = 0; k < n; k++) {
            ops.append(k > 0 ? ", " : "").append(puts[k] == null ? "delete " + keys[k]
                    : "put " + puts[k].what + " at " + keys[k]);
        }
        if (refused == null ? got != null : !refused.isInstance(got)
                && !(either && got instanceof IllegalArgumentException)) {
            throw fail(where, "an rw() of " + ops + ": " + (got == null ? "taken"
                    : got.toString()) + ", expected " + (refused == null ? "taken"
                    : refused.getSimpleName()), null, got);
        }
        if (got == null) {
            for (Map.Entry<String, Put> e : last.entrySet()) {
                if (e.getValue() == null) {
                    ref.remove(e.getKey());
                } else {
                    ref.put(e.getKey(), e.getValue());
                }
            }
            stats.count("rw of " + n);
        } else {
            stats.count("rw refused");
        }
    }
    
    /** A value of one of the kinds that look like others. */
    Put kindValue(Random r) {
        Gen g = new Gen(r.nextLong());
        switch (r.nextInt(13)) {
        case 0: {
            String s = randomString(r);
            return new Put(s, s.getBytes(StandardCharsets.UTF_8), "String");
        }
        case 1: {
            String s = "bergo\u0001" + randomString(r);
            return new Put(s, s.getBytes(StandardCharsets.UTF_8), "String bergo1");
        }
        case 2: {
            byte[] b = format1Ascii(r);
            return new Put(new String(b, StandardCharsets.ISO_8859_1), b,
                    "String of format 1");
        }
        case 3: {
            byte[] b = Ref.write(kindObject(g, r), true);
            return new Put(b, b.clone(), "byte[] of format 2");
        }
        case 4: {
            byte[] b = Ref.write(kindObject(g, r), true);
            byte[] m;
            do {
                m = mutateBytes(b, r);
            } while (ObjectFormat.isStoredObject(m));
            if (m.length > 0 && r.nextBoolean()) {
                m[0] = (byte) 0x82;
            }
            return new Put(m, m.clone(), "byte[] not quite an object");
        }
        case 5: {
            String[] f1 = {ObjectFormatTester.FORMAT_1_ALL, ObjectFormatTester.FORMAT_1_DEFAULTS,
                    "626572676f010000", "626572676f01ffff"};
            byte[] b = StringUtil.hexStringToBytes(f1[r.nextInt(f1.length)]);
            return new Put(b, b.clone(), "byte[] of format 1");
        }
        case 6: {
            byte[] b = format1Ascii(r);
            return new Put(b, b.clone(), "byte[] of format 1, ASCII");
        }
        case 7: {
            byte[] b = randomBytes(r);
            return new Put(b, b.clone(), "byte[]");
        }
        case 8: {
            byte[] b = randomString(r).getBytes(StandardCharsets.UTF_8);
            return new Put(b, b.clone(), "byte[] of UTF-8");
        }
        case 9: {
            DbObject d = new DbObject(Ref.write(kindObject(g, r), true));
            return new Put(d, d.getBytes(), "DbObject");
        }
        case 10: {
            Kind k = new Kind();
            k.s = r.nextInt(4) == 0 ? null : randomString(r);
            k.l = (Long) levelValue(IndexKeys.LONG, r);
            k.b = r.nextInt(4) == 0 ? null : randomBytes(r);
            k.d = r.nextInt(8) == 0 ? Double.NaN : (Double) levelValue(IndexKeys.DOUBLE, r);
            return new Put(k, DbObject.toDbObject(k).getBytes(), "Kind");
        }
        case 11:
            return r.nextBoolean() ? new Put("", new byte[0], "String empty")
                    : new Put(new byte[0], new byte[0], "byte[] empty");
        default: {
            byte[] b = {(byte) 0x82, 0x48, 0};
            return r.nextBoolean() ? new Put(b, b.clone(), "byte[] the empty object")
                    : new Put(new byte[] {(byte) 0x82}, new byte[] {(byte) 0x82},
                    "byte[] the header");
        }
        }
    }
    
    /** An object with the indexes' fields, of their kinds mostly. */
    static Obj kindObject(Gen g, Random r) {
        Obj o = r.nextInt(3) == 0 ? g.sample() : new Obj();
        for (int k = 0; k < INDEXES.length; k++) {
            if (r.nextInt(5) > 0) {
                o.fields.put(INDEXES[k], r.nextInt(5) == 0 ? anyValue(r) : kindValue(
                        TYPE_OF[k], r));
            }
        }
        return o;
    }
    
    /**
     * A whole object of format 1 by its structure (ObjectFormat.isFormat1's Javadoc) whose
     * bytes are all ASCII, so that a String can hold them: "bergo", 1, a count, a table of
     * hashes and offsets, fields of types n, i, l, s, b and a.
     */
    static byte[] format1Ascii(Random r) {
        int n = r.nextInt(4);
        if (n == 0) {
            return new byte[] {'b', 'e', 'r', 'g', 'o', 1, 0, 0};
        }
        List<byte[]> fields = new ArrayList<>();
        for (int k = 0; k < n; k++) {
            ByteArrayOutputStream f = new ByteArrayOutputStream();
            char type = "nilsba".charAt(r.nextInt(6));
            f.write(type);
            f.write(1);
            f.write(0);
            f.write('a' + k);
            switch (type) {
            case 'n':
                f.write(r.nextInt(2));
                break;
            case 'i':
                for (int j = 0; j < 4; j++) {
                    f.write(r.nextInt(0x80));
                }
                break;
            case 'l':
                for (int j = 0; j < 8; j++) {
                    f.write(r.nextInt(0x80));
                }
                break;
            case 'a':
                f.write('x');
                f.write('z');
                break;
            default: {
                int size = r.nextInt(6);
                f.write(size);
                f.write(0);
                f.write(0);
                f.write(0);
                for (int j = 0; j < size; j++) {
                    f.write('a' + r.nextInt(26));
                }
                break;
            }
            }
            fields.add(f.toByteArray());
        }
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        out.write('b');
        out.write('e');
        out.write('r');
        out.write('g');
        out.write('o');
        out.write(1);
        out.write(n);
        out.write(0);
        int offset = 8 + 6 * n;
        for (byte[] f : fields) {
            out.write('h');
            out.write('h');
            out.write(offset);
            out.write(0);
            out.write(0);
            out.write(0);
            offset += f.length;
        }
        for (byte[] f : fields) {
            out.write(f, 0, f.length);
        }
        byte[] b = out.toByteArray();
        if (!ObjectFormat.isFormat1(b) || offset >= 0x80) {
            throw new AssertionError("not format 1 in ASCII: " + StringUtil.toHex(b));
        }
        return b;
    }
    
    /** Every get, every listing and every active index against the rules. */
    void verify(bergdb.pub.Connection c, Map<String, Put> ref, boolean[] active, Random r,
            String where) {
        for (String key : KEYS) {
            Put p = ref.get(key);
            byte[] b = p == null ? null : p.stored;
            String at = where + ", " + key + (p == null ? "" : " (" + p.what + ")");
            // byte[]: the stored bytes.
            Assert(Arrays.equals((byte[]) get(c, key, byte[].class), b), at,
                    "get as byte[]", b);
            // String: its UTF-8, or DataFormatException.
            check(at, "get as String", b, () -> c.get(key, String.class),
                    p == null ? null : expectString(b));
            check(at, "get as Object", b, () -> c.get(key, Object.class),
                    p == null ? null : expectObject(key, b));
            check(at, "get as DbObject", b, () -> c.get(key, DbObject.class),
                    p == null ? null : expectDbObject(key, b));
            check(at, "get as Kind", b, () -> c.get(key, Kind.class),
                    p == null ? null : expectKind(key, b));
        }
        for (String dir : new String[] {"/k/", "/n/"}) {
            listing(c, dir, byte[].class, ref, where);
            listing(c, dir, Object.class, ref, where);
            listing(c, dir, String.class, ref, where);
            listing(c, dir, DbObject.class, ref, where);
            listing(c, dir, Kind.class, ref, where);
        }
        for (int k = 0; k < INDEXES.length; k++) {
            if (active[k]) {
                scan(c, k, ref, r, where);
            }
        }
    }
    
    /** What a read gives: the value (compared by sameRead) or an exception's class. */
    interface Read {
        Object read();
    }
    
    void check(String at, String what, byte[] b, Read read, Object want) {
        Object got;
        try {
            got = read.read();
        } catch (Throwable e) {
            got = e.getClass();
            if (!(want instanceof Class) || !((Class<?>) want).isInstance(e)) {
                throw fail(at, what + ": threw " + e + ", expected " + show(want), b, e);
            }
            return;
        }
        if (!sameRead(want, got)) {
            throw fail(at, what + ": " + show(got) + ", expected " + show(want)
                    + (want instanceof Kind && got instanceof Kind ? ": " + diff(want, got,
                    "Kind") : ""), b, null);
        }
    }
    
    static Object get(bergdb.pub.Connection c, String key, Class<?> type) {
        return c.get(key, type);
    }
    
    /** Whether two reads are the same: bytes, Strings, DbObjects by bytes, Kinds by fields. */
    static boolean sameRead(Object want, Object got) {
        if (want == null || got == null) {
            return want == got;
        } else if (want instanceof byte[]) {
            return got instanceof byte[] && Arrays.equals((byte[]) want, (byte[]) got);
        } else if (want instanceof DbObject) {
            return got instanceof DbObject && Arrays.equals(((DbObject) want).getBytes(),
                    ((DbObject) got).getBytes());
        } else if (want instanceof Kind) {
            return got instanceof Kind && diff(want, got, "Kind") == null;
        }
        return want.equals(got);
    }
    
    /** get(key, String.class): the UTF-8 decoded, or DataFormatException (bergdb 021-06). */
    static Object expectString(byte[] b) {
        return Ref.wellFormed(b) ? new String(b, StandardCharsets.UTF_8)
                : bergdb.pub.DataFormatException.class;
    }
    
    /** get(key, Object.class), by Connection.get's Javadoc. */
    static Object expectObject(String key, byte[] b) {
        if (objectKey(key) && ObjectFormat.isFormat1(b)) {
            return bergdb.pub.ObjectCreationException.class;
        }
        if (objectKey(key) && b.length > 0 && (b[0] & 0xff) == 0x82 && refAccepts(b)) {
            return new DbObject(b);
        }
        if (key.endsWith(".txt")) {
            return expectString(b);
        }
        return b;
    }
    
    /** get(key, DbObject.class): the stored object, or ObjectCreationException. */
    static Object expectDbObject(String key, byte[] b) {
        return refAccepts(b) ? new DbObject(b) : bergdb.pub.ObjectCreationException.class;
    }
    
    static Object expectKind(String key, byte[] b) {
        return refAccepts(b) ? refConvert(Ref.read(b), Kind.class)
                : bergdb.pub.ObjectCreationException.class;
    }
    
    static boolean refAccepts(byte[] b) {
        try {
            Ref.read(b);
            return true;
        } catch (Refused e) {
            return false;
        }
    }
    
    /** Whether a value is an object to the listings: UsePrimaryBuilder's Javadoc. */
    static boolean listedAsObject(String key, byte[] b) {
        return objectKey(key) && (ObjectFormat.isFormat1(b) || (b.length > 0
                && (b[0] & 0xff) == 0x82 && refAccepts(b)));
    }
    
    /**
     * usePrimary(type) of a directory against the reference: its own keys in key order, each
     * of the type's kind (UsePrimaryBuilder's Javadoc), each value or exception as get's.
     */
    void listing(bergdb.pub.Connection c, String dir, Class<?> type, Map<String, Put> ref,
            String where) {
        List<String> want = new ArrayList<>();
        for (Map.Entry<String, Put> e : ref.entrySet()) {
            String key = e.getKey();
            if (!key.startsWith(dir)) {
                continue;
            }
            boolean object = listedAsObject(key, e.getValue().stored);
            if (type == byte[].class || type == Object.class
                    || (type == String.class) != object) {
                want.add(key);
            }
        }
        want.sort((x, y) -> Arrays.compareUnsigned(bergdb.dag.Keys.toBytes(PubKeys.u2i(x)),
                bergdb.dag.Keys.toBytes(PubKeys.u2i(y))));
        String at = where + ", usePrimary(" + type.getSimpleName() + ") of " + dir;
        java.util.Iterator<? extends bergdb.pub.Kv<?>> it = c.usePrimary(type).dir(dir).kvs()
                .iterator();
        int k = 0;
        while (true) {
            boolean has;
            try {
                has = it.hasNext();
            } catch (Throwable e) {
                throw fail(at, "hasNext() threw " + e, null, e);
            }
            if (!has) {
                break;
            }
            Assert(k < want.size(), at, "more keys than " + want, null);
            String key = want.get(k++);
            byte[] b = ref.get(key).stored;
            Object expect = type == byte[].class ? b : type == Object.class
                    ? expectObject(key, b) : type == String.class ? expectString(b)
                    : type == DbObject.class ? (ObjectFormat.isFormat1(b)
                    ? bergdb.pub.ObjectCreationException.class : new DbObject(b))
                    : ObjectFormat.isFormat1(b) ? bergdb.pub.ObjectCreationException.class
                    : refConvert(Ref.read(b), Kind.class);
            final java.util.Iterator<? extends bergdb.pub.Kv<?>> fit = it;
            Object[] kv = new Object[1];
            check(at + ", " + key, "next()", b, () -> {
                bergdb.pub.Kv<?> x = fit.next();
                kv[0] = x.key();
                return x.value();
            }, expect);
            Assert(kv[0] == null || kv[0].equals(key), at, "the key " + kv[0] + ", expected "
                    + key, b);
            stats.lookups++;
        }
        Assert(k == want.size(), at, k + " keys, expected " + want, null);
    }
    
    /** A whole scan of index k against the reference's entries, in order. */
    void scan(bergdb.pub.Connection c, int k, Map<String, Put> ref, Random r, String where) {
        IndexDefinition d = new IndexDefinition(INDEXES[k], "/k/", 1, true,
                new String[] {INDEX_TYPES[k]}, new String[][] {{INDEXES[k]}});
        List<byte[]> entries = new ArrayList<>();
        Map<String, String> keys = new java.util.HashMap<>();
        for (Map.Entry<String, Put> e : ref.entrySet()) {
            String key = e.getKey();
            if (!key.startsWith("/k/")) {
                continue;
            }
            String ikey = PubKeys.u2i(key);
            byte[] levels = refLevels(d, ikey, e.getValue().stored);
            if (levels != null) {
                byte[] entry = insert(levels, levels.length, IndexKeys.fileKey(ikey));
                entries.add(entry);
                keys.put(StringUtil.toHex(entry), key);
            }
        }
        entries.sort(Arrays::compareUnsigned);
        String at = where + ", useIndex(" + INDEXES[k] + ")";
        int n = 0;
        for (bergdb.pub.Kv<Kind> kv : c.useIndex(INDEXES[k], Kind.class).kvs()) {
            Assert(n < entries.size(), at, "more results than the " + entries.size()
                    + " entries", null);
            String key = keys.get(StringUtil.toHex(entries.get(n++)));
            Assert(kv.key().equals(key), at, "the key " + kv.key() + ", expected " + key, null);
            Object want = refConvert(Ref.read(ref.get(key).stored), Kind.class);
            Assert(diff(want, kv.value(), "Kind") == null, at, "the value at " + key + ": "
                    + diff(want, kv.value(), "Kind"), ref.get(key).stored);
            stats.lookups++;
        }
        Assert(n == entries.size(), at, n + " results, expected " + entries.size(), null);
        
        // Scans with bounds (020-10, section 3.4), against the entries' level values.
        List<Object> values = new ArrayList<>();
        List<String> sorted = new ArrayList<>();
        for (byte[] entry : entries) {
            String key = keys.get(StringUtil.toHex(entry));
            sorted.add(key);
            values.add(levelOf(k, Ref.read(ref.get(key).stored)));
        }
        for (int t = 0; t < 4; t++) {
            boundedScan(c, k, sorted, values, r, at);
        }
    }
    
    /** The value of index k's level in a decoded object of its kind. */
    static Object levelOf(int k, Obj o) {
        Object v = o.fields.get(INDEXES[k]);
        switch (TYPE_OF[k]) {
        case IndexKeys.LONG:
            return v;
        case IndexKeys.DOUBLE:
            return Double.longBitsToDouble(((Dbl) v).bits);
        case IndexKeys.STRING:
            return text(v);
        default:
            return ObjectFormatTester.bytes(((Bin) v).bytes);
        }
    }
    
    /**
     * One scan of index k with eq, from, to, from and to, or prefix, forward or backward:
     * the keys whose level meets the bound, in the entries' order (020-10, section 3.4); a
     * NaN, a lone surrogate or an argument of another type refused with
     * IllegalArgumentException.
     */
    void boundedScan(bergdb.pub.Connection c, int k, List<String> keys, List<Object> values,
            Random r, String where) {
        char type = TYPE_OF[k];
        bergdb.pub.UseIndexBuilder<Kind> b = c.useIndex(INDEXES[k], Kind.class);
        if (r.nextInt(12) == 0) {
            Object bad = type == IndexKeys.DOUBLE ? (Object) Double.NaN
                    : type == IndexKeys.STRING ? (r.nextBoolean() ? "x\ud800" : (Object) 5L)
                    : type == IndexKeys.LONG ? "5" : (Object) 5L;
            try {
                bound(b, r.nextInt(4), bad, true);
                throw fail(where, "a bound " + show(bad) + " taken", null, null);
            } catch (IllegalArgumentException e) {
                stats.count("bound refused");
                return;
            }
        }
        Object v = values.isEmpty() || r.nextInt(3) == 0 ? levelValue(type, r)
                : near(type, values.get(r.nextInt(values.size())), r);
        Object w = values.isEmpty() || r.nextInt(3) == 0 ? levelValue(type, r)
                : near(type, values.get(r.nextInt(values.size())), r);
        boolean iv = r.nextBoolean();
        boolean iw = r.nextBoolean();
        int how = r.nextInt(type == IndexKeys.STRING || type == IndexKeys.BYTES ? 5 : 4);
        String what;
        switch (how) {
        case 0:
            bound(b, 0, v, true);
            what = "eq(" + show(v) + ")";
            break;
        case 1:
            bound(b, 1, v, iv);
            what = "from(" + show(v) + ", " + iv + ")";
            break;
        case 2:
            bound(b, 2, v, iv);
            what = "to(" + show(v) + ", " + iv + ")";
            break;
        case 3:
            bound(b, 1, v, iv);
            bound(b, 2, w, iw);
            what = "from(" + show(v) + ", " + iv + ").to(" + show(w) + ", " + iw + ")";
            break;
        default:
            bound(b, 3, v, true);
            what = "prefix(" + show(v) + ")";
            break;
        }
        boolean back = r.nextBoolean();
        if (back) {
            b.backward();
        }
        List<String> want = new ArrayList<>();
        for (int i = 0; i < keys.size(); i++) {
            Object x = values.get(i);
            int cv = compareValues(type, x, v);
            boolean in;
            switch (how) {
            case 0:
                in = cv == 0;
                break;
            case 1:
                in = cv > 0 || (iv && cv == 0);
                break;
            case 2:
                in = cv < 0 || (iv && cv == 0);
                break;
            case 3: {
                int cw = compareValues(type, x, w);
                in = (cv > 0 || (iv && cv == 0)) && (cw < 0 || (iw && cw == 0));
                break;
            }
            default:
                in = type == IndexKeys.STRING ? ((String) x).startsWith((String) v)
                        : startsWith((byte[]) x, (byte[]) v);
                break;
            }
            if (in) {
                want.add(keys.get(i));
            }
        }
        if (back) {
            Collections.reverse(want);
        }
        List<String> got = new ArrayList<>();
        for (bergdb.pub.Kv<Kind> kv : b.kvs()) {
            got.add(kv.key());
        }
        Assert(got.equals(want), where, what + (back ? ".backward()" : "") + ": " + got
                + ", expected " + want, null);
        stats.count("bounded scan");
    }
    
    /** eq (0), from (1), to (2) or prefix (3) of a value, by its Java type. */
    static void bound(bergdb.pub.UseIndexBuilder<Kind> b, int how, Object v, boolean inclusive) {
        if (v instanceof Long) {
            long x = (Long) v;
            if (how == 0) {
                b.eq(x);
            } else if (how == 1) {
                b.from(x, inclusive);
            } else if (how == 2) {
                b.to(x, inclusive);
            } else {
                throw new IllegalArgumentException("no prefix of a long");
            }
        } else if (v instanceof Double) {
            double x = (Double) v;
            if (how == 0) {
                b.eq(x);
            } else if (how == 1) {
                b.from(x, inclusive);
            } else if (how == 2) {
                b.to(x, inclusive);
            } else {
                throw new IllegalArgumentException("no prefix of a double");
            }
        } else if (v instanceof String) {
            String x = (String) v;
            if (how == 0) {
                b.eq(x);
            } else if (how == 1) {
                b.from(x, inclusive);
            } else if (how == 2) {
                b.to(x, inclusive);
            } else {
                b.prefix(x);
            }
        } else {
            byte[] x = (byte[]) v;
            if (how == 0) {
                b.eq(x);
            } else if (how == 1) {
                b.from(x, inclusive);
            } else if (how == 2) {
                b.to(x, inclusive);
            } else {
                b.prefix(x);
            }
        }
    }
    
    // ======== Area 5: what a start reads of the indexes (020-10, section 4.5) ========
    
    /** The Data Object of area 5. */
    public static class Item {
        public String s;
        public long n;
        
        public Item() {}
    }
    
    static bergdb.pub.Database startOn(bergdb.stream.MemoryStream stream) {
        bergdb.pub.DatabaseBuilder builder = bergdb.pub.Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        return builder.start();
    }
    
    /**
     * One iteration of area 5: a database with two indexes on a memory stream, one change of
     * its internal keys written through the Core (a definition's bytes or fields, a
     * definition's key, a marker's key, an entry's key, a key under /#i/dii/, or a definition
     * made through IndexBuilder with edge names, directories and paths), and a start on a
     * copy of the stream: it starts exactly when the reference says the keys and values under
     * /#i/ are an index's (020-10, sections 4.1, 4.2 and 4.5), else it is refused with
     * InternalDataException (VersioningStreamException for format 1), nothing else; started,
     * each index is scanned, and every definition read is the one written.
     */
    void startsOne(long i) {
        Random r = random(seed, i);
        String where = "starts seed " + seed + " iteration " + i;
        stats.iterations++;
        stats.inputs++;
        bergdb.stream.MemoryStream stream = new bergdb.stream.MemoryStream();
        bergdb.pub.Database db = startOn(stream);
        String what;
        boolean expectOk;
        boolean scanMayRefuse = false;      // entries that a changed key or definition
                                            // no longer parses
        Class<?> refusal = bergdb.core.InternalDataException.class;
        byte[] key;
        byte[] value = new byte[0];
        try {
            bergdb.core.Db core = ((DatabaseImp) db).getDb();
            bergdb.pub.Connection c = db.connection();
            for (int k = 0; k < 4; k++) {
                Item x = new Item();
                x.s = "v" + r.nextInt(3);
                x.n = k;
                c.put("/p/x" + k, x);
                c.put("/q/y" + k, x);
            }
            db.indexBuilder("a").dir("/p/").type("string").field("s").start().join();
            db.indexBuilder("ab").dir("/q/").type("long").field("n").type("string")
                    .field("s").start().join();
            IndexDefinition a = IndexDefinition.read(core, "a", Long.MAX_VALUE);
            IndexDefinition ab = IndexDefinition.read(core, "ab", Long.MAX_VALUE);
            switch (r.nextInt(8)) {
            case 7: {       // a key under /p/ that is no key of it, then a build over /p/
                byte[][] junk = {bergdb.dag.Keys.toBytes("/dp/-a/b"),
                        bergdb.dag.Keys.toBytes("/dp/-a/-x0"),
                        bergdb.dag.Keys.toBytes("/dp/-a/dq/-c"),
                        bergdb.dag.Keys.toBytes("/dp/-"),
                        insert(bergdb.dag.Keys.toBytes("/dp/-z"), 6, new byte[] {(byte) 0xff}),
                        insert(bergdb.dag.Keys.toBytes("/dp/-z"), 6, new byte[] {'/' + 2})};
                Item x = new Item();
                x.s = "v" + r.nextInt(3);
                core.execute(core.trans().put(junk[r.nextInt(junk.length)],
                        DbObject.toDbObject(x).getBytes()).build());
                bergdb.pub.util.JobStatus status;
                try {
                    status = db.indexBuilder("c").dir("/p/").type("string").field("s")
                            .start().join();
                } catch (bergdb.pub.util.IndexBuildException e) {
                    throw fail(where, "a build over a key that is no key of the directory "
                            + "failed: " + e.getCause(), null, e);
                }
                IndexDefinition cd = ((DatabaseImp) db).getIndexManager().definition("c");
                int entries = ((DatabaseImp) db).getIndexManager().entries("c", cd.gen(),
                        Long.MAX_VALUE).size();
                Assert(status.state() == bergdb.pub.util.JobStatus.State.ACTIVE
                        && entries == 4, where, "a build over a key that is no key of the "
                        + "directory: " + status.state() + ", " + entries + " entries, not 4",
                        null);
                key = a.key();
                value = a.toBytes();
                expectOk = true;
                what = "a build over a key that is no key of the directory";
                break;
            }
            case 0: {
                byte[] b = a.toBytes();
                value = r.nextBoolean() ? mutateBytes(b, r) : extreme(b, r);
                key = a.key();
                expectOk = refDefinition(value);
                what = "a definition's bytes changed";
                scanMayRefuse = true;
                break;
            }
            case 1: {
                Obj o = ObjectFormatTester.codecDecode(a.toBytes());
                changeDefinition(o, r);
                try {
                    value = Ref.write(o, true);
                } catch (Refused e) {
                    value = a.toBytes();
                }
                key = a.key();
                expectOk = refDefinition(value);
                what = "a definition's field changed";
                scanMayRefuse = true;
                break;
            }
            case 2: {
                byte[] head = IndexKeys.definitionsPrefix();
                byte[] k0 = IndexKeys.definitionKey("c");
                key = insert(head, head.length, mutateBytes(Arrays.copyOfRange(k0, head.length,
                        k0.length), r));
                String name = keyName(key, head, r);
                if ("a".equals(name) || "ab".equals(name)) {
                    key = k0;
                    name = "c";
                }
                value = new IndexDefinition(name == null ? "c" : name, "/r/", 5, true,
                        new String[] {"long"}, new String[][] {{"n"}}).toBytes();
                expectOk = name != null;
                what = "a definition's key changed";
                break;
            }
            case 3: {
                long gen = r.nextBoolean() ? a.gen() : 1 + r.nextInt(1000);
                byte[] head = IndexKeys.markersPrefix();
                byte[] k0 = IndexKeys.markerKey(r.nextBoolean() ? "a" : "zz", gen);
                byte[] tail = Arrays.copyOfRange(k0, head.length, k0.length);
                key = insert(head, head.length, r.nextInt(3) == 0 ? tail : mutateBytes(tail, r));
                IndexKeys.Marker m;
                try {
                    m = IndexKeys.parseMarker(key);
                } catch (bergdb.core.InternalDataException e) {
                    m = null;
                }
                expectOk = m != null && !(m.name.equals("a") && m.gen == a.gen())
                        && !(m.name.equals("ab") && m.gen == ab.gen());
                what = "a marker's key changed";
                break;
            }
            case 4: {       // a start reads no entry
                byte[] p = (r.nextBoolean() ? a : ab).generationPrefix();
                byte[] tail = new byte[r.nextInt(12)];
                r.nextBytes(tail);
                key = insert(p, p.length, tail);
                expectOk = true;
                scanMayRefuse = true;
                what = "an entry's key changed";
                break;
            }
            case 5: {
                byte[] head = IndexKeys.format1Prefix();
                byte[] tail = new byte[r.nextInt(4)];
                r.nextBytes(tail);
                key = insert(head, head.length, tail);
                expectOk = false;
                refusal = bergdb.storage.VersioningStreamException.class;
                what = "a key under /#i/dii/";
                break;
            }
            default: {
                apiDefinition(db, r);
                key = a.key();
                value = a.toBytes();
                expectOk = true;
                what = "a definition made through IndexBuilder";
                break;
            }
            }
            core.execute(core.trans().put(key, value).build());
            db.sync();
        } finally {
            db.close();
        }
        
        bergdb.pub.Database again = null;
        Throwable got = null;
        try {
            again = startOn(stream.copy());
            bergdb.core.Db core = ((DatabaseImp) again).getDb();
            for (String name : new String[] {"a", "ab"}) {
                IndexDefinition d = ((DatabaseImp) again).getIndexManager().definition(name);
                IndexDefinition stored = IndexDefinition.read(core, name, Long.MAX_VALUE);
                Assert(d == null ? stored == null : d.equals(stored), where, what
                        + ": the start holds " + d + ", the stream " + stored, key);
                if (d != null && d.isActive()) {
                    try {
                        for (Item x : again.connection().useIndex(name, Item.class)
                                .objects()) {
                            Assert(x != null, where, "a null value", key);
                        }
                    } catch (bergdb.core.InternalDataException e) {
                        // A changed entry's key, or an entry of a changed definition, that
                        // does not parse: refused by the scan that meets it (020-10, section
                        // 4.4; F16-1).
                        Assert(scanMayRefuse, where, what + ": a scan threw " + e, key);
                        stats.count("scan refused a changed entry");
                    }
                }
            }
        } catch (Failure e) {
            throw e;
        } catch (Throwable e) {
            got = e;
        } finally {
            if (again != null) {
                again.close();
            }
        }
        if (expectOk ? got != null : !refusal.isInstance(got)) {
            throw fail(where, what + ": the start " + (got == null ? "went on" : "threw " + got)
                    + ", expected " + (expectOk ? "a start" : refusal.getSimpleName())
                    + "; the key " + IndexKeys.show(key), value, got);
        }
        stats.count(what + (got == null ? ": started" : ": refused"));
    }
    
    /** The name of a definition's key, or null if a start refuses it. */
    static String keyName(byte[] key, byte[] head, Random r) {
        try {
            return IndexKeys.nameOfDefinitionKey(key);
        } catch (bergdb.core.InternalDataException e) {
            return null;
        }
    }
    
    /** Whether bytes are a definition by 020-10, section 4.2 (refValidDefinition). */
    static boolean refDefinition(byte[] b) {
        try {
            return refValidDefinition(Ref.read(b));
        } catch (Refused e) {
            return false;
        }
    }
    
    /** An index made through IndexBuilder, of edge names, directories and paths, or refused. */
    static void apiDefinition(bergdb.pub.Database db, Random r) {
        try {
            bergdb.pub.IndexBuilder b = db.indexBuilder(indexName(r)).dir(dir(r));
            int levels = 1 + r.nextInt(r.nextBoolean() ? IndexDefinition.MAX_LEVELS : 2);
            for (int k = 0; k < levels; k++) {
                b.type(IndexKeys.typeName(IndexKeys.TYPES[r.nextInt(4)]));
                String[] path = path(r);
                if (path.length == 1 && r.nextBoolean()) {
                    b.field(path[0]);
                } else {
                    b.nestedField(path);
                }
            }
            b.start().join();
        } catch (IllegalArgumentException | IllegalStateException
                | bergdb.pub.IndexAlreadyExistsException e) {
            // The builder's refusals; the database is as before.
        }
    }
    
    // ======== The smaller readers: the format-1 guess, UTF-8, bkeys ========
    
    /**
     * One iteration of the smaller readers that 2026.4 added: ObjectFormat.isFormat1 on
     * changed objects of format 1 against a reference written from its Javadoc;
     * StringUtil.isWellFormedUtf8 and ObjectFormat.utf8Fault on bytes of well-formed and
     * ill-formed UTF-8 against Java's decoder (021-06; 020-07, R11); Keys.bkey2ikeyOrNull,
     * whose ikey's bkey is the bkey again (021-06).
     */
    void guessesOne(long i) {
        Random r = random(seed, i);
        String where = "guesses seed " + seed + " iteration " + i;
        stats.iterations++;
        stats.inputs++;
        // The format-1 guess.
        byte[] f1;
        switch (r.nextInt(4)) {
        case 0:
            f1 = StringUtil.hexStringToBytes(r.nextBoolean() ? ObjectFormatTester.FORMAT_1_ALL
                    : ObjectFormatTester.FORMAT_1_DEFAULTS);
            break;
        case 1:
            f1 = new byte[] {'b', 'e', 'r', 'g', 'o', 1, (byte) (r.nextBoolean() ? 0 : 0xff),
                    (byte) (r.nextBoolean() ? 0 : 0xff)};
            break;
        default:
            f1 = format1Ascii(r);
            break;
        }
        byte[] m = r.nextInt(5) == 0 ? f1 : r.nextBoolean() ? mutateBytes(f1, r)
                : extremeFormat1(f1, r);
        boolean got;
        try {
            got = ObjectFormat.isFormat1(m);
        } catch (Throwable e) {
            throw fail(where, "isFormat1 threw " + e, m, e);
        }
        boolean want = refIsFormat1(m);
        Assert(got == want, where, "isFormat1 says " + got + ", the reference " + want, m);
        stats.count(got ? "format 1" : "not format 1");
        
        // UTF-8: three readers agree.
        byte[] u = randomString(r).getBytes(StandardCharsets.UTF_8);
        if (r.nextBoolean()) {
            u = illFormed(u, r);
        }
        if (r.nextInt(4) == 0) {
            u = mutateBytes(u.length == 0 ? new byte[] {'a'} : u, r);
        }
        boolean wf = Ref.wellFormed(u);
        Assert(StringUtil.isWellFormedUtf8(u) == wf, where, "isWellFormedUtf8 "
                + StringUtil.isWellFormedUtf8(u) + ", Java's decoder " + wf, u);
        Assert((ObjectFormat.utf8Fault(u, 0, u.length) < 0) == wf, where, "utf8Fault "
                + ObjectFormat.utf8Fault(u, 0, u.length) + ", Java's decoder " + wf, u);
        stats.count(wf ? "UTF-8 well-formed" : "UTF-8 ill-formed");
        
        // A bkey's ikey, and its bkey again.
        byte[] k = u.length == 0 ? new byte[] {3} : u.clone();
        for (int j = 0; j < k.length; j++) {
            if (r.nextInt(4) == 0) {
                k[j] = (byte) SPECIAL[r.nextInt(SPECIAL.length)];
            }
        }
        String ikey = bergdb.dag.Keys.bkey2ikeyOrNull(k);
        boolean has = true;
        byte[] x = new byte[k.length];
        for (int j = 0; j < k.length && has; j++) {
            int c = k[j] & 0xff;
            has = c != 0 && c != '/' + 2;
            x[j] = (byte) (c == 1 ? '/' : c - 2);
        }
        has = has && Ref.wellFormed(x);
        Assert((ikey != null) == has, where, "bkey2ikeyOrNull " + (ikey != null)
                + ", the reference " + has, k);
        if (ikey != null) {
            Assert(Arrays.equals(bergdb.dag.Keys.toBytes(ikey), k), where, "the bkey of "
                    + "bkey2ikeyOrNull's ikey is another", k);
        }
    }
    
    /** A format-1 object with a number of its table or a field changed to an extreme. */
    static byte[] extremeFormat1(byte[] b, Random r) {
        byte[] m = b.clone();
        if (m.length <= 8) {
            return m;
        }
        int p = 6 + r.nextInt(m.length - 6);
        int size = 1 << r.nextInt(3);
        long[] e = {0, 1, -1, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, Integer.MAX_VALUE,
                Integer.MIN_VALUE, m.length, m.length - p, r.nextInt(m.length + 4)};
        long x = e[r.nextInt(e.length)];
        for (int k = 0; k < size && p + k < m.length; k++) {
            m[p + k] = (byte) (x >>> (8 * k));
        }
        return m;
    }
    
    /**
     * Whether 'b' is a whole object of format 1 by its structure, as ObjectFormat.isFormat1's
     * Javadoc says, written here apart: "bergo", 1, a count n (a little-endian short): -1 or
     * 0 and nothing after it, or 1 to 32,767 and n entries of 6 bytes (a hash, not checked,
     * and an offset, an int) and the n fields, each starting at its offset, the first right
     * after the table, each ending where the next starts and the last at the end; a field is
     * a type of "nildsbao", a name's size (a short, at least 1), the name, and a value that
     * fills the field: n 1 byte, 0 or 1; i 4; l and d 8; s, b and o a size (an int) and that
     * many bytes, or -1 and nothing, o's a whole object's length at least (8) and starting
     * "bergo" 1; a ends with 'z' or 'Z'.
     */
    static boolean refIsFormat1(byte[] b) {
        java.nio.ByteBuffer bb = java.nio.ByteBuffer.wrap(b)
                .order(java.nio.ByteOrder.LITTLE_ENDIAN);
        if (b.length < 8 || !new String(b, 0, 5, StandardCharsets.ISO_8859_1).equals("bergo")
                || b[5] != 1) {
            return false;
        }
        int n = bb.getShort(6);
        if (n == 0 || n == -1) {
            return b.length == 8;
        }
        if (n < 0) {
            return false;
        }
        long first = 8 + 6L * n;
        if (first > b.length) {
            return false;
        }
        long[] offsets = new long[n + 1];
        for (int i = 0; i < n; i++) {
            offsets[i] = bb.getInt(8 + 6 * i + 2);
        }
        offsets[n] = b.length;
        if (offsets[0] != first) {
            return false;
        }
        for (int i = 0; i < n; i++) {
            long p = offsets[i];
            long end = offsets[i + 1];
            if (end <= p || end > b.length || p < first) {
                return false;
            }
            int f = (int) p;
            int length = (int) (end - p);
            if (length < 4 || "nildsbao".indexOf((char) (b[f] & 0xff)) < 0) {
                return false;
            }
            int nameSize = bb.getShort(f + 1);
            if (nameSize < 1 || 3 + nameSize >= length) {
                return false;
            }
            int v = f + 3 + nameSize;
            int size = (int) end - v;
            switch ((char) b[f]) {
            case 'n':
                if (size != 1 || (b[v] != 0 && b[v] != 1)) {
                    return false;
                }
                break;
            case 'i':
                if (size != 4) {
                    return false;
                }
                break;
            case 'l':
            case 'd':
                if (size != 8) {
                    return false;
                }
                break;
            case 'a':
                if (b[(int) end - 1] != 'z' && b[(int) end - 1] != 'Z') {
                    return false;
                }
                break;
            default: {
                if (size < 4) {
                    return false;
                }
                int s = bb.getInt(v);
                if (s == -1) {
                    if (size != 4) {
                        return false;
                    }
                } else if (s != size - 4) {
                    return false;
                } else if (b[f] == 'o' && (s < 8 || !new String(b, v + 4, 5,
                        StandardCharsets.ISO_8859_1).equals("bergo") || b[v + 9] != 1)) {
                    return false;
                }
                break;
            }
            }
        }
        return true;
    }
    
    // ======== The corpus for the programs written apart ========

    /**
     * One line: the bytes in hex, the verdict ("ok" or the code), the codes expected ("-" if
     * none, "ok"), the decoded value in the corpus's notation, and the lookups as PATH=VALUE
     * separated by ';' (a path its names in hex joined by '.'; VALUE "absent").
     */
    void writeCorpus(byte[] m, String code, Set<String> expect, Obj value,
            List<List<byte[]>> paths) {
        stats.corpus++;
        StringBuilder s = new StringBuilder(StringUtil.toHex(m).toLowerCase());
        s.append('\t').append(code == null ? "ok" : code);
        s.append('\t').append(expect == null ? "-" : expect == OK ? "ok"
                : String.join(",", new java.util.TreeSet<>(expect)));
        s.append('\t');
        if (code == null) {
            ct(value, s);
            s.append('\t');
            int k = 0;
            for (List<byte[]> path : paths) {
                if (k++ >= 12) {
                    break;
                }
                for (int j = 0; j < path.size(); j++) {
                    s.append(j > 0 ? "." : "").append(StringUtil.toHex(path.get(j)).toLowerCase());
                }
                s.append('=');
                Object v = Ref.lookup(value, path);
                if (v == null) {
                    s.append("absent");
                } else {
                    ct(v, s);
                }
                s.append(';');
            }
        } else {
            s.append("-\t-");
        }
        corpus.println(s);
    }

    /** The corpus's notation of a value (FormatFuzzer's xcheck.py and XF2.java read it). */
    static void ct(Object v, StringBuilder s) {
        if (v instanceof Obj) {
            s.append('{');
            boolean first = true;
            for (Map.Entry<String, Object> e : ((Obj) v).fields.entrySet()) {
                s.append(first ? "" : ",").append(StringUtil.toHex(ObjectFormatTester.bytes(
                        e.getKey())).toLowerCase()).append(':');
                ct(e.getValue(), s);
                first = false;
            }
            s.append('}');
        } else if (v instanceof Arr) {
            s.append('[');
            boolean first = true;
            for (Object e : ((Arr) v).elements) {
                s.append(first ? "" : ",");
                ct(e, s);
                first = false;
            }
            s.append(']');
        } else if (v instanceof Long) {
            s.append('i').append(v);
        } else if (v instanceof Dbl) {
            s.append('d').append(String.format("%016x", ((Dbl) v).bits));
        } else if (v instanceof Str) {
            s.append('s').append(StringUtil.toHex(ObjectFormatTester.bytes(((Str) v).bytes))
                    .toLowerCase());
        } else if (v instanceof Bin) {
            s.append('b').append(StringUtil.toHex(ObjectFormatTester.bytes(((Bin) v).bytes))
                    .toLowerCase());
        } else {
            s.append((Boolean) v ? 'T' : 'F');
        }
    }

    // ======== Failures ========

    Failure fail(String where, String what, byte[] input, Throwable cause) {
        return new Failure(where + ": " + what + (input == null ? "" : "; input ("
                + input.length + " bytes) " + StringUtil.toHex(input, 0, Math.min(
                input.length, 600)) + (input.length > 600 ? "..." : "")), cause);
    }

    void Assert(boolean ok, String where, String what, byte[] input) {
        if (!ok) {
            throw fail(where, what, input, null);
        }
    }

    // ======== Running ========

    /** The areas, by name. */
    static final String[] AREAS = {"objects", "keys", "data", "kinds", "starts", "guesses"};

    /** One iteration of an area. */
    void one(String area, long i) {
        switch (area) {
        case "objects":
            objectsOne(i);
            break;
        case "keys":
            keysOne(i);
            break;
        case "data":
            dataOne(i);
            break;
        case "kinds":
            kindsOne(i);
            break;
        case "starts":
            startsOne(i);
            break;
        case "guesses":
            guessesOne(i);
            break;
        default:
            throw new IllegalArgumentException("no area " + area);
        }
    }

    /**
     * Runs 'area' from iteration 'first' until 'iterations' are done or 'millis' have passed,
     * whichever comes first; returns the next iteration.
     */
    long run(String area, long first, long iterations, long millis) {
        long end = System.currentTimeMillis() + Math.min(millis, Long.MAX_VALUE / 2);
        long i = first;
        while (i - first < iterations && System.currentTimeMillis() < end) {
            try {
                one(area, i);
            } catch (Failure e) {
                throw e;
            } catch (Throwable e) {
                throw new Failure(area + " seed " + seed + " iteration " + i + ": " + e, e);
            }
            i++;
        }
        return i;
    }

    // The unit group: each area for a fixed number of iterations of seed 1, about 2 seconds
    // in all; java/stress/fuzz.sh runs them for minutes, new seeds each day.
    
    /** Area objects: 3,000 iterations of seed 1. */
    @Nano
    public static void testFuzzObjects() {
        FormatFuzzer f = new FormatFuzzer(1);
        f.run("objects", 0, 3000, Long.MAX_VALUE);
        bergdb.nanotest.Assert.assertTrue(f.stats.toString(), f.stats.accepted > 300
                && f.stats.refused > 1000 && f.stats.expected > 1000);
    }
    
    /** Area keys: 3,000 iterations of seed 1. */
    @Nano
    public static void testFuzzKeys() {
        FormatFuzzer f = new FormatFuzzer(1);
        f.run("keys", 0, 3000, Long.MAX_VALUE);
        bergdb.nanotest.Assert.assertTrue(f.stats.toString(), f.stats.inputs > 10000);
    }
    
    /** Area data: 2,000 iterations of seed 1. */
    @Nano
    public static void testFuzzData() {
        FormatFuzzer f = new FormatFuzzer(1);
        f.run("data", 0, 2000, Long.MAX_VALUE);
        bergdb.nanotest.Assert.assertTrue(f.stats.toString(), f.stats.counts.get(
                "round trip") > 100);
    }
    
    /** Area starts: 200 starts of seed 1. */
    @Nano
    public static void testFuzzStarts() {
        FormatFuzzer f = new FormatFuzzer(1);
        f.run("starts", 0, 200, Long.MAX_VALUE);
        bergdb.nanotest.Assert.assertEquals(f.stats.toString(), 200, f.stats.iterations);
    }
    
    /** Area guesses: 5,000 iterations of seed 1. */
    @Nano
    public static void testFuzzGuesses() {
        FormatFuzzer f = new FormatFuzzer(1);
        f.run("guesses", 0, 5000, Long.MAX_VALUE);
        bergdb.nanotest.Assert.assertTrue(f.stats.toString(), f.stats.counts.get(
                "format 1") > 500 && f.stats.counts.get("UTF-8 ill-formed") > 500);
    }
    
    /** Area kinds: 40 databases of seed 1. */
    @Nano
    public static void testFuzzKinds() {
        FormatFuzzer f = new FormatFuzzer(1);
        f.run("kinds", 0, 40, Long.MAX_VALUE);
        bergdb.nanotest.Assert.assertTrue(f.stats.toString(), f.stats.inputs > 300
                && f.stats.counts.get("bounded scan") > 50);
    }

    /**
     * Usage: FormatFuzzer AREA|all SEED SECONDS [FIRST [CORPUS [EVERY]]]: runs the area (each,
     * for all) from iteration FIRST (default 0) for SECONDS; prints its counts; a failure is
     * printed with its seed and iteration, and the exit status is 1. CORPUS, a file for the
     * programs written apart (area objects), gets every EVERY-th input and each one with a
     * known verdict.
     */
    public static void main(String[] args) throws IOException {
        if (args.length < 3) {
            System.err.println("Usage: FormatFuzzer AREA|all SEED SECONDS [FIRST [CORPUS "
                    + "[EVERY]]]");
            System.exit(2);
        }
        String[] areas = args[0].equals("all") ? AREAS : args[0].split(",");
        long seed = Long.parseLong(args[1]);
        long millis = (long) (Double.parseDouble(args[2]) * 1000);
        long first = args.length > 3 ? Long.parseLong(args[3]) : 0;
        FormatFuzzer f = new FormatFuzzer(seed);
        if (args.length > 4) {
            f.corpus = new PrintStream(new FileOutputStream(args[4]), false, "UTF-8");
            f.corpusEvery = args.length > 5 ? Integer.parseInt(args[5]) : 1;
        }
        int status = 0;
        for (String area : areas) {
            long t0 = System.currentTimeMillis();
            f.stats = new Stats();
            try {
                long next = f.run(area, first, Long.MAX_VALUE, millis / areas.length);
                System.out.println("FormatFuzzer " + area + " seed " + seed + ": iterations "
                        + first + " to " + (next - 1) + ", " + (System.currentTimeMillis() - t0)
                        + " ms: " + f.stats);
            } catch (Failure e) {
                System.out.println("FormatFuzzer " + area + " seed " + seed + ": FAILED: "
                        + e.getMessage());
                if (e.getCause() != null) {
                    e.getCause().printStackTrace(System.out);
                }
                status = 1;
            }
        }
        if (f.corpus != null) {
            f.corpus.close();
        }
        System.out.println(status == 0 ? "FUZZ OK" : "FUZZ FAILED");
        System.exit(status);
    }
}
