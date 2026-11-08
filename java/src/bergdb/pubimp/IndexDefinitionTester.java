package bergdb.pubimp;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.InternalDataException;
import bergdb.core.Trans;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.DataFormatException;
import bergdb.pubimp.ObjectFormatTester.Arr;
import bergdb.pubimp.ObjectFormatTester.Bin;
import bergdb.pubimp.ObjectFormatTester.Dbl;
import bergdb.pubimp.ObjectFormatTester.Obj;
import bergdb.pubimp.ObjectFormatTester.Record;
import bergdb.pubimp.ObjectFormatTester.Str;
import bergdb.pubimp.ObjectFormatTester.Vn;

/**
 * Tests of IndexDefinition: an index's definition, its stored bytes (bergdb 020-10, section
 * 4.2) and its function (section 3.3), as 020-10, section 10.2, asks of step I0:
 * <ul>
 * <li>the vector index-definition-2 of doc-files/object-vectors.txt is the writer's bytes;
 *     definitions round trip;</li>
 * <li>every row of 4.2's table refused when broken, one test per row, and the rest of 4.2
 *     (exactly these fields, the name from the key, a stored object of format 2); the
 *     definition at a lookup time, read from a database;</li>
 * <li>the function's table (3.3) by stored kind, absent fields, paths through non-objects,
 *     values that are not objects, format 1, and the 4,096-byte limit; random objects against
 *     a reference written apart, on the model of ObjectFormatTester.</li>
 * </ul>
 * The test objects are written with ObjectFormatTester's codec of the model (Obj, Arr, ...),
 * so that they do not depend on DbObject. The night group runs the random function test with
 * more seeds.
 *
 * @author Frans Lundberg
 */
public class IndexDefinitionTester {
    private IndexDefinitionTester() {}

    static final String VECTOR = "index-definition-2";

    /** The definition of the vector index-definition-2. */
    static IndexDefinition sample() {
        return new IndexDefinition("fromAmount", "/payments/", 17941752000000000L, true,
                new String[] {"string", "long"}, new String[][] {{"from"}, {"amount"}});
    }

    /** A valid definition in VN (020-07, section 13.1), as the refusals' starting point. */
    static final String BASE = "{\"dir\":s\"/p/\",\"gen\":i7,\"levels\":[{\"path\":[s\"a\"],"
            + "\"type\":s\"long\"}],\"state\":s\"building\",\"version\":i1}";

    // ======== The bytes (020-10, section 4.2) ========

    /** The vector index-definition-2 is the writer's bytes of sample(), and reads back. */
    @Nano
    public static void testVector() throws IOException {
        Record rec = null;
        for (Record r : ObjectFormatTester.readVectors()) {
            if (r.kind.equals("valid") && r.id.equals(VECTOR)) {
                rec = r;
            }
        }
        Assert.assertTrue("the vector " + VECTOR, rec != null);
        byte[] b = ObjectFormatTester.unhex(rec.one("bytes"));
        ObjectFormatTester.assertBytes(VECTOR, b, sample().toBytes());
        Assert.assertEquals(sample(), IndexDefinition.fromBytes("fromAmount", b));
        Assert.assertEquals(Vn.parse(rec.one("value")), ObjectFormatTester.codecDecode(b));
    }

    /**
     * Definitions round trip: written, they pass 020-07's full check, read back equal, and
     * hold exactly 4.2's fields; parts with '.', ',', U+0000 and astral characters (S2-F14),
     * 8 levels, 16 parts, parts of 255 bytes, every type, both states, the edges of gen.
     */
    @Nano
    public static void testRoundTrip() {
        String[] part255 = {repeat("\u00e5", 127) + "x"};
        String[] parts16 = new String[16];
        Arrays.fill(parts16, "p");
        IndexDefinition[] defs = {
            sample(),
            new IndexDefinition("a", "/", 1, false, new String[] {"bytes"},
                    new String[][] {{"a.b", "c,d", "e f"}}),
            new IndexDefinition("x.y", "/a/b/c/", Long.MAX_VALUE, true,
                    new String[] {"double", "string", "bytes", "long", "long", "double",
                            "string", "bytes"},
                    new String[][] {{"a"}, {"b"}, {"c"}, {"d"}, {"e", "f"}, {"\u0000"},
                            {"\ud83d\ude00"}, part255}),
            new IndexDefinition("\u00e5", "/\u00e5 x/", 2, false, new String[] {"string"},
                    new String[][] {parts16}),
        };
        for (IndexDefinition d : defs) {
            byte[] b = d.toBytes();
            ObjectFormat.checkStored(b);
            IndexDefinition r = IndexDefinition.fromBytes(d.name(), b);
            Assert.assertEquals(d, r);
            Assert.assertEquals(d.hashCode(), r.hashCode());
            ObjectFormatTester.assertBytes(d.name(), b, r.toBytes());
            Obj o = ObjectFormatTester.codecDecode(b);
            Assert.assertEquals("[dir, gen, levels, state, version]", o.fields.keySet()
                    .toString());
            Assert.assertEquals(new Str(chars(d.dir())), o.fields.get("dir"));
            Assert.assertEquals(d.gen(), o.fields.get("gen"));
            Assert.assertEquals(new Str(d.isActive() ? "active" : "building"),
                    o.fields.get("state"));
            Assert.assertEquals(1L, o.fields.get("version"));
            Arr levels = (Arr) o.fields.get("levels");
            Assert.assertEquals(d.levelCount(), levels.elements.size());
            for (int i = 0; i < d.levelCount(); i++) {
                Obj level = (Obj) levels.elements.get(i);
                Assert.assertEquals("[path, type]", level.fields.keySet().toString());
                Assert.assertEquals(new Str(d.typeName(i)), level.fields.get("type"));
                Arr path = (Arr) level.fields.get("path");
                Assert.assertEquals(d.path(i).length, path.elements.size());
                for (int k = 0; k < d.path(i).length; k++) {
                    Assert.assertEquals(new Str(chars(d.path(i)[k])), path.elements.get(k));
                }
                Assert.assertEquals(IndexKeys.type(d.typeName(i)), d.type(i));
            }
        }

        Assert.assertEquals("/dp/dq/", new IndexDefinition("n", "/p/q/", 1, false,
                new String[] {"long"}, new String[][] {{"a"}}).idir());
        Assert.assertTrue("another name", !sample().equals(new IndexDefinition("other",
                "/payments/", 17941752000000000L, true, new String[] {"string", "long"},
                new String[][] {{"from"}, {"amount"}})));
        Assert.assertTrue("another path", !sample().equals(new IndexDefinition("fromAmount",
                "/payments/", 17941752000000000L, true, new String[] {"string", "long"},
                new String[][] {{"from"}, {"amount", "x"}})));
    }

    /** The activation: the state only changes; the bytes differ in the state only. */
    @Nano
    public static void testActivated() {
        IndexDefinition b = new IndexDefinition("n", "/p/", 9, false, new String[] {"long"},
                new String[][] {{"a"}});
        Assert.assertFalse(b.isActive());
        IndexDefinition a = b.activated();
        Assert.assertTrue(a.isActive());
        Assert.assertEquals(new IndexDefinition("n", "/p/", 9, true, new String[] {"long"},
                new String[][] {{"a"}}), a);
        Obj ob = ObjectFormatTester.codecDecode(b.toBytes());
        Obj oa = ObjectFormatTester.codecDecode(a.toBytes());
        ob.fields.remove("state");
        oa.fields.remove("state");
        Assert.assertEquals(ob, oa);
        Assert.assertArrayEquals(IndexKeys.definitionKey("n"), a.key());
        Assert.assertArrayEquals(IndexKeys.generationPrefix("n", 9), a.generationPrefix());
    }

    // ======== The refusals of 020-10, section 4.2: one test per row ========

    /** Not a stored object of format 2 (020-07's full check): refused, naming the key. */
    @Nano
    public static void testRefusedNotAnObject() throws IOException {
        byte[] good = ObjectFormatTester.codecWrite(obj(BASE));
        IndexDefinition.fromBytes("n", good);
        assertRefusedBytes("empty", "n", new byte[0], "format 2");
        assertRefusedBytes("a string", "n", "hello".getBytes(StandardCharsets.UTF_8),
                "format 2");
        assertRefusedBytes("trailing", "n", IndexKeysTester.concat(good,
                new byte[] {0}), "trailing");
        assertRefusedBytes("cut", "n", Arrays.copyOf(good, good.length - 1), "format 2");
        byte[] wide = good.clone();
        wide[1] = 0x49;
        assertRefusedBytes("another width", "n", wide, "format 2");
        for (Record r : ObjectFormatTester.readVectors()) {
            if (r.kind.equals("invalid") && r.id.startsWith("format-1")) {
                assertRefusedBytes(r.id, "n", ObjectFormatTester.unhex(r.one("bytes")),
                        "format-1");
            }
        }
    }

    /** Exactly 4.2's five fields, no other: a field more, or any of them absent. */
    @Nano
    public static void testRefusedFields() {
        assertRefused("a field more", with(BASE, "name", "s\"n\""), "'name'");
        assertRefused("a field more, x", with(BASE, "x", "i1"), "'x'");
        for (String f : new String[] {"version", "dir", "gen", "state", "levels"}) {
            assertRefused("no " + f, with(BASE, f, null), "'" + f + "'");
        }
    }

    /** Row 'version': an integer, 1. */
    @Nano
    public static void testRefusedVersion() {
        for (String v : new String[] {"i2", "i0", "i-1", "i256", "s\"1\"", "d3ff0000000000000",
                "true", "[i1]", "{}"}) {
            assertRefused("version " + v, with(BASE, "version", v), "'version'");
        }
    }

    /** Row 'dir': a string, the directory as the user gave it, valid by udir2idir. */
    @Nano
    public static void testRefusedDir() {
        for (String v : new String[] {"s\"\"", "s\"p/\"", "s\"/p\"", "s\"/p//q/\"",
                "s\"//\"", "i5", "b\"/p/\"", "[s\"/p/\"]", "{}"}) {
            assertRefused("dir " + v, with(BASE, "dir", v), "'dir'");
        }
        IndexDefinition.fromBytes("n", ObjectFormatTester.codecWrite(with(BASE, "dir",
                "s\"/\"")));
    }

    /** Row 'gen': an integer above 0. */
    @Nano
    public static void testRefusedGen() {
        for (String v : new String[] {"i0", "i-1", "i-9223372036854775808", "s\"7\"",
                "d401c000000000000", "true", "b\"7\""}) {
            assertRefused("gen " + v, with(BASE, "gen", v), "'gen'");
        }
        IndexDefinition.fromBytes("n", ObjectFormatTester.codecWrite(with(BASE, "gen",
                "i9223372036854775807")));
    }

    /** Row 'state': the string building or active. */
    @Nano
    public static void testRefusedState() {
        for (String v : new String[] {"s\"deleting\"", "s\"creating\"", "s\"Active\"", "s\"\"",
                "s\"active \"", "s\"building\\x00\"", "i1", "b\"active\"", "true"}) {
            assertRefused("state " + v, with(BASE, "state", v), "'state'");
        }
    }

    /**
     * Row 'levels': an array of 1 to 8 objects, each exactly {type: string, path: array of
     * strings}; type long, double, string or bytes; path of 1 to 16 strings, each a name of 1
     * to 255 bytes.
     */
    @Nano
    public static void testRefusedLevels() {
        String level = "{\"path\":[s\"a\"],\"type\":s\"long\"}";
        String[] bad = {
            "s\"x\"", "i1", "{}", "[]",
            "[" + repeat(level + ",", 8) + level + "]",
            "[s\"x\"]", "[[" + level + "]]", "[i1]",
            "[{\"path\":[s\"a\"],\"type\":s\"long\",\"x\":i1}]",
            "[{\"type\":s\"long\"}]",
            "[{\"path\":[s\"a\"]}]",
            "[{\"path\":[s\"a\"],\"type\":i1}]",
            "[{\"path\":[s\"a\"],\"type\":s\"int\"}]",
            "[{\"path\":[s\"a\"],\"type\":s\"string/unicode\"}]",
            "[{\"path\":[s\"a\"],\"type\":s\"Long\"}]",
            "[{\"path\":s\"a\",\"type\":s\"long\"}]",
            "[{\"path\":[],\"type\":s\"long\"}]",
            "[{\"path\":[" + repeat("s\"a\",", 16) + "s\"a\"],\"type\":s\"long\"}]",
            "[{\"path\":[i1],\"type\":s\"long\"}]",
            "[{\"path\":[s\"\"],\"type\":s\"long\"}]",
            "[{\"path\":[s\"" + repeat("x", 256) + "\"],\"type\":s\"long\"}]",
            "[{\"path\":[{}],\"type\":s\"long\"}]",
            "[{\"path\":[b\"a\"],\"type\":s\"long\"}]",
            "[" + level + ",{\"path\":[s\"a\"],\"type\":s\"float\"}]",
        };
        for (String v : bad) {
            assertRefused("levels " + v, with(BASE, "levels", v), "'levels'");
        }
        String ok8 = "[" + repeat(level + ",", 7) + level + "]";
        Assert.assertEquals(8, IndexDefinition.fromBytes("n", ObjectFormatTester.codecWrite(
                with(BASE, "levels", ok8))).levelCount());
        String ok16 = "[{\"path\":[" + repeat("s\"a\",", 15) + "s\"" + repeat("x", 255)
                + "\"],\"type\":s\"bytes\"}]";
        Assert.assertEquals(16, IndexDefinition.fromBytes("n", ObjectFormatTester.codecWrite(
                with(BASE, "levels", ok16))).path(0).length);
    }

    /** The name, from the key: 020-10, section 3.1's rule. */
    @Nano
    public static void testRefusedName() {
        byte[] b = ObjectFormatTester.codecWrite(obj(BASE));
        for (String name : new String[] {"", "a b", "a\tb", "a/b", "\u2003",
                repeat("a", 256)}) {
            try {
                IndexDefinition.fromBytes(name, b);
                throw new AssertionError("name " + IndexKeysTester.show(name) + ": accepted");
            } catch (InternalDataException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("name"));
            }
        }
        Assert.assertEquals("primary", IndexDefinition.fromBytes("primary", b).name());
    }

    /** The writer's side: the constructor refuses what 4.2 and 3.1 do not allow. */
    @Nano
    public static void testConstructorRefusals() {
        String[] t1 = {"long"};
        String[][] p1 = {{"a"}};
        new IndexDefinition("n", "/p/", 1, false, t1, p1);
        refusedArg("name", () -> new IndexDefinition("a b", "/p/", 1, false, t1, p1));
        refusedArg("name null", () -> new IndexDefinition(null, "/p/", 1, false, t1, p1));
        refusedArg("dir", () -> new IndexDefinition("n", "/p", 1, false, t1, p1));
        refusedArg("dir null", () -> new IndexDefinition("n", null, 1, false, t1, p1));
        refusedArg("dir, a lone surrogate", () -> new IndexDefinition("n", "/\ud800/", 1,
                false, t1, p1));
        refusedArg("gen 0", () -> new IndexDefinition("n", "/p/", 0, false, t1, p1));
        refusedArg("gen -1", () -> new IndexDefinition("n", "/p/", -1, false, t1, p1));
        refusedArg("no level", () -> new IndexDefinition("n", "/p/", 1, false, new String[0],
                new String[0][]));
        String[] t9 = new String[9];
        String[][] p9 = new String[9][];
        Arrays.fill(t9, "long");
        Arrays.fill(p9, new String[] {"a"});
        refusedArg("9 levels", () -> new IndexDefinition("n", "/p/", 1, false, t9, p9));
        refusedArg("types and paths", () -> new IndexDefinition("n", "/p/", 1, false,
                new String[] {"long", "long"}, p1));
        refusedArg("type", () -> new IndexDefinition("n", "/p/", 1, false,
                new String[] {"int"}, p1));
        refusedArg("type null", () -> new IndexDefinition("n", "/p/", 1, false,
                new String[] {null}, p1));
        refusedArg("path empty", () -> new IndexDefinition("n", "/p/", 1, false, t1,
                new String[][] {{}}));
        refusedArg("path null", () -> new IndexDefinition("n", "/p/", 1, false, t1,
                new String[][] {null}));
        String[] parts17 = new String[17];
        Arrays.fill(parts17, "a");
        refusedArg("17 parts", () -> new IndexDefinition("n", "/p/", 1, false, t1,
                new String[][] {parts17}));
        refusedArg("part empty", () -> new IndexDefinition("n", "/p/", 1, false, t1,
                new String[][] {{"a", ""}}));
        refusedArg("part null", () -> new IndexDefinition("n", "/p/", 1, false, t1,
                new String[][] {{null}}));
        refusedArg("part 256 bytes", () -> new IndexDefinition("n", "/p/", 1, false, t1,
                new String[][] {{repeat("\u00e5", 128)}}));
        refusedArg("part, a lone surrogate", () -> new IndexDefinition("n", "/p/", 1, false,
                t1, new String[][] {{"a\udc00"}}));

        // The definition keeps copies of the arrays it is given.
        String[] t = {"long"};
        String[][] p = {{"a", "b"}};
        IndexDefinition d = new IndexDefinition("n", "/p/", 1, false, t, p);
        t[0] = "string";
        p[0][1] = "c";
        Assert.assertEquals("long", d.typeName(0));
        Assert.assertEquals("b", d.path(0)[1]);
        d.path(0)[1] = "x";
        Assert.assertEquals("b", d.path(0)[1]);
    }

    /**
     * read(db, name, t): the definition at a lookup time, from a database: none before it,
     * building, then active, none after its deletion; bytes that break 4.2 an
     * InternalDataException; a name that breaks 3.1 has none.
     */
    @Nano
    public static void testRead() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        try {
            IndexDefinition building = new IndexDefinition("n", "/p/", 50, false,
                    new String[] {"long"}, new String[][] {{"a"}});
            clock.setTime(100);
            long t1 = execute(db, db.trans().put(building.key(), building.toBytes()));
            clock.setTime(200);
            long t2 = execute(db, db.trans().put(building.key(),
                    building.activated().toBytes()));
            clock.setTime(300);
            long t3 = execute(db, db.trans().delete(building.key()));
            clock.setTime(400);
            byte[] bad = ObjectFormatTester.codecWrite(with(BASE, "state", "s\"deleting\""));
            long t4 = execute(db, db.trans().put(building.key(), bad));

            assertNull(IndexDefinition.read(db, "n", t1 - 1));
            Assert.assertEquals(building, IndexDefinition.read(db, "n", t1));
            Assert.assertEquals(building, IndexDefinition.read(db, "n", t2 - 1));
            Assert.assertEquals(building.activated(), IndexDefinition.read(db, "n", t2));
            assertNull(IndexDefinition.read(db, "n", t3));
            assertNull(IndexDefinition.read(db, "m", t2));
            assertNull(IndexDefinition.read(db, "a/b", t2));
            assertNull(IndexDefinition.read(db, "", t2));
            for (long t : new long[] {t4, Long.MAX_VALUE}) {
                try {
                    IndexDefinition.read(db, "n", t);
                    throw new AssertionError("bad bytes read");
                } catch (InternalDataException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains("/#i/didef/-n")
                            && e.getMessage().contains("'state'"));
                }
            }
            refusedArg("null name", () -> IndexDefinition.read(db, null, Long.MAX_VALUE));
        } finally {
            db.close();
        }
    }

    // ======== The function (020-10, section 3.3) ========

    /**
     * 3.3's table by stored kind: each type takes exactly its kind, at every width; -0.0 is
     * 0.0's entry; NaN, booleans, arrays and objects give none; nothing is converted.
     */
    @Nano
    public static void testFunctionTable() {
        String[] kinds = {"i0", "i-128", "i127", "i128", "i-32769", "i2147483648",
                "i-9223372036854775808", "i9223372036854775807",
                "d3ff8000000000000", "d8000000000000000", "d0000000000000000",
                "d7ff8000000000000", "dfff0000000000000", "d7ff0000000000000",
                "d0000000000000001",
                "s\"\"", "s\"a\\x00\\x01\"", "s\"" + repeat("x", 200) + "\"", "s<f09f9880>",
                "b\"\"", "b<0001ff>", "b\"" + repeat("y", 200) + "\"",
                "true", "false", "[]", "[i1]", "{}", "{\"v\":i1}"};
        int entries = 0;
        for (char type : IndexKeys.TYPES) {
            IndexDefinition d = new IndexDefinition("n", "/p/", 1, false,
                    new String[] {IndexKeys.typeName(type)}, new String[][] {{"v"}});
            for (String kind : kinds) {
                Obj o = obj("{\"v\":" + kind + "}");
                byte[] want = refLevels(o, d);
                byte[] got = d.entryLevels("/dp/-k", ObjectFormatTester.codecWrite(o));
                String what = IndexKeys.typeName(type) + " level, " + kind;
                assertLevels(what, want, got);
                Object v = o.fields.get("v");
                boolean kindMatches = type == IndexKeys.LONG ? v instanceof Long
                        : type == IndexKeys.DOUBLE ? v instanceof Dbl
                        && ((Dbl) v).bits != ObjectFormatTester.NAN
                        : type == IndexKeys.STRING ? v instanceof Str : v instanceof Bin;
                Assert.assertEquals(what, kindMatches, got != null);
                if (got != null) {
                    entries++;
                }
            }
        }
        Assert.assertEquals(8 + 6 + 4 + 3, entries);

        // -0.0 has 0.0's entry; the object keeps -0.0.
        IndexDefinition d = new IndexDefinition("n", "/p/", 1, false, new String[] {"double"},
                new String[][] {{"v"}});
        Assert.assertArrayEquals(d.entryLevels("/dp/-k", write("{\"v\":d0000000000000000}")),
                d.entryLevels("/dp/-k", write("{\"v\":d8000000000000000}")));
        Assert.assertArrayEquals(IndexKeys.encodeLong(-7), new IndexDefinition("n", "/p/", 1,
                false, new String[] {"long"}, new String[][] {{"v"}}).entryLevels("/dp/-k",
                write("{\"v\":i-7}")));
    }

    /** Absent fields give no entry: one level absent is enough; names are exact bytes. */
    @Nano
    public static void testFunctionAbsent() {
        IndexDefinition d = new IndexDefinition("n", "/p/", 1, false,
                new String[] {"long", "string"}, new String[][] {{"a"}, {"b"}});
        Assert.assertTrue("both", d.entryLevels("/dp/-k",
                write("{\"a\":i1,\"b\":s\"x\"}")) != null);
        for (String vn : new String[] {"{}", "{\"a\":i1}", "{\"b\":s\"x\"}",
                "{\"A\":i1,\"b\":s\"x\"}", "{\"a\\x00\":i1,\"b\":s\"x\"}",
                "{\"a\":i1,\"bb\":s\"x\"}", "{\"a\":i1,\"c\":s\"x\"}"}) {
            assertNull(vn, d.entryLevels("/dp/-k", write(vn)));
        }
        IndexDefinition e = new IndexDefinition("n", "/p/", 1, false, new String[] {"long"},
                new String[][] {{"\u00e5"}});
        Assert.assertTrue("a non-ASCII name", e.entryLevels("/dp/-k",
                write("{<c3a5>:i3}")) != null);
        assertNull(e.entryLevels("/dp/-k", write("{\"a\":i3}")));
    }

    /**
     * Paths: through nested objects; a path through a field that is absent, a scalar, a
     * string, an array, gives no entry; a name with '.' is one part; 16 parts.
     */
    @Nano
    public static void testFunctionPaths() {
        byte[] nested = write("{\"a\":{\"b\":{\"c\":i5}},\"s\":s\"t\",\"l\":[{\"b\":i1}],"
                + "\"a.b\":i9,\"n\":i2}");
        assertLevels("a.b.c", IndexKeys.encodeLong(5), level("long", nested, "a", "b", "c"));
        assertNull("a.b, an object", level("long", nested, "a", "b"));
        assertNull("a, an object", level("bytes", nested, "a"));
        assertNull("a.x.c", level("long", nested, "a", "x", "c"));
        assertNull("a.b.c.d, through an integer", level("long", nested, "a", "b", "c",
                "d"));
        assertNull("n.b, through an integer", level("long", nested, "n", "b"));
        assertNull("s.b, through a string", level("string", nested, "s", "b"));
        assertNull("l.b, through an array", level("long", nested, "l", "b"));
        assertNull("x.b, through an absent field", level("long", nested, "x", "b"));
        assertLevels("'a.b', one part", IndexKeys.encodeLong(9), level("long", nested, "a.b"));

        // 16 parts: 15 nested objects, the top at level 1, the deepest at level 16.
        String vn = "i42";
        String[] parts = new String[16];
        for (int i = 15; i >= 0; i--) {
            parts[i] = "f" + i;
            if (i > 0) {
                vn = "{\"f" + i + "\":" + vn + "}";
            }
        }
        byte[] deep = write("{\"f0\":" + vn + "}");
        assertLevels("16 parts", IndexKeys.encodeLong(42), level("long", deep, parts));
    }

    /**
     * Values that are not objects give no entry (020-10, section 3.3, rule 1): a String's
     * bytes, a byte[], bytes that start with 0x82 and fail the full check, a key with a
     * suffix; ".obj" is an object key. A format-1 object is refused: DataFormatException.
     */
    @Nano
    public static void testFunctionNotObjects() throws IOException {
        IndexDefinition d = new IndexDefinition("n", "/p/", 1, false, new String[] {"long"},
                new String[][] {{"a"}});
        byte[] o = write("{\"a\":i1}");
        Assert.assertTrue("an object", d.entryLevels("/dp/-k", o) != null);
        Assert.assertTrue(".obj", d.entryLevels("/dp/-k.obj", o) != null);
        assertNull(".txt", d.entryLevels("/dp/-k.txt", o));
        assertNull(".json", d.entryLevels("/dp/-k.json", o));
        assertNull("empty", d.entryLevels("/dp/-k", new byte[0]));
        assertNull("the header", d.entryLevels("/dp/-k", new byte[] {(byte) 0x82}));
        assertNull("a string", d.entryLevels("/dp/-k", "a1".getBytes(
                StandardCharsets.UTF_8)));
        assertNull("trailing", d.entryLevels("/dp/-k", IndexKeysTester
                .concat(o, new byte[] {0})));
        assertNull("cut", d.entryLevels("/dp/-k", Arrays.copyOf(o, o.length - 1)));
        assertNull("bergo, version 2", d.entryLevels("/dp/-k",
                new byte[] {'b', 'e', 'r', 'g', 'o', 2, 0, 0}));
        Random r = new Random(8);
        for (int k = 0; k < 2000; k++) {
            byte[] b = new byte[r.nextInt(12)];
            r.nextBytes(b);
            if (b.length > 1 && r.nextBoolean()) {
                b[0] = (byte) 0x82;
            }
            byte[] got = d.entryLevels("/dp/-k", b);
            Assert.assertTrue("an entry of a non-object", got == null
                    || ObjectFormat.isStoredObject(b));
        }

        for (Record rec : ObjectFormatTester.readVectors()) {
            if (rec.kind.equals("invalid") && rec.id.startsWith("format-1")) {
                byte[] b = ObjectFormatTester.unhex(rec.one("bytes"));
                try {
                    d.entryLevels("/dp/-k1", b);
                    throw new AssertionError(rec.id + ": not refused");
                } catch (DataFormatException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains("/dp/-k1")
                            && e.getMessage().contains("format 1"));
                }
                assertNull("format 1 at a key with a suffix", d.entryLevels("/dp/-k.txt",
                        b));
            }
        }
    }

    /**
     * The limit: levels of 4,096 bytes in all give an entry, 4,097 none (020-10, section
     * 3.3, rule 3), with E's escapes counted; a value of a megabyte gives none.
     */
    @Nano
    public static void testFunctionLimit() {
        IndexDefinition s = new IndexDefinition("n", "/p/", 1, false, new String[] {"string"},
                new String[][] {{"s"}});
        Assert.assertEquals(4096, s.entryLevels("/dp/-k", writeString("s",
                repeat("x", 4095))).length);
        assertNull(s.entryLevels("/dp/-k", writeString("s", repeat("x", 4096))));
        Assert.assertEquals(4096, s.entryLevels("/dp/-k", writeString("s",
                repeat("\u0000", 2047) + "x")).length);
        assertNull(s.entryLevels("/dp/-k", writeString("s", repeat("\u0000", 2048))));
        assertNull(s.entryLevels("/dp/-k", writeString("s", repeat("x", 1 << 20))));

        IndexDefinition b = new IndexDefinition("n", "/p/", 1, false, new String[] {"bytes"},
                new String[][] {{"b"}});
        byte[] zeros = new byte[2048];
        zeros[2047] = 5;
        Assert.assertEquals(4096, b.entryLevels("/dp/-k", writeBytes("b", zeros)).length);
        assertNull(b.entryLevels("/dp/-k", writeBytes("b", new byte[2048])));
        byte[] ff = new byte[4095];
        Arrays.fill(ff, (byte) 0xff);
        Assert.assertEquals(4096, b.entryLevels("/dp/-k", writeBytes("b", ff)).length);

        // Levels in all: a long (8 bytes) and a string.
        IndexDefinition ls = new IndexDefinition("n", "/p/", 1, false,
                new String[] {"long", "string", "double"}, new String[][] {{"a"}, {"s"},
                {"d"}});
        Obj o = obj("{\"a\":i1,\"d\":d3ff0000000000000}");
        o.fields.put("s", new Str(repeat("x", 4096 - 8 - 8 - 1)));
        Assert.assertEquals(4096, ls.entryLevels("/dp/-k", ObjectFormatTester.codecWrite(o))
                .length);
        o.fields.put("s", new Str(repeat("x", 4096 - 8 - 8)));
        assertNull(ls.entryLevels("/dp/-k", ObjectFormatTester.codecWrite(o)));
    }

    /** entry(): the generation's prefix, the levels, K (020-10, sections 4.1 and 4.4). */
    @Nano
    public static void testEntry() {
        IndexDefinition d = sample();
        byte[] o = write("{\"amount\":i500,\"from\":s\"1001\",\"to\":s\"1002\"}");
        byte[] levels = d.entryLevels("/dpayments/-p1", o);
        Assert.assertArrayEquals(IndexKeysTester.concat(IndexKeys.encodeString("1001"),
                IndexKeys.encodeLong(500)), levels);
        byte[] entry = d.entry("/dpayments/-p1", o);
        Assert.assertArrayEquals(IndexKeysTester.concat(d.generationPrefix(), levels,
                IndexKeys.fileKey("/dpayments/-p1")), entry);
        IndexKeys.Entry e = IndexKeys.parseEntry(entry, d.generationPrefix(), d.types());
        Assert.assertEquals("1001", e.value(0));
        Assert.assertEquals(500L, e.value(1));
        Assert.assertEquals("-p1", e.fileName());
        assertNull(d.entry("/dpayments/-p1", write("{\"from\":s\"1001\"}")));
    }

    /** Random objects of the model against the reference, refLevels(), seed 9. */
    @Nano
    public static void testFunctionRandom() {
        int[] st = new int[2];
        runFunction(new Random(9), 3000, st);
        Assert.assertTrue("entries " + st[0] + ", none " + st[1], st[0] > 1000 && st[1] > 1000);
    }

    /** The night's run: NIGHT_SEEDS seeds of NIGHT_OBJECTS random objects, new each day. */
    @Nano("night")
    public static void testFunctionNight(TestEnvironment c) {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        int[] st = new int[2];
        for (long seed = base; seed < base + NIGHT_SEEDS; seed++) {
            runFunction(new Random(seed), NIGHT_OBJECTS, st);
        }
        c.out().println("IndexDefinitionTester: seeds " + base + " to "
                + (base + NIGHT_SEEDS - 1) + ": " + st[0] + " entries, " + st[1] + " none");
    }

    static final int NIGHT_SEEDS = 20;
    static final int NIGHT_OBJECTS = 50000;

    /** Usage: IndexDefinitionTester [SEED [OBJECTS]]: the random function test. */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int n = args.length > 1 ? Integer.parseInt(args[1]) : NIGHT_OBJECTS;
        int[] st = new int[2];
        long t0 = System.nanoTime();
        runFunction(new Random(seed), n, st);
        System.out.println("IndexDefinitionTester: seed " + seed + ": " + st[0] + " entries, "
                + st[1] + " none; " + (System.nanoTime() - t0) / 1000000 + " ms");
    }

    static final String[] NAMES = {"a", "b", "c", "a.b", "x,y", "\u00e5", "\u0000"};

    /**
     * 'n' random objects, each with three random definitions of 1 to 3 levels, whose paths
     * mostly follow the object's fields and whose types mostly match the values found.
     */
    static void runFunction(Random r, int n, int[] st) {
        for (int k = 0; k < n; k++) {
            Obj o = randomObj(r, 1);
            byte[] b = ObjectFormatTester.codecWrite(o);
            for (int q = 0; q < 3; q++) {
                int levels = 1 + r.nextInt(3);
                String[] types = new String[levels];
                String[][] paths = new String[levels][];
                for (int i = 0; i < levels; i++) {
                    paths[i] = randomPath(r, o);
                    Object v = at(o, paths[i]);
                    char t = v instanceof Long ? IndexKeys.LONG : v instanceof Dbl
                            ? IndexKeys.DOUBLE : v instanceof Str ? IndexKeys.STRING
                            : IndexKeys.BYTES;
                    types[i] = IndexKeys.typeName(r.nextInt(4) != 0 ? t
                            : IndexKeys.TYPES[r.nextInt(4)]);
                }
                IndexDefinition d = new IndexDefinition("n", "/p/", 1, false, types, paths);
                byte[] want = refLevels(o, d);
                byte[] got = d.entryLevels("/dp/-k", b);
                if (!Arrays.equals(want, got)) {
                    throw new AssertionError("object " + o + ", definition " + d + ": want "
                            + (want == null ? "none" : IndexKeysTester.hex(want)) + ", got "
                            + (got == null ? "none" : IndexKeysTester.hex(got)));
                }
                st[got == null ? 1 : 0]++;
            }
        }
    }

    /** A path that mostly follows the object's fields, and may stop at an object. */
    private static String[] randomPath(Random r, Obj o) {
        List<String> parts = new ArrayList<>();
        Object v = o;
        while (true) {
            String name;
            if (v instanceof Obj && !((Obj) v).fields.isEmpty() && r.nextInt(5) != 0) {
                List<String> names = new ArrayList<>(((Obj) v).fields.keySet());
                String chars = names.get(r.nextInt(names.size()));
                v = ((Obj) v).fields.get(chars);
                name = new String(ObjectFormatTester.bytes(chars), StandardCharsets.UTF_8);
            } else {
                name = NAMES[r.nextInt(NAMES.length)];
                v = null;
            }
            parts.add(name);
            if (!(v instanceof Obj) || r.nextInt(4) == 0) {
                return parts.toArray(new String[0]);
            }
        }
    }

    /** The value at the path, followed through objects, or null. */
    static Object at(Obj o, String[] path) {
        Object v = o;
        for (String part : path) {
            if (!(v instanceof Obj)) {
                return null;
            }
            v = ((Obj) v).fields.get(chars(part));
        }
        return v;
    }

    private static Obj randomObj(Random r, int level) {
        Obj o = new Obj();
        int n = r.nextInt(6);
        for (int i = 0; i < n; i++) {
            o.fields.put(chars(NAMES[r.nextInt(NAMES.length)]), randomValue(r, level));
        }
        return o;
    }

    private static Object randomValue(Random r, int level) {
        switch (r.nextInt(level < 3 ? 9 : 5)) {
        case 0:
            return IndexKeysTester.randomLong(r);
        case 1: {
            int c = r.nextInt(5);
            long bits = c == 0 ? ObjectFormatTester.NAN : c == 1 ? 0x8000000000000000L
                    : Double.doubleToLongBits(IndexKeysTester.randomDouble(r));
            return new Dbl(bits);
        }
        case 2: {
            String s = IndexKeysTester.randomString(r);
            if (r.nextInt(20) == 0) {
                s = repeat(s.isEmpty() ? "x" : s, 4096 / (s.length() + 1) + r.nextInt(30));
            }
            return new Str(chars(s));
        }
        case 3: {
            byte[] b = IndexKeysTester.randomBytes(r);
            if (r.nextInt(20) == 0) {
                b = Arrays.copyOf(b, 4080 + r.nextInt(30));
            }
            return new Bin(ObjectFormatTester.chars(b));
        }
        case 4:
            return r.nextBoolean();
        case 5: {
            Arr a = new Arr();
            int n = r.nextInt(3);
            for (int i = 0; i < n; i++) {
                a.elements.add(r.nextBoolean() ? IndexKeysTester.randomLong(r)
                        : randomObj(r, level + 2));
            }
            return a;
        }
        case 6:
            return IndexKeysTester.randomLong(r);
        default:
            return randomObj(r, level + 1);
        }
    }

    // ======== The reference: 3.3 over the model, written apart from IndexDefinition ========

    /**
     * f(o) by 020-10, section 3.3, over the model's Java values: each level's path followed
     * through objects (Obj); the value found must be of the level's kind (Long, Dbl but NaN,
     * Str, Bin); encoded by 4.4 as IndexKeysTester's references write it; none above 4,096
     * bytes.
     */
    static byte[] refLevels(Obj o, IndexDefinition d) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        for (int i = 0; i < d.levelCount(); i++) {
            Object v = at(o, d.path(i));
            byte[] e;
            switch (d.typeName(i)) {
            case "long":
                if (!(v instanceof Long)) {
                    return null;
                }
                e = IndexKeysTester.refLong((Long) v);
                break;
            case "double":
                if (!(v instanceof Dbl) || Double.isNaN(Double.longBitsToDouble(((Dbl) v).bits))) {
                    return null;
                }
                e = IndexKeysTester.refDouble(Double.longBitsToDouble(((Dbl) v).bits));
                break;
            case "string":
                if (!(v instanceof Str)) {
                    return null;
                }
                e = refE(ObjectFormatTester.bytes(((Str) v).bytes));
                break;
            default:
                if (!(v instanceof Bin)) {
                    return null;
                }
                e = refE(ObjectFormatTester.bytes(((Bin) v).bytes));
                break;
            }
            out.write(e, 0, e.length);
        }
        return out.size() > 4096 ? null : out.toByteArray();
    }

    /** E of 020-10, section 4.4, written apart: 00 as 01 01, 01 as 01 02, then 00. */
    static byte[] refE(byte[] b) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        for (byte x : b) {
            if (x == 0 || x == 1) {
                out.write(1);
                out.write(x + 1);
            } else {
                out.write(x);
            }
        }
        out.write(0);
        return out.toByteArray();
    }

    // ======== Helpers ========

    private static byte[] level(String type, byte[] value, String... path) {
        return new IndexDefinition("n", "/p/", 1, false, new String[] {type},
                new String[][] {path}).entryLevels("/dp/-k", value);
    }

    private static void assertLevels(String what, byte[] want, byte[] got) {
        if (!Arrays.equals(want, got)) {
            throw new AssertionError(what + ": want " + (want == null ? "none"
                    : IndexKeysTester.hex(want)) + ", got " + (got == null ? "none"
                    : IndexKeysTester.hex(got)));
        }
    }

    static Obj obj(String vn) {
        return (Obj) Vn.parse(vn);
    }

    static byte[] write(String vn) {
        return ObjectFormatTester.codecWrite(obj(vn));
    }

    /** A stored object with one string field: its UTF-8 from a Java String. */
    static byte[] writeString(String name, String s) {
        Obj o = new Obj();
        o.fields.put(chars(name), new Str(chars(s)));
        return ObjectFormatTester.codecWrite(o);
    }

    static byte[] writeBytes(String name, byte[] b) {
        Obj o = new Obj();
        o.fields.put(chars(name), new Bin(ObjectFormatTester.chars(b)));
        return ObjectFormatTester.codecWrite(o);
    }

    /** BASE with the field 'name' set to the VN value, or removed if null. */
    static Obj with(String base, String name, String vn) {
        Obj o = obj(base);
        if (vn == null) {
            o.fields.remove(chars(name));
        } else {
            o.fields.put(chars(name), Vn.parse(vn));
        }
        return o;
    }

    private static void assertRefused(String what, Obj o, String part) {
        assertRefusedBytes(what, "n", ObjectFormatTester.codecWrite(o), part);
    }

    private static void assertRefusedBytes(String what, String name, byte[] b, String part) {
        try {
            IndexDefinition.fromBytes(name, b);
        } catch (InternalDataException e) {
            String m = e.getMessage();
            Assert.assertTrue(what + ": the key named: " + m, m.contains("/#i/didef/-" + name));
            Assert.assertTrue(what + ": " + part + " named: " + m, m.contains(part));
            return;
        }
        throw new AssertionError(what + ": accepted");
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

    private static void refusedArg(String what, Runnable r) {
        IndexKeysTester.assertRefusedArg(what, r);
    }

    private static long execute(Db db, Trans.Builder b) {
        Trans t = b.build();
        db.execute(t);
        return t.tt;
    }

    /** A Java String's UTF-8 bytes as the model's chars (one char a byte). */
    static String chars(String s) {
        return ObjectFormatTester.chars(s.getBytes(StandardCharsets.UTF_8));
    }

    static String repeat(String s, int n) {
        return IndexKeysTester.repeat(s, n);
    }
}
