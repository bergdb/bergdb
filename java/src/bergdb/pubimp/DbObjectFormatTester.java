package bergdb.pubimp;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DbArray;
import bergdb.pub.DbBoolean;
import bergdb.pub.DbByteArray;
import bergdb.pub.DbDouble;
import bergdb.pub.DbLong;
import bergdb.pub.DbObject;
import bergdb.pub.DbString;
import bergdb.pub.DbValue;
import bergdb.pub.Factory;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.RwEnvironment;
import bergdb.pub.util.BadFormatException;
import bergdb.pubimp.ObjectFormatTester.Arr;
import bergdb.pubimp.ObjectFormatTester.Bin;
import bergdb.pubimp.ObjectFormatTester.Dbl;
import bergdb.pubimp.ObjectFormatTester.Gen;
import bergdb.pubimp.ObjectFormatTester.Obj;
import bergdb.pubimp.ObjectFormatTester.Record;
import bergdb.pubimp.ObjectFormatTester.Ref;
import bergdb.pubimp.ObjectFormatTester.Str;
import bergdb.pubimp.ObjectFormatTester.Vn;

/**
 * Tests of DbObject, its Builder and the value classes in format 2 (bergdb 020-07; 020-08,
 * section 6.2, T2 to T7, and section 6.3, H0 through DbObject):
 * <ul>
 * <li>T2: every valid vector is read by new DbObject(), its getters and paths giving the
 *     value, and built again by the Builder to the same bytes; every invalid one is refused
 *     with BadFormatException, and a get of it at a key with ObjectCreationException, in
 *     rw() too, the database going on;</li>
 * <li>T3: the writer's refusals, each naming its place;</li>
 * <li>T4: one integer; T5: doubles; T6: sizes; T7: lookup names;</li>
 * <li>H0a through the Builder: random values built by the Builder to Ref's bytes, and read
 *     back by DbObject; H0b through DbObject: every mutant of the samples is read by
 *     new DbObject() exactly when the full check accepts it, and refused with
 *     BadFormatException, never another exception, when not.</li>
 * </ul>
 * The tests use ObjectFormatTester's vectors, Ref, Gen and value model.
 *
 * @author Frans Lundberg
 */
public class DbObjectFormatTester {
    private DbObjectFormatTester() {}

    /** H0a's random values through the Builder, in the unit group. */
    static final int UNIT_TREES = 300;

    // ======== T2: the vectors through DbObject ========

    /**
     * T2: each valid vector read by new DbObject(), its fields and lookups giving the
     * record's values through the getters, and built again by the Builder from its value to
     * the same bytes; each invalid one refused with BadFormatException.
     */
    @Nano
    public static void testVectorsThroughDbObject() throws IOException {
        int valid = 0, invalid = 0, lookups = 0;
        for (Record rec : ObjectFormatTester.readVectors()) {
            String where = rec.kind + " " + rec.id;
            if (rec.kind.equals("valid")) {
                byte[] b = ObjectFormatTester.unhex(rec.one("bytes"));
                Obj value = (Obj) Vn.parse(rec.one("value"));
                DbObject o = new DbObject(b);
                assertObject(where, value, o);
                ObjectFormatTester.assertBytes(where + ": its bytes", b, o.getBytes());
                ObjectFormatTester.assertBytes(where + ": built", b, build(value).getBytes());
                for (String lookup : rec.all("lookup")) {
                    Vn p = new Vn(lookup);
                    List<byte[]> path = p.path();
                    String result = lookup.substring(p.i + 1);
                    Object want = result.equals("absent") ? null : Vn.parse(result);
                    if (lookup(where + ": lookup " + lookup, o, path, want)) {
                        lookups++;
                    }
                }
                valid++;
            } else if (rec.kind.equals("invalid")) {
                byte[] b = ObjectFormatTester.unhex(rec.one("bytes"));
                assertRefused(where, b);
                invalid++;
            }
        }
        Assert.assertEquals("valid records", 33, valid);
        Assert.assertEquals("invalid records", 84, invalid);
        Assert.assertTrue("lookups: " + lookups, lookups > 300);
    }

    /**
     * T2: a get of each invalid vector at a key, as a class and as DbObject, throws
     * ObjectCreationException, outside rw() and inside, and the database goes on; a get as
     * Object gives the bytes (020-08, section 3: not a stored object, so a byte[]).
     */
    @Nano
    public static void testInvalidVectorsAtAKey() throws IOException {
        Database db = Factory.database().memory().start();
        try {
            final Connection c = db.connection();
            int n = 0;
            for (Record rec : ObjectFormatTester.readVectors()) {
                if (!rec.kind.equals("invalid")) {
                    continue;
                }
                final String key = "/bad/" + n++;
                final byte[] b = ObjectFormatTester.unhex(rec.one("bytes"));
                c.put(key, b);
                for (final Class<?> clazz : new Class<?>[] {OneLong.class, DbObject.class}) {
                    String where = rec.id + " as " + clazz.getSimpleName();
                    assertCreationRefused(where, () -> c.get(key, clazz));
                    assertCreationRefused(where + " in rw()", () -> c.rw(new Action() {
                        public void run(RwEnvironment env) {
                            env.put("/written", "x");
                            env.get(key, clazz);
                        }
                    }));
                }
                if (rec.one("rules").contains("format-1")) {
                    // An object of 2026.3 and before is refused, naming the format (020-08,
                    // step 3).
                    assertCreationRefused(rec.id + " as Object", () -> c.get(key, Object.class));
                } else {
                    Object asObject = c.get(key, Object.class);
                    Assert.assertTrue(rec.id + " as Object: " + asObject, 
                            asObject instanceof byte[] && Arrays.equals(b, (byte[]) asObject));
                }
            }
            Assert.assertEquals(84, n);
            Assert.assertNull(c.get("/written", String.class));     // no rw() committed
            c.put("/later", "x");                                    // not failed
            Assert.assertEquals("x", c.get("/later", String.class));
        } finally {
            db.close();
        }
    }

    public static class OneLong {
        public long v;
        public OneLong() {}
    }

    private static void assertCreationRefused(String where, Runnable r) {
        try {
            r.run();
        } catch (ObjectCreationException e) {
            return;
        } catch (Throwable e) {
            throw new AssertionError(where + ": not an ObjectCreationException, " + e, e);
        }
        throw new AssertionError(where + ": no exception");
    }

    /** new DbObject(b) refuses with BadFormatException, and nothing else. */
    static void assertRefused(String where, byte[] b) {
        try {
            new DbObject(b);
        } catch (BadFormatException e) {
            return;
        } catch (Throwable e) {
            throw new AssertionError(where + ": not a BadFormatException, " + e, e);
        }
        throw new AssertionError(where + ": accepted");
    }

    // ======== T3: the writer's refusals ========

    /** T3: names of 0 and 256 bytes, refused by the Builder and by toDbObject(). */
    @Nano
    public static void testNameLengths() {
        String a255 = "a".repeat(255);
        // The header, the type byte 49 (w = 2: the field has 258 bytes), the count, the end.
        Assert.assertEquals(1 + 1 + 2 + 2 + 258, new DbObject.Builder().addLong(a255, 1)
                .build().getBytes().length);
        assertArgRefused("an empty name", () -> new DbObject.Builder().addLong("", 1));
        assertArgRefused("a name of 256 bytes", "256",
                () -> new DbObject.Builder().addLong("a".repeat(256), 1));
        assertArgRefused("a name of 256 bytes in UTF-8", "256",
                () -> new DbObject.Builder().addLong("é".repeat(128), 1));
        new DbObject.Builder().addLong("é".repeat(127) + "a", 1).build();

        Assert.assertEquals(1L, DbObject.toDbObject(new Name255()).getLong(a255));
        assertArgRefused("a field name of 256 bytes", "256",
                () -> DbObject.toDbObject(new Name256()));
        Holder h = new Holder();
        h.inner = new Name256();
        // The class check names the class and where it is (bergdb 020-09, V7).
        assertArgRefused("a nested field name of 256 bytes", "Name256 at 'inner'",
                () -> DbObject.toDbObject(h));
    }

    public static class Name255 {
        public long aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa = 1;
    }

    public static class Name256 {
        public long aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa = 1;
    }

    public static class Holder {
        public Name256 inner;
    }
    
    /** A field of 15 dimensions: the top object level 1, the arrays 2 to 16. */
    public static class Holder15 {
        public int[][][][][][][][][][][][][][][] inner;
    }
    
    /** A field of 16 dimensions: the innermost array at level 17. */
    public static class Holder16 {
        public int[][][][][][][][][][][][][][][][] inner;
    }

    /** T3: an object of 32,767 fields is built; one more field is refused by the Builder. */
    @Nano
    public static void testFieldCount() {
        DbObject.Builder b = new DbObject.Builder();
        for (int k = 0; k < 32767; k++) {
            b.addLong(String.format("%05d", k), k);
        }
        DbObject o = b.build();
        Assert.assertEquals(32767, o.getFieldCount());
        Assert.assertEquals(32766L, o.getLong("32766"));
        b.addLong("00000", 7);          // a name again: replaced, not a field more
        assertArgRefused("32,768 fields", () -> b.addLong("32767", 1));
    }

    public static class Node {
        public int v;
        public Node next;
        public Node() {}
    }

    static Node chain(int length) {
        Node head = null;
        for (int i = length - 1; i >= 0; i--) {
            Node n = new Node();
            n.v = i;
            n.next = head;
            head = n;
        }
        return head;
    }

    /**
     * T3: 16 levels are taken and 17 refused, naming the path: by objects (020-09, W24); by
     * arrays at the top (W25: the wrapping object is level 1, so 15 dimensions are taken);
     * by arrays in a field; by the Builder, from each container's height.
     */
    @Nano
    public static void testDepth() {
        DbObject o = DbObject.toDbObject(chain(16));
        Assert.assertEquals(15L, o.getLong(new String[] {"next", "next", "next", "next",
                "next", "next", "next", "next", "next", "next", "next", "next", "next", "next",
                "next", "v"}));
        assertArgRefused("17 objects", "next.next", () -> DbObject.toDbObject(chain(17)));

        DbObject.toDbObject(nestedIntArray(15));
        assertArgRefused("16 dimensions at the top", "deeper than 16",
                () -> DbObject.toDbObject(nestedIntArray(16)));
        Holder15 h15 = new Holder15();
        h15.inner = (int[][][][][][][][][][][][][][][]) nestedIntArray(15);
        DbObject.toDbObject(h15);
        Holder16 h16 = new Holder16();
        h16.inner = (int[][][][][][][][][][][][][][][][]) nestedIntArray(16);
        assertArgRefused("16 dimensions in a field", "'inner[0][0]",
                () -> DbObject.toDbObject(h16));

        // The Builder: an object of height 16 is built, of 17 refused; an array of height 15
        // is built, of 16 refused (it can only be stored at level 2 or below).
        DbObject deep = new DbObject.Builder().build();
        for (int level = 2; level <= 16; level++) {
            deep = new DbObject.Builder().addObject("o", deep).build();
        }
        final DbObject deep16 = deep;
        assertArgRefused("an object of 17 levels", () -> new DbObject.Builder()
                .addObject("o", deep16).build());
        DbArray a = new DbArray.Builder().build();
        for (int level = 2; level <= 15; level++) {
            a = new DbArray.Builder().add(a).build();
        }
        new DbObject.Builder().addArray("a", a).build();
        final DbArray a15 = a;
        assertArgRefused("an array of 16 levels", () -> new DbObject.Builder()
                .addArray("a", new DbArray.Builder().add(a15).build()).build());

        // An object read from bytes has its height too.
        final DbObject read16 = new DbObject(deep16.getBytes());
        assertArgRefused("an object read from bytes, 17 levels", () -> new DbObject.Builder()
                .addObject("o", read16).build());
    }

    /** An int[] of 'n' dimensions, each of length 1. */
    static Object nestedIntArray(int n) {
        Object a = new int[] {7};
        for (int k = 1; k < n; k++) {
            Object outer = java.lang.reflect.Array.newInstance(a.getClass(), 1);
            java.lang.reflect.Array.set(outer, 0, a);
            a = outer;
        }
        return a;
    }

    /** T3: toDbObject(null) is refused. */
    @Nano
    public static void testNullAtTheTop() {
        assertArgRefused("toDbObject(null)", () -> DbObject.toDbObject(null));
    }

    // ======== T4: one integer ========

    public static class B { public byte x = 5; }
    public static class S { public short x = 5; }
    public static class C { public char x = 5; }
    public static class I { public int x = 5; }
    public static class L { public long x = 5; }
    public static class WB { public Byte x = 5; }
    public static class WS { public Short x = 5; }
    public static class WC { public Character x = 5; }
    public static class WI { public Integer x = 5; }
    public static class WL { public Long x = 5L; }

    /**
     * T4: byte, short, char, int, long and their wrappers holding 5 give the same bytes,
     * the integer 5 in 2 bytes (020-07, R9); getType answers 'l', has() takes 'i' for an
     * integer in int's range (020-08, section 3).
     */
    @Nano
    public static void testOneInteger() {
        Object[] objects = {new B(), new S(), new C(), new I(), new L(), new WB(), new WS(),
                new WC(), new WI(), new WL()};
        for (Object x : objects) {
            DbObject o = DbObject.toDbObject(x);
            Assert.assertEquals(x.getClass().getSimpleName(), "8248010401781005",
                    StringUtil.toHex(o.getBytes()));
            Assert.assertEquals('l', o.getType("x"));
            Assert.assertTrue(o.has("x", DbObject.LONG));
            Assert.assertTrue(o.has("x", DbObject.INT));
            Assert.assertEquals(5, o.getInt("x"));
            Assert.assertEquals(5L, o.getLong("x"));
        }

        long[] values = {Byte.MIN_VALUE, Byte.MAX_VALUE, Short.MIN_VALUE, Short.MAX_VALUE,
                Character.MAX_VALUE, Integer.MIN_VALUE, Integer.MAX_VALUE,
                Integer.MIN_VALUE - 1L, Integer.MAX_VALUE + 1L, Long.MIN_VALUE, Long.MAX_VALUE};
        for (long v : values) {
            DbObject o = new DbObject(new DbObject.Builder().addLong("x", v).build().getBytes());
            Assert.assertEquals('l', o.getType("x"));
            Assert.assertEquals(v, o.getLong("x"));
            boolean fits = v == (int) v;
            Assert.assertEquals("has 'i' of " + v, fits, o.has("x", DbObject.INT));
            Assert.assertEquals(fits ? (int) v : 0, o.getInt("x"));
            Assert.assertEquals(fits, o.has(new String[] {"x"}, DbObject.INT));
            Assert.assertEquals(fits ? (int) v : 0, o.getInt(new String[] {"x"}));
        }

        L big = new L();
        big.x = 3000000000L;
        DbObject o = DbObject.toDbObject(big);
        Assert.assertEquals(3000000000L, o.toJavaObject(L.class).x);
        // Clamped (bergdb 020-09, section 5.4); a DataFormatException until 020-08's step 8.
        Assert.assertEquals(Integer.MAX_VALUE, o.toJavaObject(I.class).x);
        big.x = -7;
        Assert.assertEquals(-7, DbObject.toDbObject(big).toJavaObject(I.class).x);
        Assert.assertEquals((char) 65, new DbObject.Builder().addLong("x", 65).build()
                .toJavaObject(C.class).x);
    }

    // ======== T5: doubles ========

    public static class D { public double x; }
    public static class F { public float x; }

    /** T5: a NaN with a payload is stored as the one NaN; -0.0 is kept; a float's NaN. */
    @Nano
    public static void testDoubles() {
        D d = new D();
        d.x = Double.longBitsToDouble(0x7ff0000000000001L);
        DbObject o = DbObject.toDbObject(d);
        Assert.assertEquals("8248010b017846000000000000f87f", StringUtil.toHex(o.getBytes()));
        Assert.assertTrue(Double.isNaN(new DbObject(o.getBytes()).getDouble("x")));
        Assert.assertTrue(Double.isNaN(o.toJavaObject(D.class).x));

        d.x = -0.0;
        o = DbObject.toDbObject(d);
        Assert.assertEquals("8248010b017846" + "0000000000000080",
                StringUtil.toHex(o.getBytes()));
        Assert.assertEquals(0x8000000000000000L, Double.doubleToRawLongBits(
                new DbObject(o.getBytes()).getDouble("x")));
        Assert.assertEquals(0x8000000000000000L, Double.doubleToRawLongBits(
                o.toJavaObject(D.class).x));

        F f = new F();
        f.x = Float.NaN;
        o = DbObject.toDbObject(f);
        Assert.assertEquals("8248010b017846000000000000f87f", StringUtil.toHex(o.getBytes()));
        Assert.assertTrue(Float.isNaN(o.toJavaObject(F.class).x));

        byte[] nan = new DbObject.Builder().addDbValue("x",
                new DbDouble(Double.longBitsToDouble(0xfff8000000000001L))).build().getBytes();
        Assert.assertEquals("8248010b017846000000000000f87f", StringUtil.toHex(nan));
    }

    // ======== T6: sizes ========

    public static class Payment {
        public String from = "1001";
        public String to = "1002";
        public long amount = 500;
        public Payment() {}
    }

    public static class Person {
        public String name = "P1000";
        public Person() {}
    }

    /**
     * T6: Payment 36 bytes, Person 16, an index definition of one level 96, each the bytes of
     * its vector (020-05, section 12b.3, and the header).
     */
    @Nano
    public static void testSizes() throws IOException {
        Map<String, byte[]> vectors = new TreeMap<>();
        for (Record rec : ObjectFormatTester.readVectors()) {
            if (rec.kind.equals("valid")) {
                vectors.put(rec.id, ObjectFormatTester.unhex(rec.one("bytes")));
            }
        }
        byte[] payment = DbObject.toDbObject(new Payment()).getBytes();
        Assert.assertEquals(36, payment.length);
        ObjectFormatTester.assertBytes("payment", vectors.get("payment"), payment);
        byte[] person = DbObject.toDbObject(new Person()).getBytes();
        Assert.assertEquals(16, person.length);
        ObjectFormatTester.assertBytes("person", vectors.get("person"), person);

        DataObjectsTester.Index index = new DataObjectsTester.Index();   // Data.Index's shape
        index.dirs = new String[] {"/payments/"};
        index.fields = new String[] {"from"};
        index.typeStrings = new String[] {"string/unicode"};
        index.state = "active";
        byte[] definition = DbObject.toDbObject(index).getBytes();
        Assert.assertEquals(96, definition.length);
        ObjectFormatTester.assertBytes("index-definition", vectors.get("index-definition"),
                definition);
    }

    // ======== T7: lookup names ========

    /**
     * T7: a name with a lone surrogate is absent: it has no UTF-8 form, and is not the name
     * "a?" that a replacing encoder would give.
     */
    @Nano
    public static void testLookupNames() {
        DbObject o = new DbObject.Builder().addString("a?", "x").addLong("b", 1).build();
        Assert.assertEquals("x", o.getString("a?"));
        Assert.assertNull(o.getString("a\uD800"));
        Assert.assertEquals('z', o.getType("a\uD800"));
        Assert.assertFalse(o.has("a\uD800", DbObject.STRING));
        Assert.assertNull(o.getDbValue("a\uD800"));
        Assert.assertNull(o.getString(new String[] {"a\uD800"}));
        Assert.assertEquals('z', o.getType(""));
        Assert.assertEquals('z', o.getType("x".repeat(300)));
    }

    // ======== H0 through DbObject ========

    /**
     * H0a through the Builder: random values of ObjectFormatTester.Gen, built by the Builder
     * from the value classes, give Ref's bytes, and read back by new DbObject() give the value
     * (every NaN the one NaN).
     */
    @Nano
    public static void testH0aThroughTheBuilder() {
        Gen g = new Gen(11);
        for (int k = 0; k < UNIT_TREES; k++) {
            Obj t = g.tree();
            String where = "H0a through the Builder, value " + k;
            byte[] b = Ref.write(t, true);
            DbObject built = build(t);
            ObjectFormatTester.assertBytes(where + ": built", b, built.getBytes());
            Obj canon = (Obj) ObjectFormatTester.canon(t);
            assertObject(where + ": built", canon, built);
            assertObject(where + ": read", canon, new DbObject(b));
        }
    }

    /**
     * H0b through DbObject: every byte of the samples changed ten ways, and every cut; new
     * DbObject() of each mutant reads it exactly when the full check accepts it, and else
     * throws BadFormatException, never another exception. A read mutant is the value that
     * Ref reads.
     */
    @Nano
    public static void testH0bThroughDbObject() throws IOException {
        Map<String, byte[]> valid = new TreeMap<>();
        for (Record rec : ObjectFormatTester.readVectors()) {
            if (rec.kind.equals("valid")) {
                valid.put(rec.id, ObjectFormatTester.unhex(rec.one("bytes")));
            }
        }
        Random r = new Random(3);
        int mutants = 0, accepted = 0;
        for (String id : ObjectFormatTester.SAMPLES) {
            byte[] sample = valid.get(id);
            List<byte[]> all = new ArrayList<>();
            for (int i = 0; i < sample.length; i++) {
                int x = sample[i] & 0xff;
                int[] to = {x ^ 0x01, x ^ 0x80, x ^ 0xff, 0x00, 0x7f, 0x80, 0xff, x + 1, x - 1,
                        r.nextInt(256)};
                for (int y : to) {
                    byte[] m = sample.clone();
                    m[i] = (byte) y;
                    all.add(m);
                }
            }
            for (int length = 0; length < sample.length; length++) {
                all.add(Arrays.copyOf(sample, length));
            }
            for (byte[] m : all) {
                String where = "H0b through DbObject, " + id + ": " + StringUtil.toHex(m);
                boolean ok = ObjectFormat.isStoredObject(m);
                DbObject o = null;
                try {
                    o = new DbObject(m);
                } catch (BadFormatException e) {
                    Assert.assertFalse(where + ": refused, " + e.getMessage(), ok);
                } catch (Throwable e) {
                    throw new AssertionError(where + ": " + e, e);
                }
                if (o != null) {
                    Assert.assertTrue(where + ": read", ok);
                    assertObject(where, Ref.read(m), o);
                    accepted++;
                }
                mutants++;
            }
        }
        Assert.assertTrue("mutants " + mutants + ", accepted " + accepted, mutants > 5000
                && accepted > 1000);
    }

    // ======== The review of step 2 (2026-11-09) ========

    /**
     * The value classes are closed: no subclass of a user's can write bytes that a get then
     * refuses (the Builder does not read back what it writes); DbString's UTF-8 is made in
     * its constructor, a final field, not cached by a data race.
     */
    @Nano
    public static void testValueClassesClosed() throws ReflectiveOperationException {
        for (Class<?> c : new Class<?>[] {DbObject.class, DbArray.class, DbBoolean.class,
                DbLong.class, DbDouble.class, DbString.class, DbByteArray.class, 
                DbObject.Builder.class, DbArray.Builder.class}) {
            Assert.assertTrue(c.getName(), java.lang.reflect.Modifier.isFinal(c.getModifiers()));
        }
        for (java.lang.reflect.Constructor<?> k : DbValue.class.getDeclaredConstructors()) {
            Assert.assertFalse("DbValue's constructor is public",
                    java.lang.reflect.Modifier.isPublic(k.getModifiers()));
        }
        Assert.assertTrue(java.lang.reflect.Modifier.isFinal(DbString.class
                .getDeclaredField("utf8").getModifiers()));
    }

    /**
     * bergdb.pub and bergdb.pubimp are sealed in the jars (the review of B3, F2): a class of
     * another jar or directory cannot join them, so no class outside BergDB extends DbValue
     * or reads pubimp's package-private members. Checked when the classes come from a jar,
     * as the tests run.
     */
    @Nano
    public static void testPackagesSealed() {
        for (Class<?> c : new Class<?>[] {DbValue.class, ObjectFormat.class}) {
            java.security.CodeSource source = c.getProtectionDomain().getCodeSource();
            if (source != null && source.getLocation().getPath().endsWith(".jar")) {
                Assert.assertTrue(c.getPackage().getName() + " sealed", 
                        c.getPackage().isSealed());
            }
        }
    }

    /** A cycle's message names both places, also below an array put at the top. */
    @Nano
    public static void testCyclePlaces() {
        Node n = new Node();
        n.next = n;
        assertArgRefused("a cycle below a top-level array", "at [0].next is also at [0]",
                () -> DbObject.toDbObject(new Node[] {n}));
        assertArgRefused("a cycle at the top", "at next is also at the top",
                () -> DbObject.toDbObject(n));
    }

    // ======== Helpers ========

    /** The model's name or string, its bytes as chars, as a Java String. */
    static String string(String chars) {
        return new String(ObjectFormatTester.bytes(chars), StandardCharsets.UTF_8);
    }

    /** A DbObject built by the Builder from a value of the model. */
    static DbObject build(Obj o) {
        DbObject.Builder b = new DbObject.Builder();
        for (Map.Entry<String, Object> e : o.fields.entrySet()) {
            b.addDbValue(string(e.getKey()), dbValue(e.getValue()));
        }
        return b.build();
    }

    static DbValue dbValue(Object v) {
        if (v instanceof Obj) {
            return build((Obj) v);
        } else if (v instanceof Arr) {
            DbArray.Builder b = new DbArray.Builder();
            for (Object e : ((Arr) v).elements) {
                b.add(dbValue(e));
            }
            return b.build();
        } else if (v instanceof Boolean) {
            return new DbBoolean((Boolean) v);
        } else if (v instanceof Long) {
            return new DbLong((Long) v);
        } else if (v instanceof Dbl) {
            return new DbDouble(Double.longBitsToDouble(((Dbl) v).bits));
        } else if (v instanceof Str) {
            return new DbString(string(((Str) v).bytes));
        } else {
            return new DbByteArray(ObjectFormatTester.bytes(((Bin) v).bytes));
        }
    }

    /** 'o' holds exactly the fields of 'want', each read by getDbValue() and its getter. */
    static void assertObject(String where, Obj want, DbObject o) {
        Assert.assertEquals(where + ": the field count", want.fields.size(),
                o.getFieldCount());
        for (Map.Entry<String, Object> e : want.fields.entrySet()) {
            String name = string(e.getKey());
            String at = where + ", field " + ObjectFormatTester.text(e.getKey());
            Object v = e.getValue();
            assertValue(at, v, o.getDbValue(name));
            char type = type(v);
            Assert.assertEquals(at + ": its type", type, o.getType(name));
            Assert.assertTrue(at + ": has", o.has(name, type));
            Assert.assertTrue(at + ": has, by a path", o.has(new String[] {name}, type));
            switch (type) {
            case 'n':
                Assert.assertEquals(at, (Boolean) v, o.getBoolean(name));
                break;
            case 'l':
                Assert.assertEquals(at, (long) (Long) v, o.getLong(name));
                Assert.assertEquals(at, (long) (Long) v, o.getLong(new String[] {name}));
                break;
            case 'd':
                Assert.assertEquals(at, ((Dbl) v).bits,
                        Double.doubleToRawLongBits(o.getDouble(name)));
                break;
            case 's':
                Assert.assertEquals(at, string(((Str) v).bytes), o.getString(name));
                Assert.assertEquals(at, string(((Str) v).bytes),
                        o.getString(new String[] {name}));
                break;
            case 'b':
                Assert.assertArrayEquals(ObjectFormatTester.bytes(((Bin) v).bytes),
                        o.getByteArray(name));
                break;
            case 'a':       // its elements were checked through getDbValue()
                Assert.assertEquals(at, ((Arr) v).elements.size(), o.getArray(name).getSize());
                break;
            default:        // its fields were checked through getDbValue()
                Assert.assertEquals(at, ((Obj) v).fields.size(),
                        o.getObject(name).getFieldCount());
                ObjectFormatTester.assertBytes(at, ((DbObject) o.getDbValue(name)).getBytes(),
                        o.getObject(name).getBytes());
            }
        }
    }

    static char type(Object v) {
        return v instanceof Obj ? 'o' : v instanceof Arr ? 'a' : v instanceof Boolean ? 'n'
                : v instanceof Long ? 'l' : v instanceof Dbl ? 'd' : v instanceof Str ? 's'
                : 'b';
    }

    static void assertValue(String where, Object want, DbValue v) {
        Assert.assertTrue(where + ": no value", v != null);
        Assert.assertEquals(where + ": the type", type(want), v.getType());
        if (want instanceof Obj) {
            assertObject(where, (Obj) want, (DbObject) v);
        } else if (want instanceof Arr) {
            List<Object> elements = ((Arr) want).elements;
            DbArray a = (DbArray) v;
            Assert.assertEquals(where + ": the array's size", elements.size(), a.getSize());
            Iterator<DbValue> it = a.iterator();
            for (int i = 0; i < elements.size(); i++) {
                assertValue(where + "[" + i + "]", elements.get(i), it.next());
            }
            Assert.assertFalse(where + ": more elements", it.hasNext());
        } else if (want instanceof Boolean) {
            Assert.assertEquals(where, (Boolean) want, ((DbBoolean) v).toBoolean());
        } else if (want instanceof Long) {
            Assert.assertEquals(where, (long) (Long) want, ((DbLong) v).toLong());
        } else if (want instanceof Dbl) {
            Assert.assertEquals(where, ((Dbl) want).bits,
                    Double.doubleToRawLongBits(((DbDouble) v).toDouble()));
        } else if (want instanceof Str) {
            Assert.assertEquals(where, string(((Str) want).bytes), 
                    ((DbString) v).toStringValue());
        } else {
            Assert.assertArrayEquals(ObjectFormatTester.bytes(((Bin) want).bytes),
                    ((DbByteArray) v).getByteArray());
        }
    }

    /**
     * A lookup of the vectors by the getters: absent, or the value. False if a name of the
     * path is not well-formed UTF-8, which no String holds.
     */
    static boolean lookup(String where, DbObject o, List<byte[]> path, Object want) {
        String[] parts = new String[path.size()];
        for (int k = 0; k < parts.length; k++) {
            byte[] name = path.get(k);
            if (ObjectFormat.utf8Fault(name, 0, name.length) >= 0) {
                return false;
            }
            parts[k] = new String(name, StandardCharsets.UTF_8);
        }
        if (want == null) {
            for (char t : "nldsbao".toCharArray()) {
                Assert.assertFalse(where + ": has " + t, o.has(parts, t));
            }
            if (parts.length == 1) {
                Assert.assertEquals(where, 'z', o.getType(parts[0]));
                Assert.assertTrue(where, o.getDbValue(parts[0]) == null);
            }
            Assert.assertEquals(where, 0L, o.getLong(parts));
            Assert.assertTrue(where, o.getString(parts) == null);
            return true;
        }
        char type = type(want);
        Assert.assertTrue(where + ": has", o.has(parts, type));
        if (parts.length == 1) {
            assertValue(where, want, o.getDbValue(parts[0]));
        } else if (type == 'l') {
            Assert.assertEquals(where, (long) (Long) want, o.getLong(parts));
        } else if (type == 's') {
            Assert.assertEquals(where, string(((Str) want).bytes), o.getString(parts));
        } else if (type == 'd') {
            Assert.assertEquals(where, ((Dbl) want).bits,
                    Double.doubleToRawLongBits(o.getDouble(parts)));
        }
        return true;
    }

    static void assertArgRefused(String what, Runnable r) {
        assertArgRefused(what, "", r);
    }

    /** r throws IllegalArgumentException whose message has 'part'. */
    static void assertArgRefused(String what, String part, Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(what + ": " + e.getMessage(), e.getMessage().contains(part));
            return;
        }
        throw new AssertionError(what + ": not refused");
    }
}
