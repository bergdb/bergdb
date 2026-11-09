package bergdb.pubimp;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.module.Configuration;
import java.lang.module.ModuleDescriptor;
import java.lang.module.ModuleFinder;
import java.lang.module.ModuleReader;
import java.lang.module.ModuleReference;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.math.BigInteger;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.Set;
import java.util.stream.Stream;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.Platform;
import bergdb.nanotest.TestEnvironment;
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
import bergdb.pub.WBuilder;

/**
 * Tests of Java's binding between Data Objects and DbObjects in release 2026.4 (bergdb 020-09;
 * 020-08, section 6.2, T11 and H1), written from 020-09 before the code:
 * <ul>
 * <li>the get cases G1 to G122 (020-09, section 8.2; the rules of section 5): G1 to G109 from
 *     a table, each through the database and by DbObject.toJavaObject(Class), into All and
 *     into All0 (G111);</li>
 * <li>the class cases K1 to K18 (section 8.3; the check of section 3);</li>
 * <li>the put cases W1 to W36 (section 8.4; the rules of section 4);</li>
 * <li>the properties of section 8.5, seeded: R1, the round trip of random Data Objects; R2,
 *     the get of random stored objects against a reference of section 5's rules written in
 *     this class; R3, principle 4, All against All0. The unit group runs them with fixed seeds
 *     in a fraction of a second, the night group with more seeds.</li>
 * </ul>
 * The classes of section 8.1 and of the cases are public static nested classes here. A test
 * runs all its cases and fails at the end, listing each failed case by its ID.
 *
 * @author Frans Lundberg
 */
public class DataObjectsTester {
    private DataObjectsTester() {}

    /** The unit group's seed, and its number of random objects for R1 and for R2 and R3. */
    static final long UNIT_SEED = 20261109L;
    static final int UNIT_R1 = 400;
    static final int UNIT_R2 = 800;

    /** The night's seeds, and the random objects of each. */
    static final int NIGHT_SEEDS = 100;
    static final int NIGHT_OBJECTS = 5000;

    // ======== The classes (020-09, section 8.1) ========

    public static class Inner {
        public int v = 5;
        public int w = 6;
        public Inner() {}
    }

    /** Initial values that no case expects, but z's (020-09, section 8.1). */
    public static class All {
        public boolean z = true;        public Boolean wz = true;
        public byte b = 7;              public Byte wb = 7;
        public short s = 7;             public Short ws = 7;
        public char c = 'x';            public Character wc = 'x';
        public int i = 7;               public Integer wi = 7;
        public long l = 7;              public Long wl = 7L;
        public float f = 7;             public Float wf = 7f;
        public double d = 7;            public Double wd = 7.0;
        public String str = "init";     public byte[] bytes = {9};
        public int[] ints = {9};        public Integer[] wints = {9};
        public String[] strs = {"init"};
        public int[][] ints2 = {{9}};   public byte[][] bytes2 = {{9}};
        public Inner inner = new Inner();
        public Inner[] inners = {new Inner()};
        public All() {}
    }

    /** All's fields with no initial values: z and wz start false (020-09, G111). */
    public static class All0 {
        public boolean z;               public Boolean wz;
        public byte b;                  public Byte wb;
        public short s;                 public Short ws;
        public char c;                  public Character wc;
        public int i;                   public Integer wi;
        public long l;                  public Long wl;
        public float f;                 public Float wf;
        public double d;                public Double wd;
        public String str;              public byte[] bytes;
        public int[] ints;              public Integer[] wints;
        public String[] strs;
        public int[][] ints2;           public byte[][] bytes2;
        public Inner inner;
        public Inner[] inners;
        public All0() {}
    }

    public static class Node {
        public int v;
        public Node next;
        public Node() {}
    }

    /** The field types that All lacks, for R1 and W12, W13; it refers to itself (V9). */
    public static class Every {
        public boolean[] zs;            public Boolean[] wzs;
        public Byte[] wbs;
        public short[] ss;              public Short[] wss;
        public char[] cs;               public Character[] wcs;
        public long[] ls;               public Long[] wls;
        public float[] fs;              public Float[] wfs;
        public double[] ds;             public Double[] wds;
        public String[][] strs2;        public byte[][][] bytes3;
        public long[][][] ls3;          public Inner[][] inners2;
        public Node node;               public Node[] nodes;
        public All all;                 public Every every;
        public Every() {}
    }

    /** G110: the constructor's Inner has w 8; 'made' is the last one made (static). */
    public static class Init {
        public static Inner made;
        public Inner inner;
        public Init() {
            inner = new Inner();
            inner.w = 8;
            made = inner;
        }
    }

    /** G112, W32. */
    public static class T {
        public transient int t = 5;
        public static int st = 5;
        public int n;
    }

    /** G113, W31. */
    public static class K {
        public String key;
        public int n;
    }

    /** G114: each Log made gets the next number of a static counter. */
    public static class Log {
        public static int counter;
        public transient int number;
        public Log() {
            number = ++counter;
        }
    }

    /** G114: declared b, then a. */
    public static class Two {
        public Log b;
        public Log a;
    }

    /** G121. */
    public static class Throws {
        public Throws() {
            throw new IllegalStateException("t");
        }
    }

    /** G121. */
    public static class Holder {
        public Throws t;
    }

    /** K4, G119: a field of package access. */
    public static class Bad {
        int v;
    }

    /** W22, W23. */
    public static class SubInner extends Inner {
        public int u;
    }

    /** W21. */
    public static class Dflt {
        public String s = "dflt";
    }

    /** W27. */
    public static class Pair {
        public Inner x;
        public Inner y;
    }

    /** W33: fields declared b, then a. */
    public static class BA {
        public int b = 2;
        public int a = 1;
    }

    /** W34: no stored field. */
    public static class Empty {
    }

    // The classes of the class cases (020-09, section 8.3).

    /** K1. */
    private static class P {
        public int v;
    }

    /** K1, held. */
    public static class HoldsP {
        public P p;
    }

    /** K2. */
    public static class PrivateConstructor {
        public int v;
        private PrivateConstructor() {}
    }

    /** K3. */
    public static class IntConstructor {
        public int v;
        public IntConstructor(int v) {
            this.v = v;
        }
    }

    /** K5: valid, t ignored. */
    public static class PrivateTransient {
        public int v;
        private transient int t = 5;
    }

    /** K6. */
    public static class FinalField {
        public final int v = 1;
    }

    /** K7. */
    public static class ObjectField {
        public Object x;
    }

    /** K7. */
    public static class ListField {
        public List<String> x;
    }

    /** K7. */
    public static class RunnableField {
        public Runnable x;
    }

    /** K8, K13. */
    public enum Color { RED, GREEN }

    /** K8. */
    public static class EnumField {
        public Color x;
    }

    /** K8. */
    public static class DateField {
        public Date x;
    }

    /** K8. */
    public static class DbObjectField {
        public DbObject x;
    }

    /** K9. */
    public static class ObjectArrayField {
        public Object[] x;
    }

    /** K10. */
    public static class K10B {
        public int x;
    }

    /** K10: x hides K10B's x. */
    public static class K10C extends K10B {
        public String x;
    }

    /** K11. */
    public static class Outer {
        public Bad b;
    }

    /** K12: a package-private class. */
    static class K12B {
        public int x;
    }

    /** K12. */
    public static class K12C extends K12B {
    }

    /** K13. */
    public abstract static class Abstract13 {
        public int v;
    }

    /** K13: a subclass that is valid by itself. */
    public static class Concrete13 extends Abstract13 {
    }

    /** K13. */
    public interface Interface13 {
    }

    /** K13. */
    public static class Impl13 implements Interface13 {
        public int v;
    }

    /** K13. */
    public record Record13(int v) {
    }

    /** K13, held. */
    public static class HoldsAbstract {
        public Abstract13 x;
    }

    /** K13, held. */
    public static class HoldsInterface {
        public Interface13 x;
    }

    /** K13, held. */
    public static class HoldsEnum {
        public Color x;
    }

    /** K13, held. */
    public static class HoldsRecord {
        public Record13 x;
    }

    /** K15. */
    public static class Box<E> {
        public E value;
    }

    /** K18: the shape of 2026.3's Data.Index, which 020-10 removes. */
    public static class Index {
        public String[] dirs;
        public String[] fields;
        public String state;
        public String[] typeStrings;
        public int version = 1;
    }

    // ======== G1 to G111: the table (020-09, section 8.2) ========

    /** "refs" of 020-09, section 8.1. */
    private static final String REFS = "bytes,ints,strs,inner";

    private static final class Row {
        final String id;
        final DbValue[] stored;
        final String[][] fields;      // by group: the names of each
        final Object[] want;          // by group

        Row(String id, DbValue[] stored, String[][] fields, Object[] want) {
            this.id = id;
            this.stored = stored;
            this.fields = fields;
            this.want = want;
        }
    }

    /** A row: its ID, the stored values, then the groups, each "f1,f2" and its result. */
    private static Row row(String id, DbValue[] stored, Object... groups) {
        int n = groups.length / 2;
        String[][] fields = new String[n][];
        Object[] want = new Object[n];
        for (int k = 0; k < n; k++) {
            fields[k] = ((String) groups[2 * k]).split(",");
            want[k] = groups[2 * k + 1];
        }
        return new Row(id, stored, fields, want);
    }

    private static DbValue[] v(DbValue... values) {
        return values;
    }

    static DbValue l(long v) {
        return new DbLong(v);
    }

    static DbValue d(double x) {
        return new DbDouble(x);
    }

    static DbValue z(boolean v) {
        return new DbBoolean(v);
    }

    static DbValue s(String s) {
        return new DbString(s);
    }

    static DbValue b(int... bytes) {
        byte[] a = new byte[bytes.length];
        for (int k = 0; k < a.length; k++) {
            a[k] = (byte) bytes[k];
        }
        return new DbByteArray(a);
    }

    static DbArray a(DbValue... elements) {
        DbArray.Builder b = new DbArray.Builder();
        for (DbValue e : elements) {
            b.add(e);
        }
        return b.build();
    }

    /** An object of the names and values given, by DbObject.Builder. */
    static DbObject o(Object... namesAndValues) {
        DbObject.Builder b = new DbObject.Builder();
        for (int k = 0; k < namesAndValues.length; k += 2) {
            b.addDbValue((String) namesAndValues[k], (DbValue) namesAndValues[k + 1]);
        }
        return b.build();
    }

    static Inner inner(int v, int w) {
        Inner x = new Inner();
        x.v = v;
        x.w = w;
        return x;
    }

    /** The rows of 020-09, section 8.2, G1 to G108; G109 is in testGetTable. */
    private static Row[] rows() {
        Row[] rows = new Row[] {
            row("G1", v(l(5)), "l", 5L),
            row("G2", v(l(5)), "i,wi", 5),
            row("G3", v(l(3000000000L)), "i", 2147483647),
            row("G4", v(l(-3000000000L)), "i", -2147483648),
            row("G5", v(l(40000)), "s,ws", 32767),
            row("G6", v(l(-40000)), "s", -32768),
            row("G7", v(l(200)), "b,wb", 127),
            row("G8", v(l(-200)), "b", -128),
            row("G9", v(l(65)), "c,wc", 'A'),
            row("G10", v(l(-1)), "c", '\u0000'),
            row("G11", v(l(70000)), "c", '￿'),
            row("G12", v(l(9007199254740993L)), "d", 9.007199254740992E15),
            row("G13", v(l(9223372036854775807L)), "f", 9.223372E18f),
            row("G14", v(l(0)), "z,wz", false),
            row("G15", v(l(-7)), "z", true),
            row("G16", v(l(-42)), "str", "-42"),
            row("G17", v(l(5)), REFS, null),
            row("G18", v(d(1.5)), "d,wd", 1.5),
            row("G19", v(d(-0.0)), "d", -0.0),
            row("G20", v(d(Double.NaN)), "d", Double.NaN),
            row("G21", v(d(1e300)), "f", Float.POSITIVE_INFINITY),
            row("G22", v(d(-1e300)), "f", Float.NEGATIVE_INFINITY),
            row("G23", v(d(0.1)), "f,wf", 0.1f),
            row("G24", v(d(1.9)), "i,wi", 1),
            row("G25", v(d(-1.9)), "i", -1),
            row("G26", v(d(Double.NaN)), "i,l", 0),
            row("G27", v(d(1e10)), "i", 2147483647),
            row("G28", v(d(Double.NEGATIVE_INFINITY)), "i", -2147483648),
            row("G29", v(d(9.223372036854775807E18)), "l", Long.MAX_VALUE),
            row("G30", v(d(1e19)), "l", Long.MAX_VALUE),
            row("G31", v(d(40000.5)), "s", 32767),
            row("G32", v(d(-40000.5)), "s", -32768),
            row("G33", v(d(300.7)), "b", 127),
            row("G34", v(d(-5.5)), "c", '\u0000'),
            row("G35", v(d(1e300)), "c", '￿'),
            row("G36", v(d(0.5)), "z", true),
            row("G37", v(d(0.0), d(-0.0)), "z", false),
            row("G38", v(d(Double.NaN)), "z", false),
            row("G39", v(d(Double.POSITIVE_INFINITY)), "z", true),
            row("G40", v(d(1.5)), "str", "1.5"),
            row("G41", v(d(5.0)), "str", "5.0"),
            row("G42", v(d(Double.NaN)), "str", "NaN"),
            row("G43", v(d(1e300)), "str", "1.0E300"),
            row("G44", v(d(-0.0)), "str", "-0.0"),
            row("G45", v(d(2.5)), REFS, null),
            row("G46", v(z(true)), "z,wz", true),
            row("G47", v(z(true)), "i,l,wi", 1),
            row("G48", v(z(false)), "i,l,wi", 0),
            row("G49", v(z(true)), "c", '\u0001'),
            row("G50", v(z(true)), "d", 1.0, "wf", 1.0f),
            row("G51", v(z(false)), "str", "false"),
            row("G52", v(z(true)), REFS, null),
            row("G53", v(s("abc")), "str", "abc"),
            row("G54", v(s("12"), s("+12")), "i", 12),
            row("G55", v(s("-12")), "i", -12),
            row("G56", v(s(" 12 "), s("\t12\n")), "i", 12),
            row("G57", v(s("1.5"), s("1.5f")), "i", 1),
            row("G58", v(s("-1.9")), "i", -1),
            row("G59", v(s("1e3")), "i", 1000),
            row("G60", v(s("0x1p3")), "i", 8),
            row("G61", v(s("abc"), s(""), s("0x10")), "i,wi", 0),
            row("G62", v(s("1_000"), s("١٢")), "i", 0),
            row("G63", v(s("99999999999999999999")), "l", Long.MAX_VALUE),
            row("G64", v(s("-99999999999999999999")), "l", Long.MIN_VALUE),
            row("G65", v(s("99999999999999999999")), "i", 2147483647, "b", 127),
            row("G66", v(s("9007199254740993")), "l", 9007199254740993L),
            row("G67", v(s(" 9007199254740993 ")), "l", 9007199254740993L),
            row("G68", v(s("NaN")), "l", 0L),
            row("G69", v(s("Infinity")), "l", Long.MAX_VALUE),
            row("G70", v(s("-Infinity")), "l", Long.MIN_VALUE),
            row("G71", v(s("1.5"), s(" 1.5 ")), "d", 1.5),
            row("G72", v(s("abc")), "d", 0.0),
            row("G73", v(s("1e400")), "d", Double.POSITIVE_INFINITY),
            row("G74", v(s("NaN")), "d", Double.NaN),
            row("G75", v(s("1.00000017881393432617187499")), "f", 1.0000001f),
            row("G76", v(s("true"), s("TRUE")), "z", true),
            row("G77", v(s(" true"), s("yes"), s("1")), "z", false),
            row("G78", v(s("65")), "c", 'A'),
            row("G79", v(s("A"), s("-5")), "c", '\u0000'),
            row("G80", v(s("70000")), "c", '￿'),
            row("G81", v(s("é")), "bytes", new byte[] {-61, -87}),
            row("G82", v(s("12")), "wi", 12),
            row("G83", v(s("x")), "wi", 0),
            row("G84", v(s("abc")), "ints,strs,inner", null),
            row("G85", v(b(0x01, 0x02)), "bytes", new byte[] {1, 2}),
            row("G86", v(b(0x61, 0x62)), "str", "ab"),
            row("G87", v(b(0x61, 0xff, 0x62)), "str", "a�b"),
            row("G88", v(b(0xe2, 0x82), b(0xed, 0xa0, 0x80)), "str", "�"),
            row("G89", v(b(0xc0, 0xaf)), "str", "��"),
            row("G90", v(b(0x01)), "i,wi", 0, "z", false, "d", 0.0),
            row("G91", v(b(0x01, 0x02)), "ints,wints,inner", null),
            row("G92", v(a(l(1), l(2))), "ints", new int[] {1, 2}),
            row("G93", v(a()), "ints", new int[0]),
            row("G94", v(a(l(3000000000L), s("7"), d(1.9), z(true))),
                    "ints", new int[] {2147483647, 7, 1, 1}),
            row("G95", v(a(l(1), l(300), l(-300), s("x"))), "bytes", new byte[] {1, 127, -128, 0}),
            row("G96", v(a(l(1), s("a"), d(1.5))), "strs", new String[] {"1", "a", "1.5"}),
            row("G97", v(a(o(), a(l(2)))), "strs", new String[] {null, null}),
            row("G98", v(a(l(1), o(), s("x"))), "ints,wints", new int[] {1, 0, 0}),
            row("G99", v(a(a(l(1), l(2)), a(l(3)), l(4))),
                    "ints2", new int[][] {{1, 2}, {3}, null}),
            row("G100", v(a(b(0x01), s("a"), l(5))), "bytes2", new byte[][] {{1}, {0x61}, null}),
            row("G101", v(a(o("v", l(3)), l(5))), "inners", new Inner[] {inner(3, 6), null}),
            row("G102", v(a(l(1), l(2))), "i", 0, "z", false),
            row("G103", v(a(l(1), l(2))), "str,inner", null),
            row("G104", v(o("v", l(3))), "inner", inner(3, 6)),
            row("G105", v(o()), "inner", inner(5, 6)),
            row("G106", v(o("v", s("7"), "x", l(1))), "inner", inner(7, 6)),
            row("G107", v(o("v", l(3)), o("p", l(3))), "i", 0, "str", null),
            row("G108", v(o("v", l(3))), "ints,bytes", null),
        };
        return Platform.android() ? g88OnAndroid(rows) : rows;
    }

    /**
     * On Android, G88's two values in two rows: Android's UTF-8 decoder gives three U+FFFD for
     * ed a0 80, where Java's gives one (020-09, section 5.6; releases/next.md, Platforms;
     * bergdb 006-18-03); for e2 82 both give one.
     */
    private static Row[] g88OnAndroid(Row[] rows) {
        List<Row> list = new ArrayList<Row>();
        for (Row r : rows) {
            if (r.id.equals("G88")) {
                list.add(row("G88", v(b(0xe2, 0x82)), "str", "\ufffd"));
                list.add(row("G88", v(b(0xed, 0xa0, 0x80)), "str", "\ufffd\ufffd\ufffd"));
            } else {
                list.add(r);
            }
        }
        return list.toArray(new Row[0]);
    }

    /**
     * G1 to G109 and G111 (020-09, section 8.2): each row's stored value, alone in an object
     * {F: S}, put at a key and read into All and into All0, through the database and by
     * toJavaObject(): the field F holds the row's result in both classes (G111: the same
     * value), and every other field its class's initial value (principle 2). G85's array is
     * a new one at each get.
     */
    @Nano
    public static void testGetTable() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            int cases = 0;
            for (Row r : rows()) {
                for (DbValue stored : r.stored) {
                    for (int g = 0; g < r.fields.length; g++) {
                        for (String name : r.fields[g]) {
                            getCase(ch, c, r.id, stored, name, r.want[g]);
                            cases++;
                        }
                    }
                }
            }
            ch.eq("the table's cases", 163, cases);

            // G109: no field of its name; each field keeps its class's initial value.
            DbObject[] none = {o(), o("x", l(1)), o("p", l(3), "array", a(l(1)), "key", s("k"),
                    "Z", z(true), "inner2", o("v", l(1)), "ints ", a(l(1)))};
            for (DbObject stored : none) {
                String key = ch.key();
                c.put(key, stored);
                for (Class<?> cl : new Class<?>[] {All.class, All0.class}) {
                    String id = "G109, " + hex(stored.getBytes()) + " into " + cl.getSimpleName();
                    for (int way = 0; way < 2; way++) {
                        final int w = way;
                        ch.run(id, () -> ch.eq(id + " by " + WAYS[w], newInstance(cl),
                                get(w, c, key, stored, cl)));
                    }
                }
            }

            // G85: a new array at each get.
            ch.run("G85", () -> {
                DbObject stored = o("bytes", b(1, 2));
                String key = ch.key();
                c.put(key, stored);
                All x = c.get(key, All.class);
                All y = c.get(key, All.class);
                All p = stored.toJavaObject(All.class);
                All q = stored.toJavaObject(All.class);
                ch.isTrue("G85", x.bytes != y.bytes && p.bytes != q.bytes,
                        "the same array at two gets");
                x.bytes[0] = 9;
                p.bytes[0] = 9;
                ch.eq("G85, after a change of an earlier get's array", new byte[] {1, 2},
                        c.get(key, All.class).bytes);
                ch.eq("G85, after a change of an earlier toJavaObject's array",
                        new byte[] {1, 2}, stored.toJavaObject(All.class).bytes);
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    /** The two ways of a get (020-09, section 2). */
    private static final String[] WAYS = {"get", "toJavaObject"};

    /** A get of 'stored', at 'key' (put there before), as 'cl': way 0 by Connection.get. */
    private static <TYPE> TYPE get(int way, Connection c, String key, DbObject stored,
            Class<TYPE> cl) {
        return way == 0 ? c.get(key, cl) : stored.toJavaObject(cl);
    }

    /** One case of the table: {name: value} read into All and All0, both ways. */
    private static void getCase(Check ch, Connection c, String id, DbValue value, String name,
            Object result) {
        String where = id + ", {" + name + ": " + showModel(model(bytesOf(value))) + "}";
        DbObject stored = new DbObject.Builder().addDbValue(name, value).build();
        String key = ch.key();
        c.put(key, stored);
        Object[] got = {NONE, NONE};
        for (int k = 0; k < 2; k++) {
            Class<?> cl = k == 0 ? All.class : All0.class;
            for (int way = 0; way < 2; way++) {
                final int kk = k;
                final int w = way;
                String id1 = where + (k == 0 ? " into All" : " into All0 (G111)") + " by "
                        + WAYS[way];
                ch.run(id1, () -> {
                    Field f = cl.getField(name);
                    Object x = get(w, c, key, stored, cl);
                    ch.eq(id1, want(f.getType(), result), f.get(x));
                    Object init = newInstance(cl);
                    for (Field g : storedFields(cl)) {
                        if (!g.getName().equals(name)) {
                            ch.eq(id1 + ": " + g.getName() + " untouched (principle 2)",
                                    g.get(init), g.get(x));
                        }
                    }
                    if (w == 0) {
                        got[kk] = f.get(x);
                    }
                });
            }
        }
        if (got[0] != NONE && got[1] != NONE) {
            ch.eq(where + ": All's and All0's (G111)", got[0], got[1]);
        }
    }

    private static final Object NONE = new Object();

    /**
     * The result 'w' of a row as a value of the field type 't': an integer (Integer or
     * Long) boxed as t's integer type, exactly; int[] as Integer[] for an Integer[] field.
     */
    private static Object want(Class<?> t, Object w) {
        Class<?> bt = boxed(t);
        if (w == null) {
            if (t.isPrimitive()) {
                throw new IllegalStateException("the test: null for a " + t);
            }
            return null;
        }
        if ((bt == Byte.class || bt == Short.class || bt == Integer.class || bt == Long.class)
                && (w instanceof Integer || w instanceof Long)) {
            long v = ((Number) w).longValue();
            Object x = box(t, v);
            if (((Number) x).longValue() != v) {
                throw new IllegalStateException("the test: " + v + " is not a " + t);
            }
            return x;
        }
        if (t == Integer[].class && w instanceof int[]) {
            int[] a = (int[]) w;
            Integer[] x = new Integer[a.length];
            for (int k = 0; k < a.length; k++) {
                x[k] = a[k];
            }
            return x;
        }
        if (!bt.isInstance(w)) {
            throw new IllegalStateException("the test: " + show(w) + " for a " + t);
        }
        return w;
    }

    // ======== G110 to G122 ========

    /** G110, principle 4 nested: a new Inner, not the constructor's filled. */
    @Nano
    public static void testPrinciple4Nested() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            DbObject stored = o("inner", o("v", l(3)));
            String key = ch.key();
            c.put(key, stored);
            for (int way = 0; way < 2; way++) {
                final int w = way;
                String id = "G110 by " + WAYS[way];
                ch.run(id, () -> {
                    Init x = get(w, c, key, stored, Init.class);
                    ch.isTrue(id, x.inner != Init.made, "the constructor's Inner was kept");
                    ch.eq(id, inner(3, 6), x.inner);
                });
            }
        } finally {
            db.close();
        }
        ch.done();
    }

    /** G112: transient and static fields are not set from stored fields of their names. */
    @Nano
    public static void testIgnoredNames() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            DbObject stored = o("t", l(9), "st", l(9), "n", l(1));
            String key = ch.key();
            c.put(key, stored);
            for (int way = 0; way < 2; way++) {
                final int w = way;
                String id = "G112 by " + WAYS[way];
                ch.run(id, () -> {
                    T.st = 5;
                    T x = get(w, c, key, stored, T.class);
                    ch.eq(id + ", t", 5, x.t);
                    ch.eq(id + ", T.st", 5, T.st);
                    ch.eq(id + ", n", 1, x.n);
                });
            }
        } finally {
            db.close();
        }
        ch.done();
    }

    /** G113: a field named key is an ordinary field. */
    @Nano
    public static void testKeyField() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            DbObject[] stored = {o("n", l(1)), o("key", s("x"), "n", l(1))};
            String[] want = {null, "x"};
            for (int k = 0; k < 2; k++) {
                DbObject st = stored[k];
                String wantKey = want[k];
                c.put("/k", st);
                for (int way = 0; way < 2; way++) {
                    final int w = way;
                    String id = "G113, " + hex(st.getBytes()) + " by " + WAYS[way];
                    ch.run(id, () -> {
                        K x = get(w, c, "/k", st, K.class);
                        ch.eq(id + ", key", wantKey, x.key);
                        ch.eq(id + ", n", 1, x.n);
                    });
                }
                ch.run("G113, DbObject", () -> ch.eq("G113, getString(\"key\") of a DbObject",
                        wantKey, c.get("/k", DbObject.class).getString("key")));
            }
        } finally {
            db.close();
        }
        ch.done();
    }

    /** G114: fields are set in the order of their names, a before b. */
    @Nano
    public static void testFieldOrder() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            DbObject stored = o("a", o(), "b", o());
            String key = ch.key();
            c.put(key, stored);
            for (int way = 0; way < 2; way++) {
                final int w = way;
                String id = "G114 by " + WAYS[way];
                ch.run(id, () -> {
                    Two x = get(w, c, key, stored, Two.class);
                    ch.isTrue(id, x.a.number < x.b.number, "a's number " + x.a.number
                            + ", b's " + x.b.number);
                });
            }
        } finally {
            db.close();
        }
        ch.done();
    }

    /** G115 to G117: the top level, by the fields p and array. */
    @Nano
    public static void testTopLevel() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            ch.run("G115", () -> {
                c.put("/g115", 5);
                ch.eq("G115, int", 5, c.get("/g115", int.class));
                ch.eq("G115, long", 5L, c.get("/g115", long.class));
                ch.eq("G115, int[]", null, c.get("/g115", int[].class));
            });
            DbObject p5 = o("p", l(5));
            ch.run("G115 by toJavaObject", () -> {
                ch.eq("G115 by toJavaObject, int", 5, p5.toJavaObject(int.class));
                ch.eq("G115 by toJavaObject, long", 5L, p5.toJavaObject(long.class));
                ch.eq("G115 by toJavaObject, int[]", null, p5.toJavaObject(int[].class));
            });

            DbObject array = o("array", a(l(1), s("2"), d(3.5)));
            c.put("/g116", array);
            for (int way = 0; way < 2; way++) {
                final int w = way;
                String id = "G116 by " + WAYS[way];
                ch.run(id + ", int[]", () -> ch.eq(id + ", int[]", new int[] {1, 2, 3},
                        get(w, c, "/g116", array, int[].class)));
                ch.run(id + ", String[]", () -> ch.eq(id + ", String[]",
                        new String[] {"1", "2", "3.5"}, get(w, c, "/g116", array,
                        String[].class)));
                ch.run(id + ", Inner[]", () -> ch.eq(id + ", Inner[]", new Inner[3],
                        get(w, c, "/g116", array, Inner[].class)));
            }

            DbObject p12 = o("p", s("12"));
            DbObject pObject = o("p", o());
            DbObject v3 = o("v", l(3));
            c.put("/g117/1", p12);
            c.put("/g117/2", pObject);
            c.put("/g117/3", v3);
            for (int way = 0; way < 2; way++) {
                final int w = way;
                String id = "G117 by " + WAYS[way];
                ch.run(id + ", {p: \"12\"}", () -> ch.eq(id + ", {p: \"12\"} as Integer", 12,
                        get(w, c, "/g117/1", p12, Integer.class)));
                ch.run(id + ", {p: {}}", () -> ch.eq(id + ", {p: {}} as int", 0,
                        get(w, c, "/g117/2", pObject, int.class)));
                ch.run(id + ", {v: 3}", () -> ch.eq(id + ", {v: 3} as int", null,
                        get(w, c, "/g117/3", v3, int.class)));
            }
        } finally {
            db.close();
        }
        ch.done();
    }

    /**
     * G118 to G120: a value that is not a stored object, and the class checked first, also
     * at a key without a value; in rw(), each is the action's exception, and the database
     * goes on.
     */
    @Nano
    public static void testNotAnObjectAndCheckFirst() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            c.put("/g118", "abc");
            ch.creationRefused("G118, as Inner", () -> c.get("/g118", Inner.class), null);
            ch.creationRefused("G118, as int", () -> c.get("/g118", int.class), null);
            ch.run("G119, Inner", () -> ch.eq("G119, Inner at a key without a value", null,
                    c.get("/none", Inner.class)));
            ch.creationRefused("G119, Bad at a key without a value",
                    () -> c.get("/none", Bad.class), null);

            String[] keys = {"/g118", "/g118", "/none"};
            Class<?>[] classes = {Inner.class, int.class, Bad.class};
            for (int k = 0; k < keys.length; k++) {
                String key = keys[k];
                Class<?> cl = classes[k];
                ch.creationRefused("G120, " + key + " as " + cl.getSimpleName() + " in rw()",
                        () -> c.rw(env -> {
                            env.put("/g120/written", "x");
                            env.get(key, cl);
                        }), null);
            }
            ch.run("G120, after", () -> {
                ch.eq("G120, nothing committed", null, c.get("/g120/written", String.class));
                c.rw(env -> env.put("/g120/after", "y"));
                ch.eq("G120, the next transaction", "y", c.get("/g120/after", String.class));
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    /** G121: a constructor that throws, every time, with its exception as the cause. */
    @Nano
    public static void testConstructors() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            DbObject empty = o();
            c.put("/g121", empty);
            for (int k = 1; k <= 2; k++) {
                ch.creationRefused("G121, get " + k + " as Throws",
                        () -> c.get("/g121", Throws.class), IllegalStateException.class);
                ch.creationRefused("G121, toJavaObject " + k + " as Throws",
                        () -> empty.toJavaObject(Throws.class), IllegalStateException.class);
            }
            for (int way = 0; way < 2; way++) {
                final int w = way;
                String id = "G121, Holder of {} by " + WAYS[way];
                ch.run(id, () -> {
                    Holder h = get(w, c, "/g121", empty, Holder.class);
                    ch.isTrue(id, h != null && h.t == null, "not a Holder with t null");
                });
            }
            DbObject withT = o("t", o());
            c.put("/g121/t", withT);
            ch.creationRefused("G121, a get of {t: {}} as Holder",
                    () -> c.get("/g121/t", Holder.class), IllegalStateException.class);
            ch.creationRefused("G121, toJavaObject of {t: {}} as Holder",
                    () -> withT.toJavaObject(Holder.class), IllegalStateException.class);
        } finally {
            db.close();
        }
        ch.done();
    }

    /** G122: a primary scan of objects gives each as a get does. */
    @Nano
    public static void testScans() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            DbObject[] stored = {
                o("ints", a(l(3000000000L), s("7"), d(1.9), z(true))),     // G94
                o("inner", o("v", l(3))),                                   // G104
                o("x", l(1))                                                // G109
            };
            for (int k = 0; k < stored.length; k++) {
                c.put("/scan/" + k, stored[k]);
            }
            ch.run("G122", () -> {
                List<All> list = new ArrayList<All>();
                for (All x : c.usePrimary(All.class).dir("/scan/").objects()) {
                    list.add(x);
                }
                ch.eq("G122, the number of objects", 3, list.size());
                for (int k = 0; k < Math.min(3, list.size()); k++) {
                    ch.eq("G122, /scan/" + k, c.get("/scan/" + k, All.class), list.get(k));
                }
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    // ======== K1 to K18: the class cases (020-09, section 8.3) ========

    /**
     * A refused class: a put of 'x' (unless null), by toDbObject() and Connection.put(), is
     * refused with an IllegalArgumentException naming the class and 'mentions', and writes
     * nothing; a get as 'cl' is refused with ObjectCreationException (refusedGet).
     */
    private static void refusedClass(Check ch, Connection c, String id, Class<?> cl, Object x,
            String... mentions) {
        if (x != null) {
            refusedPut(ch, c, id, cl, x, mentions);
        }
        refusedGet(ch, c, id, cl);
    }

    /**
     * A class refused for the type of its field 'field', which is not on the list or not a
     * Data Object class: as refusedClass, but the put's message must name the field (the
     * path), and may name either class.
     */
    private static void refusedType(Check ch, Connection c, String id, Class<?> cl, Object x,
            String field) {
        refusedPut(ch, c, id, null, x, field);
        refusedGet(ch, c, id, cl);
    }

    /** A put of 'x' refused, naming 'named' (unless null) and 'mentions'; nothing written. */
    private static void refusedPut(Check ch, Connection c, String id, Class<?> named, Object x,
            String... mentions) {
        ch.argRefused(id + ", toDbObject", () -> DbObject.toDbObject(x), named, mentions);
        String key = ch.key();
        ch.argRefused(id + ", Connection.put", () -> c.put(key, x), named, mentions);
        ch.run(id + ", Connection.put", () -> ch.eq(id + ", nothing written", null,
                c.get(key, byte[].class)));
    }

    /**
     * A get as 'cl' refused with ObjectCreationException: of {}, of an object with fields,
     * at a key without a value, and by toJavaObject().
     */
    private static void refusedGet(Check ch, Connection c, String id, Class<?> cl) {
        String key = ch.key();
        c.put(key + "/a", o());
        c.put(key + "/b", o("v", l(1), "x", l(1), "b", o("v", l(1)), "p", l(1)));
        ch.creationRefused(id + ", a get of {}", () -> c.get(key + "/a", cl), null);
        ch.creationRefused(id + ", a get of {v: 1, ...}", () -> c.get(key + "/b", cl), null);
        ch.creationRefused(id + ", a get at a key without a value",
                () -> c.get(key + "/none", cl), null);
        ch.creationRefused(id + ", toJavaObject", () -> o().toJavaObject(cl), null);
    }

    /** A valid class: the put of 'x' is taken both ways, and read back equal both ways. */
    private static void validClass(Check ch, Connection c, String id, Object x) {
        Class<?> cl = x.getClass();
        ch.run(id + ", valid", () -> {
            DbObject stored = DbObject.toDbObject(x);
            String key = ch.key();
            c.put(key, x);
            ch.eq(id + ", Connection.put's bytes", stored.getBytes(),
                    c.get(key, DbObject.class).getBytes());
            ch.eq(id + ", a get", x, c.get(key, cl));
            ch.eq(id + ", toJavaObject", x, stored.toJavaObject(cl));
            ch.eq(id + ", a get at a key without a value", null, c.get(key + "/none", cl));
        });
    }

    /** K1 to K9. */
    @Nano
    public static void testClassCases1() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            refusedClass(ch, c, "K1", P.class, new P());
            HoldsP hp = new HoldsP();
            hp.p = new P();
            refusedType(ch, c, "K1, held", HoldsP.class, hp, "p");
            refusedType(ch, c, "K1, held, null", HoldsP.class, new HoldsP(), "p");
            refusedClass(ch, c, "K2", PrivateConstructor.class, new PrivateConstructor());
            refusedClass(ch, c, "K3", IntConstructor.class, new IntConstructor(1));
            refusedClass(ch, c, "K4", Bad.class, new Bad(), "v");

            PrivateTransient pt = new PrivateTransient();
            pt.v = 3;
            pt.t = 9;
            validClass(ch, c, "K5", pt);
            ch.run("K5", () -> {
                ch.eq("K5, t not stored", 'z', DbObject.toDbObject(pt).getType("t"));
                DbObject stored = o("v", l(2), "t", l(9));
                PrivateTransient x = stored.toJavaObject(PrivateTransient.class);
                ch.eq("K5, v", 2, x.v);
                ch.eq("K5, t ignored", 5, x.t);
            });

            refusedClass(ch, c, "K6", FinalField.class, new FinalField(), "v");

            ObjectField of = new ObjectField();
            of.x = 5;
            refusedType(ch, c, "K7, Object", ObjectField.class, of, "x");
            refusedType(ch, c, "K7, Object, null", ObjectField.class, new ObjectField(), "x");
            ListField lf = new ListField();
            lf.x = new ArrayList<String>();
            refusedType(ch, c, "K7, List<String>", ListField.class, lf, "x");
            RunnableField rf = new RunnableField();
            rf.x = () -> {};
            refusedType(ch, c, "K7, Runnable", RunnableField.class, rf, "x");

            EnumField ef = new EnumField();
            ef.x = Color.RED;
            refusedType(ch, c, "K8, an enum", EnumField.class, ef, "x");
            DateField df = new DateField();
            df.x = new Date();
            refusedType(ch, c, "K8, Date", DateField.class, df, "x");
            refusedType(ch, c, "K8, Date, null", DateField.class, new DateField(), "x");
            DbObjectField dof = new DbObjectField();
            dof.x = o("v", l(1));
            refusedType(ch, c, "K8, DbObject", DbObjectField.class, dof, "x");

            ObjectArrayField oaf = new ObjectArrayField();
            oaf.x = new Object[] {1};
            refusedType(ch, c, "K9", ObjectArrayField.class, oaf, "x");
            refusedType(ch, c, "K9, null", ObjectArrayField.class, new ObjectArrayField(), "x");
        } finally {
            db.close();
        }
        ch.done();
    }

    /** K10 to K18. */
    @Nano
    public static void testClassCases2() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            refusedClass(ch, c, "K10", K10C.class, new K10C(), "x");

            Outer outer = new Outer();
            outer.b = new Bad();
            refusedType(ch, c, "K11", Outer.class, outer, "b");
            refusedType(ch, c, "K11, null", Outer.class, new Outer(), "b");

            refusedClass(ch, c, "K12", K12C.class, new K12C(), "x");

            refusedGet(ch, c, "K13, an abstract class", Abstract13.class);
            refusedGet(ch, c, "K13, an interface", Interface13.class);
            refusedGet(ch, c, "K13, an enum", Color.class);
            refusedGet(ch, c, "K13, a record", Record13.class);
            refusedPut(ch, c, "K13, an enum at the top", Color.class, Color.GREEN);
            refusedPut(ch, c, "K13, a record at the top", Record13.class, new Record13(1));
            HoldsAbstract ha = new HoldsAbstract();
            refusedType(ch, c, "K13, held abstract, null", HoldsAbstract.class, ha, "x");
            HoldsAbstract ha2 = new HoldsAbstract();
            ha2.x = new Concrete13();
            refusedType(ch, c, "K13, held abstract", HoldsAbstract.class, ha2, "x");
            HoldsInterface hi = new HoldsInterface();
            hi.x = new Impl13();
            refusedType(ch, c, "K13, held interface", HoldsInterface.class, hi, "x");
            HoldsEnum he = new HoldsEnum();
            he.x = Color.RED;
            refusedType(ch, c, "K13, held enum", HoldsEnum.class, he, "x");
            HoldsRecord hr = new HoldsRecord();
            hr.x = new Record13(1);
            refusedType(ch, c, "K13, held record", HoldsRecord.class, hr, "x");

            refusedClass(ch, c, "K14, a name of 256 letters", DbObjectFormatTester.Name256.class,
                    new DbObjectFormatTester.Name256());
            validClass(ch, c, "K14, a name of 255 letters", new DbObjectFormatTester.Name255());

            Box<String> box = new Box<String>();
            box.value = "a";
            refusedType(ch, c, "K15", Box.class, box, "value");
            refusedType(ch, c, "K15, null", Box.class, new Box<String>(), "value");

            Object anonymous = new Object() {
                @SuppressWarnings("unused")
                public int x = 1;
            };
            refusedPut(ch, c, "K16", anonymous.getClass(), anonymous);

            validClass(ch, c, "K17", chain(3));
            refusedPut(ch, c, "K17, 17 Nodes", null, chain(17), "next.next");

            Index index = new Index();
            index.dirs = new String[] {"/a/", "/b/"};
            index.fields = new String[] {"name"};
            index.state = "done";
            index.typeStrings = new String[] {"s"};
            validClass(ch, c, "K18", index);
        } finally {
            db.close();
        }
        ch.done();
    }

    /** A chain of 'length' Nodes, v 0 first. */
    static Node chain(int length) {
        Node head = null;
        for (int k = length - 1; k >= 0; k--) {
            Node n = new Node();
            n.v = k;
            n.next = head;
            head = n;
        }
        return head;
    }

    /** An int[] of 'n' dimensions, each of length 1. */
    static Object nestedIntArray(int n) {
        Object a = new int[] {7};
        for (int k = 1; k < n; k++) {
            Object outer = Array.newInstance(a.getClass(), 1);
            Array.set(outer, 0, a);
            a = outer;
        }
        return a;
    }

    // ======== W1 to W36: the put cases (020-09, section 8.4) ========

    /** The bytes of the field 'name' of 'stored', or null if it has none. */
    private static byte[] fieldBytes(DbObject stored, String name) {
        DbValue v = stored.getDbValue(name);
        return v == null ? null : bytesOf(v);
    }

    /** The bytes of the field 'name' of the put of 'x'. */
    private static byte[] fieldBytes(Object x, String name) {
        return fieldBytes(DbObject.toDbObject(x), name);
    }

    /** W1 to W14: scalars and arrays, by the field's type. */
    @Nano
    public static void testPutValues() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            ch.run("W1", () -> {
                All x = new All();
                x.z = true;
                x.wz = false;
                ch.eq("W1, boolean true", bytesOf(z(true)), fieldBytes(x, "z"));
                ch.eq("W1, Boolean false", bytesOf(z(false)), fieldBytes(x, "wz"));
            });
            ch.run("W2", () -> {
                All x = new All();
                x.b = 5;
                x.s = 5;
                x.i = 5;
                x.l = 5;
                x.wb = 5;
                x.ws = 5;
                x.wi = 5;
                x.wl = 5L;
                DbObject stored = DbObject.toDbObject(x);
                for (String name : new String[] {"b", "s", "i", "l", "wb", "ws", "wi", "wl"}) {
                    ch.eq("W2, " + name, new byte[] {0x10, 0x05}, fieldBytes(stored, name));
                }
            });
            ch.run("W3", () -> {
                All x = new All();
                x.c = 'A';
                x.wc = 'A';
                ch.eq("W3, char", bytesOf(l(65)), fieldBytes(x, "c"));
                ch.eq("W3, Character", bytesOf(l(65)), fieldBytes(x, "wc"));
            });
            ch.run("W4", () -> {
                All x = new All();
                x.c = '\ud800';
                ch.eq("W4", bytesOf(l(55296)), fieldBytes(x, "c"));
            });
            ch.run("W5", () -> {
                All x = new All();
                x.f = 1.5f;
                ch.eq("W5, 1.5f", bytesOf(d(1.5)), fieldBytes(x, "f"));
                x.f = -0.0f;
                ch.eq("W5, -0.0f", new byte[] {0x46, 0, 0, 0, 0, 0, 0, 0, (byte) 0x80},
                        fieldBytes(x, "f"));
            });
            ch.run("W6", () -> {
                All x = new All();
                x.f = Float.NaN;
                ch.eq("W6, NaN", NAN_BYTES, fieldBytes(x, "f"));
                x.f = Float.MAX_VALUE;
                ch.eq("W6, MAX_VALUE", bytesOf(d(3.4028234663852886E38)), fieldBytes(x, "f"));
            });
            ch.run("W7", () -> {
                All x = new All();
                x.d = Double.longBitsToDouble(0x7ff0000000000001L);
                ch.eq("W7", NAN_BYTES, fieldBytes(x, "d"));
            });
            ch.run("W8", () -> {
                All x = new All();
                x.str = "é";
                ch.eq("W8", new byte[] {0x14, 0x02, (byte) 0xc3, (byte) 0xa9},
                        fieldBytes(x, "str"));
            });
            All w9 = new All();
            w9.str = "a\ud800";
            refusedPut(ch, c, "W9", null, w9, "str");
            ch.run("W10", () -> {
                All x = new All();
                x.bytes = new byte[] {1, 2};
                DbObject stored = DbObject.toDbObject(x);
                String key = ch.key();
                c.put(key, x);
                x.bytes[0] = 9;
                ch.eq("W10, toDbObject", new byte[] {1, 2}, stored.getByteArray("bytes"));
                ch.eq("W10, Connection.put", new byte[] {1, 2},
                        c.get(key, DbObject.class).getByteArray("bytes"));
                ch.eq("W10, the bytes", new byte[] {0x18, 0x02, 0x01, 0x02},
                        fieldBytes(stored, "bytes"));
            });
            ch.run("W11", () -> {
                All x = new All();
                x.bytes = new byte[0];
                ch.eq("W11", new byte[] {0x18, 0x00}, fieldBytes(x, "bytes"));
            });
            ch.run("W12", () -> {
                All x = new All();
                x.ints = new int[] {1, 2};
                ch.eq("W12, int[]", bytesOf(a(l(1), l(2))), fieldBytes(x, "ints"));
                Every e = new Every();
                e.cs = new char[] {'a'};
                ch.eq("W12, char[]", bytesOf(a(l(97))), fieldBytes(e, "cs"));
            });
            ch.run("W13", () -> {
                Every e = new Every();
                e.fs = new float[] {1.5f};
                e.zs = new boolean[] {true};
                ch.eq("W13, float[]", bytesOf(a(d(1.5))), fieldBytes(e, "fs"));
                ch.eq("W13, boolean[]", bytesOf(a(z(true))), fieldBytes(e, "zs"));
            });
            ch.run("W14", () -> {
                All x = new All();
                x.bytes2 = new byte[][] {{1}};
                ch.eq("W14", bytesOf(a(b(1))), fieldBytes(x, "bytes2"));
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    /** A double NaN as stored: 0x7ff8000000000000 (020-07, R12). */
    private static final byte[] NAN_BYTES = {0x46, 0, 0, 0, 0, 0, 0, (byte) 0xf8, 0x7f};

    /** W15 to W21: null array elements refused; null fields left out. */
    @Nano
    public static void testPutNulls() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            All w15 = new All();
            w15.strs = new String[] {"a", null};
            refusedPut(ch, c, "W15", null, w15, "strs[1]");
            All w16 = new All();
            w16.wints = new Integer[] {1, null};
            refusedPut(ch, c, "W16", null, w16, "wints[1]");
            All w17 = new All();
            w17.ints2 = new int[][] {{1}, null};
            refusedPut(ch, c, "W17", null, w17, "ints2[1]");
            All w18 = new All();
            w18.inners = new Inner[] {null};
            refusedPut(ch, c, "W18", null, w18, "inners[0]");
            All w19 = new All();
            w19.strs = new String[2];
            refusedPut(ch, c, "W19", null, w19, "strs[0]");

            ch.run("W20", () -> {
                All x = new All();
                x.str = null;
                x.bytes = null;
                x.ints = null;
                x.wi = null;
                x.inner = null;
                DbObject stored = DbObject.toDbObject(x);
                for (String name : new String[] {"str", "bytes", "ints", "wi", "inner"}) {
                    ch.eq("W20, " + name, 'z', stored.getType(name));
                }
                ch.eq("W20, the other fields", 20, stored.getFieldCount());
            });
            ch.run("W21", () -> {
                Dflt x = new Dflt();
                x.s = null;
                DbObject stored = DbObject.toDbObject(x);
                ch.eq("W21, left out", 'z', stored.getType("s"));
                String key = ch.key();
                c.put(key, x);
                ch.eq("W21, a get", "dflt", c.get(key, Dflt.class).s);
                ch.eq("W21, toJavaObject", "dflt", stored.toJavaObject(Dflt.class).s);
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    /** W22, W23: a value's class must be its field's type exactly. */
    @Nano
    public static void testPutClassOfValue() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            All w22 = new All();
            w22.inner = new SubInner();
            refusedPut(ch, c, "W22", SubInner.class, w22, "inner", "Inner");
            All w23 = new All();
            w23.inners = new SubInner[] {new SubInner()};
            refusedPut(ch, c, "W23, a SubInner[]", null, w23, "inners");
            All w23b = new All();
            w23b.inners = new Inner[] {new Inner(), new SubInner()};
            refusedPut(ch, c, "W23, a SubInner element", SubInner.class, w23b, "inners[1]");
        } finally {
            db.close();
        }
        ch.done();
    }

    /** W24 to W27: depth, cycles and shared objects. */
    @Nano
    public static void testPutDepthAndCycles() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            Node n16 = chain(16);
            ch.run("W24, 16 Nodes", () -> {
                DbObject stored = DbObject.toDbObject(n16);
                ch.eq("W24, 16 Nodes read back", n16, stored.toJavaObject(Node.class));
            });
            refusedPut(ch, c, "W24, 17 Nodes", null, chain(17), "next.next");

            Object a15 = nestedIntArray(15);
            ch.run("W25, 15 dimensions", () -> {
                DbObject stored = DbObject.toDbObject(a15);
                ch.eq("W25, 15 dimensions, the field array", 'a', stored.getType("array"));
                ch.eq("W25, read back", a15, stored.toJavaObject(a15.getClass()));
            });
            refusedPut(ch, c, "W25, 16 dimensions", null, nestedIntArray(16));

            Node w26 = new Node();
            w26.next = w26;
            refusedPut(ch, c, "W26", null, w26, "cycle", "next");

            ch.run("W27", () -> {
                Pair p = new Pair();
                Inner shared = inner(1, 2);
                p.x = shared;
                p.y = shared;
                DbObject stored = DbObject.toDbObject(p);
                ch.eq("W27, two equal objects", fieldBytes(stored, "x"), fieldBytes(stored, "y"));
                String key = ch.key();
                c.put(key, p);
                for (int way = 0; way < 2; way++) {
                    String id = "W27 by " + WAYS[way];
                    Pair r = get(way, c, key, stored, Pair.class);
                    ch.isTrue(id, r.x != r.y, "one object for both fields");
                    ch.eq(id + ", x", shared, r.x);
                    ch.eq(id + ", y", shared, r.y);
                }
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    /** W28 to W30: the top level. */
    @Nano
    public static void testPutTopLevel() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            ch.argRefused("W28, null by toDbObject", () -> DbObject.toDbObject(null), null);
            ch.argRefused("W28, null by Connection.put", () -> c.put("/w28", null), null);
            refusedPut(ch, c, "W28, an Object[]", null, new Object[] {1});

            ch.run("W29, 5", () -> {
                ch.eq("W29, 5", o("p", l(5)).getBytes(), DbObject.toDbObject(5).getBytes());
                c.put("/w29/5", 5);
                ch.eq("W29, 5 by Connection.put", o("p", l(5)).getBytes(),
                        c.get("/w29/5", DbObject.class).getBytes());
            });
            ch.run("W29, 'A'", () -> {
                ch.eq("W29, 'A'", o("p", l(65)).getBytes(), DbObject.toDbObject('A').getBytes());
                c.put("/w29/A", 'A');
                ch.eq("W29, 'A' by Connection.put", o("p", l(65)).getBytes(),
                        c.get("/w29/A", DbObject.class).getBytes());
            });
            ch.run("W30", () -> {
                ch.eq("W30", o("array", a(l(1))).getBytes(),
                        DbObject.toDbObject(new int[] {1}).getBytes());
                c.put("/w30", new int[] {1});
                ch.eq("W30 by Connection.put", o("array", a(l(1))).getBytes(),
                        c.get("/w30", DbObject.class).getBytes());
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    /** W31 to W34: which fields are stored, and in what order. */
    @Nano
    public static void testPutFields() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            ch.run("W31", () -> {
                K k = new K();
                k.key = "x";
                k.n = 1;
                ch.eq("W31, toDbObject", "x", DbObject.toDbObject(k).getString("key"));
                c.put("/w31", k);
                ch.eq("W31, Connection.put", "x",
                        c.get("/w31", DbObject.class).getString("key"));
                ch.eq("W31, a get", "x", c.get("/w31", K.class).key);
            });
            ch.run("W32", () -> {
                DbObject stored = DbObject.toDbObject(new T());
                ch.eq("W32, transient", 'z', stored.getType("t"));
                ch.eq("W32, static", 'z', stored.getType("st"));
                ch.eq("W32, the stored", o("n", l(0)).getBytes(), stored.getBytes());
            });
            ch.run("W33", () -> ch.eq("W33", new byte[] {(byte) 0x82, 0x48, 2, 4, 8,
                    1, 'a', 0x10, 1, 1, 'b', 0x10, 2}, DbObject.toDbObject(new BA()).getBytes()));
            ch.run("W34", () -> ch.eq("W34", new byte[] {(byte) 0x82, 0x48, 0},
                    DbObject.toDbObject(new Empty()).getBytes()));
        } finally {
            db.close();
        }
        ch.done();
    }

    /** W35, W36: a refused value in w() and in rw(); nothing written, the database goes on. */
    @Nano
    public static void testPutTransactions() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            All valid = new All();
            All refused = new All();
            refused.strs = new String[] {"a", null};

            ch.run("W35", () -> {
                WBuilder w = c.w().put("/w35/a", valid);
                ch.argRefused("W35, at the call", () -> w.put("/w35/b", refused), null,
                        "strs[1]");
                ch.eq("W35, nothing written", null, c.get("/w35/a", byte[].class));
                ch.eq("W35, nothing written", null, c.get("/w35/b", byte[].class));
            });

            ch.argRefused("W36", () -> c.rw(env -> {
                env.put("/w36/a", valid);
                env.put("/w36/b", refused);
            }), null, "strs[1]");
            ch.run("W36, after", () -> {
                ch.eq("W36, nothing written", null, c.get("/w36/a", byte[].class));
                c.put("/w36/c", "x");
                ch.eq("W36, the database goes on", "x", c.get("/w36/c", String.class));
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    // ======== A stored value too large, refused before a copy (bergdb 021-23) ========

    public static class Parts {
        public byte[][] parts;
        public Parts() {}
    }

    public static class PartsArray {
        public Parts[] all;
        public PartsArray() {}
    }

    public static class Rows {
        public double[][] rows;
        public Rows() {}
    }

    public static class Texts {
        public String[] texts;
        public Texts() {}
    }

    /**
     * A put of an object whose stored value would pass 2^31 - 9 bytes, Java's largest array,
     * is refused with IllegalArgumentException that names the place and the limit, before
     * anything is copied: here objects of 1 to 8 MiB in memory, 2.2 GB stored, as many
     * references to one array (bergdb 021-23; 020-24-12, U12-1). The put copied each element
     * into its array's buffer and checked the array's size only then: OutOfMemoryError with
     * a heap below about 5 GB, which in rw() failed the database; above it, "size: a value
     * of ..." without the place. By toDbObject(), put(), w() and rw(): nothing written, and
     * the database goes on.
     */
    @Nano
    public static void testPutTooLarge() {
        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            byte[] mib = new byte[1 << 20];
            Parts parts = new Parts();
            parts.parts = new byte[2100][];
            Arrays.fill(parts.parts, mib);
            tooLarge(ch, c, "021-23, 2100 references to 1 MiB of bytes", parts, "parts[2047]");

            Rows rows = new Rows();
            rows.rows = new double[240][];
            Arrays.fill(rows.rows, new double[1 << 20]);
            tooLarge(ch, c, "021-23, 240 references to 2^20 doubles", rows, "rows[227]");

            Parts one = new Parts();
            one.parts = new byte[][] {mib};
            PartsArray all = new PartsArray();
            all.all = new Parts[2100];
            Arrays.fill(all.all, one);
            tooLarge(ch, c, "021-23, 2100 references to an object", all, "all[2047].parts[0]");

            byte[][] top = new byte[2100][];
            Arrays.fill(top, mib);
            tooLarge(ch, c, "021-23, an array at the top", top, "[2047]");
        } finally {
            db.close();
        }
        ch.done();
    }

    /** 'x' refused as too large, at 'at', in each way; nothing written; the database on. */
    private static void tooLarge(Check ch, Connection c, String id, Object x, String at) {
        String[] mentions = {"too large", "'" + at + "'", ObjectFormat.MAX_ARRAY + " bytes",
                "2^31 - 1"};
        refusedPut(ch, c, id, null, x, mentions);
        String key = ch.key();
        ch.argRefused(id + ", w()", () -> c.w().put(key, x).execute(), null, mentions);
        ch.argRefused(id + ", rw()", () -> c.rw(env -> env.put(key, x)), null, mentions);
        ch.run(id + ", after", () -> {
            ch.eq(id + ", nothing written", null, c.get(key, byte[].class));
            c.put(key + "/after", "x");
            ch.eq(id + ", the database goes on", "x", c.get(key + "/after", String.class));
        });
    }

    /**
     * The size counted first is the size written, exactly: with the limit at the stored
     * value's size the put is taken, with one byte less refused, at the top and in each kind
     * of field and array (bergdb 021-23); r1() checks it for each random object. The place
     * named is where the count passes the limit: in a string, a nested object, a frame.
     */
    @Nano
    public static void testStoredSizeExact() {
        Check ch = new Check();
        String text = "a\u00e9\u20ac\ud83d\ude00".repeat(40);
        Texts texts = new Texts();
        texts.texts = new String[] {text, "", text};
        Rows rows = new Rows();
        rows.rows = new double[][] {{}, {1.5, Double.NaN}};
        Object[] values = {5, 'A', -1L, true, 2.5f, text, "", new int[] {1, 300, 70000, -1},
                new long[] {Long.MIN_VALUE, 0}, new short[] {-129, 128}, new char[] {'a', 0xffff},
                new boolean[] {true}, new float[] {1}, new double[0], new String[] {"x", text},
                new Integer[] {1, 128}, new byte[][] {{}, new byte[200], new byte[40000]},
                nestedIntArray(15), chain(16), texts, rows, new Parts(), new Empty()};
        for (Object x : values) {
            exactSize(ch, "021-23, " + x.getClass().getTypeName(), x);
        }
        ch.run("021-23, the place", () -> {
            // 822 bytes: the header, "texts", 0x42, strings of 403, 2 and 403 bytes, 0x43
            // (counted first), the frame of 5 bytes last; Node's object of 34: the frame of
            // its "next" counted at 22 to 26.
            int size = DbObject.toDbObject(texts).getBytes().length;
            ch.eq("021-23, the size of texts", 822, size);
            ch.argRefused("021-23, in a string",
                    () -> DataObjects.toDbObject(texts, size - 200), null, "'texts[2]'");
            ch.argRefused("021-23, the frame",
                    () -> DataObjects.toDbObject(texts, size - 1), null, "at the top");
            Node n = chain(3);
            ch.eq("021-23, the size of a Node", 34, DbObject.toDbObject(n).getBytes().length);
            ch.argRefused("021-23, a nested frame",
                    () -> DataObjects.toDbObject(n, 24), null, "'next'");
        });
        ch.done();
    }

    /** The stored size of 'x', with the limit at it and one byte below. */
    static void exactSize(Check ch, String id, Object x) {
        ch.run(id, () -> {
            byte[] stored = DbObject.toDbObject(x).getBytes();
            ch.eq(id + ", at the limit", stored,
                    DataObjects.toDbObject(x, stored.length).getBytes());
            ch.argRefused(id + ", a byte below",
                    () -> DataObjects.toDbObject(x, stored.length - 1), null, "too large");
        });
    }

    // ======== R1: the round trip (020-09, section 8.5) ========

    /** R1 with the unit group's seed. */
    @Nano
    public static void testRoundTrip() {
        Check ch = new Check();
        Database db = memory();
        try {
            r1(ch, db.connection(), UNIT_SEED, UNIT_R1);
        } finally {
            db.close();
        }
        ch.done();
    }

    /**
     * R1: 'count' random Data Objects from 'seed', each put and read back into its class:
     * each field as put, or the constructor's value for a null field; and when no field is
     * null, the put of what was read has the bytes of the put. One in ten goes through the
     * database (when 'c' is not null), the others by toDbObject() and toJavaObject().
     */
    static void r1(Check ch, Connection c, long seed, int count) {
        ObjectGen g = new ObjectGen(seed);
        for (int k = 0; k < count; k++) {
            Object x = g.top();
            Class<?> cl = x.getClass();
            String id = "R1, seed " + seed + ", object " + k + " (" + cl.getSimpleName() + ")";
            boolean viaDb = c != null && k % 10 == 0;
            exactSize(ch, id + ", its size", x);
            ch.run(id, () -> {
                DbObject stored = DbObject.toDbObject(x);
                Object r;
                if (viaDb) {
                    String key = ch.key();
                    c.put(key, x);
                    r = c.get(key, cl);
                } else {
                    r = stored.toJavaObject(cl);
                }
                ch.eq(id, withDefaults(x), r);
                if (!hasNullField(x)) {
                    ch.eq(id + ", the put of the get", stored.getBytes(),
                            DbObject.toDbObject(r).getBytes());
                }
            });
        }
    }

    /**
     * What R1 reads back: 'x' with each null field, at any depth, as its class's constructor
     * gives it (020-09, section 4.3).
     */
    static Object withDefaults(Object x) {
        if (x == null) {
            return null;
        }
        Class<?> cl = x.getClass();
        if (cl.isArray()) {
            if (cl.getComponentType().isPrimitive()) {
                return x;
            }
            int n = Array.getLength(x);
            Object a = Array.newInstance(cl.getComponentType(), n);
            for (int k = 0; k < n; k++) {
                Array.set(a, k, withDefaults(Array.get(x, k)));
            }
            return a;
        }
        if (isScalar(cl)) {
            return x;
        }
        Object init = newInstance(cl);
        Object copy = newInstance(cl);
        for (Field f : storedFields(cl)) {
            Object v = fieldValue(f, x);
            setField(f, copy, v == null ? fieldValue(f, init) : withDefaults(v));
        }
        return copy;
    }

    /** True if a stored field of 'x', at any depth, is null. */
    static boolean hasNullField(Object x) {
        Class<?> cl = x.getClass();
        if (cl.isArray()) {
            if (!cl.getComponentType().isPrimitive()) {
                for (int k = 0; k < Array.getLength(x); k++) {
                    if (hasNullField(Array.get(x, k))) {
                        return true;
                    }
                }
            }
            return false;
        }
        if (isScalar(cl)) {
            return false;
        }
        for (Field f : storedFields(cl)) {
            Object v = fieldValue(f, x);
            if (v == null || hasNullField(v)) {
                return true;
            }
        }
        return false;
    }

    /**
     * R1's random Data Objects over All, All0, Inner, Node and Every: values at every edge,
     * null fields, no null array element, depth 1 to 16.
     */
    static final class ObjectGen {
        final Random r;

        ObjectGen(long seed) {
            r = new Random(seed);
        }

        Object top() {
            switch (r.nextInt(6)) {
            case 0:
                return object(Inner.class, 1);
            case 1:
                return chain(1 + r.nextInt(16));
            case 2:
                return object(All0.class, 1);
            case 3:
                return object(Every.class, 1);
            default:
                return object(All.class, 1);
            }
        }

        /** A new 'cl' at 'level', each field random or null. */
        Object object(Class<?> cl, int level) {
            Object x = newInstance(cl);
            for (Field f : storedFields(cl)) {
                Class<?> t = f.getType();
                if (!t.isPrimitive()) {
                    int p = isDataObjectClass(t) ? (t == Node.class ? 5 : 2) : 8;
                    if (r.nextInt(p) == 0) {
                        setField(f, x, null);
                        continue;
                    }
                }
                setField(f, x, value(t, level + 1));
            }
            return x;
        }

        /**
         * A value of the type 't'; one that is an array or an object would be at 'level', so
         * it is null if that is above 16.
         */
        Object value(Class<?> t, int level) {
            if (t == boolean.class || t == Boolean.class) {
                return r.nextBoolean();
            } else if (t == byte.class || t == Byte.class) {
                return (byte) integer(Byte.MIN_VALUE, Byte.MAX_VALUE);
            } else if (t == short.class || t == Short.class) {
                return (short) integer(Short.MIN_VALUE, Short.MAX_VALUE);
            } else if (t == char.class || t == Character.class) {
                return r.nextInt(5) == 0 ? (char) (0xd800 + r.nextInt(0x800))
                        : (char) integer(0, 0xffff);
            } else if (t == int.class || t == Integer.class) {
                return (int) integer(Integer.MIN_VALUE, Integer.MAX_VALUE);
            } else if (t == long.class || t == Long.class) {
                return integer(Long.MIN_VALUE, Long.MAX_VALUE);
            } else if (t == float.class || t == Float.class) {
                return float32();
            } else if (t == double.class || t == Double.class) {
                return float64();
            } else if (t == String.class) {
                return string(r);
            } else if (t == byte[].class) {
                return bytes();
            }
            if (level > 16) {
                return null;
            }
            if (t.isArray()) {
                Class<?> e = t.getComponentType();
                int n = r.nextInt(4) == 0 ? 0 : 1 + r.nextInt(3);
                if (isContainer(e) && level + 1 > 16) {
                    n = 0;
                }
                Object a = Array.newInstance(e, n);
                for (int k = 0; k < n; k++) {
                    Array.set(a, k, value(e, level + 1));
                }
                return a;
            }
            return object(t, level);
        }

        long integer(long min, long max) {
            switch (r.nextInt(8)) {
            case 0:
                return min;
            case 1:
                return max;
            case 2:
                return 0;
            case 3:
                return Math.max(min, -1);
            case 4:
                return 1;
            default:
                if (min == Long.MIN_VALUE) {
                    return r.nextLong();
                }
                return min + Math.floorMod(r.nextLong(), max - min + 1);
            }
        }

        float float32() {
            switch (r.nextInt(14)) {
            case 0:
                return Float.NaN;
            case 1:
                return -0.0f;
            case 2:
                return 0.0f;
            case 3:
                return Float.POSITIVE_INFINITY;
            case 4:
                return Float.NEGATIVE_INFINITY;
            case 5:
                return Float.MIN_VALUE;
            case 6:
                return Float.MAX_VALUE;
            case 7:
                return -Float.MAX_VALUE;
            case 8:
                return Float.intBitsToFloat(0x7fc00001);      // a NaN with a payload
            default:
                return Float.intBitsToFloat(r.nextInt());
            }
        }

        double float64() {
            switch (r.nextInt(14)) {
            case 0:
                return Double.NaN;
            case 1:
                return -0.0;
            case 2:
                return 0.0;
            case 3:
                return Double.POSITIVE_INFINITY;
            case 4:
                return Double.NEGATIVE_INFINITY;
            case 5:
                return Double.MIN_VALUE;
            case 6:
                return Double.MAX_VALUE;
            case 7:
                return -Double.MAX_VALUE;
            case 8:
                return Double.longBitsToDouble(0x7ff0000000000001L);
            default:
                return Double.longBitsToDouble(r.nextLong());
            }
        }

        byte[] bytes() {
            byte[] b = new byte[r.nextInt(4) == 0 ? 0 : r.nextInt(6)];
            r.nextBytes(b);
            return b;
        }
    }

    /**
     * A random well-formed string: U+0000 to U+10FFFF, surrogate pairs, and the edges; one in
     * four empty.
     */
    static String string(Random r) {
        int n = r.nextInt(4) == 0 ? 0 : 1 + r.nextInt(7);
        StringBuilder b = new StringBuilder();
        int[] edges = {0, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xe000, 0xfffd, 0xffff, 0x10000,
                0x10ffff};
        for (int k = 0; k < n; k++) {
            int cp;
            switch (r.nextInt(5)) {
            case 0:
                cp = r.nextInt(0x80);
                break;
            case 1:
                cp = edges[r.nextInt(edges.length)];
                break;
            case 2:
                cp = 0x10000 + r.nextInt(0x100000);
                break;
            default:
                do {
                    cp = r.nextInt(0x10000);
                } while (cp >= 0xd800 && cp <= 0xdfff);
            }
            b.appendCodePoint(cp);
        }
        return b.toString();
    }

    // ======== R2 and R3: the get against a reference (020-09, section 8.5) ========

    /**
     * R2 and R3 with the unit group's seed; first, the reference (ref) gives the result of
     * each case of G1 to G108, so that R2 checks the get against the table's rules.
     */
    @Nano
    public static void testTableReference() {
        Check ch = new Check();
        for (Row r : rows()) {
            for (DbValue stored : r.stored) {
                Object m = model(bytesOf(stored));
                for (int g = 0; g < r.fields.length; g++) {
                    for (String name : r.fields[g]) {
                        String id = r.id + ", {" + name + ": " + showModel(m) + "}, the reference";
                        Object want = r.want[g];
                        ch.run(id, () -> {
                            Class<?> t = All.class.getField(name).getType();
                            ch.eq(id, want(t, want), ref(m, t));
                        });
                    }
                }
            }
        }
        Database db = memory();
        try {
            r2(ch, db.connection(), UNIT_SEED, UNIT_R2);
        } finally {
            db.close();
        }
        ch.done();
    }

    /**
     * R2 and R3: 'count' random stored objects from 'seed', read into All and All0: no
     * exception; each matching field of All equals the reference's value (ref, section 5's
     * rules), each other field All's initial value (R2); each matching field of All0 equals
     * All's (R3). One in sixteen goes through the database (when 'c' is not null).
     */
    static void r2(Check ch, Connection c, long seed, int count) {
        ModelGen g = new ModelGen(seed);
        All init = new All();
        for (int k = 0; k < count; k++) {
            Map<String, Object> m = g.top();
            String id = "seed " + seed + ", object " + k;
            boolean viaDb = c != null && k % 16 == 0;
            ch.run("R2, " + id, () -> {
                DbObject stored = (DbObject) toDb(m);
                All x;
                if (viaDb) {
                    String key = ch.key();
                    c.put(key, stored);
                    x = c.get(key, All.class);
                } else {
                    x = stored.toJavaObject(All.class);
                }
                All0 x0 = stored.toJavaObject(All0.class);
                for (Field f : storedFields(All.class)) {
                    String name = f.getName();
                    Object got = f.get(x);
                    if (m.containsKey(name)) {
                        Object v = m.get(name);
                        ch.eq("R2, " + id + ", " + name + " of " + showModel(v),
                                ref(v, f.getType()), got);
                        ch.eq("R3, " + id + ", " + name + " of " + showModel(v), got,
                                All0.class.getField(name).get(x0));
                    } else {
                        ch.eq("R2, " + id + ", " + name + " absent", f.get(init), got);
                    }
                }
            });
        }
    }

    // The reference of 020-09, section 5, written from the document. A stored value is a
    // model: Long (integer), Double, Boolean, String, byte[] (bytes), List (array) and Map
    // (object). ref(m, t) is what a field of type t holds after a get of m; for an absent
    // field, the get leaves the constructor's value (principle 2), which the callers check.

    /** The value of a field of type 't' after a get of the stored value 'm' (section 5). */
    static Object ref(Object m, Class<?> t) {
        if (t == boolean.class || t == Boolean.class) {
            return refBoolean(m);
        } else if (isIntegerType(t)) {
            return box(t, refInteger(m, t));
        } else if (t == float.class || t == Float.class) {
            return refFloat(m);
        } else if (t == double.class || t == Double.class) {
            return refDouble(m);
        } else if (t == String.class) {
            return refString(m);
        } else if (t == byte[].class) {
            return refBytes(m);
        } else if (t.isArray()) {
            return refArray(m, t.getComponentType());
        }
        return refObject(m, t);
    }

    /** Section 5.4: into boolean. */
    static boolean refBoolean(Object m) {
        if (m instanceof Long) {
            return (Long) m != 0;
        } else if (m instanceof Double) {
            double x = (Double) m;
            return x != 0.0 && !Double.isNaN(x);
        } else if (m instanceof Boolean) {
            return (Boolean) m;
        } else if (m instanceof String) {
            return Boolean.parseBoolean((String) m);
        }
        return false;
    }

    /** Sections 5.4 and 5.5: into an integer type 't', clamped to it. */
    static long refInteger(Object m, Class<?> t) {
        if (m instanceof Long) {
            return clamp((Long) m, t);
        } else if (m instanceof Double) {
            return clamp((long) (double) (Double) m, t);
        } else if (m instanceof Boolean) {
            return (Boolean) m ? 1 : 0;
        } else if (m instanceof String) {
            String text = ((String) m).trim();
            if (text.matches("[+-]?[0-9]+")) {
                BigInteger v = new BigInteger(text);
                long x = v.bitLength() <= 63 ? v.longValue()
                        : v.signum() > 0 ? Long.MAX_VALUE : Long.MIN_VALUE;
                return clamp(x, t);
            }
            try {
                return clamp((long) Double.parseDouble(text), t);
            } catch (NumberFormatException e) {
                return 0;
            }
        }
        return 0;
    }

    /** Sections 5.4 and 5.5: into float. */
    static float refFloat(Object m) {
        if (m instanceof Long) {
            return (float) (long) (Long) m;
        } else if (m instanceof Double) {
            return (float) (double) (Double) m;
        } else if (m instanceof Boolean) {
            return (Boolean) m ? 1.0f : 0.0f;
        } else if (m instanceof String) {
            try {
                return Float.parseFloat((String) m);
            } catch (NumberFormatException e) {
                return 0.0f;
            }
        }
        return 0.0f;
    }

    /** Sections 5.4 and 5.5: into double. */
    static double refDouble(Object m) {
        if (m instanceof Long) {
            return (double) (long) (Long) m;
        } else if (m instanceof Double) {
            return (Double) m;
        } else if (m instanceof Boolean) {
            return (Boolean) m ? 1.0 : 0.0;
        } else if (m instanceof String) {
            try {
                return Double.parseDouble((String) m);
            } catch (NumberFormatException e) {
                return 0.0;
            }
        }
        return 0.0;
    }

    /** Sections 5.4 and 5.6: into String. */
    static String refString(Object m) {
        if (m instanceof Long) {
            return Long.toString((Long) m);
        } else if (m instanceof Double) {
            return Double.toString((Double) m);
        } else if (m instanceof Boolean) {
            return (Boolean) m ? "true" : "false";
        } else if (m instanceof String) {
            return (String) m;
        } else if (m instanceof byte[]) {
            return new String((byte[]) m, StandardCharsets.UTF_8);
        }
        return null;
    }

    /** Sections 5.4, 5.6 and 5.7: into byte[]. */
    static byte[] refBytes(Object m) {
        if (m instanceof String) {
            return ((String) m).getBytes(StandardCharsets.UTF_8);
        } else if (m instanceof byte[]) {
            return ((byte[]) m).clone();
        } else if (m instanceof List) {
            List<?> list = (List<?>) m;
            byte[] b = new byte[list.size()];
            for (int k = 0; k < b.length; k++) {
                b[k] = (byte) refInteger(list.get(k), byte.class);
            }
            return b;
        }
        return null;
    }

    /** Section 5.7: into E[] other than byte[]. */
    static Object refArray(Object m, Class<?> e) {
        if (!(m instanceof List)) {
            return null;
        }
        List<?> list = (List<?>) m;
        Object a = Array.newInstance(e, list.size());
        for (int k = 0; k < list.size(); k++) {
            Array.set(a, k, ref(list.get(k), e));
        }
        return a;
    }

    /** Sections 5.3 and 5.8: into a Data Object class. */
    static Object refObject(Object m, Class<?> t) {
        if (!(m instanceof Map)) {
            return null;
        }
        Map<?, ?> map = (Map<?, ?>) m;
        Object x = newInstance(t);
        for (Field f : storedFields(t)) {
            if (map.containsKey(f.getName())) {
                setField(f, x, ref(map.get(f.getName()), f.getType()));
            }
        }
        return x;
    }

    /** 'v' clamped to the integer type 't' (020-09, section 2). */
    static long clamp(long v, Class<?> t) {
        long min;
        long max;
        if (t == byte.class || t == Byte.class) {
            min = Byte.MIN_VALUE;
            max = Byte.MAX_VALUE;
        } else if (t == short.class || t == Short.class) {
            min = Short.MIN_VALUE;
            max = Short.MAX_VALUE;
        } else if (t == char.class || t == Character.class) {
            min = 0;
            max = 0xffff;
        } else if (t == int.class || t == Integer.class) {
            min = Integer.MIN_VALUE;
            max = Integer.MAX_VALUE;
        } else {
            return v;
        }
        return Math.max(min, Math.min(max, v));
    }

    static boolean isIntegerType(Class<?> t) {
        return t == byte.class || t == Byte.class || t == short.class || t == Short.class
                || t == char.class || t == Character.class || t == int.class
                || t == Integer.class || t == long.class || t == Long.class;
    }

    /** The integer 'v' boxed as the integer type 't', by Java's cast. */
    static Object box(Class<?> t, long v) {
        if (t == byte.class || t == Byte.class) {
            return (byte) v;
        } else if (t == short.class || t == Short.class) {
            return (short) v;
        } else if (t == char.class || t == Character.class) {
            return (char) v;
        } else if (t == int.class || t == Integer.class) {
            return (int) v;
        }
        return v;
    }

    /** A stored value's bytes as a model, by 020-07's encodings (the table's values). */
    static Object model(byte[] b) {
        int[] p = {0};
        Object m = model(b, p);
        if (p[0] != b.length) {
            throw new IllegalStateException("the test: " + hex(b));
        }
        return m;
    }

    private static Object model(byte[] b, int[] p) {
        int t = b[p[0]++] & 0xff;
        if (t >= 0x10 && t <= 0x13) {                   // an integer of 1, 2, 4 or 8 bytes
            int n = 1 << (t - 0x10);
            long v = le(b, p, n);
            return n == 8 ? v : v << (64 - 8 * n) >> (64 - 8 * n);
        } else if (t >= 0x14 && t <= 0x16 || t >= 0x18 && t <= 0x1a) {   // a string, bytes
            int n = (int) le(b, p, 1 << (t & 3));
            byte[] x = Arrays.copyOfRange(b, p[0], p[0] + n);
            p[0] += n;
            return t <= 0x16 ? new String(x, StandardCharsets.UTF_8) : x;
        } else if (t == 0x42) {
            List<Object> list = new ArrayList<Object>();
            while ((b[p[0]] & 0xff) != 0x43) {
                list.add(model(b, p));
            }
            p[0]++;
            return list;
        } else if (t == 0x44 || t == 0x45) {
            return t == 0x44;
        } else if (t == 0x46) {
            return Double.longBitsToDouble(le(b, p, 8));
        } else if (t >= 0x48 && t <= 0x4a) {            // an object: count, ends, fields
            int w = t == 0x48 ? 1 : t == 0x49 ? 2 : 4;
            int count = (int) le(b, p, w);
            p[0] += count * w;
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            for (int k = 0; k < count; k++) {
                int n = b[p[0]++] & 0xff;
                String name = new String(b, p[0], n, StandardCharsets.UTF_8);
                p[0] += n;
                m.put(name, model(b, p));
            }
            return m;
        }
        throw new IllegalStateException("the test: the type byte " + t);
    }

    /** 'n' bytes at p[0], little-endian, unsigned; p[0] moves past them. */
    private static long le(byte[] b, int[] p, int n) {
        long v = 0;
        for (int k = n - 1; k >= 0; k--) {
            v = v << 8 | (b[p[0] + k] & 0xff);
        }
        p[0] += n;
        return v;
    }

    /** A model as a stored value. */
    static DbValue toDb(Object m) {
        if (m instanceof Long) {
            return new DbLong((Long) m);
        } else if (m instanceof Double) {
            return new DbDouble((Double) m);
        } else if (m instanceof Boolean) {
            return new DbBoolean((Boolean) m);
        } else if (m instanceof String) {
            return new DbString((String) m);
        } else if (m instanceof byte[]) {
            return new DbByteArray((byte[]) m);
        } else if (m instanceof List) {
            DbArray.Builder b = new DbArray.Builder();
            for (Object e : (List<?>) m) {
                b.add(toDb(e));
            }
            return b.build();
        }
        DbObject.Builder b = new DbObject.Builder();
        for (Map.Entry<?, ?> e : ((Map<?, ?>) m).entrySet()) {
            b.addDbValue((String) e.getKey(), toDb(e.getValue()));
        }
        return b.build();
    }

    /** The texts of 020-09, section 5.5, and more. */
    private static final String[] TEXTS = {"12", "+12", "-12", " 12 ", "\t12\n", "1.5", "1.5f",
        "-1.9", "1e3", "0x1p3", "abc", "", "0x10", "1_000", "١٢",
        "99999999999999999999", "-99999999999999999999", "9007199254740993",
        " 9007199254740993 ", "NaN", "Infinity", "-Infinity", " 1.5 ", "1e400", "-1e400",
        "1.00000017881393432617187499", "true", "TRUE", " true", "yes", "1", "0", "65", "A",
        "-5", "70000", "é", "-0", "+-1", "1.", ".5", "1e-400", "-0.0", "0x1.8p1", "1d",
        "2147483648", "-2147483649", "32768", "-32769", "65536", "128", "-129", "+NaN",
        " 12", (char) 0 + "12" + (char) 0, "9223372036854775807", "9223372036854775808",
        "-9223372036854775808", "-9223372036854775809", "1e19", "0.5", "40000.5", "300.7",
        "+", "-", " ", "false", "False"};

    /** Bytes, well-formed and ill-formed UTF-8 (020-09, section 5.6). */
    private static final int[][] BYTES = {{}, {0x61, 0x62}, {0x61, 0xff, 0x62}, {0xe2, 0x82},
        {0xed, 0xa0, 0x80}, {0xc0, 0xaf}, {0xf4, 0x90, 0x80, 0x80}, {0xc3, 0xa9}, {0x80},
        {0xf0, 0x9f, 0x98, 0x80}, {0x31, 0x32}, {0x00}, {0xfe, 0xff}};

    /** The integers at the edges of the integer types. */
    private static final long[] INTEGERS = {0, 1, -1, 5, 65, 127, 128, -128, -129, 255, 256,
        32767, 32768, -32768, -32769, 65535, 65536, Integer.MAX_VALUE, Integer.MAX_VALUE + 1L,
        Integer.MIN_VALUE, Integer.MIN_VALUE - 1L, Long.MAX_VALUE, Long.MIN_VALUE,
        9007199254740993L, 3000000000L, -3000000000L, 0xd800, 0xdfff};

    /** The doubles at the edges. */
    private static final double[] DOUBLES = {Double.NaN, 0.0, -0.0, Double.POSITIVE_INFINITY,
        Double.NEGATIVE_INFINITY, Double.MIN_VALUE, Double.MAX_VALUE, -Double.MAX_VALUE, 0.5,
        1.5, 1.9, -1.9, -0.5, 0.1, 9.223372036854775807E18, -9.223372036854775808E18, 1e19,
        -1e19, 1e10, 40000.5, -40000.5, 300.7, -5.5, 65535.9, 65536.0, 1e300, -1e300,
        Float.MAX_VALUE, 3.5e38, 1.0e-46, Double.longBitsToDouble(0x7ff0000000000001L),
        127.9, -128.9, 2147483647.5, -2147483648.5};

    /** The names of All's stored fields. */
    private static final String[] ALL_NAMES = {"z", "wz", "b", "wb", "s", "ws", "c", "wc",
        "i", "wi", "l", "wl", "f", "wf", "d", "wd", "str", "bytes", "ints", "wints", "strs",
        "ints2", "bytes2", "inner", "inners"};

    /** Other names: a stored field the class lacks. */
    private static final String[] OTHER_NAMES = {"x", "p", "array", "key", "v", "Z", "zz",
        "é", "inner ", "t"};

    /** The names of nested objects: Inner's and others. */
    private static final String[] INNER_NAMES = {"v", "w", "v", "w", "x", "p", "array", "z"};

    /** R2's random stored objects, as models (ref). */
    static final class ModelGen {
        final Random r;
        int maxLevel;

        ModelGen(long seed) {
            r = new Random(seed);
        }

        /** A top object: names of All's fields and others, values of every kind. */
        Map<String, Object> top() {
            maxLevel = r.nextInt(8) == 0 ? 16 : 2 + r.nextInt(4);
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            int n = r.nextInt(9);
            for (int k = 0; k < n; k++) {
                if (r.nextInt(5) == 0) {
                    m.put(OTHER_NAMES[r.nextInt(OTHER_NAMES.length)], value(2));
                } else {
                    String name = ALL_NAMES[r.nextInt(ALL_NAMES.length)];
                    m.put(name, r.nextInt(5) < 2 ? natural(name, 2) : value(2));
                }
            }
            return m;
        }

        /** A value of the kind of All's field 'name', at 'level' if a container. */
        Object natural(String name, int level) {
            switch (name) {
            case "z": case "wz":
                return r.nextBoolean();
            case "f": case "wf": case "d": case "wd":
                return float64();
            case "str":
                return text();
            case "bytes":
                return r.nextBoolean() ? bytes() : array(level);
            case "inner":
                return object(level);
            case "ints": case "wints": case "strs": case "ints2": case "bytes2": case "inners":
                return array(level);
            default:
                return r.nextInt(4) == 0 ? float64() : integer();
            }
        }

        /** A value of any kind; an array or an object at 'level', only up to maxLevel. */
        Object value(int level) {
            switch (r.nextInt(level <= maxLevel ? 7 : 5)) {
            case 0:
                return integer();
            case 1:
                return float64();
            case 2:
                return r.nextBoolean();
            case 3:
                return text();
            case 4:
                return bytes();
            case 5:
                return array(level);
            default:
                return object(level);
            }
        }

        List<Object> array(int level) {
            List<Object> list = new ArrayList<Object>();
            int n = r.nextInt(5);
            for (int k = 0; k < n; k++) {
                list.add(value(level + 1));
            }
            return list;
        }

        Map<String, Object> object(int level) {
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            int n = r.nextInt(4);
            for (int k = 0; k < n; k++) {
                m.put(INNER_NAMES[r.nextInt(INNER_NAMES.length)], value(level + 1));
            }
            return m;
        }

        Long integer() {
            switch (r.nextInt(4)) {
            case 0:
            case 1:
                return INTEGERS[r.nextInt(INTEGERS.length)];
            case 2:
                return r.nextLong();
            default:
                return (long) r.nextInt(2001) - 1000;
            }
        }

        Double float64() {
            switch (r.nextInt(4)) {
            case 0:
            case 1:
                return DOUBLES[r.nextInt(DOUBLES.length)];
            case 2:
                return Double.longBitsToDouble(r.nextLong());
            default:
                return r.nextGaussian() * Math.pow(10, r.nextInt(25) - 4);
            }
        }

        String text() {
            switch (r.nextInt(4)) {
            case 0:
            case 1:
                return TEXTS[r.nextInt(TEXTS.length)];
            case 2:
                StringBuilder b = new StringBuilder();
                if (r.nextInt(3) == 0) {
                    b.append(r.nextBoolean() ? '+' : '-');
                }
                int n = 1 + r.nextInt(r.nextBoolean() ? 6 : 24);
                for (int k = 0; k < n; k++) {
                    b.append((char) ('0' + r.nextInt(10)));
                }
                if (r.nextInt(4) == 0) {
                    String[] tails = {".5", "e2", "e-3", ".25e1", "f", ".", "e400"};
                    b.append(tails[r.nextInt(tails.length)]);
                }
                return r.nextInt(4) == 0 ? " " + b + "\t" : b.toString();
            default:
                return string(r);
            }
        }

        byte[] bytes() {
            if (r.nextBoolean()) {
                int[] b = BYTES[r.nextInt(BYTES.length)];
                byte[] x = new byte[b.length];
                for (int k = 0; k < b.length; k++) {
                    x[k] = (byte) b[k];
                }
                return x;
            }
            if (r.nextBoolean()) {
                return string(r).getBytes(StandardCharsets.UTF_8);
            }
            byte[] x = new byte[r.nextInt(6)];
            r.nextBytes(x);
            return x;
        }
    }

    // ======== The night ========

    /**
     * The night's run of R1, R2 and R3: NIGHT_SEEDS seeds, new each day (the day's number
     * times 1000), NIGHT_OBJECTS random objects each.
     */
    @Nano("night")
    public static void testPropertiesNight(TestEnvironment env) {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        env.out().println("DataObjectsTester: seeds " + base + " to " + (base + NIGHT_SEEDS - 1)
                + ", " + NIGHT_OBJECTS + " objects each for R1 and for R2 and R3");
        Check ch = new Check();
        Database db = memory();
        try {
            for (long seed = base; seed < base + NIGHT_SEEDS; seed++) {
                r1(ch, db.connection(), seed, NIGHT_OBJECTS);
                r2(ch, db.connection(), seed, NIGHT_OBJECTS);
            }
        } finally {
            db.close();
        }
        env.out().println("DataObjectsTester: " + ch.count + " checks");
        ch.done();
    }

    /**
     * Usage: DataObjectsTester [SEED [COUNT [DB]]]: R1, R2 and R3 on COUNT random objects
     * from SEED (default: the time, and NIGHT_OBJECTS), by toDbObject() and toJavaObject();
     * with DB 1, as the night's run, one in ten of R1's and one in sixteen of R2's through a
     * database in memory, a put and a get (bergdb 020-17).
     */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int count = args.length > 1 ? Integer.parseInt(args[1]) : NIGHT_OBJECTS;
        boolean withDb = args.length > 2 && args[2].equals("1");
        long t0 = System.nanoTime();
        Check ch = new Check();
        Database db = withDb ? memory() : null;
        try {
            r1(ch, db == null ? null : db.connection(), seed, count);
            r2(ch, db == null ? null : db.connection(), seed, count);
        } finally {
            if (db != null) {
                db.close();
            }
        }
        System.out.println("DataObjectsTester: seed " + seed + ", " + ch.count + " checks, "
                + ch.failed + " failed; " + (System.nanoTime() - t0) / 1000000 + " ms");
        ch.done();
    }

    // ======== Helpers ========

    private static Database memory() {
        return Factory.database().memory().start();
    }

    interface Body {
        void run() throws Exception;
    }

    /**
     * The checks of a test: each failure is kept with its case's ID, and done() fails the
     * test with them all, so that one run shows every case that fails.
     */
    static final class Check {
        final ArrayList<String> failures = new ArrayList<String>();     // the first 1000
        int count;
        int failed;
        private int keys;

        /** A new key of the test's database. */
        String key() {
            return "/t/" + keys++;
        }

        void fail(String id, String message) {
            failed++;
            if (failures.size() < 1000) {
                String m = id + ": " + message;
                failures.add(m.length() > 600 ? m.substring(0, 600) + "..." : m);
            }
        }

        void isTrue(String id, boolean b, String message) {
            count++;
            if (!b) {
                fail(id, message);
            }
        }

        /** 'got' equals 'want' by eq (020-09, section 8.5). */
        void eq(String id, Object want, Object got) {
            count++;
            String d = diff("", want, got);
            if (d != null) {
                fail(id, d);
            }
        }

        /** Runs a case; an exception from it is the case's failure. */
        void run(String id, Body body) {
            try {
                body.run();
            } catch (Throwable e) {
                fail(id, "threw " + e);
            }
        }

        /**
         * An IllegalArgumentException from 'body', its message naming the class 'named'
         * (unless null) and each of 'mentions'.
         */
        void argRefused(String id, Body body, Class<?> named, String... mentions) {
            count++;
            try {
                body.run();
            } catch (IllegalArgumentException e) {
                String m = String.valueOf(e.getMessage());
                if (named != null && !mentionsClass(m, named)) {
                    fail(id, "the message does not name " + named.getName() + ": " + m);
                }
                for (String w : mentions) {
                    if (!mentions(m, w)) {
                        fail(id, "the message does not name '" + w + "': " + m);
                    }
                }
                return;
            } catch (Throwable e) {
                fail(id, "not an IllegalArgumentException: " + e);
                return;
            }
            fail(id, "taken, not refused");
        }

        /** An ObjectCreationException from 'body', with a 'cause' (unless null) as its cause. */
        void creationRefused(String id, Body body, Class<? extends Throwable> cause) {
            count++;
            try {
                body.run();
            } catch (ObjectCreationException e) {
                if (cause != null && !cause.isInstance(e.getCause())) {
                    fail(id, "its cause is " + e.getCause() + ", not a " + cause.getName());
                }
                return;
            } catch (Throwable e) {
                fail(id, "not an ObjectCreationException: " + e);
                return;
            }
            fail(id, "no exception");
        }

        /** Fails the test if a check failed, showing the first 60 (the property show). */
        void done() {
            if (failed == 0) {
                return;
            }
            StringBuilder b = new StringBuilder(failed + " failed (of " + count + " checks):");
            int shown = Math.min(failures.size(), Integer.getInteger("DataObjectsTester.show",
                    60));
            for (int k = 0; k < shown; k++) {
                b.append("\n    ").append(failures.get(k));
            }
            if (shown < failed) {
                b.append("\n    ... and " + (failed - shown) + " more");
            }
            throw new AssertionError(b.toString());
        }
    }

    /** True if the message 'm' names the class 'c': its name, or its simple name as a word. */
    static boolean mentionsClass(String m, Class<?> c) {
        if (m.contains(c.getName()) || m.contains(c.getTypeName())) {
            return true;
        }
        String simple = c.getSimpleName();
        return !simple.isEmpty() && word(m, simple);
    }

    /** True if 'm' names 'w': as a word if 'w' is a name, else as it is ("strs[1]"). */
    static boolean mentions(String m, String w) {
        for (int k = 0; k < w.length(); k++) {
            if (!isWordChar(w.charAt(k))) {
                return m.contains(w);
            }
        }
        return word(m, w);
    }

    private static boolean word(String m, String w) {
        for (int p = m.indexOf(w); p >= 0; p = m.indexOf(w, p + 1)) {
            int end = p + w.length();
            if ((p == 0 || !isWordChar(m.charAt(p - 1)))
                    && (end == m.length() || !isWordChar(m.charAt(end)))) {
                return true;
            }
        }
        return false;
    }

    private static boolean isWordChar(char ch) {
        return Character.isLetterOrDigit(ch) || ch == '_';
    }

    /** The test's own list of a class's stored fields (020-09, V3), in name order. */
    private static final ClassValue<Field[]> FIELDS = new ClassValue<Field[]>() {
        protected Field[] computeValue(Class<?> c) {
            ArrayList<Field> list = new ArrayList<Field>();
            for (Class<?> k = c; k != null && k != Object.class; k = k.getSuperclass()) {
                for (Field f : k.getDeclaredFields()) {
                    int m = f.getModifiers();
                    if (Modifier.isPublic(m) && !Modifier.isStatic(m)
                            && !Modifier.isTransient(m) && !f.isSynthetic()) {
                        list.add(f);
                    }
                }
            }
            list.sort((x, y) -> Arrays.compareUnsigned(
                    x.getName().getBytes(StandardCharsets.UTF_8),
                    y.getName().getBytes(StandardCharsets.UTF_8)));
            return list.toArray(new Field[0]);
        }
    };

    static Field[] storedFields(Class<?> c) {
        return FIELDS.get(c);
    }

    static Object fieldValue(Field f, Object x) {
        try {
            return f.get(x);
        } catch (IllegalAccessException e) {
            throw new IllegalStateException(e);
        }
    }

    static void setField(Field f, Object x, Object value) {
        try {
            f.set(x, value);
        } catch (IllegalAccessException e) {
            throw new IllegalStateException(e);
        }
    }

    static Object newInstance(Class<?> c) {
        try {
            return c.getConstructor().newInstance();
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException(e);
        }
    }

    /** The scalars of Java's binding: the wrappers and String. */
    static boolean isScalar(Class<?> c) {
        return c == Boolean.class || c == Byte.class || c == Short.class || c == Character.class
                || c == Integer.class || c == Long.class || c == Float.class
                || c == Double.class || c == String.class;
    }

    static boolean isDataObjectClass(Class<?> t) {
        return !t.isPrimitive() && !t.isArray() && !isScalar(t);
    }

    /** An array other than byte[], or a Data Object class: a level of its own. */
    static boolean isContainer(Class<?> t) {
        return (t.isArray() && t != byte[].class) || isDataObjectClass(t);
    }

    static Class<?> boxed(Class<?> t) {
        if (!t.isPrimitive()) {
            return t;
        }
        return Array.get(Array.newInstance(t, 1), 0).getClass();
    }

    /**
     * The first difference of 'got' from 'want' by eq (020-09, section 8.5), or null: boxed
     * equals for primitives and wrappers (NaN equals NaN, -0.0 is not 0.0), String.equals,
     * Arrays.equals for byte[], arrays of one class and length with eq elements, Data Objects
     * of one class with eq stored fields.
     */
    static String diff(String path, Object want, Object got) {
        if (want == got) {
            return null;
        }
        if (want == null || got == null || want.getClass() != got.getClass()) {
            return at(path, want, got);
        }
        Class<?> c = want.getClass();
        if (c == byte[].class) {
            return Arrays.equals((byte[]) want, (byte[]) got) ? null : at(path, want, got);
        }
        if (c.isArray()) {
            int n = Array.getLength(want);
            if (n != Array.getLength(got)) {
                return at(path, want, got);
            }
            for (int k = 0; k < n; k++) {
                String d = diff(path + "[" + k + "]", Array.get(want, k), Array.get(got, k));
                if (d != null) {
                    return d;
                }
            }
            return null;
        }
        if (isScalar(c) || storedFields(c).length == 0 && !c.getName().startsWith("bergdb.")) {
            return want.equals(got) ? null : at(path, want, got);
        }
        for (Field f : storedFields(c)) {
            String p = path.isEmpty() ? f.getName() : path + "." + f.getName();
            String d = diff(p, fieldValue(f, want), fieldValue(f, got));
            if (d != null) {
                return d;
            }
        }
        return null;
    }

    private static String at(String path, Object want, Object got) {
        return (path.isEmpty() ? "" : "at " + path + ": ") + "want " + show(want) + ", got "
                + show(got);
    }

    static boolean eq(Object want, Object got) {
        return diff("", want, got) == null;
    }

    /** A value for a message, its type shown: 5L, 1.5f, 'c', "s", byte[]{01 02}, [...]. */
    static String show(Object x) {
        String s = show1(x);
        return s.length() > 200 ? s.substring(0, 200) + "..." : s;
    }

    private static String show1(Object x) {
        if (x == null) {
            return "null";
        } else if (x instanceof String) {
            return "\"" + escape((String) x) + "\"";
        } else if (x instanceof Character) {
            return "'" + escape(x.toString()) + "'";
        } else if (x instanceof Long) {
            return x + "L";
        } else if (x instanceof Float) {
            return x + "f";
        } else if (x instanceof Double) {
            double v = (Double) x;
            return v == 0 || Double.isNaN(v) ? x + " (" + Long.toHexString(
                    Double.doubleToRawLongBits(v)) + ")" : x.toString();
        } else if (x instanceof Byte) {
            return "(byte) " + x;
        } else if (x instanceof Short) {
            return "(short) " + x;
        } else if (x instanceof byte[]) {
            return "byte[]{" + hex((byte[]) x) + "}";
        } else if (x.getClass().isArray()) {
            StringBuilder b = new StringBuilder(x.getClass().getComponentType().getSimpleName()
                    + "[]{");
            for (int k = 0; k < Array.getLength(x); k++) {
                b.append(k == 0 ? "" : ", ").append(show1(Array.get(x, k)));
            }
            return b.append("}").toString();
        } else if (isScalar(x.getClass()) || !x.getClass().getName().startsWith("bergdb.")) {
            return x.toString();
        }
        StringBuilder b = new StringBuilder(x.getClass().getSimpleName() + "{");
        Field[] fields = storedFields(x.getClass());
        for (int k = 0; k < fields.length; k++) {
            b.append(k == 0 ? "" : ", ").append(fields[k].getName()).append(": ")
                    .append(show1(fieldValue(fields[k], x)));
        }
        return b.append("}").toString();
    }

    /** A model for a message (ref). */
    static String showModel(Object m) {
        String s = showModel1(m);
        return s.length() > 200 ? s.substring(0, 200) + "..." : s;
    }

    private static String showModel1(Object m) {
        if (m instanceof String) {
            return "\"" + escape((String) m) + "\"";
        } else if (m instanceof byte[]) {
            return "b(" + hex((byte[]) m) + ")";
        } else if (m instanceof List) {
            StringBuilder b = new StringBuilder("[");
            for (Object e : (List<?>) m) {
                b.append(b.length() == 1 ? "" : ", ").append(showModel1(e));
            }
            return b.append("]").toString();
        } else if (m instanceof Map) {
            StringBuilder b = new StringBuilder("{");
            for (Map.Entry<?, ?> e : ((Map<?, ?>) m).entrySet()) {
                b.append(b.length() == 1 ? "" : ", ").append(escape((String) e.getKey()))
                        .append(": ").append(showModel1(e.getValue()));
            }
            return b.append("}").toString();
        }
        return String.valueOf(m);
    }

    /** Java's escapes for the chars outside printable ASCII. */
    static String escape(String s) {
        StringBuilder b = new StringBuilder();
        for (int k = 0; k < s.length(); k++) {
            char ch = s.charAt(k);
            if (ch >= 0x20 && ch < 0x7f && ch != '"' && ch != '\\') {
                b.append(ch);
            } else {
                b.append(String.format("\\u%04x", (int) ch));
            }
        }
        return b.toString();
    }

    static String hex(byte[] b) {
        StringBuilder s = new StringBuilder();
        for (int k = 0; k < b.length; k++) {
            s.append(k == 0 ? "" : " ").append(String.format("%02x", b[k] & 0xff));
        }
        return s.toString();
    }

    /** The bytes of a stored value. */
    static byte[] bytesOf(DbValue v) {
        byte[] b = new byte[v.getByteSize()];
        v.write(b, 0);
        return b;
    }

    // ======== The review of step 8 (2026-11-09) ========

    /** A Data Object class that extends Number: a class of the platform below it (V5). */
    public static class Money extends Number {
        private static final long serialVersionUID = 1L;
        public long cents;
        public Money() {}
        public int intValue() {
            return (int) cents;
        }
        public long longValue() {
            return cents;
        }
        public float floatValue() {
            return cents;
        }
        public double doubleValue() {
            return cents;
        }
    }

    public static class HoldsMoney {
        public Money m;
        public HoldsMoney() {}
    }

    public static class HoldsMoneyArray {
        public Money[] ms;
        public HoldsMoneyArray() {}
    }

    /** Extends a platform class whose instance fields are transient (V5). */
    public static class Stamp extends java.util.Date {
        private static final long serialVersionUID = 1L;
        public Stamp() {}
    }

    /** A bounded type variable, erased to Inner (V9). */
    public static class BoundedBox<T extends Inner> {
        public T value;
        public BoundedBox() {}
    }

    public static class BoundedArrayBox<T extends Inner> {
        public T[] values;
        public BoundedArrayBox() {}
    }

    /** Its static initializer throws: the first use, and every later one, fail. */
    public static class BadInit {
        static {
            if (Boolean.parseBoolean("true")) {
                throw new IllegalStateException("BadInit");
            }
        }
        public int v;
        public BadInit() {}
    }

    /** Its static initializer throws an Error, not an exception; first used by a get. */
    public static class BadInitError {
        static {
            if (Boolean.parseBoolean("true")) {
                throw new AssertionError("BadInitError");
            }
        }
        public int v;
        public BadInitError() {}
    }

    /** As BadInitError, first used by a get in rw(). */
    public static class BadInitErrorRw {
        static {
            if (Boolean.parseBoolean("true")) {
                throw new AssertionError("BadInitErrorRw");
            }
        }
        public int v;
        public BadInitErrorRw() {}
    }

    /**
     * The review of step 8 (020-08): (1, 3) a class that extends a class of the Java
     * platform, such as Number or Date, is not a Data Object (V5 for every superclass below
     * Object): a Money extends Number was stored as its longValue() and read back as null, a
     * Stamp extends Date as {} and read back as the time of the read; (4) a bounded type
     * variable is not on the list (V9); (5) void.class is no class to get; (2) a class whose
     * static initializer threw is an ObjectCreationException at every get, also in rw(),
     * and the database goes on (a NoClassDefFoundError escaped at the second); (6) a primary
     * scan checks its class first, also over an empty directory (020-09, section 3.3).
     */
    @Nano
    public static void testReviewOfStep8() {
        Check ch = new Check();
        Database db = memory();
        try {
            final Connection c = db.connection();
            HoldsMoney hm = new HoldsMoney();
            hm.m = new Money();
            hm.m.cents = 5;
            refusedType(ch, c, "Money in a field", HoldsMoney.class, hm, "m");
            HoldsMoneyArray hms = new HoldsMoneyArray();
            hms.ms = new Money[] {new Money()};
            refusedType(ch, c, "Money[] in a field", HoldsMoneyArray.class, hms, "ms");
            refusedClass(ch, c, "Money", Money.class, new Money(), "Number");
            refusedClass(ch, c, "Stamp", Stamp.class, new Stamp(), "Date");

            BoundedBox<Inner> bb = new BoundedBox<Inner>();
            bb.value = new Inner();
            refusedClass(ch, c, "BoundedBox", BoundedBox.class, bb, "value");
            BoundedArrayBox<Inner> bab = new BoundedArrayBox<Inner>();
            refusedClass(ch, c, "BoundedArrayBox", BoundedArrayBox.class, bab, "values");

            ch.creationRefused("void.class", () -> o("p", o()).toJavaObject(void.class), null);
            ch.creationRefused("void.class at a key", () -> c.get("/void", void.class), null);

            c.put("/bad-init", o("v", l(1)));
            for (int k = 0; k < 3; k++) {
                ch.creationRefused("BadInit, get " + k, () -> c.get("/bad-init", BadInit.class),
                        null);
                ch.creationRefused("BadInit, get in rw() " + k, () -> c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        env.get("/bad-init", BadInit.class);
                    }
                }), null);
            }
            c.put("/later", "x");       // the database goes on
            ch.eq("BadInit, the database goes on", "x", c.get("/later", String.class));

            // An Error of a static initializer, which the JVM throws as it is (bergdb 020-13,
            // bug 2): an ObjectCreationException at the first use too, also in rw(), where
            // the database goes on. Before, the AssertionError passed, and failed the
            // database in rw().
            for (int k = 0; k < 3; k++) {
                ch.creationRefused("BadInitError, get " + k,
                        () -> c.get("/bad-init", BadInitError.class), null);
                ch.creationRefused("BadInitErrorRw, get in rw() " + k, () -> c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        env.get("/bad-init", BadInitErrorRw.class);
                    }
                }), null);
            }
            c.put("/later", "y");
            ch.eq("BadInitError, the database goes on", "y", c.get("/later", String.class));

            ch.creationRefused("a primary scan of an empty directory as Bad",
                    () -> c.usePrimary(Bad.class).dir("/empty/").objects().iterator()
                    .hasNext(), null);
            ch.creationRefused("a primary scan's builder as Bad",
                    () -> c.usePrimary(Bad.class), null);
        } finally {
            db.close();
        }
        ch.done();
    }

    /**
     * Its static initializer throws an Error, which Java passes as it is: it wraps only an
     * Exception in an ExceptionInInitializerError (JLS 12.4.2).
     */
    public static class ErrorInit {
        static {
            if (Boolean.parseBoolean("true")) {
                throw new AssertionError("ErrorInit");
            }
        }
        public int v;
        public ErrorInit() {}
    }

    /** As ErrorInit, reached through a field of HoldsErrorInit. */
    public static class ErrorInitInner {
        static {
            if (Boolean.parseBoolean("true")) {
                throw new AssertionError("ErrorInitInner");
            }
        }
        public int v;
        public ErrorInitInner() {}
    }

    public static class HoldsErrorInit {
        public ErrorInitInner inner;
        public HoldsErrorInit() {}
    }

    /**
     * The Codex review's X2 (bergdb 020-14): a class whose static initializer throws an Error,
     * not an Exception, is an ObjectCreationException at every get, at the top and nested,
     * also in rw(), and the database goes on (020-09, section 5.2). Until 2026-11-09 the
     * Error of the first use escaped the get, and in rw() failed the database.
     */
    @Nano
    public static void testInitializerError() {
        Check ch = new Check();
        Database db = memory();
        try {
            final Connection c = db.connection();
            c.put("/error-init", o("v", l(1)));
            c.put("/holds-error-init", o("inner", o("v", l(1))));
            for (int k = 0; k < 3; k++) {
                ch.creationRefused("ErrorInit, get in rw() " + k, () -> c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        env.get("/error-init", ErrorInit.class);
                    }
                }), null);
                ch.creationRefused("ErrorInit, get " + k,
                        () -> c.get("/error-init", ErrorInit.class), null);
                ch.creationRefused("HoldsErrorInit, get in rw() " + k, () -> c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        env.get("/holds-error-init", HoldsErrorInit.class);
                    }
                }), null);
                ch.creationRefused("HoldsErrorInit, toJavaObject " + k,
                        () -> o("inner", o()).toJavaObject(HoldsErrorInit.class), null);
            }
            ch.run("the database goes on", () -> {
                c.put("/later", "x");
                ch.eq("the database goes on", "x", c.get("/later", String.class));
            });
        } finally {
            db.close();
        }
        ch.done();
    }

    /** A generic Data Object class: valid, whatever its type argument. */
    public static class GenericBox<T> {
        public int n;
        public GenericBox() {}
    }

    /**
     * The Codex review's X3 (bergdb 020-14): a public class of an exported package that
     * inherits a public field from a public class of a package that is not exported to BergDB
     * is not a Data Object (V6 for each class that declares a stored field, 020-09, section
     * 3.2): refused at a put with IllegalArgumentException and at a get with
     * ObjectCreationException, also of {} and at a key without a value (section 3.3). Until
     * 2026-11-09 the check took it, and Field.get and Field.set threw IllegalAccessException:
     * an IllegalArgumentException at the put that did not say why, and an
     * ObjectCreationException at a get only for a stored object with the field. The same with
     * the superclass in the exported package is valid. And (section 3.3) a class whose field's
     * generic type names a class that is not there is not valid, a LinkageError's case:
     * Field.getGenericType() threw TypeNotPresentException from the put and the get.
     */
    @Nano
    public static void testClassesOfAModule() throws Exception {
        Platform.skipOnAndroid("it makes a module layer (java.lang.module), which Android "
                + "does not have; there V6 has no modules to check");
        Map<String, byte[]> files = new HashMap<String, byte[]>();
        files.put("hidden/Base.class", classFile("hidden/Base", "java/lang/Object", "value",
                "I", null));
        files.put("model/Person.class", classFile("model/Person", "hidden/Base", null, null,
                null));
        files.put("model/Base2.class", classFile("model/Base2", "java/lang/Object", "value",
                "I", null));
        files.put("model/Person2.class", classFile("model/Person2", "model/Base2", null, null,
                null));
        ClassLoader loader = moduleLoader("bergdb.test.x3", files, "model", "hidden");
        Class<?> person = loader.loadClass("model.Person");
        Class<?> person2 = loader.loadClass("model.Person2");
        Assert.assertTrue("a named module", person.getModule().isNamed());
        Assert.assertTrue("hidden not exported", !person.getModule().isExported("hidden"));

        String box = DataObjectsTester.class.getName().replace('.', '/') + "$GenericBox";
        final byte[] gone = classFile("gone/Holder", "java/lang/Object", "box",
                "L" + box + ";", "L" + box + "<Lgone/Missing;>;");
        Class<?> holder = new ClassLoader(DataObjectsTester.class.getClassLoader()) {
            protected Class<?> findClass(String name) throws ClassNotFoundException {
                if (name.equals("gone.Holder")) {
                    return defineClass(name, gone, 0, gone.length);
                }
                throw new ClassNotFoundException(name);
            }
        }.loadClass("gone.Holder");

        Check ch = new Check();
        Database db = memory();
        try {
            Connection c = db.connection();
            refusedClass(ch, c, "X3, Person", person, person.getConstructor().newInstance(),
                    "value", "hidden.Base", "V6");
            Object p2 = person2.getConstructor().newInstance();
            person2.getField("value").setInt(p2, 42);
            validClass(ch, c, "X3, Person2", p2);
            refusedClass(ch, c, "gone.Holder", holder, holder.getConstructor().newInstance(),
                    "Missing");
        } finally {
            db.close();
        }
        ch.done();
    }

    /**
     * A class loader of a new module layer with one module, 'name', whose classes are 'files'
     * (path to class file), that exports 'exported' and has the packages 'others' too.
     */
    static ClassLoader moduleLoader(String name, final Map<String, byte[]> files,
            String exported, String... others) throws Exception {
        ModuleDescriptor d = ModuleDescriptor.newModule(name).exports(exported)
                .packages(Set.of(others)).build();
        final ModuleReference ref = new ModuleReference(d, null) {
            public ModuleReader open() {
                return new ModuleReader() {
                    public Optional<URI> find(String path) {
                        return Optional.empty();
                    }

                    public Optional<InputStream> open(String path) {
                        byte[] b = files.get(path);
                        return b == null ? Optional.empty()
                                : Optional.of(new ByteArrayInputStream(b));
                    }

                    public Stream<String> list() {
                        return files.keySet().stream();
                    }

                    public void close() {}
                };
            }
        };
        ModuleFinder finder = new ModuleFinder() {
            public Optional<ModuleReference> find(String n) {
                return n.equals(name) ? Optional.of(ref) : Optional.empty();
            }

            public Set<ModuleReference> findAll() {
                return Set.of(ref);
            }
        };
        ModuleLayer boot = ModuleLayer.boot();
        Configuration cf = boot.configuration().resolve(finder, ModuleFinder.of(),
                Set.of(name));
        return boot.defineModulesWithOneLoader(cf, ClassLoader.getSystemClassLoader())
                .findLoader(name);
    }

    /**
     * The bytes of a class file (version 52, Java 8): the public class 'name' (internal form,
     * "a/B") extends 'superName', with a public constructor that calls the superclass's, and,
     * unless 'field' is null, the public instance field 'field' of the descriptor 'type' and
     * the generic signature 'signature' (or none if null). Written here, as the tests run
     * without a compiler.
     */
    static byte[] classFile(String name, String superName, String field, String type,
            String signature) throws IOException {
        ByteArrayOutputStream bytes = new ByteArrayOutputStream();
        DataOutputStream out = new DataOutputStream(bytes);
        out.writeInt(0xCAFEBABE);
        out.writeShort(0);
        out.writeShort(52);
        out.writeShort(14);                         // the constant pool, 1 to 13
        utf8(out, name);                            // 1
        out.writeByte(7);                           // 2, Class 1
        out.writeShort(1);
        utf8(out, superName);                       // 3
        out.writeByte(7);                           // 4, Class 3
        out.writeShort(3);
        utf8(out, "<init>");                        // 5
        utf8(out, "()V");                           // 6
        out.writeByte(12);                          // 7, NameAndType 5 6
        out.writeShort(5);
        out.writeShort(6);
        out.writeByte(10);                          // 8, Methodref 4 7
        out.writeShort(4);
        out.writeShort(7);
        utf8(out, "Code");                          // 9
        utf8(out, field == null ? "f" : field);     // 10
        utf8(out, type == null ? "I" : type);       // 11
        utf8(out, "Signature");                     // 12
        utf8(out, signature == null ? "I" : signature);     // 13
        out.writeShort(0x0021);                     // public, super
        out.writeShort(2);
        out.writeShort(4);
        out.writeShort(0);                          // no interfaces
        if (field == null) {
            out.writeShort(0);
        } else {
            out.writeShort(1);
            out.writeShort(0x0001);                 // public
            out.writeShort(10);
            out.writeShort(11);
            if (signature == null) {
                out.writeShort(0);
            } else {
                out.writeShort(1);
                out.writeShort(12);
                out.writeInt(2);
                out.writeShort(13);
            }
        }
        out.writeShort(1);                          // the constructor
        out.writeShort(0x0001);
        out.writeShort(5);
        out.writeShort(6);
        out.writeShort(1);
        out.writeShort(9);                          // Code
        out.writeInt(17);
        out.writeShort(1);                          // max stack
        out.writeShort(1);                          // max locals
        out.writeInt(5);
        out.write(new byte[] {0x2a, (byte) 0xb7, 0, 8, (byte) 0xb1});  // super(); return
        out.writeShort(0);
        out.writeShort(0);
        out.writeShort(0);                          // no attributes of the class
        out.flush();
        return bytes.toByteArray();
    }

    private static void utf8(DataOutputStream out, String s) throws IOException {
        out.writeByte(1);
        out.writeUTF(s);
    }
}
