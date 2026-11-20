import bergdb.pub.*;
// Single-type import: a3-limits' Limits, in the same unnamed package, hides bergdb.pub.*'s.
import bergdb.pub.Limits;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/** Functional schema evolution and stored-value checks. Usage: D6SchemaValues DIR SEED. */
public final class D6SchemaValues {
    public static class B { public byte v = 99; public B() { } }
    public static class S { public short v = 99; public S() { } }
    public static class C { public char v = 99; public C() { } }
    public static class I { public int v = 99; public I() { } }
    public static class L { public long v = 99; public L() { } }
    public static class F { public float v = 99; public F() { } }
    public static class D { public double v = 99; public D() { } }
    public static class N { public boolean v = true; public N() { } }
    public static class T { public String v = "constructor"; public T() { } }
    public static class Bytes { public byte[] v = {99}; public Bytes() { } }
    public static class Ints { public int[] v = {99}; public Ints() { } }
    public static class Texts { public String[] v = {"constructor"}; public Texts() { } }
    record Source(Object value, DbValue stored) { }
    final List<Source> sources = new ArrayList<>();
    final Map<String, DbObject> oracle = new LinkedHashMap<>();
    long assertions, conversions;
    static void check(boolean ok, String m) { if (!ok) throw new IllegalStateException(m); }
    static BigInteger integer(Object o) {
        if (o instanceof Long n) return BigInteger.valueOf(n);
        if (o instanceof Boolean b) return BigInteger.valueOf(b ? 1 : 0);
        if (o instanceof Double d) return BigInteger.valueOf((long) (double) d);
        if (o instanceof String s) {
            String t = s.trim();
            if (t.matches("[+-]?[0-9]+")) return new BigInteger(t);
            try { return BigInteger.valueOf((long) Double.parseDouble(t)); } catch (NumberFormatException bad) { return BigInteger.ZERO; }
        }
        return BigInteger.ZERO;
    }
    static long clamp(Object o, long min, long max) {
        return integer(o).max(BigInteger.valueOf(min)).min(BigInteger.valueOf(max)).longValue();
    }
    static double floating(Object o, boolean single) {
        if (o instanceof Long n) return single ? (float) (long) n : (double) (long) n;
        if (o instanceof Boolean b) return b ? 1 : 0;
        if (o instanceof Double d) return single ? (float) (double) d : d;
        if (o instanceof String s) {
            try { return single ? Float.parseFloat(s) : Double.parseDouble(s); } catch (NumberFormatException bad) { return 0; }
        }
        return 0;
    }
    static boolean truth(Object o) {
        if (o instanceof Boolean b) return b;
        if (o instanceof Long n) return n != 0;
        if (o instanceof Double d) return !d.isNaN() && d != 0;
        return o instanceof String s && s.equalsIgnoreCase("true");
    }
    static String text(Object o) {
        if (o instanceof String s) return s;
        if (o instanceof Long || o instanceof Double || o instanceof Boolean) return o.toString();
        return o instanceof byte[] b ? new String(b, StandardCharsets.UTF_8) : null;
    }
    void add(Object o) {
        DbValue value;
        if (o instanceof Long n) value = new DbLong(n);
        else if (o instanceof Double d) value = new DbDouble(d);
        else if (o instanceof Boolean b) value = new DbBoolean(b);
        else if (o instanceof String s) value = new DbString(s);
        else if (o instanceof byte[] b) value = new DbByteArray(b);
        else throw new IllegalStateException("bad source");
        sources.add(new Source(o, value));
    }
    void prepare(long seed) {
        for (long n : new long[]{Long.MIN_VALUE, Long.MIN_VALUE + 1, -2147483649L, Integer.MIN_VALUE, -32769, -32768, -129,
                -128, -1, 0, 1, 127, 128, 255, 32767, 32768, 65535, 65536, Integer.MAX_VALUE, 2147483648L,
                9007199254740991L, 9007199254740992L, 9007199254740993L, Long.MAX_VALUE - 1, Long.MAX_VALUE}) add(n);
        for (double d : new double[]{Double.NEGATIVE_INFINITY, -Double.MAX_VALUE, (double) Long.MIN_VALUE, -2147483648.5,
                -128.9, -1.9, -Double.MIN_VALUE, -0.0, 0.0, Double.MIN_VALUE, 0.1f, 0.1, 1.9, 127.9,
                32767.9, 65535.9, 2147483647.9, Math.nextDown((double) Long.MAX_VALUE), (double) Long.MAX_VALUE,
                1e300, Double.POSITIVE_INFINITY, Double.NaN}) add(d);
        add(true); add(false);
        for (String s : new String[]{"", "0", "-0", "12.7", "-12.7", "042", "+42", "42d", "42f", "42L", "4_2", "0x1p4", "0x2A",
                "\t42\n", "\u00a042", "٤٢", "Infinity", "-Infinity", "NaN", "nan", "1e999", "-1e999", "true", "TRUE", " true",
                "9223372036854775807", "9223372036854775808", "-9223372036854775809", "9".repeat(400), "-" + "9".repeat(400),
                "0.0000000000000000001", "😀", "\u0000", " 中 "}) add(s);
        add(new byte[]{}); add(new byte[]{0, 1, (byte) 0xff}); add(new byte[]{(byte) 0xc0, (byte) 0xaf}); add("true".getBytes(StandardCharsets.UTF_8));
        Random r = new Random(seed);
        for (int i = 0; i < 150; i++) {
            long n = r.nextLong(); add(n); add(Long.toString(n)); add(Double.longBitsToDouble(r.nextLong()));
        }
        List<Object> elements = List.of(1L, -1L, 300L, 70000L, 12.7, -12.7, Double.NaN, true, "66", "B", new byte[]{1});
        DbArray.Builder a = new DbArray.Builder();
        for (Object e : elements) {
            if (e instanceof Long l) a.add(new DbLong(l)); else if (e instanceof Double d) a.add(new DbDouble(d));
            else if (e instanceof Boolean b) a.add(new DbBoolean(b)); else if (e instanceof String s) a.add(new DbString(s));
            else a.add(new DbByteArray((byte[]) e));
        }
        sources.add(new Source(elements, a.build()));
        sources.add(new Source(Map.of("nested", 42), new DbObject.Builder().addLong("nested", 42).build()));
    }
    void verify(Connection c, String key, Object source) {
        String where = key + " source=" + (source instanceof byte[] b ? Arrays.toString(b) : source);
        check(c.get(key, B.class).v == clamp(source, Byte.MIN_VALUE, Byte.MAX_VALUE), "byte " + where);
        check(c.get(key, S.class).v == clamp(source, Short.MIN_VALUE, Short.MAX_VALUE), "short " + where);
        check(c.get(key, C.class).v == clamp(source, Character.MIN_VALUE, Character.MAX_VALUE), "char " + where);
        check(c.get(key, I.class).v == clamp(source, Integer.MIN_VALUE, Integer.MAX_VALUE), "int " + where);
        check(c.get(key, L.class).v == clamp(source, Long.MIN_VALUE, Long.MAX_VALUE), "long " + where);
        float f = c.get(key, F.class).v; double d = c.get(key, D.class).v;
        check(Float.floatToIntBits(f) == Float.floatToIntBits((float) floating(source, true)), "float " + where + " got=" + f);
        check(Double.doubleToLongBits(d) == Double.doubleToLongBits(floating(source, false)), "double " + where + " got=" + d);
        check(c.get(key, N.class).v == truth(source), "boolean " + where);
        check(Objects.equals(c.get(key, T.class).v, text(source)), "String " + where);
        byte[] bytes = source instanceof byte[] b ? b : source instanceof String s ? s.getBytes(StandardCharsets.UTF_8) : null;
        int[] ints = null; String[] texts = null;
        if (source instanceof List<?> list) {
            bytes = new byte[list.size()]; ints = new int[list.size()]; texts = new String[list.size()];
            for (int n = 0; n < list.size(); n++) {
                bytes[n] = (byte) clamp(list.get(n), Byte.MIN_VALUE, Byte.MAX_VALUE);
                ints[n] = (int) clamp(list.get(n), Integer.MIN_VALUE, Integer.MAX_VALUE); texts[n] = text(list.get(n));
            }
        }
        check(Arrays.equals(c.get(key, Bytes.class).v, bytes), "byte[] " + where);
        check(Arrays.equals(c.get(key, Ints.class).v, ints), "int[] " + where);
        check(Arrays.equals(c.get(key, Texts.class).v, texts), "String[] " + where);
        check(Arrays.equals(c.get(key, DbObject.class).getBytes(), oracle.get(key).getBytes()), "stored bytes " + where);
        conversions += 12; assertions += 13;
    }
    void values(Database db, long seed) {
        Connection c = db.connection(); Random random = new Random(seed);
        String[] names = {"a", "\u0000", "\u0001", "v", "\ue000", "𐀀", "😀", "中", "å", "z"};
        Map<String, Long> fields = new LinkedHashMap<>(); for (int n = 0; n < names.length; n++) fields.put(names[n], (long) n);
        byte[] canonical = null;
        for (int run = 0; run < 20; run++) {
            List<String> order = new ArrayList<>(fields.keySet()); Collections.shuffle(order, random);
            DbObject.Builder builder = new DbObject.Builder();
            for (String name : order) builder.addLong(name, fields.get(name));
            DbObject object = builder.build(); byte[] bytes = object.getBytes();
            if (canonical == null) canonical = bytes.clone(); else check(Arrays.equals(bytes, canonical), "noncanonical field order");
            for (String name : names) check(object.getLong(name) == fields.get(name), "field lookup " + name);
            Arrays.fill(bytes, (byte) 0); check(Arrays.equals(object.getBytes(), canonical), "getBytes exposed mutable bytes");
            DbObject read = new DbObject(canonical); byte[] input = canonical.clone(); DbObject copied = new DbObject(input);
            Arrays.fill(input, (byte) 0); check(Arrays.equals(copied.getBytes(), canonical), "constructor did not copy");
            check(Arrays.equals(read.getBytes(), copied.getBytes()), "constructor changed canonical value"); assertions += 14;
        }
        DbObject.Builder many = new DbObject.Builder();
        for (int i = 0; i < 32767; i++) many.addInt("f" + i, i);
        DbObject full = many.build(); check(full.getFieldCount() == 32767, "field count mismatch");
        try { many.addInt("extra", 1); throw new IllegalStateException("32768th field accepted"); }
        catch (IllegalArgumentException good) { }
        check(Arrays.equals(full.getBytes(), many.build().getBytes()), "refused field changed builder");
        many.addInt("f0", 77); DbObject replaced = many.build(); check(replaced.getInt("f0") == 77, "replace at field limit refused");
        c.put("/values/full", replaced);
        DbObject got = c.get("/values/full", DbObject.class);
        for (int i = 0; i < 32767; i++) check(got.getInt("f" + i) == (i == 0 ? 77 : i), "wide object field mismatch");
        assertions += 32771;
        DbObject nested = new DbObject.Builder().addLong("n", 1).build();
        for (int i = 1; i < 16; i++) nested = new DbObject.Builder().addObject("child", nested).build();
        DbObject depth16 = nested;
        try { new DbObject.Builder().addObject("child", nested).build(); throw new IllegalStateException("depth 17 accepted"); }
        catch (IllegalArgumentException good) { }
        c.put("/values/depth", depth16);
        DbObject cursor = c.get("/values/depth", DbObject.class);
        for (int i = 1; i < 16; i++) {
            cursor = cursor.getObject("child"); check(cursor != null, "lost nested object");
            check(Arrays.equals(new DbObject(cursor.getBytes()).getBytes(), cursor.getBytes()), "nested view not standalone");
        }
        check(cursor.getLong("n") == 1, "lost bottom field"); assertions += 31;
        DbObject oversized = new DbObject.Builder().addDbValue("v", new DbByteArray(new byte[Limits.MAX_VALUE_BYTES])).build();
        check(oversized.getBytes().length > Limits.MAX_VALUE_BYTES, "size setup wrong");
        WBuilder w = c.w().put("/values/poison.txt", "must not commit");
        try { w.put("/values/oversized", oversized); throw new IllegalStateException("oversized object accepted"); }
        catch (IllegalArgumentException good) { }
        boolean refused = false;
        try { w.execute(); } catch (IllegalStateException good) { refused = true; }
        check(refused, "poisoned object builder committed");
        check(!c.exists("/values/poison.txt") && !c.exists("/values/oversized"), "oversized object leaked writes"); assertions += 3;
        System.out.println("canonical ordering, wide objects, nested views, immutability and size refusal checked");
    }
    public static void main(String[] args) throws Exception {
        String path = args[0]; long seed = Long.parseLong(args[1]); check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D6SchemaValues seed=" + seed);
        D6SchemaValues app = new D6SchemaValues(); app.prepare(seed);
        try (Database db = Factory.database().create(path).cacheSizeInMb(64).start()) {
            Connection c = db.connection();
            for (int n = 0; n < app.sources.size(); n++) {
                Source s = app.sources.get(n); String key = "/schema/" + n;
                DbObject o = new DbObject.Builder().addDbValue("v", s.stored).build();
                c.put(key, o); app.oracle.put(key, o); app.verify(c, key, s.value);
            }
            c.put("/schema/absent", new DbObject.Builder().build());
            check(c.get("/schema/absent", I.class).v == 99 && c.get("/schema/absent", T.class).v.equals("constructor"), "absent field default lost");
            app.values(db, seed); db.sync();
        }
        try (Database db = Factory.database().open(path).cacheSizeInMb(64).start()) {
            Connection c = db.connection();
            for (int n = 0; n < app.sources.size(); n++) app.verify(c, "/schema/" + n, app.sources.get(n).value);
        }
        System.out.println("OK D6SchemaValues sources=" + app.sources.size() + " conversions=" + app.conversions + " assertions=" + app.assertions + " restart=checked");
    }
}
