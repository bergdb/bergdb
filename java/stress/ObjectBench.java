package bergdb.core;

import java.util.Arrays;
import java.util.Locale;
import java.util.Random;
import java.util.UUID;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pubimp.DatabaseImp;
import bergdb.pubimp.DbObject;

/**
 * The measurements of stored objects, bergdb 020-08, section 7 (step 4; 020-02, section 6,
 * points 2 and 3): format 2 against format 1, and the cost of 020-10's step I1 for puts at
 * keys without a suffix. Written 2026-11-09.
 *
 * <p>Compiled once against the candidate by build.sh, with the stress tests, and run with
 * each build's jar on the class path, so it uses only what both have: DbObject.toDbObject,
 * new DbObject(byte[]), getBytes, getLong and getString by name and by path, the Pub API's
 * puts, gets and indexBuilder(...).start().join(), and the Core's stream length. Run by
 * java/stress/objectbench.sh, which runs each build in its own JVM in ABBA order and prints
 * the medians of the runs.
 *
 * <p>Each line "RESULT id value unit" is one figure of one JVM; the lower the better but
 * for the rates (unit "/s") and the sizes (unit "B"):
 * <ul>
 * <li>M1-SAMPLE, the writer: DbObject.toDbObject of 020-05's samples (section 5.1: Person,
 *     Payment, Foobar, Dialog, an index definition as Data.Index, Customer; and Order and
 *     Blob of 020-05's run), ns an object.</li>
 * <li>M2-SAMPLE, the read of bytes: new DbObject(bytes) of the sample's stored bytes, the
 *     copy and the full check (format 1: the copy and the full parse), ns.</li>
 * <li>M3, lookups on a DbObject made once, hot: Payment's amount (getLong) and from
 *     (getString), Customer's zip (its last field), Dialog's personB.id (a path), ns.</li>
 * <li>M4, a get end to end: N Payments in memory, uniform random keys, one thread: into
 *     Payment.class, as DbObject with one getString, and as byte[] (the Core's get with the
 *     Pub layer's key conversion), ns a get.</li>
 * <li>M5, an index update: puts of Payment, one a transaction, into a directory with a
 *     string index on from, and into one without an index, µs a put.</li>
 * <li>M6, a build: a string index on from over N Payments, start().join(), seconds.</li>
 * <li>M7, bytes: a Payment's stored bytes, and the stream's bytes a Payment after the
 *     load of M6 (transactions of 1,000 puts).</li>
 * <li>M8, the cost of step I1: w() of String puts at keys without a suffix (an object key:
 *     the index manager's lock and a read time since I1, without an index) against keys
 *     with ".txt", one put a w() and 100 puts a w(), µs a w().</li>
 * </ul>
 *
 * <p>Usage: java -Xms8g -Xmx8g -cp BUILD/bergdb.jar:java/build/stress bergdb.core.ObjectBench
 * [quick|full]. quick: small sizes, about 10 s; full: 1,000,000 objects, about 45 s a JVM on
 * F53.
 *
 * @author Frans Lundberg
 */
public class ObjectBench {

    // ======== The samples (020-05, section 5.1, and its run's Order and Blob) ========

    public static class Person {
        public String name;
        public Person() {}
    }

    public static class Payment {
        public String from;
        public String to;
        public long amount;
        public Payment() {}
    }

    public static class Foobar {
        public int id;
        public String name;
        public String uuid;
        public boolean flag1;
        public boolean flag2;
        public boolean flag3;
        public String data;
        public Foobar() {}
    }

    public static class PersonId {
        public long id;
        public PersonId() {}
    }

    public static class Dialog {
        public PersonId personA;
        public PersonId personB;
        public Dialog() {}
    }

    /** The fields of 2026.3's index definition, Data.Index, which 020-10's I2 removes. */
    public static class IndexInfo {
        public String[] dirs;
        public String[] fields;
        public String[] typeStrings;
        public String state;
        public int version = 1;
        public IndexInfo() {}
    }

    public static class Customer {
        public long id;
        public String name;
        public String email;
        public String street;
        public String city;
        public String zip;
        public String country;
        public long created;
        public boolean active;
        public double score;
        public String[] tags;
        public int[] counts;
        public Customer() {}
    }

    public static class Line {
        public String item;
        public long qty;
        public double price;
        public Line() {}
    }

    public static class Order {
        public long id;
        public String customer;
        public Line[] lines;
        public String status;
        public Order() {}
    }

    public static class Blob {
        public String name;
        public String type;
        public byte[] data;
        public Blob() {}
    }

    static final String[] SAMPLE_NAMES = {"Person", "Payment", "Foobar", "Dialog", "Index",
            "Customer", "Order", "Blob"};

    static Object[] samples() {
        Person person = new Person();
        person.name = "P1000";
        Payment payment = payment(1001, 1002, 500);
        Foobar foobar = new Foobar();
        foobar.id = 1234;
        foobar.name = "FoobarName_1234";
        UUID u = new UUID(0x1234567890abcdefL, 0xfedcba0987654321L);
        foobar.uuid = u.toString();
        foobar.flag2 = true;
        foobar.flag3 = true;
        foobar.data = "This is some pseudo-random data 1234 " + u;
        Dialog dialog = new Dialog();
        dialog.personA = new PersonId();
        dialog.personA.id = 1;
        dialog.personB = new PersonId();
        dialog.personB.id = 2;
        IndexInfo index = new IndexInfo();
        index.dirs = new String[] {"/payments/"};
        index.fields = new String[] {"from"};
        index.typeStrings = new String[] {"string/unicode"};
        index.state = "active";
        Customer c = new Customer();
        c.id = 1234567;
        c.name = "Anna Lindqvist";
        c.email = "anna.lindqvist@example.com";
        c.street = "Storgatan 12";
        c.city = "Uppsala";
        c.zip = "753 20";
        c.country = "SE";
        c.created = 1794050000000L;
        c.active = true;
        c.score = 4.25;
        c.tags = new String[] {"gold", "newsletter", "eu"};
        c.counts = new int[] {3, 0, 17, 250, 1};
        Order order = new Order();
        order.id = 100234;
        order.customer = "/customers/1234567";
        order.status = "shipped";
        order.lines = new Line[10];
        for (int i = 0; i < 10; i++) {
            Line l = new Line();
            l.item = "item-" + (4000 + 17 * i);
            l.qty = 1 + i % 3;
            l.price = 9.5 + i;
            order.lines[i] = l;
        }
        Blob blob = new Blob();
        blob.name = "photo-2026-11-08.jpg";
        blob.type = "image/jpeg";
        blob.data = new byte[100000];
        for (int i = 0; i < blob.data.length; i++) {
            blob.data[i] = (byte) (i * 31);
        }
        return new Object[] {person, payment, foobar, dialog, index, c, order, blob};
    }

    static Payment payment(long from, long to, long amount) {
        Payment p = new Payment();
        p.from = Long.toString(from);
        p.to = Long.toString(to);
        p.amount = amount;
        return p;
    }

    // ======== Sizes ========

    final boolean full;
    /** Rounds of a timed loop; its median is reported. */
    final int rounds;
    /** Objects in memory for M4 and M6. */
    final int objects;
    /** Gets in a round of M4. */
    final int gets;
    /** Puts of M5. */
    final int indexPuts;
    /** w()s of one put of M8. */
    final int smallWs;

    ObjectBench(boolean full) {
        this.full = full;
        this.rounds = full ? 11 : 5;
        this.objects = full ? 1000000 : 50000;
        this.gets = full ? 1000000 : 100000;
        this.indexPuts = full ? 100000 : 10000;
        this.smallWs = full ? 200000 : 20000;
    }

    /** A sink, so that the JIT keeps the measured work. */
    static volatile long sink;

    static void result(String id, double value, String unit) {
        System.out.println(String.format(Locale.ROOT, "RESULT %s %.1f %s", id, value, unit));
    }

    static void say(String s) {
        System.out.println("# " + s);
    }

    /** A timed piece of work: one round of n operations, its checksum. */
    interface Work {
        long run(int n);
    }

    /**
     * The median of rounds of the work, in ns an operation, with n chosen so that a round
     * takes about 20 ms; after a warm-up of as many rounds.
     */
    double nsPerOp(Work w) {
        int n = 16;
        while (true) {
            long t0 = System.nanoTime();
            sink += w.run(n);
            long dt = System.nanoTime() - t0;
            if (dt > 20000000L || n >= 1 << 26) {
                break;
            }
            n *= 2;
        }
        for (int i = 0; i < rounds; i++) {
            sink += w.run(n);
        }
        double[] r = new double[rounds];
        for (int i = 0; i < rounds; i++) {
            long t0 = System.nanoTime();
            sink += w.run(n);
            r[i] = (System.nanoTime() - t0) / (double) n;
        }
        return median(r);
    }

    static double median(double[] r) {
        double[] s = r.clone();
        Arrays.sort(s);
        return s.length % 2 == 1 ? s[s.length / 2] : (s[s.length / 2 - 1] + s[s.length / 2]) / 2;
    }

    // ======== M1 to M3: the codec ========

    void codec() {
        Object[] samples = samples();
        for (int k = 0; k < samples.length; k++) {
            final Object sample = samples[k];
            final String name = SAMPLE_NAMES[k];
            try {
                final byte[] bytes = DbObject.toDbObject(sample).getBytes();
                result("M1-" + name, nsPerOp(n -> {
                    long x = 0;
                    for (int i = 0; i < n; i++) {
                        x += DbObject.toDbObject(sample).getBytes().length;
                    }
                    return x;
                }), "ns");
                result("M2-" + name, nsPerOp(n -> {
                    long x = 0;
                    for (int i = 0; i < n; i++) {
                        x += new DbObject(bytes).getBytes().length;
                    }
                    return x;
                }), "ns");
                result("M7-bytes-" + name, bytes.length, "B");
            } catch (RuntimeException e) {
                say(name + ": not measured, " + e);
            }
        }
        final DbObject payment = DbObject.toDbObject(samples[1]);
        final DbObject customer = DbObject.toDbObject(samples[5]);
        final DbObject dialog = DbObject.toDbObject(samples[3]);
        final String[] path = {"personB", "id"};
        check(payment.getLong("amount") == 500 && "1001".equals(payment.getString("from"))
                && "753 20".equals(customer.getString("zip")) && dialog.getLong(path) == 2,
                "the lookups' values");
        result("M3-Payment.amount", nsPerOp(n -> {
            long x = 0;
            for (int i = 0; i < n; i++) {
                x += payment.getLong("amount");
            }
            return x;
        }), "ns");
        result("M3-Payment.from", nsPerOp(n -> {
            long x = 0;
            for (int i = 0; i < n; i++) {
                x += payment.getString("from").length();
            }
            return x;
        }), "ns");
        result("M3-Customer.zip", nsPerOp(n -> {
            long x = 0;
            for (int i = 0; i < n; i++) {
                x += customer.getString("zip").length();
            }
            return x;
        }), "ns");
        result("M3-Dialog.personB.id", nsPerOp(n -> {
            long x = 0;
            for (int i = 0; i < n; i++) {
                x += dialog.getLong(path);
            }
            return x;
        }), "ns");
    }

    // ======== M4: gets ========

    static String key(String dir, int i) {
        return dir + "p" + i;
    }

    /** Puts n Payments into dir, 1,000 a transaction; the stream's bytes they took. */
    static long load(Database db, String dir, int n) {
        Connection c = db.connection();
        long before = streamLength(db);
        for (int i = 0; i < n; i += 1000) {
            WBuilder w = c.w();
            for (int j = i; j < Math.min(n, i + 1000); j++) {
                w.put(key(dir, j), payment(1000 + j % 997, 2000 + j % 991, j));
            }
            w.execute();
        }
        return streamLength(db) - before;
    }

    static long streamLength(Database db) {
        return ((DatabaseImp) db).getDb().internal().nodeStream().getNextPos();
    }

    void gets() {
        Database db = Factory.database().memory().start();
        try {
            long t0 = System.nanoTime();
            load(db, "/g/", objects);
            say(String.format(Locale.ROOT, "M4: %d Payments loaded in %.1f s", objects,
                    (System.nanoTime() - t0) / 1e9));
            final Connection c = db.connection();
            final Random r = new Random(4);
            final int n = objects;
            final String[] keys = new String[4096];
            final int[] ks = new int[keys.length];
            double[] intoClass = new double[rounds];
            double[] asDbObject = new double[rounds];
            double[] asBytes = new double[rounds];
            for (int round = -2; round < rounds; round++) {
                for (int i = 0; i < keys.length; i++) {
                    ks[i] = r.nextInt(n);
                    keys[i] = key("/g/", ks[i]);
                }
                int g = gets / 3;
                long s = 0;
                long a = System.nanoTime();
                for (int i = 0; i < g; i++) {
                    int j = i & (keys.length - 1);
                    Payment p = c.get(keys[j], Payment.class);
                    if (p.amount != ks[j]) {
                        throw new AssertionError("M4: " + keys[j] + " gave " + p.amount);
                    }
                }
                long b = System.nanoTime();
                for (int i = 0; i < g; i++) {
                    s += c.get(keys[i & (keys.length - 1)], DbObject.class).getString("from")
                            .length();
                }
                long d = System.nanoTime();
                for (int i = 0; i < g; i++) {
                    s += c.get(keys[i & (keys.length - 1)], byte[].class).length;
                }
                long e = System.nanoTime();
                sink += s;
                if (round >= 0) {
                    intoClass[round] = (b - a) / (double) g;
                    asDbObject[round] = (d - b) / (double) g;
                    asBytes[round] = (e - d) / (double) g;
                }
            }
            result("M4-get-into-Payment", median(intoClass), "ns");
            result("M4-get-DbObject-getString", median(asDbObject), "ns");
            result("M4-get-byte[]", median(asBytes), "ns");
        } finally {
            db.close();
        }
    }

    // ======== M5 and M6: indexes ========

    void indexUpdates() {
        for (boolean indexed : new boolean[] {true, false}) {
            Database db = Factory.database().memory().start();
            try {
                Connection c = db.connection();
                if (indexed) {
                    Job job = db.indexBuilder("byFrom").dir("/i/").type("string").field("from")
                            .start();
                    say("M5: the index on an empty directory: " + job.join().note());
                }
                int warm = indexPuts / 10;
                for (int i = 0; i < warm; i++) {
                    c.put(key("/i/", objects + i), payment(1000 + i % 997, 2000, i));
                }
                long t0 = System.nanoTime();
                for (int i = 0; i < indexPuts; i++) {
                    c.put(key("/i/", i), payment(1000 + i % 997, 2000 + i % 991, i));
                }
                double us = (System.nanoTime() - t0) / 1000.0 / indexPuts;
                result(indexed ? "M5-put-indexed" : "M5-put-not-indexed", us, "us");
            } finally {
                db.close();
            }
        }
    }

    void build() {
        Database db = Factory.database().memory().start();
        try {
            long t0 = System.nanoTime();
            long bytes = load(db, "/b/", objects);
            say(String.format(Locale.ROOT, "M6: %d Payments loaded in %.1f s", objects,
                    (System.nanoTime() - t0) / 1e9));
            result("M7-stream-bytes-a-Payment", bytes / (double) objects, "B");
            long t1 = System.nanoTime();
            Job job = db.indexBuilder("byFrom").dir("/b/").type("string").field("from").start();
            JobStatus status = job.join();
            double s = (System.nanoTime() - t1) / 1e9;
            say("M6: " + status.note());
            result("M6-build-s", s, "s");
            result("M6-build-objects-a-second", objects / s, "/s");
        } finally {
            db.close();
        }
    }

    // ======== M8: step I1's cost ========

    void stringPuts() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            for (int batch : new int[] {1, 100}) {
                int ws = batch == 1 ? smallWs : smallWs / 100;
                double[] objectKeys = new double[rounds];
                double[] txtKeys = new double[rounds];
                int next = 0;
                for (int round = -2; round < rounds; round++) {
                    int per = Math.max(1, ws / rounds);
                    for (int o = 0; o < 2; o++) {
                        int kind = (o + round) & 1;     // each kind first in every other round
                        String suffix = kind == 0 ? "" : ".txt";
                        String dir = kind == 0 ? "/s" + batch + "/" : "/t" + batch + "/";
                        long t0 = System.nanoTime();
                        for (int i = 0; i < per; i++) {
                            WBuilder w = c.w();
                            for (int j = 0; j < batch; j++) {
                                int k = next + i * batch + j;
                                w.put(dir + "k" + k + suffix, "v" + k);
                            }
                            w.execute();
                        }
                        double us = (System.nanoTime() - t0) / 1000.0 / per;
                        if (round >= 0) {
                            (kind == 0 ? objectKeys : txtKeys)[round] = us;
                        }
                    }
                    next += per * batch;
                }
                result("M8-w" + batch + "-String-object-key", median(objectKeys), "us");
                result("M8-w" + batch + "-String-txt-key", median(txtKeys), "us");
            }
        } finally {
            db.close();
        }
    }

    // ======== Run ========

    static void check(boolean ok, String what) {
        if (!ok) {
            throw new AssertionError("ObjectBench: wrong " + what);
        }
    }

    public static void main(String[] args) {
        boolean full = args.length > 0 && args[0].equals("full");
        ObjectBench b = new ObjectBench(full);
        byte[] person = DbObject.toDbObject(samples()[0]).getBytes();
        String format = (person[0] & 0xff) == 0x82 ? "2" : person[0] == 'b' ? "1" : "?";
        say("ObjectBench, " + (full ? "full" : "quick") + "; object format " + format + "; "
                + System.getProperty("java.vm.name") + " " + System.getProperty("java.version")
                + "; max heap " + Runtime.getRuntime().maxMemory() / 1000000 + " MB");
        say("class path " + System.getProperty("java.class.path"));
        long t0 = System.nanoTime();
        b.codec();
        b.gets();
        b.indexUpdates();
        b.build();
        b.stringPuts();
        say(String.format(Locale.ROOT, "ObjectBench done in %.0f s",
                (System.nanoTime() - t0) / 1e9));
    }
}
