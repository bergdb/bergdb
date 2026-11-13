import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DbArray;
import bergdb.pub.DbLong;
import bergdb.pub.DbObject;
import bergdb.pub.DbString;
import bergdb.pub.Factory;
import bergdb.pub.Limits;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.stream.FileStream;

/**
 * User code against the release jar alone (bergdb 020-10, section 7): build.sh
 * compiles and runs it with build/bergdb-release.jar as the only class path, so it
 * can use only what the release jar holds. It checks that src-dev's classes are
 * not there, then uses the Pub API's puts, gets and deletes of String and byte[]
 * values (w(), rw(), a lookup at an earlier time) and a DbObject, built with its
 * Builder, a nested object and a DbArray (bergdb 020-10, step B3: DbObject and its
 * classes in bergdb.pub), on a database in a directory, stops it, starts it again
 * and reads again; Limits' key check (bergdb 026-02); and the Core's Db on another
 * directory. Not in a bergdb package,
 * so it sees only what is public.
 *
 * Usage: java -ea -cp bergdb-release.jar ReleaseDemo.java DIR  (DIR new or empty)
 */
public class ReleaseDemo {
    /** Classes of src-dev that the release jar must not hold: bergdb.jar's Main-Class and more. */
    static final String[] NOT_RELEASED = {
            "bergdb.dev.Run", "bergdb.dev.Unit", "bergdb.Help", "bergdb.test.Pack",
            "bergdb.demo.Demo", "frans.PayDemo"};

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        for (String name : NOT_RELEASED) {
            check(!loadable(name), "the release jar holds " + name + ", a class of src-dev");
        }

        String pubDir = new File(dir, "pub").getPath();
        Time first;
        try (Database database = Factory.database().create(pubDir).start()) {
            Connection c = database.connection();
            Limits.checkKey("/fruit/apple");
            check(Limits.keyBytes("/fruit/apple") == 14
                    && Limits.keyBytes("/" + "k".repeat(110)) == 112, "Limits");
            first = c.put("/fruit/apple", "red").getTime();
            c.w().put("/fruit/banana", "yellow").put("/bytes/b", new byte[] {0, 1, 2}).execute();
            DbArray tags = new DbArray.Builder().add(new DbString("red")).add(new DbLong(7))
                    .build();
            DbObject where = new DbObject.Builder().addString("city", "Uppsala").build();
            c.put("/obj/apple", new DbObject.Builder().addString("name", "apple")
                    .addLong("weight", 150).addObject("where", where).addArray("tags", tags)
                    .build());
            Transaction rw = c.rw(env -> {
                String apple = env.get("/fruit/apple", String.class);
                env.put("/fruit/apple", "green");
                env.delete("/fruit/banana");
                env.setOutput("was", apple);
            });
            check("red".equals(rw.getOutput("was", String.class)), "rw's output");
            c.sync();
            read(c, first);
        }
        try (Database database = Factory.database().open(pubDir).start()) {
            read(database.connection(), first);
        }

        File coreDir = new File(dir, "core");
        Db db = Db.builder().mainStream(new FileStream(coreDir)).start();
        Trans t = db.trans().put("/core/k", "v").build();
        db.execute(t);
        db.close();
        db = Db.builder().mainStream(new FileStream(coreDir)).start();
        byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments("/core/k"), db.newGetData());
        db.close();
        check(v != null && "v".equals(new String(v, StandardCharsets.UTF_8)), "Db's getOne");

        System.out.println("ReleaseDemo OK: no class of src-dev; the Pub API, a DbObject and Db, "
                + "with a restart, on the release jar alone");
    }

    /** The reads, the same before and after the restart. */
    static void read(Connection c, Time first) {
        DbObject apple = c.get("/obj/apple", DbObject.class);
        check(apple != null && "apple".equals(apple.getString("name"))
                && apple.getLong("weight") == 150
                && "Uppsala".equals(apple.getObject("where").getString("city"))
                && apple.getArray("tags").getSize() == 2, "the DbObject");
        check("green".equals(c.get("/fruit/apple", String.class)), "apple");
        check(!c.exists("/fruit/banana"), "banana deleted");
        check(Arrays.equals(new byte[] {0, 1, 2}, c.get("/bytes/b", byte[].class)), "bytes");
        c.setLookupTime(first);
        check("red".equals(c.get("/fruit/apple", String.class)), "apple at the first time");
        check(!c.exists("/fruit/banana"), "banana at the first time");
        c.setLookupTime(Time.MAX);
    }

    static boolean loadable(String name) {
        try {
            Class.forName(name, false, ReleaseDemo.class.getClassLoader());
            return true;
        } catch (ClassNotFoundException e) {
            return false;
        }
    }

    static void check(boolean ok, String message) {
        if (!ok) {
            throw new AssertionError(message);
        }
    }
}
