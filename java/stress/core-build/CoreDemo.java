import java.io.File;
import java.nio.charset.StandardCharsets;

import bergdb.core.Db;
import bergdb.core.StoredTrans;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * User code that calls Db directly, with only the Core Layer on the class path
 * (bergdb 006-08). It uses the Core Data API (execute, getOne, getMany, getTrans)
 * on a database in a directory, stops it, starts it again and reads again.
 * Not in a bergdb package, so it sees only what is public.
 *
 * Usage: java -ea -cp bergdb-core.jar:. CoreDemo DIR  (DIR new or empty)
 */
public class CoreDemo {
    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);

        Db db = Db.builder().mainStream(new FileStream(dir)).start();
        Trans first = db.trans().put("/fruit/apple", "red").put("/fruit/banana", "yellow").build();
        db.execute(first);
        Trans second = db.trans().put("/fruit/apple", "green").delete("/fruit/banana").build();
        db.execute(second);
        db.sync(SyncLevel.ORDINARY);
        String before = read(db, first.tt, second.tt);
        db.close();

        db = Db.builder().mainStream(new FileStream(dir)).start();
        String after = read(db, first.tt, second.tt);
        db.close();

        System.out.print(before);
        check(before.equals(after), "the reads after the restart differ:\n" + after);
        System.out.println("CoreDemo OK: the same reads after a restart");
    }

    /**
     * The reads, checked, as text: getOne at both times, getMany, getTrans. The scan reads
     * the demo's own keys, those under "/fruit": the Core API shows BergDB's keys too, under
     * "/#", as the startup distance's KV that every database has (Db, "Keys and the layers
     * above"; bergdb 028-15).
     */
    static String read(Db db, long time1, long time2) {
        StringBuilder b = new StringBuilder();
        GetData gd = db.newGetData();
        String apple1 = string(db.getOne(time1, Keys.toSegments("/fruit/apple"), gd));
        String apple2 = string(db.getOne(Long.MAX_VALUE, Keys.toSegments("/fruit/apple"), gd));
        long tpos = gd.tpos;
        String banana1 = string(db.getOne(time1, Keys.toSegments("/fruit/banana"), gd));
        String banana2 = string(db.getOne(Long.MAX_VALUE, Keys.toSegments("/fruit/banana"), gd));
        check("red".equals(apple1) && "green".equals(apple2), "apple: " + apple1 + ", " + apple2);
        check("yellow".equals(banana1) && banana2 == null, "banana: " + banana1 + ", " + banana2);
        b.append("getOne: apple " + apple1 + " then " + apple2
                + ", banana " + banana1 + " then " + banana2 + "\n");

        for (long time : new long[] {time1, Long.MAX_VALUE}) {
            GetMany g = db.newGetMany();
            g.lookupTime = time;
            g.startKey = Keys.toSegments("/fruit");
            g.stopCondition = new GetMany.Prefix(Keys.toSegments("/fruit"));
            db.getMany(g);
            StringBuilder kvs = new StringBuilder();
            for (Kvt kvt : g.result) {
                kvs.append(" " + Keys.toString(kvt.key) + "=" + string(kvt.value));
            }
            check(g.result.size() == (time == time1 ? 2 : 1), "getMany:" + kvs);
            b.append("getMany at " + (time == time1 ? "the first time:" : "the latest time:") + kvs + "\n");
        }

        StoredTrans t = db.getTrans(tpos);
        check(t.tt == time2, "getTrans: time " + t.tt + ", not " + time2);
        b.append("getTrans: the latest apple's transaction is the second one\n");
        return b.toString();
    }

    static String string(byte[] value) {
        return value == null ? null : new String(value, StandardCharsets.UTF_8);
    }

    static void check(boolean ok, String message) {
        if (!ok) {
            throw new AssertionError(message);
        }
    }
}
