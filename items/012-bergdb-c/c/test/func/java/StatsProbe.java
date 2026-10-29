import java.io.File;

import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Java's side of f_settings.c's test settings_and_status_as_java (bergdb 012-13): a
 * fixed sequence of transactions, reads, setters, syncs and a restart on the test
 * clock, through Db's public API, with Db's getters printed at fixed points, one line
 * each. f_settings.c runs the same sequence through bergdb.h and compares its lines
 * with the ones this program printed, which it holds as text (the durable length only
 * after a sync and a start, where Java's does not depend on its buffer thread's
 * timing). To print them again:
 *
 *   test/cross/java-build.sh
 *   javac -cp build/java/classes -d build/probe test/func/java/StatsProbe.java
 *   java -ea -cp build/java/classes:build/probe StatsProbe NEW_DIR
 *
 * and BERGDB_STATS_OUT=FILE build/test/func settings_ writes C's lines to FILE (and keeps
 * C's database, whose files equal Java's).
 */
public class StatsProbe {
    static final CoreTestClock clock = new CoreTestClock();
    static Db db;

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        clock.setTime(1000);
        open(dir);
        print("open", true);
        for (int i = 0; i < 150; i++) {
            clock.setTime(2_000_000L + i * 1_000_000L);
            Trans.Builder b = db.trans();
            b.put(Keys.toBytes("/k/" + (i * 7 % 50)), value(i, 100 + (i % 7) * 30));
            b.put(Keys.toBytes("/k/" + ((i * 7 + 1) % 50)), ("x" + i).getBytes("UTF-8"));
            if (i % 5 == 0) {
                b.delete(Keys.toBytes("/k/" + (i * 3 % 50)));
            }
            db.execute(b.build());
            if (i % 10 == 0) {
                GetData gd = db.newGetData();
                db.getOne(Long.MAX_VALUE, Keys.toSegments("/k/" + (i % 50)), gd);
                try {
                    db.getOne(2_000_000L + (i - 1) * 1_000_000L, Keys.toSegments("/k/" + ((i + 1) % 50)), gd);
                } catch (LookupTimeNotAvailableException e) {
                    System.out.println("unavailable i=" + i);
                }
                GetMany g = db.newGetMany();
                g.stopCondition = new GetMany.GetN(5);
                db.getMany(g);
            }
            if (i == 50) {
                print("t50", false);
            }
            if (i == 60) {
                db.setStartupDistance(10);              // clamped to 400,000: the dummy
                print("setsd", false);
                db.setStartupDistance(400_000);         // the value in force: nothing
                print("setsd-same", false);
            }
            if (i == 70) {
                db.setRetainDuration(20_000_000L);
                db.setReclaimInternalFraction(0.1);
                db.setCacheSizeIndicator(150_000_000L);
                print("setters", false);
            }
            if (i == 100) {
                db.sync(SyncLevel.STRONG);
                print("sync", true);
            }
        }
        print("end", false);
        db.close();
        open(dir);
        print("reopen", true);
        for (int i = 150; i < 152; i++) {
            clock.setTime(2_000_000L + i * 1_000_000L);
            db.execute(db.trans().put(Keys.toBytes("/k/" + i), value(i, 10)).build());
        }
        db.sync(SyncLevel.ORDINARY);
        print("reopen-sync", true);
        db.close();
    }

    static void open(File dir) throws Exception {
        DbBuilder b = Db.builder();
        b.mainStream(new FileStream(dir));
        b.testSetupExceptStream();
        b.clock(clock);
        b.maxNodeSize8();
        b.startupDistance(1000);
        b.retainDuration(10_000_000L);
        db = b.build();
        db.start();
    }

    static byte[] value(int i, int n) {
        byte[] v = new byte[n];
        for (int j = 0; j < n; j++) {
            v[j] = (byte) (i * 31 + j);
        }
        return v;
    }

    static void print(String at, boolean durable) {
        System.out.println("at=" + at
                + " length=" + db.getStreamLength()
                + (durable ? " durable=" + db.getDurableLength() : "")
                + " lastMeta=" + db.getLastTransPosOfLastValidMetaBlock()
                + " firstTime=" + db.getFirstAvailableLookupTime()
                + " firstPos=" + db.getFirstAvailablePos()
                + " sd=" + db.getStartupDistance()
                + " cache=" + db.getCacheSizeIndicator()
                + " retain=" + db.getRetainDuration()
                + " fraction=" + db.getInternalFraction()
                + " iterations=" + db.getReclaimIterationCount()
                + " trans=" + db.getTransactionCount()
                + " kvs=" + db.getKvCount()
                + " gets=" + db.getGetOpCount());
    }
}
