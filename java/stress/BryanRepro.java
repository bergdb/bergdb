package bergdb.core;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.Factory;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

/**
 * The bug report of 2015-11-10 (ISSUE151111, from Bryan Wisdom), as a regression test.
 * Each cycle starts the database on the same directory with a finite retain duration
 * (so reclaim is scheduled), reads all objects, deletes them, creates new ones, and
 * stops. The original program repeated this forever, with 10 s between cycles, on
 * C:\berg\db. The 2017 code fails when it starts, after about 12 cycles, with "A
 * ValueNode cannot be dirty" (the bounded-startup defects, bergdb 011-04, level 2).
 *
 * Adapted from the original DbTest.java and Foobar.java: the directory, the number of
 * cycles and the pause are arguments, and each cycle checks the number of objects it
 * finds, which the original did not.
 *
 * Usage: java -cp bergdb.jar:. bergdb.core.BryanRepro [cycles [pauseMs [dir]]]
 *   Defaults: 40 cycles, no pause (the original: 10000 ms), a new temporary
 *   directory. A given dir must be empty. At least 15 cycles are needed to fail
 *   on the 2017 code.
 * Prints "Done: ... 0 failures" if all cycles pass.
 */
public class BryanRepro {
    static final int COUNT = 10000;

    public static class Foobar {
        public int id;
        public String name;
        public String uuid;
        public boolean flag1;
        public boolean flag2;
        public boolean flag3;
        public String data;

        public Foobar() {
        }

        public Foobar(int id, String name, String uuid, boolean flag1, boolean flag2,
                boolean flag3, String data) {
            this.id = id;
            this.name = name;
            this.uuid = uuid;
            this.flag1 = flag1;
            this.flag2 = flag2;
            this.flag3 = flag3;
            this.data = data;
        }

        public int getId() {
            return id;
        }

        public String getName() {
            return name;
        }

        public String getUuid() {
            return uuid;
        }

        public boolean isFlag1() {
            return flag1;
        }

        public boolean isFlag2() {
            return flag2;
        }

        public boolean isFlag3() {
            return flag3;
        }

        public String getData() {
            return data;
        }

        static String toStr(int id) {
            return String.format("/%d", id);
        }

        @Override
        public String toString() {
            return toStr(id);
        }
    }

    public static void main(String[] args) throws Exception {
        int cycles = args.length > 0 ? Integer.parseInt(args[0]) : 40;
        long pauseMs = args.length > 1 ? Long.parseLong(args[1]) : 0;
        File dir = args.length > 2 ? new File(args[2]) : Files.createTempDirectory("bryan").toFile();
        dir.mkdirs();
        long t0 = System.currentTimeMillis();
        int lastId = 0;
        int cycle = 0;
        try {
            for (cycle = 1; cycle <= cycles; cycle++) {
                lastId = runJob(dir, lastId + 1, cycle > 1 ? COUNT : 0);
                if (pauseMs > 0) {
                    Thread.sleep(pauseMs);
                }
            }
        } catch (Throwable e) {
            System.out.println("FAILED in cycle " + cycle + " of " + cycles + ": " + e);
            e.printStackTrace(System.out);
            System.exit(1);
        }
        System.out.println("Done: " + cycles + " cycles, 0 failures, "
                + (System.currentTimeMillis() - t0) / 1000 + " s.");
    }

    /** One run of the original program: start, read, delete, create, sync, stop. */
    static int runJob(File dir, int startId, int expectedExisting) {
        int lastId = startId + COUNT;
        Database db = Factory.database().dir(dir.getPath())
                .retainDuration(Duration.seconds(10.0)).start();
        Connection conn = db.connection();

        List<Integer> list = new ArrayList<Integer>();
        for (Foobar f : conn.usePrimary(Foobar.class).objects()) {
            list.add(f.getId());
        }
        if (list.size() != expectedExisting) {
            throw new IllegalStateException("found " + list.size() + " objects, expected "
                    + expectedExisting);
        }

        for (Integer id : list) {
            conn.delete(Foobar.toStr(id));
        }

        for (int id = startId; id < lastId; id++) {
            Foobar fb = create(id);
            conn.put(fb.toString(), fb);
        }

        db.sync();
        db.stop();
        return lastId;
    }

    static Foobar create(int id) {
        UUID uuid = UUID.randomUUID();
        return new Foobar(id, String.format("FoobarName_%d", id), uuid.toString(),
                false, true, true, String.format("This is some pseudo-random data %s %s", id, uuid));
    }
}
