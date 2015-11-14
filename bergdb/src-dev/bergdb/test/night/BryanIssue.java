package bergdb.test.night;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.TestClock;

/**
 * ISSUE151111, reported by Bryan (e-mail address removed).
 * This code is a modification of code from his bug report.
 */
public class BryanIssue {
    private String dbPath;
    private PrintStream out;
    
    @Nano("night")
    private static void testIt(TestEnvironment env) throws Exception {
        new BryanIssue().go(env);
    }

    private void go(TestEnvironment env) throws IOException, InterruptedException {
        File tempDir = env.createTempDir();
        this.dbPath = tempDir.getAbsolutePath();
        this.out = env.out();
        int id = 0;
        
        for (int i = 0; i < 10; i++) {
            id = runJob(id + 1);
        }
    }

    private int runJob(final int startId) {
        final int count = 10000;
        final int lastId = startId + count;
        int currentId = startId;

        Database db = Factory.database().dir(dbPath).retainDuration(Duration.seconds(10.0))
                .clock(new TestClock()).start();

        Connection c = db.connection();

        List<Integer> list = new ArrayList<Integer>();
        for (Dummy f : c.usePrimary(Dummy.class).objects()) {
            list.add(f.id);
        }

        out.println(String.format("Iterated: %d items", list.size()));

        // Deletes all existing entries.
        for (Integer id : list) {
            c.delete(toKey(id));
        }

        out.println(String.format("Deleted: %d items", list.size()));

        // Creates more entries...
        while (currentId < lastId) {
            Dummy f = createFoobar(currentId);
            c.put(toKey(f.id), f);
            currentId++;
        }

        out.println(String.format("Created: %d items", count));

        db.sync();
        db.stop();

        out.println(String.format("SHUTDOWN lastId = %d", lastId));

        return lastId;
    }
    
    public static String toKey(int id) {
        return String.format("/%d", id);
    }
    
    public static Dummy createFoobar(int id) {
      UUID uuid = UUID.randomUUID();

      return new Dummy(
        id,
        String.format("FoobarName_%d", id),
        uuid.toString(),
        false,
        true,
        true,
        String.format("This is some pseudo-random data %s %s", id, uuid));
    }
    
    public static class Dummy {
        public int id;
        public String name;
        public String uuid;
        public boolean flag1;
        public boolean flag2;
        public boolean flag3;
        public String data;

        public Dummy() {}
        
        public Dummy(final int id, final String name, final String uuid, final boolean flag1,
                final boolean flag2, final boolean flag3, final String data) {
            this.id = id;
            this.name = name;
            this.uuid = uuid;
            this.flag1 = flag1;
            this.flag2 = flag2;
            this.flag3 = flag3;
            this.data = data;
        }
    }
}
