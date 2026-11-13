import java.io.File;
import java.lang.management.ManagementFactory;
import java.util.ArrayList;
import java.util.List;
import bergdb.pub.*;
/** bergdb 026-07: how many small file databases start in this heap (U10-2's case), up to MAX. */
public class ManyProbe {
    public static void main(String[] args) throws Exception {
        int max = Integer.parseInt(args[1]);
        List<Database> dbs = new ArrayList<>();
        try {
            for (int i = 0; i < max; i++) {
                Database db = Factory.database().create(new File(args[0], "f" + i).getPath()).start();
                db.connection().w().put("/k", "v" + i).execute();
                dbs.add(db);
            }
            System.out.println("started " + dbs.size() + " of " + max + ", no OutOfMemoryError");
        } catch (OutOfMemoryError e) {
            System.out.println("OutOfMemoryError after " + dbs.size() + " started databases");
        }
        System.gc();
        System.out.printf("heap used after GC: %.1f MB%n",
                ManagementFactory.getMemoryMXBean().getHeapMemoryUsage().getUsed() / 1e6);
        for (Database d : dbs) d.close();
    }
}
