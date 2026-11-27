import bergdb.pub.*;
import java.io.File;
import java.nio.file.*;

/**
 * bergdb 028-66's review (2026-11-27): a start that refuses a stream whose first position is
 * after reclaim's cut (Reclaim.initFromDb) writes created.txt first, if it is missing
 * (Db.writeCreatedTxtIfMissing() comes before initFromDb). A Pub database of about 8 MB,
 * startup distance 1 MB, never cut; created.txt and the first stream file removed by hand;
 * the start is refused ("lacks bytes"); then created.txt is there again. Prints
 * CREATED TXT WRITTEN BEFORE THE REFUSAL, or CREATED TXT NOT WRITTEN.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar ../items/028-todo/66-cut-deletes-lag/CreatedTxtProbe.java
 *   java -ea -cp CLASSES:build/bergdb.jar CreatedTxtProbe DIR
 * DIR must not exist; it is removed at the end.
 */
public class CreatedTxtProbe {
    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        Database db = Factory.database().create(dir.getPath()).start();
        db.setStartupDistanceInMb(1);
        Connection c = db.connection();
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 1500; i++) sb.append((char) ('a' + i % 26));
        for (int n = 0; n < 5000; n++) c.w().put("/v/" + (n % 100), n + " " + sb).execute();
        db.close();
        File created = new File(dir, "created.txt");
        File first = new File(dir, "00000000000000.bergdb");
        if (!created.delete() || !first.delete()) throw new AssertionError("could not remove");
        try {
            Factory.database().open(dir.getPath()).start().close();
            System.out.println("PROBE: started; not the case to show");
            System.exit(1);
        } catch (RuntimeException e) {
            System.out.println("refused: " + e.getMessage().substring(0,
                    Math.min(200, e.getMessage().length())));
        }
        System.out.println(created.exists() ? "CREATED TXT WRITTEN BEFORE THE REFUSAL"
                : "CREATED TXT NOT WRITTEN");
        for (File f : dir.listFiles()) f.delete();
        dir.delete();
    }
}
