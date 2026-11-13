import java.io.File;
import java.util.ArrayList;
import java.util.List;
import bergdb.pub.*;
public class HistProbe {
    public static void main(String[] args) throws Exception {
        List<Database> dbs = new ArrayList<>();
        for (int i = 0; i < 50; i++) {
            Database db = Factory.database().create(new File(args[0], "f" + i).getPath()).start();
            db.connection().w().put("/k", "v" + i).execute();
            db.connection().sync();
            dbs.add(db);
        }
        System.out.println("ready"); System.out.flush();
        Thread.sleep(8000);
        for (Database d : dbs) d.close();
    }
}
