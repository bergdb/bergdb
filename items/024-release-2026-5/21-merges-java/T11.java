import java.io.File;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * 024-21, T11 by hand: "write DIR" makes a Pub database with puts and deletes; "open DIR"
 * starts it and prints what happens. Run each with one jar: 2026.4's or the branch's.
 */
public class T11 {
    public static void main(String[] a) throws Exception {
        String dir = a[1];
        if (a[0].equals("write")) {
            try (Database d = Factory.database().create(dir).start()) {
                Connection c = d.connection();
                for (int i = 0; i < 300; i++) c.put("/k/" + i, "v" + i);
                for (int i = 0; i < 300; i++) if (i % 3 != 0) c.w().delete("/k/" + i).execute();
                c.sync();
            }
            System.out.println("written " + dir);
        } else {
            try (Database d = Factory.database().open(dir).start()) {
                System.out.println("opened: /k/3 = " + d.connection().get("/k/3", String.class));
            } catch (Throwable e) {
                Throwable x = e;
                while (x != null) {
                    System.out.println("refused: " + x.getClass().getName() + ": " + x.getMessage());
                    x = x.getCause();
                }
            }
        }
    }
}
