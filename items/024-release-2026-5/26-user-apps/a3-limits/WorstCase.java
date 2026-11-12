import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.Trans;
import bergdb.stream.FileStream;

import java.io.File;
import java.util.*;

/**
 * Part of app 3 of 024-26: transactions at the limits that make the most index nodes dirty.
 * Db's "Limits" says the limits bound what a transaction can make dirty, so that within
 * them only key or value transformations can meet the older refusals (005-17, 005-31).
 * So every transaction here, 500 keys of 111 bytes with no shared start, put or deleted,
 * on databases of each node size with many keys already, must be taken.
 *
 * Usage: java -cp bergdb-release.jar:out WorstCase DIR [keysBefore]
 */
public class WorstCase {
    public static void main(String[] a) throws Exception {
        File base = new File(a[0]);
        int before = a.length > 1 ? Integer.parseInt(a[1]) : 20000;
        int fails = 0;
        for (int ns : new int[] {8, 14, 30, 62}) {
            File dir = new File(base, "n" + ns);
            Common.rmrf(dir);
            Common.Model m = new Common.Model();
            Random r = new Random(ns);
            DbBuilder b = Db.builder().mainStream(new FileStream(dir, false)).startupDistance(400_000);
            if (ns == 8) b.maxNodeSize8(); else if (ns == 14) b.maxNodeSize14(); else if (ns == 62) b.maxNodeSize62(); else b.maxNodeSize30();
            try (Db db = b.start()) {
                // Background: keys of 111 bytes, random, so that paths are deep and disjoint.
                List<Common.K> all = new ArrayList<>();
                for (int i = 0; i < before; i += 500) {
                    Map<Common.K, byte[]> ops = new LinkedHashMap<>();
                    for (int j = 0; j < 500; j++) { byte[] k = new byte[Db.MAX_KEY_BYTES]; r.nextBytes(k); k[0] = 0x30; ops.put(new Common.K(k), new byte[0]); }
                    Common.exec(db, m, ops);
                    all.addAll(ops.keySet());
                }
                String[] kinds = {"put 500 new", "delete 500 scattered", "put 500 new with 32 MiB", "delete 500 + overwrite"};
                for (String kind : kinds) {
                    Map<Common.K, byte[]> ops = new LinkedHashMap<>();
                    if (kind.startsWith("put")) {
                        int vlen = kind.contains("32 MiB") ? (int) ((Db.MAX_TRANS_BYTES - 500L * Db.MAX_KEY_BYTES) / 500) : 0;
                        for (int j = 0; j < 500; j++) { byte[] k = new byte[Db.MAX_KEY_BYTES]; r.nextBytes(k); k[0] = 0x30; ops.put(new Common.K(k), new byte[vlen]); }
                    } else {
                        Collections.shuffle(all, r);
                        for (Common.K k : all) {
                            if (ops.size() >= 500) break;
                            if (m.latest.containsKey(k)) ops.put(k, kind.contains("overwrite") && ops.size() % 2 == 0 ? new byte[] {1} : Common.DELETED);
                        }
                    }
                    try {
                        Common.exec(db, m, ops);
                        if (kind.startsWith("put")) all.addAll(ops.keySet());
                        System.out.println("node " + ns + ": " + kind + ": taken");
                    } catch (Exception e) {
                        fails++;
                        System.out.println("FAIL node " + ns + ": " + kind + " refused within the limits: " + e);
                    }
                }
                Common.verifyFull(db, m, Long.MAX_VALUE, "node " + ns);
            }
            try (Db db = Db.builder().mainStream(new FileStream(dir, false)).start()) {
                Common.verifyFull(db, m, Long.MAX_VALUE, "node " + ns + " after restart");
            } catch (Exception e) {
                // the restart's builder has no node size: a database of another size is refused (005-50)
                DbBuilder b2 = Db.builder().mainStream(new FileStream(dir, false));
                if (ns == 8) b2.maxNodeSize8(); else if (ns == 14) b2.maxNodeSize14(); else if (ns == 62) b2.maxNodeSize62(); else b2.maxNodeSize30();
                try (Db db = b2.start()) { Common.verifyFull(db, m, Long.MAX_VALUE, "node " + ns + " after restart"); }
            }
            Common.rmrf(dir);
        }
        System.out.println(fails == 0 ? "OK WorstCase" : "FAIL WorstCase: " + fails + " refused");
        if (fails > 0) System.exit(1);
    }
}
