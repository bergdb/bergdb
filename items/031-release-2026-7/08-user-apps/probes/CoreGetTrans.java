import bergdb.core.Db;
import bergdb.core.StoredTrans;
import bergdb.core.StoredValueNode;
import bergdb.core.Trans;
import bergdb.stream.MemoryStream;
import bergdb.dag.Keys;

import java.util.*;

/**
 * 031-08: Db.getTrans(t.tpos) of an application's own commit under reclaim (2026.7: a
 * commit's record carries reclaim's step): the value nodes against the KVs that the
 * transaction put.
 *
 * Usage: java -cp bergdb-release.jar:. CoreGetTrans
 */
public class CoreGetTrans {
    public static void main(String[] a) throws Exception {
        long[] now = {17_700_000_000_000_000L};
        try (Db db = Db.builder().mainStream(new MemoryStream()).clock(() -> now[0]).start()) {
            db.setStartupDistance(100_000);
            db.setRetainDuration(10_000_000L);           // 1 s
            Random r = new Random(1);
            int more = 0, copies = 0, commits = 0;
            for (int i = 0; i < 3000; i++) {
                now[0] += 2_000_000;                      // 0.2 s
                Trans.Builder b = db.trans();
                Set<String> mine = new HashSet<>();
                for (int j = 0; j < 20; j++) {
                    byte[] k = {0x10, (byte) r.nextInt(256), (byte) r.nextInt(8)};
                    byte[] v = new byte[r.nextInt(400)];
                    r.nextBytes(v);
                    b.put(k, v);
                    mine.add(Arrays.toString(k));
                }
                Trans t = b.build();
                db.execute(t);
                commits++;
                StoredTrans st = db.getTrans(t.tpos);
                List<StoredValueNode> vns = st.getValueNodes();
                int others = 0, marked = 0;
                for (StoredValueNode vn : vns) {
                    String k = Arrays.toString(Keys.toBytes(vn.getKey()));
                    if (!mine.contains(k)) { others++; if (vn.isCopy()) marked++; }
                }
                if (others > 0) {
                    more++;
                    copies += marked;
                    if (more <= 3) System.out.println("commit " + i + ": getTrans(t.tpos) lists " + vns.size() + " value nodes for "
                            + mine.size() + " KVs put; " + others + " others, " + marked + " of them with the copy mark; st.tt "
                            + (st.tt == t.tt ? "== t.tt" : st.tt + " != t.tt " + t.tt));
                }
            }
            System.out.println(more + " of " + commits + " commits list value nodes that they did not put (" + copies + " with the copy mark)");
        }
    }
}
