package bergdb.core;

import java.io.File;
import java.util.*;

import bergdb.dag.*;

/**
 * bergdb 028-86's probe: G4's run of CountGates (the twin, n = 0, or the emptied database),
 * then the key nodes that the scan of every key follows, each with its KEY klongs: deleted
 * (D), shadowed (S) or live (L); the dead klongs of all after each of the drive's last 1,000
 * transactions (the last R) and every 1,000th, and the most of one node at any of them.
 * Args: label n [drive] [dir]. From java/, after build.sh:
 *   javac -d PROBE -cp build/bergdb.jar:build/stress G4Dump.java
 *   java -Xmx4g -cp PROBE:build/bergdb.jar:build/stress bergdb.core.G4Dump g4-emptied 1000000
 *   java -Xmx4g -cp PROBE:build/bergdb.jar:build/stress bergdb.core.G4Dump g4-twin 0
 */
public class G4Dump {
    public static void main(String[] a) throws Exception {
        String label = a[0];
        int nn = Integer.parseInt(a[1]);
        CountGates x = new CountGates();
        x.n = nn;
        x.vs = 100;
        x.dt = 10000;
        x.retain = 1 * CountGates.SEC;
        x.base = new File(a.length > 3 ? a[3] : "build/g4dump-data");
        int rTx = (int) (x.retain / x.dt);
        int drive = a.length > 2 ? Integer.parseInt(a[2]) : 40 * rTx;
        CountGates.Run r = x.new Run(label, 100000);
        r.db.setRetainDuration(x.retain);
        r.exec(r.db.trans().put("/a.txt", CountGates.HELLO), "create");
        if (nn > 0) {
            x.fill(r, CountGates.range(0, nn), 100, "fill");
            for (int k = 0; k < nn; ) {
                Trans.Builder b = r.db.trans();
                for (int j = 0; j < 100 && k < nn; j++, k++) b.delete(CountGates.key(k));
                r.exec(b, "delete");
            }
            System.out.println(label + " filled and deleted " + nn + "; " + r.state());
        }
        long[] dead = new long[drive + 1];
        for (int k = 1; k <= drive; k++) {
            r.exec(r.db.trans().put("/a.txt", CountGates.value(1000, k)), "drive");
            if (k > drive - 1000 || k % 1000 == 0) {
                dead[k] = count(r, false);
            }
        }
        System.out.println(label + " drive " + drive + "; " + r.state());
        long most = 0, least = Long.MAX_VALUE, sum = 0;
        for (int k = drive - 999; k <= drive; k++) {
            most = Math.max(most, dead[k]);
            least = Math.min(least, dead[k]);
            sum += dead[k];
        }
        System.out.println(label + " last R (1000 transactions): dead least " + least + " mean "
                + (sum / 1000.0) + " most " + most + "; the most dead klongs of one node at any "
                + "sample " + nodeMost);
        StringBuilder all = new StringBuilder();
        for (int k = drive - 999; k <= drive; k++) all.append(dead[k]).append(' ');
        System.out.println(label + " lastR " + all);
        StringBuilder sb = new StringBuilder();
        for (int k = drive - 299; k <= drive; k++) sb.append(dead[k]).append(k % 50 == 0 ? "\n" : " ");
        System.out.println(label + " dead klongs after each of the last 300 transactions:\n" + sb);
        sb = new StringBuilder();
        for (int k = 1000; k <= drive; k += 1000) sb.append(dead[k]).append(' ');
        System.out.println(label + " dead klongs every 1000th transaction: " + sb);
        count(r, true);
        r.close();
    }

    static long nodeMost;

    static long count(CountGates.Run r, boolean print) {
        synchronized (r.db.internal().getWriteLock()) {
            final HashSet<Long> ids = new HashSet<Long>();
            final long[] tot = new long[3];
            final StringBuilder sb = new StringBuilder();
            final PointerFollower inner = r.db.internal().nodeCollection().maintenance();
            PointerFollower f = new PointerFollower() {
                public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
                    Node n = inner.followPointer(predecessor, pointerIndex, op);
                    if (n instanceof KeyNode && ids.add(n.getId())) {
                        KeyNode kn = (KeyNode) n;
                        int sz = kn.getSize();
                        long del = kn.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
                        int keys = 0, dl = 0, sh = 0;
                        StringBuilder ks = new StringBuilder();
                        for (int i = 0; i < sz; i++) {
                            long k = kn.getKlong(i);
                            if (!Klong.isKey(k)) continue;
                            keys++;
                            String s = Klong.getKeyString(k);
                            if (Klong.isDeleted(del, i)) { dl++; ks.append(" D:").append(s); continue; }
                            long cv = Klong.getCompareValue(k);
                            boolean shadowed = false;
                            for (int j = i + 1; j < sz && !shadowed; j++) {
                                long k2 = kn.getKlong(j);
                                shadowed = Klong.isKey(k2) && Klong.getCompareValue(k2) == cv;
                            }
                            if (shadowed) { sh++; ks.append(" S:").append(s); }
                            else ks.append(" L:").append(s);
                        }
                        nodeMost = Math.max(nodeMost, dl + sh);
                        tot[0] += keys;
                        tot[1] += dl + sh;
                        sb.append(String.format("  node %d size %d segleaf=%s keys=%d deleted=%d shadowed=%d:%s%n",
                                kn.getId(), sz, kn.isSegmentLeaf(), keys, dl, sh, ks));
                    }
                    return n;
                }
            };
            GetMany g = r.db.newGetMany();
            g.gd.pointerFollower = f;
            r.db.getMany(g);
            if (print) {
                System.out.println("nodes " + ids.size() + " keyKlongs " + tot[0] + " dead " + tot[1]);
                System.out.print(sb);
            }
            return tot[1];
        }
    }
}
