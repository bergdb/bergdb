package bergdb.core;

import java.lang.reflect.Method;
import java.util.*;

import bergdb.common.Bytes;
import bergdb.dag.Klong;
import bergdb.storage.RecoverableStream;

/** 024-21: find again the copies of CorruptStreamTester's pinned tests in a new stream. */
public class CstFind {
    static Method nodeCopy;

    static CorruptStreamTester.Copy nc(CorruptStreamTester.Original o, CorruptStreamTester.Record r,
            int[] node, byte[] nb, String what) throws Exception {
        return (CorruptStreamTester.Copy) nodeCopy.invoke(null, o, r, node, nb, what);
    }

    public static void main(String[] a) throws Exception {
        nodeCopy = CorruptStreamTester.class.getDeclaredMethod("nodeCopy",
                CorruptStreamTester.Original.class, CorruptStreamTester.Record.class, int[].class,
                byte[].class, String.class);
        nodeCopy.setAccessible(true);
        int x0 = Integer.parseInt(a[1]), x1 = Integer.parseInt(a[2]);
        for (int x = x0; x <= x1; x++) {
            long seed = x * 31L + CorruptStreamTester.LONG.name.hashCode();
            System.out.println("seed X" + x + " = " + seed);
            if (one(a[0], seed)) return;
        }
    }

    static boolean one(String mode, long seed) throws Exception {
        CorruptStreamTester.Original o = CorruptStreamTester.write(CorruptStreamTester.LONG, seed);
        if (mode.equals("t12")) {
            List<CorruptStreamTester.Record> recs = new ArrayList<CorruptStreamTester.Record>(o.records);
            Collections.reverse(recs);
            int found = 0;
            for (CorruptStreamTester.Record r : recs) {
                for (int[] n : r.nodes) {
                    if (r.bytes[n[0] + 4] != 20) continue;
                    int k = (n[1] - 32) / 16;
                    List<Integer> times = new ArrayList<Integer>();
                    for (int i = 0; i < k; i++) {
                        if (Klong.isTime(Bytes.bytesToLongLE(r.bytes, n[0] + 32 + 8 * i))) times.add(i);
                    }
                    if (times.size() < 3 || times.get(0) != 0) continue;
                    int last = times.get(times.size() - 1);
                    long p0 = RecoverableStream.getSpos(r.tpos, n[0] + 34);
                    long p1 = RecoverableStream.getSpos(r.tpos, n[0] + 32 + 8 * last + 2);
                    List<CorruptStreamTester.Copy> cs = new ArrayList<CorruptStreamTester.Copy>();
                    CorruptStreamTester.flips(o, Arrays.asList((int) p0, (int) p1), new int[] {0xff}, cs);
                    byte[] nb = Arrays.copyOfRange(r.bytes, n[0], n[0] + n[1]);
                    Bytes.intToBytesLE(0x7ffffff8, nb, 36);
                    cs.add(nc(o, r, n, nb, "int " + 0x7ffffff8 + " at its byte 36"));
                    String[] m = new String[3];
                    boolean ok = true;
                    for (int i = 0; i < 3; i++) {
                        CorruptStreamTester.Outcome out = CorruptStreamTester.check(o, cs.get(i));
                        m[i] = CorruptStreamTester.refusal(o, cs.get(i));
                        ok &= out.failure == null && out.kind.startsWith("refused");
                    }
                    boolean strict = !"loose".equals(System.getProperty("mode"));
                    if (!strict || (ok && m[0] != null && m[0].startsWith("Time not increasing") && m[1] != null
                            && m[1].contains("before the startup section") && m[2] != null
                            && m[2].startsWith("Bad spos of pointer 0"))) {
                        System.out.println("CANDIDATE rec " + r.tpos + " node " + n[0] + " size " + n[1]
                                + " flips " + p0 + " " + p1 + "\n  " + m[0] + "\n  " + m[1] + "\n  " + m[2]);
                        if (++found >= 1) return true;
                    }
                }
            }
            return false;
        } else if (mode.equals("cyc2")) {
            for (CorruptStreamTester.Record r : o.records) {
                int[] n = r.nodes.get(0);
                if (n[0] != 32 || r.bytes[n[0] + 4] != 20) continue;
                int k = (n[1] - 32) / 16;
                for (int i = 0; i < k; i++) {
                    long pos = Bytes.bytesToLongLE(r.bytes, n[0] + 32 + 8 * k + 8 * i);
                    long klong = Bytes.bytesToLongLE(r.bytes, n[0] + 32 + 8 * i);
                    if (pos <= 0 || pos >= r.tpos || (pos & 7) != 0) continue;
                    byte[] nb = Arrays.copyOfRange(r.bytes, n[0], n[0] + n[1]);
                    Bytes.longToBytesLE(pos, nb, 8);
                    CorruptStreamTester.Copy c = nc(o, r, n, nb, "prevPos set to " + pos);
                    CorruptStreamTester.Results res = new CorruptStreamTester.Results();
                    CorruptStreamTester.checkAll(o, Arrays.asList(c), 1, 60, res);
                    String key = res.counts.isEmpty() ? "" : res.counts.keySet().iterator().next();
                    if (key.startsWith("node: read failed")) {
                        System.out.println("CANDIDATE rec " + r.tpos + " node 32 pointer " + i + " pos " + pos + ": " + res.counts);
                        return true;
                    }
                }
            }
            return false;
        } else {
            for (CorruptStreamTester.Record r : o.records) {
                int[] n = r.nodes.get(0);
                if (n[0] != 32 || r.bytes[n[0] + 4] != 20) continue;
                byte[] nb = Arrays.copyOfRange(r.bytes, n[0], n[0] + n[1]);
                nb[8] ^= (byte) 0x80;
                CorruptStreamTester.Copy c = nc(o, r, n, nb, "xor 128 at its byte 8");
                CorruptStreamTester.Results res = new CorruptStreamTester.Results();
                CorruptStreamTester.checkAll(o, Arrays.asList(c), 1, 60, res);
                String k = res.counts.isEmpty() ? "" : res.counts.keySet().iterator().next();
                if (k.startsWith("node: read failed")) {
                    System.out.println("CANDIDATE rec " + r.tpos + ": " + res.counts);
                    return true;
                }
            }
        }
        return false;
    }
}
