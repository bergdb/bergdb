package bergdb.core;

import bergdb.common.Bytes;

/** 024-21: the records and nodes of a CorruptStreamTester original: NodeMap CONFIG SEED. */
public class NodeMap {
    public static void main(String[] a) {
        CorruptStreamTester.Config c = null;
        for (CorruptStreamTester.Config x : new CorruptStreamTester.Config[] {
                CorruptStreamTester.ALL, CorruptStreamTester.META, CorruptStreamTester.LONG,
                CorruptStreamTester.TAKE}) {
            if (x.name.equals(a[0])) c = x;
        }
        CorruptStreamTester.Original o = CorruptStreamTester.write(c, Long.parseLong(a[1]));
        int t = 0;
        for (CorruptStreamTester.Record r : o.records) {
            StringBuilder sb = new StringBuilder();
            for (int[] n : r.nodes) {
                byte type = r.bytes[n[0] + 4];
                sb.append(" [" + n[0] + ":" + n[1] + " t" + type);
                if (n[1] >= 32 && type == 20) {
                    sb.append(" id" + Bytes.bytesToLongLE(r.bytes, n[0] + 24) + " prev"
                            + Bytes.bytesToLongLE(r.bytes, n[0] + 8));
                }
                sb.append("]");
            }
            System.out.println("rec " + (t++) + " tpos " + r.tpos + " size " + r.size + sb);
        }
    }
}
