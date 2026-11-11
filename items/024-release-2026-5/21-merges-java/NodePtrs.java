package bergdb.core;

import bergdb.common.Bytes;

/** 024-21: a key node's pointers in a CorruptStreamTester original: NodePtrs CONFIG SEED TPOS OFFSET. */
public class NodePtrs {
    public static void main(String[] a) {
        CorruptStreamTester.Config c = null;
        for (CorruptStreamTester.Config x : new CorruptStreamTester.Config[] {
                CorruptStreamTester.ALL, CorruptStreamTester.META, CorruptStreamTester.LONG,
                CorruptStreamTester.TAKE}) {
            if (x.name.equals(a[0])) c = x;
        }
        CorruptStreamTester.Original o = CorruptStreamTester.write(c, Long.parseLong(a[1]));
        CorruptStreamTester.Record r = o.recordAt(Long.parseLong(a[2]));
        int off = Integer.parseInt(a[3]);
        int size = Bytes.bytesToIntLE(r.bytes, off);
        int n = (size - 32) / 16;
        System.out.println("node at " + a[2] + "+" + off + " size " + size + " type " + r.bytes[off + 4]
                + " flags16 " + r.bytes[off + 16] + " id " + Bytes.bytesToLongLE(r.bytes, off + 24) + " klongs " + n);
        for (int i = 0; i < n; i++) {
            long k = Bytes.bytesToLongLE(r.bytes, off + 32 + 8 * i);
            long p = Bytes.bytesToLongLE(r.bytes, off + 32 + 8 * n + 8 * i);
            System.out.println("  " + i + " klong " + Long.toHexString(k) + " pos " + p + " (byte " + (32 + 8 * n + 8 * i) + ")");
        }
    }
}
